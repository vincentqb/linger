"""Live virtual-terminal ownership checks.

The probe is an ordinary foreground PTY program, not a shell detector. It puts
its tty in raw mode, emits DA1, and records exactly what it reads back. The
same probe runs with zero, one, and two presentation clients.
"""

import fcntl
import json
import os
import pathlib
import pty
import select
import shutil
import struct
import subprocess
import sys
import termios
import time
import tty

ROOT = pathlib.Path(__file__).resolve().parent.parent
LINGER = str(ROOT / ".lake/build/bin/linger")
DA1_QUERY = b"\x1b[c"
DA1_REPLY = b"\x1b[?1;2c"


def probe_main(result_path, ready_path, trigger_path):
    """Child side: ask one terminal query and persist the observed reply."""
    try:
        tty.setraw(0)
        pathlib.Path(ready_path).write_text("ready")
        deadline = time.time() + 8
        while not os.path.exists(trigger_path) and time.time() < deadline:
            time.sleep(0.01)
        if not os.path.exists(trigger_path):
            raise RuntimeError("trigger timeout")

        query = bytes.fromhex(os.environ["PROBE_QUERY_HEX"]) \
            if os.environ.get("PROBE_QUERY_HEX") else DA1_QUERY
        os.write(1, query)
        reply = b""
        deadline = time.time() + 2
        while time.time() < deadline:
            readable, _, _ = select.select([0], [], [], 0.1)
            if readable:
                chunk = os.read(0, 4096)
                if not chunk:
                    break
                reply += chunk
            elif reply:
                # One quiet interval after the reply catches duplicate writes.
                break

        pathlib.Path(result_path).write_text(json.dumps({
            "reply": list(reply),
            "TERM": os.environ.get("TERM"),
            "TERM_PROGRAM": os.environ.get("TERM_PROGRAM"),
            "TERM_PROGRAM_VERSION": os.environ.get("TERM_PROGRAM_VERSION"),
        }))
        os.write(1, b"\r\nPROBE-DONE\r\n")
        time.sleep(0.25)
        return 0
    except Exception as exc:  # surfaced to the parent through the result file
        pathlib.Path(result_path).write_text(json.dumps({"error": repr(exc)}))
        return 1


if len(sys.argv) == 5 and sys.argv[1] == "--probe":
    sys.exit(probe_main(sys.argv[2], sys.argv[3], sys.argv[4]))


LDIR = os.environ.get("LINGER_TEST_DIR", f"/tmp/linger-terminal-{os.getpid()}")
os.makedirs(LDIR, exist_ok=True)
BASE_ENV = dict(os.environ, LINGER_DIR=LDIR, SHELL="/bin/sh")


def wait_for(path, timeout=8):
    deadline = time.time() + timeout
    while time.time() < deadline:
        if os.path.exists(path):
            return True
        time.sleep(0.03)
    return False


def drain(fd, secs):
    out = b""
    deadline = time.time() + secs
    while time.time() < deadline:
        readable, _, _ = select.select([fd], [], [], 0.08)
        if readable:
            try:
                chunk = os.read(fd, 65536)
            except OSError:
                break
            if not chunk:
                break
            out += chunk
    return out


def spawn_attach(name, env):
    pid, fd = pty.fork()
    if pid == 0:
        os.execve(LINGER, [LINGER, "attach", name], env)
    fcntl.ioctl(fd, termios.TIOCSWINSZ, struct.pack("HHHH", 24, 80, 0, 0))
    return pid, fd


def stop_client(pid, fd):
    try:
        os.close(fd)
    except OSError:
        pass
    try:
        os.waitpid(pid, 0)
    except ChildProcessError:
        pass


def run_probe_case(index, clients, inherited_term, query_hex=None):
    name = f"term-{index}-{clients}"
    case = pathlib.Path(LDIR) / name
    case.mkdir(exist_ok=True)
    result = str(case / "result.json")
    ready = str(case / "ready")
    trigger = str(case / "trigger")

    env = dict(BASE_ENV, TERM_PROGRAM="inherited-program",
               TERM_PROGRAM_VERSION="9.9.9")
    if query_hex:
        env["PROBE_QUERY_HEX"] = query_hex
    if inherited_term is None:
        env.pop("TERM", None)
    else:
        env["TERM"] = inherited_term

    daemon = subprocess.Popen(
        [LINGER, "__daemon", name, str(ROOT), sys.executable, __file__,
         "--probe", result, ready, trigger],
        env=env, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
    )
    attached = []
    try:
        if not wait_for(ready):
            return {"error": "probe did not become ready", "client_out": []}

        for _ in range(clients):
            pid, fd = spawn_attach(name, BASE_ENV)
            attached.append((pid, fd))
            time.sleep(0.35)
            drain(fd, 0.15)  # discard initial restore

        pathlib.Path(trigger).write_text("go")
        if not wait_for(result):
            return {"error": "probe did not answer", "client_out": []}
        data = json.loads(pathlib.Path(result).read_text())

        client_out = []
        for _, fd in attached:
            client_out.append(drain(fd, 1.2))
        data["client_out"] = client_out
        try:
            daemon.wait(timeout=5)
        except subprocess.TimeoutExpired:
            data["daemon_timeout"] = True
        return data
    finally:
        if daemon.poll() is None:
            daemon.terminate()
            try:
                daemon.wait(timeout=2)
            except subprocess.TimeoutExpired:
                daemon.kill()
        for pid, fd in attached:
            stop_client(pid, fd)


def expect(condition, name):
    print(("PASS" if condition else "FAIL"), name)
    return 0 if condition else 1


fails = 0
cases = [
    run_probe_case(0, 0, None),
    run_probe_case(1, 1, "xterm-kitty"),
    run_probe_case(2, 2, "screen"),
]

for clients, data in enumerate(cases):
    reply = bytes(data.get("reply", []))
    fails += expect(reply == DA1_REPLY,
                    f"DA1 progresses with {clients} client(s), exactly one reply")
    fails += expect(
        data.get("TERM") == "xterm-256color" and
        data.get("TERM_PROGRAM") == "linger" and
        data.get("TERM_PROGRAM_VERSION") == "0.1.0",
        f"stable child terminal profile with {clients} client(s)",
    )
    if clients:
        outs = data.get("client_out", [])
        fails += expect(
            len(outs) == clients and all(b"PROBE-DONE" in out for out in outs) and
            all(DA1_QUERY not in out for out in outs),
            f"owned query hidden while ordinary output reaches {clients} client(s)",
        )

fails += expect(
    [bytes(case.get("reply", [])) for case in cases] == [DA1_REPLY] * 3,
    "reply stream is roster-independent",
)

# Original regression only: interactive fish must consume a command before any
# client attaches. The marker is a file, not echoed terminal output, so startup
# echo cannot make this pass accidentally.
# XTGETTCAP reply injection: linger writes query replies into the child's own
# input, and the request is untrusted child output. A raw echo of a payload
# carrying a CR let a `cat` of a hostile file run a command. The reply must
# carry no line terminator. Payload: 54 (hex '5','4') CR ; i d > x CR — the CRs
# are the injection primitive.
evil_hex = "1b502b7135340d3b69643e780d1b5c"
inj = run_probe_case(9, 0, None, query_hex=evil_hex)
inj_reply = bytes(inj.get("reply", []))
fails += expect(inj_reply != b"" and 0x0D not in inj_reply and 0x0A not in inj_reply,
                "XTGETTCAP reply carries no CR/LF (no command injection)")
# non-vacuity: linger did answer the query (a filtered negative reply came back)
fails += expect(inj_reply.startswith(b"\x1bP0+r"),
                "XTGETTCAP still answered (filtered negative reply reached the child)")

fish = shutil.which("fish")
if fish:
    marker = pathlib.Path(LDIR) / "fish-command-ran"
    fish_env = dict(BASE_ENV, SHELL=fish, TERM="inherited-fish-term")
    subprocess.run(
        [LINGER, "run", "fish-regression", "printf", "ok", ">", str(marker)],
        env=fish_env, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        timeout=10,
    )
    fish_ok = wait_for(str(marker), timeout=6)
    fails += expect(fish_ok, "fish regression: detached command executes before attach")
    subprocess.run([LINGER, "kill", "fish-regression"], env=fish_env,
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=10)
else:
    print("PASS fish regression skipped (fish not installed)")

print(f"FAILURES: {fails}")
sys.exit(1 if fails else 0)
