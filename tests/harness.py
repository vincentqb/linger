"""Shared pty-suite harness: the helpers every e2e suite was re-deriving.

WHY THIS EXISTS. Nine suites each carried their own copy of the same six things
— the binary path, the `LINGER_DIR`/`SHELL` env, `drain`, `expect`, a one-shot
`linger(...)` runner, and the `info`/`field` porcelain readers. They had already
drifted: three spellings of the final line, `timeout=15` on some subprocess calls
and not others, and two suites that read a porcelain field with subtly different
loops. `tests/procs.py` set the precedent that a shared test module is house-legal;
this is the rest of it.

`spawn` is the one genuinely new thing, and it fixes a race the copies all had:
`pty.fork()` then `ioctl(TIOCSWINSZ)` sets the window size *after* the child may
already have read it, so a client's reported geometry was whatever won. Setting
the slave's size before the fork removes the race — which matters the moment a
test's subject IS the reported geometry (`watch_test.py`).

MIGRATION STATUS (pin-the-gaps item 1). `watch_test.py` uses this; the nine older
suites still carry their copies and are deliberately untouched — porting them is a
ten-file diff across a green gate, which the one-item-in-flight rule in AGENTS.md
says not to fold into another spec's step. It is now cheap and safe to do, because
every suite has a check-count floor in `tests/e2e.sh`: a port that silently drops
an assertion fails the gate instead of passing quietly. Do it as its own commit.
"""
import fcntl
import os
import pathlib
import select
import struct
import subprocess
import termios
import time

LINGER = str(pathlib.Path(__file__).resolve().parent.parent / '.lake/build/bin/linger')

# One-shot subprocess timeout. Every call goes through it, so a wedged daemon
# fails the suite instead of hanging the gate.
TIMEOUT = 15


def make_env(slug):
    """A private `LINGER_DIR` for one suite, plus the env every child needs.

    Per-suite and pid-suffixed so two suites — or a suite and the developer's own
    sessions — can never see each other's sockets or checkpoints.
    """
    ldir = os.environ.get('LINGER_TEST_DIR', f'/tmp/linger-{slug}-{os.getpid()}')
    os.makedirs(ldir, exist_ok=True)
    return ldir, dict(os.environ, LINGER_DIR=ldir, SHELL='/bin/sh')


def spawn(env, argv, rows=24, cols=80):
    """`linger <argv>` on a pty whose winsize is set BEFORE exec.

    Returns `(pid, master_fd)`. The pre-fork `TIOCSWINSZ` is the point: the
    fork-then-ioctl idiom races the child's own startup `winsizeGet`, which is
    invisible until a test asserts on the geometry a client reported.
    """
    mfd, sfd = os.openpty()
    fcntl.ioctl(sfd, termios.TIOCSWINSZ, struct.pack('HHHH', rows, cols, 0, 0))
    pid = os.fork()
    if pid == 0:
        os.close(mfd)
        os.setsid()
        fcntl.ioctl(sfd, termios.TIOCSCTTY, 0)
        os.dup2(sfd, 0)
        os.dup2(sfd, 1)
        os.dup2(sfd, 2)
        if sfd > 2:
            os.close(sfd)
        os.execve(LINGER, [LINGER, *argv], env)
        os._exit(127)
    os.close(sfd)
    return pid, mfd


def resize(fd, rows, cols):
    """Resize a live pty, as a user dragging their window would."""
    fcntl.ioctl(fd, termios.TIOCSWINSZ, struct.pack('HHHH', rows, cols, 0, 0))


def drain(fd, secs):
    """Everything readable from `fd` within a wall-clock window.

    Returns early on EOF or error, so a dead client costs the window once rather
    than every call.
    """
    out = b''
    end = time.time() + secs
    while time.time() < end:
        r, _, _ = select.select([fd], [], [], 0.1)
        if r:
            try:
                b = os.read(fd, 65536)
            except OSError:
                break
            if not b:
                break
            out += b
    return out


def detach(fd):
    """Send the ctrl-\\ detach key, tolerating an already-closed client."""
    try:
        os.write(fd, b'\x1c')
    except OSError:
        pass


def bye(pid, fd, send_detach=True):
    """Retire a pty client: detach, close, reap. Idempotent and never raises."""
    if send_detach:
        detach(fd)
        time.sleep(0.6)
    try:
        os.close(fd)
    except OSError:
        pass
    try:
        os.waitpid(pid, 0)
    except ChildProcessError:
        pass


def cli(env):
    """The one-shot verb helpers, bound to one suite's env.

    Returns `(linger, info, field)`:
      * `linger(*args)` — a `CompletedProcess` with **bytes** stdout/stderr.
      * `info(name)`    — `linger info <name>` as a dict of its k/v records.
      * `field(n, k)`   — one porcelain field of one session's `ls` row.
    """
    def linger(*args):
        return subprocess.run([LINGER, *args], env=env, capture_output=True,
                              timeout=TIMEOUT)

    def info(name):
        d = {}
        for line in linger('info', name).stdout.decode().splitlines():
            if '\t' in line:
                k, v = line.split('\t', 1)
                d[k] = v
        return d

    def field(name, key):
        cur = None
        for line in linger('ls', '--porcelain').stdout.decode().splitlines():
            if line.startswith('name\t'):
                cur = line.split('\t', 1)[1]
            elif cur == name and line.startswith(key + '\t'):
                return line.split('\t', 1)[1]
        return None

    return linger, info, field


def expect(cond, name):
    """Print one check's verdict; return 1 on failure so callers can sum.

    `e2e.sh` reads both the `FAILURES: n` last line AND the count of these
    `PASS `/`FAIL ` lines against a per-suite floor, so the leading token and the
    space after it are load-bearing — do not reformat.
    """
    print(('PASS' if cond else 'FAIL'), name)
    return 0 if cond else 1
