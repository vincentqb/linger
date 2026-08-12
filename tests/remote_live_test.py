"""Live remote test against a REAL second machine over real ssh.

Unlike tests/remote_test.py (fake ssh on PATH, hermetic, in the gate),
this needs an actual reachable host running a real `lzmx`. Not part of
e2e.sh. Usage:

    LZMX_REMOTE=gpu2 python3 tests/remote_live_test.py

Assumes the remote has `lzmx` on its non-interactive PATH and two live
sessions named `alpha` and `beta` (the harness does not create them —
the driving session sets them up, see the surrounding transcript).
"""
import os, pty, time, select, subprocess, sys, fcntl, struct, termios, pathlib, re

ROOT = pathlib.Path(__file__).resolve().parent.parent
LZMX = str(ROOT / '.lake/build/bin/lzmx')
HOST = os.environ.get('LZMX_REMOTE', 'gpu2')
LDIR = os.environ.get('LZMX_TEST_DIR', '/tmp/lzmx-live-' + str(os.getpid()))
os.makedirs(LDIR, exist_ok=True)

# lzmx shells out to `ssh <host> ...`; a wedged local ssh-agent would hang
# that child, so run with the agent env removed (equivalent to
# IdentityAgent=none). The host's key is taken from ~/.ssh/config.
ENV = {k: v for k, v in os.environ.items() if k != 'SSH_AUTH_SOCK'}
ENV.update(LZMX_DIR=LDIR, SHELL='/bin/sh')

def spawn_tui():
    pid, fd = pty.fork()
    if pid == 0:
        os.execve(LZMX, [LZMX, '-r', HOST], ENV)   # remote via flag, not env
    fcntl.ioctl(fd, termios.TIOCSWINSZ, struct.pack('HHHH', 30, 110, 0, 0))
    return pid, fd

def drain(fd, secs):
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

def plain(bs):
    return re.sub(r'\x1b\[[0-9;?]*[A-Za-z]', '', bs.decode('utf-8', errors='replace'))

def expect(cond, name):
    print(('PASS' if cond else 'FAIL'), name)
    return 0 if cond else 1

fails = 0
print(f'driving local lzmx TUI against real remote: {HOST}')

# TUI lists the remote's sessions over real ssh
pid, fd = spawn_tui()
screen = plain(drain(fd, 6.0))   # first gather runs `ssh HOST lzmx list --porcelain`
fails += expect(f'alpha@{HOST}' in screen, f'remote session alpha@{HOST} listed over real ssh')
fails += expect(f'beta@{HOST}' in screen, f'remote session beta@{HOST} listed over real ssh')

# filter to alpha and confirm the preview came from `ssh HOST lzmx history alpha`
os.write(fd, b'alph')
screen = plain(drain(fd, 5.0))
fails += expect('hello-from-alpha-on-gpu2' in screen,
                'remote preview streamed real scrollback over ssh')

# enter -> execs `ssh -t HOST lzmx attach alpha`; we land in the real remote shell
os.write(fd, b'\r')
time.sleep(3.0)
drain(fd, 2.0)
os.write(fd, b'echo REMOTE-PWD-$(hostname)\r')
out = plain(drain(fd, 4.0))
fails += expect('REMOTE-PWD-ip-' in out, 'attach dropped into the real remote shell (ran a command there)')

# detach from the remote session (ctrl-\), leaving it alive on the remote
os.write(fd, b'\x1c')
time.sleep(1.5)
try:
    os.close(fd)
except OSError:
    pass

# the remote session must still be alive after we detached
r = subprocess.run(['ssh', '-o', 'BatchMode=yes', '-o', 'ConnectTimeout=5', HOST,
                    'lzmx list --porcelain'],
                   env=ENV, capture_output=True, text=True)
fails += expect('name\talpha' in r.stdout, 'remote session survived detach (still listed)')

print('FAILURES:', fails)
sys.exit(1 if fails else 0)
