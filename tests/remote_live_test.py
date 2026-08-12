"""Live remote test against a REAL second machine over real ssh.

Unlike tests/remote_test.py (fake ssh on PATH, hermetic, in the gate),
this needs an actual reachable host running a real `lzmx`. Not part of
e2e.sh. Usage:

    LZMX_REMOTE=gpu2 python3 tests/remote_live_test.py

Assumes the remote has `lzmx` on its non-interactive PATH and two live
sessions named `alpha` and `beta`.
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


def plain(bs):
    return re.sub(r'\x1b\[[0-9;?]*[A-Za-z]', '', bs.decode('utf-8', errors='replace'))


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


def expect(cond, name):
    print(('PASS' if cond else 'FAIL'), name)
    return 0 if cond else 1


fails = 0
print(f'driving local overview + remote attach against real host: {HOST}')

# the overview folds the remote's sessions in over real ssh
r = subprocess.run([LZMX, '-r', HOST], env=ENV, stdin=subprocess.DEVNULL,
                   capture_output=True, text=True, timeout=20)
fails += expect(f'alpha@{HOST}' in r.stdout, f'remote alpha@{HOST} listed over real ssh')
fails += expect(f'beta@{HOST}' in r.stdout, f'remote beta@{HOST} listed over real ssh')

# `attach alpha@HOST` execs `ssh -t HOST lzmx attach alpha` -> real remote shell
pid, fd = pty.fork()
if pid == 0:
    os.execve(LZMX, [LZMX, 'attach', f'alpha@{HOST}'], ENV)
fcntl.ioctl(fd, termios.TIOCSWINSZ, struct.pack('HHHH', 30, 110, 0, 0))
time.sleep(3.0)
drain(fd, 2.0)
os.write(fd, b'echo REMOTE-HOST-$(hostname)\r')
out = plain(drain(fd, 5.0))
fails += expect('REMOTE-HOST-' in out, 'attach name@host dropped into the real remote shell')

# detach from the remote session (ctrl-\), leaving it alive on the remote
os.write(fd, b'\x1c')
time.sleep(1.5)
try:
    os.close(fd)
except OSError:
    pass

# the remote session must still be alive after we detached
r = subprocess.run(['ssh', '-o', 'BatchMode=yes', '-o', 'ConnectTimeout=5', HOST,
                    'lzmx ls --porcelain'],
                   env=ENV, capture_output=True, text=True)
fails += expect('name\talpha' in r.stdout, 'remote session survived detach (still listed)')

print('FAILURES:', fails)
sys.exit(1 if fails else 0)
