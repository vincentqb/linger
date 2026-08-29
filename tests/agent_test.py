"""Agent-verbs e2e (specs/agent-cli.md): see and drive a session one-shot.

Step 1: `linger info <name>` and the observability fields -- geometry + cursor
(what `capture` needs), `alt`, and `outseq` (the change cursor: "look again
only when it moved"). Pinned against the rendered porcelain, end to end.
"""
import os, pty, time, subprocess, fcntl, struct, termios, sys, pathlib

LINGER = str(pathlib.Path(__file__).resolve().parent.parent / '.lake/build/bin/linger')
LDIR = os.environ.get('LINGER_TEST_DIR', '/tmp/linger-agent-' + str(os.getpid()))
os.makedirs(LDIR, exist_ok=True)
ENV = dict(os.environ, LINGER_DIR=LDIR, SHELL='/bin/sh')


def linger(*args, **kw):
    return subprocess.run([LINGER, *args], env=ENV, capture_output=True,
                          timeout=15, **kw)


def info(name):
    """`linger info <name>` as a dict (one session's k\\tv records)."""
    out = linger('info', name).stdout.decode()
    d = {}
    for line in out.splitlines():
        if '\t' in line:
            k, v = line.split('\t', 1)
            d[k] = v
    return d


def expect(cond, label):
    print(('PASS' if cond else 'FAIL'), label)
    return 0 if cond else 1


fails = 0

# -- Step 1: info -------------------------------------------------------------

linger('run', 'ag', 'true')          # upsert a headless session (default shell)
time.sleep(1.5)

i = info('ag')
fails += expect(i.get('cols') == '80' and i.get('rows') == '24',
                'headless session reports the 80x24 default size')
fails += expect(i.get('alt') == 'false', 'alt is false outside a full-screen app')
fails += expect(i.get('cursorx', '').isdigit() and i.get('cursory', '').isdigit(),
                'cursor position is reported as numbers')
fails += expect(i.get('outseq', '').isdigit(), 'outseq is reported as a number')

# outseq moves when output happens -- the change cursor
before = int(info('ag').get('outseq', '0'))
linger('send', 'ag', 'echo', 'MOVED')
time.sleep(1.2)
after = int(info('ag').get('outseq', '0'))
fails += expect(after > before, 'outseq increases after output')

# geometry follows an attached terminal
pid, fd = pty.fork()
if pid == 0:
    os.execve(LINGER, [LINGER, 'attach', 'ag'], ENV)
fcntl.ioctl(fd, termios.TIOCSWINSZ, struct.pack('HHHH', 30, 100, 0, 0))
time.sleep(1.5)
fails += expect(info('ag').get('cols') == '100' and info('ag').get('rows') == '30',
                'info reflects the attached terminal size')
os.write(fd, b'\x1c')          # detach
time.sleep(0.8)
os.close(fd)
os.waitpid(pid, 0)

# info against a missing session fails cleanly
r = linger('info', 'nosuch')
fails += expect(r.returncode == 1 and b'no session' in r.stderr,
                'info on a missing session exits 1 with a message')

linger('kill', 'ag')
print(f'FAILURES: {fails}')
sys.exit(1 if fails else 0)
