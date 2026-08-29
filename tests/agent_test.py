"""Agent-verbs e2e (specs/agent-cli.md): see and drive a session one-shot.

Step 1: `linger info <name>` and the observability fields -- geometry + cursor
(what `capture` needs), `alt`, and `outseq` (the change cursor: "look again
only when it moved"). Step 2: `linger capture <name>` -- the screen as plain
text, one line per row, and capturing marks the session seen. All pinned
against the rendered porcelain/bytes, end to end.
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
linger('run', 'ag', 'echo', 'MOVED')
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

# -- Step 2: capture ----------------------------------------------------------

linger('run', 'ag', 'echo', 'CAPTURED-MARKER')
time.sleep(1.2)

cap = linger('capture', 'ag')
lines = cap.stdout.decode().split('\n')
rows = int(info('ag').get('rows', '0'))
fails += expect(cap.returncode == 0 and b'CAPTURED-MARKER' in cap.stdout,
                'capture shows what the session printed')
# screenText is LF-terminated per row: split yields rows + one trailing ''
fails += expect(len(lines) == rows + 1 and lines[-1] == '',
                'capture is exactly one line per row')

# capture marks the session seen (the porcelain unseen flag flips)
fails += expect(info('ag').get('unseen') == 'false' and
                info('ag').get('behind') == '0',
                'capture marks the session seen')
linger('run', 'ag', 'echo', 'again')
time.sleep(1.2)
fails += expect(info('ag').get('unseen') == 'true',
                'output after a capture reads unseen again')

# capture is the screen, not the transcript: flood past one screen and the
# capture stays `rows` lines while history grows beyond it
linger('run', 'ag', 'seq', '1', '60')
time.sleep(1.5)
cap2 = linger('capture', 'ag').stdout.decode().split('\n')
hist = linger('history', 'ag').stdout.decode().split('\n')
fails += expect(len(cap2) == rows + 1 and len(hist) > len(cap2),
                'capture stays screen-sized while history grows')

r = linger('capture', 'nosuch')
fails += expect(r.returncode == 1, 'capture on a missing session exits 1')

# -- Step 3: send - (raw stdin) -----------------------------------------------

# a full command line with its newline arrives verbatim and executes. The
# marker is asserted on the *expansion* (GOT-42), which the typed line does
# not contain -- the tty echoes typed input onto the screen, so asserting on
# the typed text would pass even if the newline was lost and nothing ran.
r = linger('send', 'ag', '-', input=b'echo "GOT-$((40+2))"\n')
time.sleep(1.2)
fails += expect(r.returncode == 0 and
                'GOT-42' in linger('capture', 'ag').stdout.decode(),
                'send - delivers bytes verbatim (newline included: it ran)')

# a control byte works: ^C interrupts a foreground child, after which the
# queued next line is read and runs (same trick: the typed line says
# INTER""RUPTED-OK, only the executed output says INTERRUPTED-OK)
linger('run', 'ag', 'sleep', '100')
time.sleep(1.0)
linger('send', 'ag', '-', input=b'\x03')
time.sleep(0.5)
linger('run', 'ag', 'echo', 'INTER""RUPTED-OK')
time.sleep(1.2)
fails += expect('INTERRUPTED-OK' in linger('capture', 'ag').stdout.decode(),
                'send - carries ^C (the sleep died, the shell came back)')

# empty stdin is a clean no-op
r = linger('send', 'ag', '-', input=b'')
fails += expect(r.returncode == 0, 'send - with empty stdin exits 0')

r = linger('send', 'nosuch', '-', input=b'x')
fails += expect(r.returncode == 1, 'send - on a missing session exits 1')

linger('kill', 'ag')
print(f'FAILURES: {fails}')
sys.exit(1 if fails else 0)
