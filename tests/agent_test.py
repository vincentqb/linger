"""Agent-verbs e2e (specs/agent-cli.md): see and drive a session one-shot.

Step 1: `linger info <name>` and the observability fields -- geometry + cursor
(what `capture` needs), `alt`, and `outseq` (the change cursor: "look again
only when it moved"). Step 2: `linger capture <name>` -- the screen as plain
text, one line per row, and capturing marks the session seen. Step 3:
`linger send <name> -` -- stdin to the pty byte-exact (the oracles assert on
shell *expansions*: the tty echoes typed input onto the screen, so a typed-text
marker would pass even if the bytes never ran; see SCRATCHPAD 2026-08-19).
Step 4: `linger resize` -- applies detached (down to the child's own winsize,
via `stty size`), refused while a client is attached. All pinned against the
rendered porcelain/bytes, end to end.
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

# -- Step 4: resize -----------------------------------------------------------

linger('run', 'rz', 'true')
time.sleep(1.5)

r = linger('resize', 'rz', '120', '40')
time.sleep(1.0)
i = info('rz')
fails += expect(r.returncode == 0 and i.get('cols') == '120' and i.get('rows') == '40',
                'control resize applies to a detached session')

# the pty winsize followed too: the child's own stty sees it (SIGWINCH path)
linger('run', 'rz', 'stty', 'size')
time.sleep(1.2)
fails += expect('40 120' in linger('capture', 'rz').stdout.decode(),
                'the child observes the new winsize (stty size: 40 120)')

# an attached client owns the size: refused, loudly, and nothing moves
pid, fd = pty.fork()
if pid == 0:
    os.execve(LINGER, [LINGER, 'attach', 'rz'], ENV)
fcntl.ioctl(fd, termios.TIOCSWINSZ, struct.pack('HHHH', 24, 80, 0, 0))
time.sleep(1.5)
r = linger('resize', 'rz', '90', '25')
fails += expect(r.returncode == 1 and b'owns the size' in r.stderr,
                'resize is refused while a client is attached')
fails += expect(info('rz').get('cols') == '80',
                'a refused resize moved nothing')
os.write(fd, b'\x1c')
time.sleep(0.8)
os.close(fd)
os.waitpid(pid, 0)

r = linger('resize', 'rz', '90', '25')
time.sleep(0.8)
fails += expect(r.returncode == 0 and info('rz').get('cols') == '90',
                'resize applies again once the client detached')

# client-side validation: 1..1000 (clampDim's range)
fails += expect(linger('resize', 'rz', '0', '10').returncode == 2 and
                linger('resize', 'rz', '5000', '10').returncode == 2,
                'zero and oversize are rejected client-side')
fails += expect(linger('resize', 'nosuch', '80', '24').returncode == 1,
                'resize on a missing session exits 1')

linger('kill', 'rz')
print(f'FAILURES: {fails}')
sys.exit(1 if fails else 0)
