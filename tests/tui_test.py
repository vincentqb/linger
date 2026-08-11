"""TUI e2e: drive `lzmx` (bare) in a pty — list, filter, preview,
create-by-typing, kill with confirm, quit."""
import os, pty, time, select, subprocess, sys, fcntl, struct, termios, pathlib, re

LZMX = str(pathlib.Path(__file__).resolve().parent.parent / '.lake/build/bin/lzmx')
LDIR = os.environ.get('LZMX_TEST_DIR', '/tmp/lzmx-tui-' + str(os.getpid()))
os.makedirs(LDIR, exist_ok=True)
ENV = dict(os.environ, LZMX_DIR=LDIR, SHELL='/bin/sh')

def spawn_tui():
    pid, fd = pty.fork()
    if pid == 0:
        os.execve(LZMX, [LZMX], ENV)
    fcntl.ioctl(fd, termios.TIOCSWINSZ, struct.pack('HHHH', 24, 80, 0, 0))
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
    txt = bs.decode('utf-8', errors='replace')
    return re.sub(r'\x1b\[[0-9;?]*[A-Za-z]', '', txt)

def expect(cond, name):
    print(('PASS' if cond else 'FAIL'), name)
    return 0 if cond else 1

fails = 0

# two sessions with recognizable content
subprocess.run([LZMX, 'run', 'alpha', 'echo preview-alpha-content'], env=ENV)
subprocess.run([LZMX, 'run', 'beta', 'echo preview-beta-content'], env=ENV)
time.sleep(1.0)

# open the TUI: both sessions listed, first previewed
pid, fd = spawn_tui()
screen = plain(drain(fd, 2.5))
fails += expect('alpha' in screen and 'beta' in screen, 'both sessions listed')
fails += expect('live' in screen, 'status bar shows live count')
fails += expect('preview-alpha-content' in screen or 'preview-beta-content' in screen,
                'preview pane shows session content')

# filter: typing narrows to beta
os.write(fd, b'bet')
screen = plain(drain(fd, 1.5))
fails += expect('beta' in screen and 'preview-beta-content' in screen,
                'typing filters and re-previews')

# clear the query
os.write(fd, b'\x7f\x7f\x7f')
drain(fd, 0.7)

# kill flow: C-x arms, C-x kills the selected (alpha, first row)
os.write(fd, b'\x18')
screen = plain(drain(fd, 1.0))
fails += expect('C-x again to kill' in screen, 'first C-x asks to confirm')
os.write(fd, b'\x18')
time.sleep(1.0)
drain(fd, 1.0)
ls = subprocess.run([LZMX, 'list'], env=ENV, capture_output=True, text=True).stdout
fails += expect('alpha' not in ls and 'beta' in ls, 'confirmed C-x kills the session')

# quit
os.write(fd, b'\x1b')
time.sleep(0.5)
gone = os.waitpid(pid, os.WNOHANG)
fails += expect(gone[0] == pid, 'esc quits the TUI')

# create-by-typing: a fresh TUI, type a new name, enter → attach upsert
pid2, fd2 = spawn_tui()
drain(fd2, 1.5)
os.write(fd2, b'gamma-new\r')
time.sleep(2.0)
out = plain(drain(fd2, 2.0))
ls = subprocess.run([LZMX, 'list'], env=ENV, capture_output=True, text=True).stdout
fails += expect('gamma-new' in ls, 'enter on no-match creates the session (upsert)')
# we are now INSIDE gamma-new (exec'd attach); detach out
os.write(fd2, b'\x1c')
time.sleep(0.5)

for n in ('beta', 'gamma-new'):
    subprocess.run([LZMX, 'kill', n], env=ENV)

print('FAILURES:', fails)
sys.exit(1 if fails else 0)
