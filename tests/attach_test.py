import os, pty, time, select, signal, sys, subprocess, fcntl, struct, termios

import pathlib
LINGER = str(pathlib.Path(__file__).resolve().parent.parent / '.lake/build/bin/linger')
LDIR = os.environ.get('LINGER_TEST_DIR', '/tmp/linger-e2e-' + str(os.getpid()))
os.makedirs(LDIR, exist_ok=True)
ENV = dict(os.environ, LINGER_DIR=LDIR, SHELL='/bin/sh')

def spawn_attach(name):
    pid, fd = pty.fork()
    if pid == 0:
        os.execve(LINGER, [LINGER, 'attach', name], ENV)
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

def expect(cond, name):
    print(('PASS' if cond else 'FAIL'), name)
    return 0 if cond else 1

fails = 0

# 1. attach creates a live shell
pid, fd = spawn_attach('demo')
time.sleep(0.8)
os.write(fd, b'echo marker-$((21+21))\r')
out = drain(fd, 2.0)
fails += expect(b'marker-42' in out, 'attach: command executes, output streams back')

# 2. ctrl-\\ detaches; the client exits but the session lives
os.write(fd, b'\x1c')
time.sleep(0.5)
try:
    wpid, status = os.waitpid(pid, os.WNOHANG)
except ChildProcessError:
    wpid = pid
fails += expect(wpid == pid or drain(fd, 1.0) is not None, 'detach: client exited on ctrl-backslash')
ls = subprocess.run([LINGER, 'list'], env=ENV, capture_output=True, text=True).stdout
fails += expect('demo' in ls, 'detach: session still listed')

# 3. background output while detached reaches the emulator
subprocess.run([LINGER, 'send', 'demo', 'echo while-detached-$((40+2))\n'], env=ENV)
time.sleep(0.8)
hist = subprocess.run([LINGER, 'history', 'demo'], env=ENV, capture_output=True, text=True).stdout
fails += expect('while-detached-42' in hist, 'session advances while nobody attached')

# 4. reattach: restore shows the old screen contents
pid2, fd2 = spawn_attach('demo')
out2 = drain(fd2, 1.5)
fails += expect(b'marker-42' in out2 and b'while-detached-42' in out2,
                'reattach: restore replays prior screen')

# 5. two clients mirror output
pid3, fd3 = spawn_attach('demo')
drain(fd3, 1.0)
os.write(fd2, b'echo both-$((2+1))\r')
time.sleep(0.8)
o2 = drain(fd2, 1.0)
o3 = drain(fd3, 1.0)
fails += expect(b'both-3' in o2 and b'both-3' in o3, 'two clients mirror the session')

# 6. exit inside the shell ends the session and notifies clients
os.write(fd2, b'exit\r')
time.sleep(1.0)
ls2 = subprocess.run([LINGER, 'list'], env=ENV, capture_output=True, text=True).stdout
fails += expect('demo' not in ls2, 'shell exit ends the session')
o2 = drain(fd2, 1.0) + drain(fd3, 0.5)

# 7. wait returns the exit status
subprocess.run([LINGER, 'run', 'w1', 'sh -c "sleep 0.3; exit 7"'], env=ENV)
# run spawns a shell and types the command; the shell itself then exits with 7? no --
# the command runs inside the shell; make the shell exec it:
subprocess.run([LINGER, 'kill', 'w1'], env=ENV)
time.sleep(0.3)
subprocess.run([LINGER, 'run', 'w2', 'exec sh -c "sleep 0.5; exit 7"'], env=ENV)
t0 = time.time()
rc = subprocess.run([LINGER, 'wait', 'w2'], env=ENV).returncode
took = time.time() - t0
fails += expect(rc == 7 and took >= 0.2, f'wait blocks until exit and returns status (rc={rc}, took={took:.2f}s)')

# 8. bare `attach` (no name) attaches the default session "main"
pid_m, fd_m = pty.fork()
if pid_m == 0:
    os.execve(LINGER, [LINGER, 'attach'], ENV)   # no name -> defaultName "main"
fcntl.ioctl(fd_m, termios.TIOCSWINSZ, struct.pack('HHHH', 24, 80, 0, 0))
time.sleep(0.8)
ls_m = subprocess.run([LINGER, 'list'], env=ENV, capture_output=True, text=True).stdout
fails += expect('main' in ls_m, 'bare `attach` creates the default session "main"')
os.write(fd_m, b'\x1c')   # detach
time.sleep(0.4)
subprocess.run([LINGER, 'kill', 'main'], env=ENV)

# 9. detach hands the terminal back (Render.leaveAnsi). A full-screen app's
#    opening sequences are set from inside the session; after ctrl-\\ the client
#    must undo every one of them, or the user's shell is left on the alt screen
#    with mouse reporting on, no cursor, a six-line scroll region and every
#    ASCII character rendered as a box glyph. termios restores none of this.
pid_h, fd_h = spawn_attach('hyg')
time.sleep(0.8)
drain(fd_h, 0.3)
os.write(fd_h, (r"printf '\033[?1049h\033[?1000h\033[?1006h\033[?25l\033[?2004h"
                r"\033[?7l\033[5;10r\033(0\033[1;31;4m\033[?1h\033=X'" + "\r").encode())
time.sleep(0.6)
dirty = drain(fd_h, 0.8)
fails += expect(b'\x1b[?1049h' in dirty and b'\x1b[5;10r' in dirty,
                'hygiene: the app state really reached the client terminal')
os.write(fd_h, b'\x1c')            # detach
back = drain(fd_h, 1.5)
for seqs, what in [((b'\x1b[?1049l',), 'leaves the alt screen'),
                   ((b'\x1b[4l',), 'clears insert mode'),
                   ((b'\x1b[?25h',), 'shows the cursor'),
                   ((b'\x1b[?2004l',), 'clears bracketed paste'),
                   ((b'\x1b[?1000l', b'\x1b[?1002l', b'\x1b[?1003l', b'\x1b[?1006l'),
                    'clears mouse reporting'),
                   ((b'\x1b[?1004l',), 'clears focus events'),
                   ((b'\x1b[?1l', b'\x1b>'), 'restores normal cursor/keypad keys'),
                   ((b'\x1b[?6l',), 'clears origin mode'),
                   ((b'\x1b[?7h',), 'restores autowrap'),
                   ((b'\x1b[r',), 'restores the full scroll region'),
                   ((b'\x1b(B', b'\x1b)B', b'\x0f'), 'restores the ASCII charset'),
                   ((b'\x1b[0m',), 'resets the pen')]:
    fails += expect(all(s in back for s in seqs), 'detach ' + what)
fails += expect(back.index(b'\x1b\\') == 0,
                'detach leads with ST (a program that died mid-OSC/DCS would eat the rest)')
subprocess.run([LINGER, 'kill', 'hyg'], env=ENV)

# 10. LINGER_NO_DETACH_KEY=1 disables the ctrl-\\ detach key (README promise, and
#     the mirror of step 2). With the env var set, ctrl-\\ is ordinary input: the
#     client stays attached and the byte reaches the session's pty.
env_nd = dict(ENV, LINGER_NO_DETACH_KEY='1')
pid_nd, fd_nd = pty.fork()
if pid_nd == 0:
    os.execve(LINGER, [LINGER, 'attach', 'nd'], env_nd)
fcntl.ioctl(fd_nd, termios.TIOCSWINSZ, struct.pack('HHHH', 24, 80, 0, 0))
time.sleep(0.8)
drain(fd_nd, 0.3)
os.write(fd_nd, b'\x1c')          # would detach if the key were enabled
time.sleep(0.5)
try:
    wpid_nd, _ = os.waitpid(pid_nd, os.WNOHANG)
except ChildProcessError:
    wpid_nd = pid_nd
fails += expect(wpid_nd == 0, 'LINGER_NO_DETACH_KEY: ctrl-\\ does not detach (client still attached)')
ls_nd = subprocess.run([LINGER, 'list'], env=ENV, capture_output=True, text=True).stdout
fails += expect('nd' in ls_nd, 'LINGER_NO_DETACH_KEY: session still live')
os.write(fd_nd, b'echo nd-$((20+2))\r')  # still interactive: input reaches the pty
time.sleep(0.6)
hist_nd = subprocess.run([LINGER, 'history', 'nd'], env=ENV, capture_output=True, text=True).stdout
fails += expect('nd-22' in hist_nd, 'LINGER_NO_DETACH_KEY: input still reaches the session')
subprocess.run([LINGER, 'kill', 'nd'], env=ENV)

print('FAILURES:', fails)
sys.exit(1 if fails else 0)
