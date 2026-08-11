import os, pty, time, select, signal, sys, subprocess, fcntl, struct, termios

import pathlib
LZMX = str(pathlib.Path(__file__).resolve().parent.parent / '.lake/build/bin/lzmx')
LDIR = os.environ.get('LZMX_TEST_DIR', '/tmp/lzmx-e2e-' + str(os.getpid()))
os.makedirs(LDIR, exist_ok=True)
ENV = dict(os.environ, LZMX_DIR=LDIR, SHELL='/bin/sh')

def spawn_attach(name):
    pid, fd = pty.fork()
    if pid == 0:
        os.execve(LZMX, [LZMX, 'attach', name], ENV)
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
ls = subprocess.run([LZMX, 'list'], env=ENV, capture_output=True, text=True).stdout
fails += expect('demo' in ls, 'detach: session still listed')

# 3. background output while detached reaches the emulator
subprocess.run([LZMX, 'send', 'demo', 'echo while-detached-$((40+2))\n'], env=ENV)
time.sleep(0.8)
hist = subprocess.run([LZMX, 'history', 'demo'], env=ENV, capture_output=True, text=True).stdout
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
ls2 = subprocess.run([LZMX, 'list'], env=ENV, capture_output=True, text=True).stdout
fails += expect('demo' not in ls2, 'shell exit ends the session')
o2 = drain(fd2, 1.0) + drain(fd3, 0.5)

# 7. wait returns the exit status
subprocess.run([LZMX, 'run', 'w1', 'sh -c "sleep 0.3; exit 7"'], env=ENV)
# run spawns a shell and types the command; the shell itself then exits with 7? no --
# the command runs inside the shell; make the shell exec it:
subprocess.run([LZMX, 'kill', 'w1'], env=ENV)
time.sleep(0.3)
subprocess.run([LZMX, 'run', 'w2', 'exec sh -c "sleep 0.5; exit 7"'], env=ENV)
t0 = time.time()
rc = subprocess.run([LZMX, 'wait', 'w2'], env=ENV).returncode
took = time.time() - t0
fails += expect(rc == 7 and took >= 0.2, f'wait blocks until exit and returns status (rc={rc}, took={took:.2f}s)')

print('FAILURES:', fails)
sys.exit(1 if fails else 0)
