"""Reboot-resume e2e: checkpoint on last detach, daemon SIGKILLed
(simulated crash/reboot), session listed as resumable, attach restores
the old screen and labels and starts a fresh shell in the saved cwd."""
import os, pty, time, select, subprocess, sys, signal, fcntl, struct, termios, pathlib

LINGER = str(pathlib.Path(__file__).resolve().parent.parent / '.lake/build/bin/linger')
LDIR = os.environ.get('LINGER_TEST_DIR', '/tmp/linger-resume-' + str(os.getpid()))
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

# create a session working in /tmp, leave a marker on screen and a label
pid, fd = spawn_attach('boot')
time.sleep(0.8)
os.write(fd, b'cd /tmp && echo survives-the-reboot-$((40+2))\r')
drain(fd, 1.5)
subprocess.run([LINGER, 'set', 'boot', 'k=v'], env=ENV)

# detach (last attached client): the machine checkpoints here
os.write(fd, b'\x1c')
time.sleep(0.8)
ckpts = [f for f in os.listdir(LDIR) if f.endswith('.ckpt')]
fails += expect(ckpts == ['boot.ckpt'], f'checkpoint written on last detach ({ckpts})')

# simulate reboot: SIGKILL the DAEMON (the pid in `list` is the shell —
# killing that is a clean exit and rightly drops the checkpoint)
cands = subprocess.run(['pgrep', '-f', '__daemon boot'], capture_output=True,
                       text=True).stdout.split()
dpid = None
for c in cands:
    try:
        env = open(f'/proc/{c}/environ', 'rb').read().decode(errors='replace')
        if f'LINGER_DIR={LDIR}' in env:
            dpid = int(c)
            break
    except OSError:
        pass
assert dpid is not None, f'daemon not found among {cands}'
os.kill(dpid, signal.SIGKILL)
time.sleep(0.3)
for f in os.listdir(LDIR):
    if f.endswith('.sock'):
        os.unlink(os.path.join(LDIR, f))

ls = subprocess.run([LINGER, 'list'], env=ENV, capture_output=True, text=True).stdout
fails += expect('resumable' in ls and 'boot' in ls, 'killed session listed as resumable')

# attach again: fresh shell, restored screen, restored labels, saved cwd
pid2, fd2 = spawn_attach('boot')
time.sleep(1.0)
out = drain(fd2, 1.5)
fails += expect(b'survives-the-reboot-42' in out, 'reattach replays pre-reboot screen')
os.write(fd2, b'pwd\r')
out = drain(fd2, 1.5)
fails += expect(b'/tmp' in out, 'fresh shell starts in the saved cwd')
labels = subprocess.run([LINGER, 'get', 'boot'], env=ENV, capture_output=True, text=True).stdout
fails += expect('k=v' in labels, 'labels survive the reboot')

# clean exit drops the checkpoint
os.write(fd2, b'exit\r')
time.sleep(1.0)
ckpts = [f for f in os.listdir(LDIR) if f.endswith('.ckpt')]
fails += expect(ckpts == [], f'clean exit drops the checkpoint ({ckpts})')

# corrupt checkpoint: daemon must start fresh, not crash
with open(os.path.join(LDIR, 'corrupt.ckpt'), 'wb') as f:
    f.write(b'LINGER\x01' + os.urandom(200))
r = subprocess.run([LINGER, 'run', 'corrupt', 'echo fresh-start-ok'], env=ENV)
time.sleep(0.8)
hist = subprocess.run([LINGER, 'history', 'corrupt'], env=ENV, capture_output=True, text=True).stdout
fails += expect('fresh-start-ok' in hist, 'corrupt checkpoint: daemon starts fresh, no crash')
subprocess.run([LINGER, 'kill', 'corrupt'], env=ENV)

print('FAILURES:', fails)
sys.exit(1 if fails else 0)
