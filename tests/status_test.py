"""Status column e2e: the unread mechanism, end to end.

`unseen` is a property of the session -- output arrived while nobody was
watching -- so the two transitions that matter are: attaching marks a session
seen, and output while detached marks it unread again. Both go through the
counter pair in Session.State (outSeq/lookSeq), and this pins them against the
rendered porcelain rather than against the internals.
"""
import os, pty, time, select, subprocess, fcntl, struct, termios, sys, pathlib

LINGER = str(pathlib.Path(__file__).resolve().parent.parent / '.lake/build/bin/linger')
LDIR = os.environ.get('LINGER_TEST_DIR', '/tmp/linger-status-' + str(os.getpid()))
os.makedirs(LDIR, exist_ok=True)
ENV = dict(os.environ, LINGER_DIR=LDIR, SHELL='/bin/sh')


def field(name, key):
    """One porcelain field of one session's row."""
    out = subprocess.run([LINGER, 'ls', '--porcelain'], env=ENV,
                         capture_output=True, timeout=15).stdout.decode()
    cur = None
    for line in out.splitlines():
        if line.startswith('name\t'):
            cur = line.split('\t', 1)[1]
        elif cur == name and line.startswith(key + '\t'):
            return line.split('\t', 1)[1]
    return None


def expect(cond, label):
    print(('PASS' if cond else 'FAIL'), label)
    return 0 if cond else 1


fails = 0
subprocess.run([LINGER, 'run', 'st', 'sh', '-c', 'sleep 60'], env=ENV,
               capture_output=True, timeout=15)
time.sleep(1.5)

# 1. a session nobody has watched, that has produced output, is unread
fails += expect(field('st', 'status') == 'wants-you', 'unwatched output reads wants-you')

# 2. attaching marks it seen: detach with no further output and it is idle
pid, fd = pty.fork()
if pid == 0:
    os.execve(LINGER, [LINGER, 'attach', 'st'], ENV)
fcntl.ioctl(fd, termios.TIOCSWINSZ, struct.pack('HHHH', 24, 80, 0, 0))
time.sleep(1.5)
os.write(fd, b'\x1c')          # detach
time.sleep(0.8)
os.close(fd)
os.waitpid(pid, 0)
fails += expect(field('st', 'status') == 'idle', 'attach marks the session seen')

# 3. output while detached makes it unread again
subprocess.run([LINGER, 'send', 'st', 'echo', 'later'], env=ENV,
               capture_output=True, timeout=15)
time.sleep(1.2)
fails += expect(field('st', 'status') == 'wants-you', 'output while away reads wants-you')
fails += expect((field('st', 'behind') or '0') != '0', 'behind counts unseen output')

# 4. the human column renders one glyph for it
human = subprocess.run([LINGER, 'ls'], env=ENV, capture_output=True,
                       timeout=15).stdout.decode()
fails += expect('\u28ff' in human, 'human listing shows the wants-you glyph')

subprocess.run([LINGER, 'kill', 'st'], env=ENV, capture_output=True, timeout=15)
print(f'FAILURES: {fails}')
sys.exit(1 if fails else 0)
