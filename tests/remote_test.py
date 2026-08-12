"""Remote-over-ssh e2e with a fake `ssh` on PATH. `lzmx -r <hosts>`
folds each host's sessions into the local overview (by running `ssh
host lzmx ls --porcelain`), tolerates an unreachable host, and refuses a
duplicate host. `lzmx attach name@host` execs `ssh -t host lzmx attach
name`. Hostile remote output must not inject a path or escape bytes into
the local listing."""
import os, pty, time, select, subprocess, sys, fcntl, struct, termios, pathlib, re

ROOT = pathlib.Path(__file__).resolve().parent.parent
LZMX = str(ROOT / '.lake/build/bin/lzmx')
LDIR = os.environ.get('LZMX_TEST_DIR', '/tmp/lzmx-remote-' + str(os.getpid()))
BIN = os.path.join(LDIR, 'fakebin')
os.makedirs(BIN, exist_ok=True)
LOG = os.path.join(LDIR, 'ssh.log')

# fake ssh: logs argv, answers `ls`/attach for a real host, fails (255)
# for "dead". The listing carries one hostile record (path name + ANSI).
FAKE_SSH = f'''#!/bin/sh
echo "$@" >> {LOG}
# strip ssh options to find the destination and remote command
while [ $# -gt 0 ]; do
  case "$1" in
    -o) shift 2 ;;
    -t) shift ;;
    --) shift; break ;;
    *) break ;;
  esac
done
host="$1"; shift
[ "$host" = "dead" ] && exit 255
case "$2" in
  ls)
    printf 'name\\tremote-work\\nstate\\tlive\\nclients\\t1\\ncmd\\tvim\\x1b[31mINJECT\\nlabel.env\\tprod\\n\\n'
    printf 'name\\t../../etc/passwd\\nstate\\tresumable\\n\\n'
    printf 'garbage line with no tabs\\n\\n'
    ;;
  attach)  printf 'FAKE-ATTACH-OK\\n'; sleep 5 ;;
esac
exit 0
'''
with open(os.path.join(BIN, 'ssh'), 'w') as f:
    f.write(FAKE_SSH)
os.chmod(os.path.join(BIN, 'ssh'), 0o755)

ENV = dict(os.environ, LZMX_DIR=LDIR, SHELL='/bin/sh',
           PATH=BIN + os.pathsep + os.environ['PATH'])


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
subprocess.run([LZMX, 'run', 'localsess', 'echo local-content'], env=ENV)
time.sleep(1.0)

# a duplicate host is a hard error, reported before anything runs (no tty
# needed — argv validation precedes the connection attempts)
dup = subprocess.run([LZMX, '-r', 'dev-a,dev-a'], env=ENV,
                     stdin=subprocess.DEVNULL, capture_output=True, text=True)
fails += expect(dup.returncode != 0 and 'more than once' in dup.stderr
                and 'dev-a' in dup.stderr, 'duplicate -r host errors loudly')

# the overview folds in the remote host's sessions (plain stdout, no tty)
r = subprocess.run([LZMX, '-r', 'dev-a,dead'], env=ENV, stdin=subprocess.DEVNULL,
                   capture_output=True, text=True, timeout=15)
out = r.stdout
fails += expect(r.returncode == 0, '`lzmx -r` exits cleanly')
fails += expect('localsess' in out, 'local session listed alongside remotes')
fails += expect('remote-work@dev-a' in out, 'remote session listed with @host tag')
fails += expect('_._.._etc_passwd' in out and '/etc/passwd' not in out,
                'hostile remote name is sanitized (no slashes, no leading dot)')
fails += expect('\x1b' not in out,
                'remote escape sequences are scrubbed from the listing')
fails += expect('@dead' not in out, 'unreachable host contributes no rows')

# `attach name@host` execs `ssh -t host lzmx attach name` (needs a tty)
pid, fd = pty.fork()
if pid == 0:
    os.execve(LZMX, [LZMX, 'attach', 'remote-work@dev-a'], ENV)
fcntl.ioctl(fd, termios.TIOCSWINSZ, struct.pack('HHHH', 24, 100, 0, 0))
attached = plain(drain(fd, 2.0))
log = open(LOG).read()
fails += expect('FAKE-ATTACH-OK' in attached, 'attach name@host reaches the remote attach')
fails += expect(re.search(r'-t (--\s+)?dev-a lzmx attach remote-work', log) is not None,
                f'remote attach ssh argv correct ({[l for l in log.splitlines() if "attach" in l]})')
try:
    os.kill(pid, 9)
except OSError:
    pass

# a `user@host` remote (multi-@) round-trips: the host is everything
# after the FIRST @, so `attach work@me@dev-a` execs ssh to `me@dev-a`
# and attaches `work` (session names never contain @ — sanitize reserves it)
pid, fd = pty.fork()
if pid == 0:
    os.execve(LZMX, [LZMX, 'attach', 'remote-work@me@dev-a'], ENV)
fcntl.ioctl(fd, termios.TIOCSWINSZ, struct.pack('HHHH', 24, 100, 0, 0))
plain(drain(fd, 2.0))
log = open(LOG).read()
fails += expect(re.search(r'-t -- me@dev-a lzmx attach remote-work', log) is not None,
                f'user@host remote round-trips via first-@ split '
                f'({[l for l in log.splitlines() if "me@dev-a" in l]})')
try:
    os.kill(pid, 9)
except OSError:
    pass

# a malformed target (empty host) is a loud error, not a silent local session
pid, fd = pty.fork()
if pid == 0:
    os.execve(LZMX, [LZMX, 'attach', 'work@'], ENV)
fcntl.ioctl(fd, termios.TIOCSWINSZ, struct.pack('HHHH', 24, 100, 0, 0))
out = plain(drain(fd, 1.5))
fails += expect('malformed' in out,
                'trailing @ errors loudly instead of creating a local session')
try:
    os.kill(pid, 9)
except OSError:
    pass

subprocess.run([LZMX, 'kill', 'localsess'], env=ENV)
print('FAILURES:', fails)
sys.exit(1 if fails else 0)
