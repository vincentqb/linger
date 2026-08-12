"""Remote-over-ssh e2e with a fake `ssh` on PATH: the TUI must list a
remote host's sessions, preview them, and exec the right ssh argv on
attach. Also checks hostile remote output can't inject anything."""
import os, pty, time, select, subprocess, sys, fcntl, struct, termios, pathlib, re, stat

ROOT = pathlib.Path(__file__).resolve().parent.parent
LZMX = str(ROOT / '.lake/build/bin/lzmx')
LDIR = os.environ.get('LZMX_TEST_DIR', '/tmp/lzmx-remote-' + str(os.getpid()))
BIN = os.path.join(LDIR, 'fakebin')
os.makedirs(BIN, exist_ok=True)
LOG = os.path.join(LDIR, 'ssh.log')

# fake ssh: logs argv, answers list/history for host "dev-a", fails for "dead"
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
  list)
    printf 'name\\tremote-work\\nstate\\tlive\\nclients\\t1\\ncmd\\tvim\\x1b[31mINJECT\\nlabel.env\\tprod\\n\\n'
    printf 'name\\t../../etc/passwd\\nstate\\tresumable\\n\\n'
    printf 'garbage line with no tabs\\n\\n'
    ;;
  history) printf 'remote-history-line-42\\n' ;;
  attach)  printf 'FAKE-ATTACH-OK\\n'; sleep 5 ;;
esac
exit 0
'''
with open(os.path.join(BIN, 'ssh'), 'w') as f:
    f.write(FAKE_SSH)
os.chmod(os.path.join(BIN, 'ssh'), 0o755)

ENV = dict(os.environ, LZMX_DIR=LDIR, SHELL='/bin/sh',
           PATH=BIN + os.pathsep + os.environ['PATH'])

def spawn_tui():
    pid, fd = pty.fork()
    if pid == 0:
        os.execve(LZMX, [LZMX, '-r', 'dev-a,dead'], ENV)   # remotes via flag
    fcntl.ioctl(fd, termios.TIOCSWINSZ, struct.pack('HHHH', 24, 100, 0, 0))
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
    return re.sub(r'\x1b\[[0-9;?]*[A-Za-z]', '', bs.decode('utf-8', errors='replace'))

def expect(cond, name):
    print(('PASS' if cond else 'FAIL'), name)
    return 0 if cond else 1

fails = 0
subprocess.run([LZMX, 'run', 'localsess', 'echo local-content'], env=ENV)
time.sleep(1.0)

# a duplicate host is a hard error, reported before anything else (no tty
# needed — argv validation precedes the environment check)
dup = subprocess.run([LZMX, '-r', 'dev-a,dev-a'], env=ENV,
                     stdin=subprocess.DEVNULL, capture_output=True, text=True)
fails += expect(dup.returncode != 0 and 'more than once' in dup.stderr
                and 'dev-a' in dup.stderr, 'duplicate -r host errors loudly')

pid, fd = spawn_tui()
screen = plain(drain(fd, 3.0))

fails += expect('localsess' in screen, 'local session listed')
fails += expect('remote-work@dev-a' in screen, 'remote session listed with host tag')
fails += expect('_._.._etc_passwd' in screen and '/etc/passwd' not in screen,
                'hostile remote name is sanitized (slashes gone, no leading dot)')
fails += expect('INJECT' not in screen or '\x1b[31m' not in screen,
                'remote escape sequences are scrubbed')
fails += expect('dead' not in screen.split('\n')[0], 'unreachable host does not break the list')

# select the remote row and check its preview comes from ssh history
os.write(fd, b'remote-w')
screen = plain(drain(fd, 2.5))
fails += expect('remote-history-line-42' in screen, 'remote preview via ssh history')

# enter → should exec ssh -t dev-a lzmx attach remote-work
os.write(fd, b'\r')
time.sleep(1.5)
out = plain(drain(fd, 1.5))
log = open(LOG).read()
fails += expect('FAKE-ATTACH-OK' in out, 'enter execs the remote attach')
fails += expect(re.search(r'-t (--\s+)?dev-a lzmx attach remote-work', log) is not None,
                f'ssh argv is correct ({[l for l in log.splitlines() if "attach" in l]})')

subprocess.run([LZMX, 'kill', 'localsess'], env=ENV)
print('FAILURES:', fails)
sys.exit(1 if fails else 0)
