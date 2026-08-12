"""Two robustness properties that only show up under adverse timing:

  1. §Row — a daemon too busy to answer `info` within the reply window
     still lists under its real name (SIGSTOP stands in for a burst of
     pty output on a loaded box), and its socket is not disturbed.
  2. name-ownership lock — with a stale socket present, concurrent
     starts of one name produce exactly one daemon and one shell; no
     daemon is left holding a pty nobody can reach.
"""
import os, subprocess, time, signal, sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
LINGER = str(ROOT / '.lake/build/bin/linger')
LDIR = os.environ.get('LINGER_TEST_DIR', '/tmp/linger-robust-' + str(os.getpid()))
os.makedirs(LDIR, exist_ok=True)
ENV = dict(os.environ, LINGER_DIR=LDIR, SHELL='/bin/sh')

def expect(cond, name):
    print(('PASS' if cond else 'FAIL'), name)
    return 0 if cond else 1

def daemon_pids(name):
    out = subprocess.run(['pgrep', '-f', f'__daemon {name}'],
                         capture_output=True, text=True).stdout.split()
    mine = []
    for c in out:
        try:
            env = open(f'/proc/{c}/environ', 'rb').read().decode(errors='replace')
            if f'LINGER_DIR={LDIR}' in env:
                mine.append(int(c))
        except OSError:
            pass
    return mine

def children_of(pids):
    ps = subprocess.run(['ps', '-eo', 'pid,ppid,args'], capture_output=True,
                        text=True).stdout.splitlines()
    return [l for l in ps if len(l.split()) > 1 and l.split()[1].isdigit()
            and int(l.split()[1]) in pids and '/bin/sh' in l]

fails = 0

# ---- 1. busy daemon still lists correctly -------------------------------
subprocess.run([LINGER, 'run', 'busy', 'echo hi'], env=ENV)
time.sleep(1.0)
dpid = daemon_pids('busy')[0]
os.kill(dpid, signal.SIGSTOP)
out = subprocess.run([LINGER, 'list'], env=ENV, capture_output=True, text=True).stdout
porc = subprocess.run([LINGER, 'list', '--porcelain'], env=ENV,
                      capture_output=True, text=True).stdout
socks = [f for f in os.listdir(LDIR) if f.endswith('.sock')]
os.kill(dpid, signal.SIGCONT)

fails += expect(out.strip() == 'busy\t(busy)',
                f'busy daemon lists under its name (got {out.strip()!r})')
fails += expect('name\tbusy' in porc, 'porcelain carries the name for a busy daemon')
fails += expect(socks == ['busy.sock'], f'busy daemon keeps its socket ({socks})')
time.sleep(0.4)
fails += expect(subprocess.run([LINGER, 'send', 'busy', 'echo x\n'], env=ENV).returncode == 0,
                'busy daemon still reachable afterwards')
subprocess.run([LINGER, 'kill', 'busy'], env=ENV)
time.sleep(0.5)

# ---- 2. stale socket + concurrent starts -> one owner --------------------
subprocess.run([LINGER, 'run', 'claim', 'echo one'], env=ENV)
time.sleep(1.0)
victim = daemon_pids('claim')[0]
os.kill(victim, signal.SIGKILL)          # leaves claim.sock behind, stale
time.sleep(0.3)
stale = [f for f in os.listdir(LDIR) if f.endswith('.sock')]
fails += expect(stale == ['claim.sock'], f'stale socket present for the race ({stale})')

procs = [subprocess.Popen([LINGER, 'run', 'claim', 'echo two'], env=ENV,
                          stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
         for _ in range(8)]
for p in procs:
    p.wait()
time.sleep(1.5)

owners = daemon_pids('claim')
shells = children_of(set(owners))
fails += expect(len(owners) == 1, f'exactly one daemon owns the name (got {len(owners)})')
fails += expect(len(shells) == 1, f'exactly one shell (got {len(shells)})')
fails += expect(subprocess.run([LINGER, 'send', 'claim', 'echo y\n'], env=ENV).returncode == 0,
                'the surviving session is reachable')
locks = sorted(f for f in os.listdir(LDIR) if f.endswith('.lock'))
# lock files are deliberately never unlinked (unlinking defeats flock),
# so earlier sessions leave theirs behind; ours must be among them
fails += expect('claim.lock' in locks, f'ownership lock file present ({locks})')
subprocess.run([LINGER, 'kill', 'claim'], env=ENV)
time.sleep(0.5)

# the lock must be re-acquirable once the owner is gone (kernel released it)
r = subprocess.run([LINGER, 'run', 'claim', 'echo three'], env=ENV)
time.sleep(1.0)
fails += expect(len(daemon_pids('claim')) == 1,
                'name is re-claimable after the owner exits (no stale lock)')
subprocess.run([LINGER, 'kill', 'claim'], env=ENV)

print('FAILURES:', fails)
sys.exit(1 if fails else 0)
