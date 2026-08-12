"""Overview e2e: bare `linger` and `linger ls` print a session list and
EXIT — they are NOT an interactive full-screen picker.

Regression guard: a first-time user once ran bare `linger`, got a
full-screen TUI (which drew a lone divider bar), typed `ls` at it, and
that created a session literally named 'ls'. The overview must be a
plain, pipeable, self-terminating listing that never blocks on stdin."""
import os, subprocess, sys, time, pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
LINGER = str(ROOT / '.lake/build/bin/linger')
LDIR = os.environ.get('LINGER_TEST_DIR', '/tmp/linger-overview-' + str(os.getpid()))
os.makedirs(LDIR, exist_ok=True)
ENV = dict(os.environ, LINGER_DIR=LDIR, SHELL='/bin/sh')


def overview(args):
    """Run an overview command with stdin closed and a hard timeout. An
    interactive picker would block on the empty stdin and trip the
    timeout (returncode reported as None) — exactly the regression."""
    try:
        r = subprocess.run([LINGER] + args, env=ENV, stdin=subprocess.DEVNULL,
                           capture_output=True, text=True, timeout=15)
        return r.returncode, r.stdout
    except subprocess.TimeoutExpired:
        return None, ''   # blocked on stdin == the TUI regression


def expect(cond, name):
    print(('PASS' if cond else 'FAIL'), name)
    return 0 if cond else 1


def label(args):
    return 'linger ' + ' '.join(args) if args else 'linger (bare)'


fails = 0

# empty state: both bare and `ls` say so and exit 0 (no hang, no tty need)
for args in ([], ['ls']):
    rc, out = overview(args)
    fails += expect(rc == 0 and 'no sessions' in out,
                    f'{label(args)} prints overview and exits')

# two live sessions: listed by name in both the bare and `ls` forms
subprocess.run([LINGER, 'run', 'alpha', 'true'], env=ENV)
subprocess.run([LINGER, 'run', 'beta', 'true'], env=ENV)
time.sleep(1.2)
for args in ([], ['ls']):
    rc, out = overview(args)
    fails += expect(rc == 0 and 'alpha' in out and 'beta' in out,
                    f'{label(args)} lists both live sessions')

rc, out = overview(['ls', '--porcelain'])
fails += expect('name\talpha' in out and 'state\tlive' in out,
                'porcelain carries name/state (the remote-parse contract)')

for n in ('alpha', 'beta'):
    subprocess.run([LINGER, 'kill', n], env=ENV)
print('FAILURES:', fails)
sys.exit(1 if fails else 0)
