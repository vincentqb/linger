"""Finding *our* daemon, portably.

Several e2e tests have to SIGKILL or SIGSTOP the daemon behind a session,
which means answering two questions: which pids are `linger __daemon
<name>` (pgrep -f, portable), and which of those belong to the test's own
`LINGER_DIR` (the hard half). The second filter is not optional: a real
session of the same name in the developer's own linger dir must never be
the one that gets killed.

`/proc/<pid>/environ` was the original answer and is Linux-only. macOS has
no /proc, and `ps -Eww -p <pid>` there prints the command with no
environment at all (measured 2026-08-19 on darwin 25.5 against a process
of the same uid), so there is no environment to read. The fallback asks
about open files instead: the daemon holds the name-ownership flock on
`<ldir>/<name>.lock` for its whole life, and holds `<ldir>/<name>.sock`
bound, so `lsof -p` names our directory iff the daemon is ours. lsof
reports the lock as `/private/tmp/...` on macOS where the socket says
`/tmp/...` (/tmp is a symlink), hence both spellings of the dir are
accepted.
"""
import os, subprocess

def _env_has_ldir(pid, ldir):
    """True/False from /proc, or None where /proc is absent (macOS)."""
    try:
        with open(f'/proc/{pid}/environ', 'rb') as f:
            return f'LINGER_DIR={ldir}' in f.read().decode(errors='replace')
    except FileNotFoundError:
        return None
    except OSError:
        return False

def _files_name_ldir(pid, ldir, name):
    out = subprocess.run(['lsof', '-nP', '-p', str(pid)],
                         capture_output=True, text=True).stdout
    return any(f'{d}/{name}.' in out for d in {ldir, os.path.realpath(ldir)})

def daemon_pids(name, ldir):
    """pids of the `__daemon <name>` daemons living in `ldir`."""
    cands = subprocess.run(['pgrep', '-f', f'__daemon {name}'],
                           capture_output=True, text=True).stdout.split()
    mine = []
    for c in cands:
        ours = _env_has_ldir(c, ldir)
        if ours is None:
            ours = _files_name_ldir(c, ldir, name)
        if ours:
            mine.append(int(c))
    return mine
