"""Graphics passthrough e2e: kitty (APC) and sixel (DCS) image protocols.

What linger promises here, and what it does not:

  * live, while attached: image bytes reach the client's terminal
    VERBATIM, because the daemon broadcasts each raw pty chunk alongside
    feeding its own emulator (Zmx/Core/Session.lean, `.ptyBytes`). No
    allow-passthrough switch, unlike tmux.
  * the emulator IGNORES the payload (parser state `.str` until ST) and
    accumulates nothing, so a megabyte of base64 cannot grow the session
    or reach the checkpoint (§Bound).
  * after detach/reattach: images are GONE. `restore` repaints from the
    cell grid, and cells hold no image data. The text screen comes back
    intact; the picture does not.

The third point is the documented limitation. This file exists so the
first two cannot regress silently — a future "render from the grid
instead of broadcasting" optimization would break images with no other
test noticing.
"""

import os, pty, time, select, sys, subprocess, fcntl, struct, termios
import pathlib

LINGER = str(pathlib.Path(__file__).resolve().parent.parent / '.lake/build/bin/linger')
LDIR = os.environ.get('LINGER_TEST_DIR', '/tmp/linger-gfx-' + str(os.getpid()))
os.makedirs(LDIR, exist_ok=True)
ENV = dict(os.environ, LINGER_DIR=LDIR, SHELL='/bin/sh')

# The real byte sequences. Written with octal escapes so /bin/sh's printf
# emits them: \033 is ESC, \134 is the backslash of the ST terminator.
# The payload marker is octal-encoded too, because the shell ECHOES the
# command line: a literal marker would appear in the text grid as echoed
# input and check 4 below would pass for the wrong reason (it did, the
# first time round).
KITTY_CMD = r"printf '\033_Gi=31,a=T,f=24,s=1,v=1;\107\106\130\120\101\131\114\117\101\104\033\134'"
KITTY_BYTES = b'\x1b_Gi=31,a=T,f=24,s=1,v=1;GFXPAYLOAD\x1b\\'
SIXEL_CMD = r"printf '\033Pq#0;2;0;0;0#0~~@@vv@@~~$\033\134'"
SIXEL_BYTES = b'\x1bPq#0;2;0;0;0#0~~@@vv@@~~$\x1b\\'


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
pid, fd = spawn_attach('gfx')
time.sleep(0.8)
drain(fd, 0.4)

# 1+2. both protocols arrive verbatim at the attached client
os.write(fd, (KITTY_CMD + '\r').encode())
time.sleep(0.5)
out = drain(fd, 0.6)
fails += expect(KITTY_BYTES in out, 'kitty APC graphics pass through verbatim')

os.write(fd, (SIXEL_CMD + '\r').encode())
time.sleep(0.5)
out = drain(fd, 0.6)
fails += expect(SIXEL_BYTES in out, 'sixel DCS graphics pass through verbatim')

# 3. the session is not wedged by either payload
os.write(fd, b'echo gfx-alive-$((20+22))\r')
time.sleep(0.6)
out = drain(fd, 0.8)
fails += expect(b'gfx-alive-42' in out, 'session still live after image payloads')

# 4. the emulator ignored the payload rather than printing it: it must not
#    appear in the text scrollback
hist = subprocess.run([LINGER, 'history', 'gfx'], env=ENV,
                      capture_output=True, timeout=10).stdout
fails += expect(b'GFXPAYLOAD' not in hist,
                'image payload does not land in the text grid')

# 5. detach, reattach: the text screen restores and the parser is sane.
#    The image is gone — that is the documented limitation, asserted here
#    so the README and the behaviour cannot drift apart.
os.write(fd, b'\x1c')
time.sleep(0.6)
os.close(fd)
os.waitpid(pid, 0)

pid2, fd2 = spawn_attach('gfx')
time.sleep(1.0)
restored = drain(fd2, 0.8)
fails += expect(b'gfx-alive-42' in restored, 'text screen restores after reattach')
fails += expect(KITTY_BYTES not in restored,
                'images are NOT replayed on reattach (documented limitation)')

os.write(fd2, b'echo after-reattach-$((21+21))\r')
time.sleep(0.6)
out = drain(fd2, 0.8)
fails += expect(b'after-reattach-42' in out, 'parser sane after a restore')

os.write(fd2, b'\x1c')
time.sleep(0.4)
os.close(fd2)
os.waitpid(pid2, 0)
subprocess.run([LINGER, 'kill', 'gfx'], env=ENV, capture_output=True, timeout=10)

# ---------------------------------------------------------------------------
# 6+7. The repaint shortcut: an application that redraws brings its OWN
# images back, and what makes it redraw is SIGWINCH. We deliver that by
# resizing the pty for the size-owning client on attach, so a reattach at a
# new size nudges the program; at the same size the kernel suppresses the
# signal (tty_do_resize compares the winsize first) and nothing redraws.
#
# Both halves are asserted because the *asymmetry* is the user-visible rule:
# "images come back if the app redraws, and it redraws when the size
# changed". The reporter logs to a file — anything on stdout would be
# replayed by `restore` and could not be told apart from a fresh signal —
# and runs in the FOREGROUND, since a background process group gets no
# SIGWINCH at all.
WLOG = os.path.join(LDIR, 'winch')
REPORTER = (f"python3 -c \"import signal,time;f=open('{WLOG}','a');"
            "signal.signal(signal.SIGWINCH, lambda *a:(f.write('W'),f.flush()));"
            "time.sleep(120)\"\r")


def winch_count():
    try:
        with open(WLOG) as f:
            return f.read().count('W')
    except FileNotFoundError:
        return 0


def spawn_sized(name, cols, rows):
    pid, fd = pty.fork()
    if pid == 0:
        os.execve(LINGER, [LINGER, 'attach', name], ENV)
    fcntl.ioctl(fd, termios.TIOCSWINSZ, struct.pack('HHHH', rows, cols, 0, 0))
    return pid, fd


pid3, fd3 = spawn_sized('winch', 80, 24)
time.sleep(1.2)
os.write(fd3, REPORTER.encode())
time.sleep(1.0)
drain(fd3, 0.4)
base = winch_count()
os.write(fd3, b'\x1c')
time.sleep(0.6)
os.close(fd3)
os.waitpid(pid3, 0)

pid4, fd4 = spawn_sized('winch', 80, 24)
time.sleep(1.6)
drain(fd4, 0.4)
same = winch_count()
fails += expect(same == base, 'same-size reattach delivers no SIGWINCH (no redraw)')
os.write(fd4, b'\x1c')
time.sleep(0.6)
os.close(fd4)
os.waitpid(pid4, 0)

pid5, fd5 = spawn_sized('winch', 100, 30)
time.sleep(1.6)
drain(fd5, 0.4)
grown = winch_count()
fails += expect(grown > same, 'reattach at a new size nudges the program (SIGWINCH)')
os.write(fd5, b'\x1c')
time.sleep(0.5)
os.close(fd5)
os.waitpid(pid5, 0)
subprocess.run([LINGER, 'kill', 'winch'], env=ENV, capture_output=True, timeout=10)

print(f'FAILURES: {fails}')
sys.exit(1 if fails else 0)
