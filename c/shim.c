/* lean-zmx C shim -- the entire non-Lean surface of the project.
 *
 * Contract (AGENTS.md): syscall + errno only. No buffering, no retry
 * policy beyond EINTR, no session logic. Every function is a thin
 * wrapper whose behavior is stated in Zmx/Posix.lean next to its
 * binding. All Lean object parameters are borrowed (@& on the Lean
 * side), so nothing here inc/decs references except allocations we
 * hand back.
 */
/* accept4 needs _GNU_SOURCE on glibc */
#define _GNU_SOURCE
#include <lean/lean.h>

#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <pty.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/file.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/un.h>
#include <sys/wait.h>
#include <termios.h>
#include <time.h>
#include <unistd.h>

/* The Lean side hardcodes Linux poll bits; hold it to the ABI. */
_Static_assert(POLLIN == 0x001, "POLLIN");
_Static_assert(POLLOUT == 0x004, "POLLOUT");
_Static_assert(POLLERR == 0x008, "POLLERR");
_Static_assert(POLLHUP == 0x010, "POLLHUP");
_Static_assert(POLLNVAL == 0x020, "POLLNVAL");

static lean_obj_res io_err(const char *what) {
    char buf[256];
    snprintf(buf, sizeof buf, "%s: %s (errno %d)", what, strerror(errno), errno);
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(buf)));
}

static lean_obj_res io_ok_unit(void) { return lean_io_result_mk_ok(lean_box(0)); }

/* -------------------------------------------------------------------- */
/* process-wide init                                                     */

/* zmx_init : IO Unit
 * SIGPIPE must be ignored: a client vanishing between poll() and write()
 * would otherwise kill the daemon. Write errors surface as EPIPE. */
LEAN_EXPORT lean_obj_res zmx_init(lean_obj_arg w) {
    (void)w;
    signal(SIGPIPE, SIG_IGN);
    return io_ok_unit();
}

/* zmx_ignore_sighup : IO Unit  (daemon: survive controlling-tty death) */
LEAN_EXPORT lean_obj_res zmx_ignore_sighup(lean_obj_arg w) {
    (void)w;
    signal(SIGHUP, SIG_IGN);
    return io_ok_unit();
}

/* -------------------------------------------------------------------- */
/* fds                                                                   */

/* zmx_close : UInt32 -> IO Unit */
LEAN_EXPORT lean_obj_res zmx_close(uint32_t fd, lean_obj_arg w) {
    (void)w;
    close((int)fd); /* errors on close are not actionable */
    return io_ok_unit();
}

/* zmx_set_nonblock : UInt32 -> IO Unit */
LEAN_EXPORT lean_obj_res zmx_set_nonblock(uint32_t fd, lean_obj_arg w) {
    (void)w;
    int fl = fcntl((int)fd, F_GETFL, 0);
    if (fl < 0 || fcntl((int)fd, F_SETFL, fl | O_NONBLOCK) < 0)
        return io_err("fcntl(O_NONBLOCK)");
    return io_ok_unit();
}

/* zmx_read : UInt32 -> USize -> IO (Option ByteArray)
 * none          = EOF (incl. EIO from a pty master whose child died)
 * some #[]      = nothing available right now (EAGAIN on nonblocking fd)
 * some bytes    = data. EINTR is retried. */
LEAN_EXPORT lean_obj_res zmx_read(uint32_t fd, size_t max, lean_obj_arg w) {
    (void)w;
    if (max > 65536) max = 65536;
    unsigned char buf[65536];
    ssize_t n;
    do { n = read((int)fd, buf, max); } while (n < 0 && errno == EINTR);
    if (n < 0) {
        if (errno == EAGAIN || errno == EWOULDBLOCK) {
            lean_object *some = lean_alloc_ctor(1, 1, 0);
            lean_ctor_set(some, 0, lean_alloc_sarray(1, 0, 0));
            return lean_io_result_mk_ok(some);
        }
        if (errno == EIO) /* pty master: slave side gone */
            return lean_io_result_mk_ok(lean_box(0));
        return io_err("read");
    }
    if (n == 0) return lean_io_result_mk_ok(lean_box(0));
    lean_object *arr = lean_alloc_sarray(1, (size_t)n, (size_t)n);
    memcpy(lean_sarray_cptr(arr), buf, (size_t)n);
    lean_object *some = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(some, 0, arr);
    return lean_io_result_mk_ok(some);
}

/* zmx_write : UInt32 -> @& ByteArray -> USize -> IO Int64
 * One write(2) attempt from offset `off`. >=0: bytes written (0 on
 * EAGAIN). -1: peer gone (EPIPE/ECONNRESET/EIO) -- a normal event for
 * daemons, not an exception. EINTR retried. */
LEAN_EXPORT lean_obj_res zmx_write(uint32_t fd, b_lean_obj_arg bytes, size_t off,
                                   lean_obj_arg w) {
    (void)w;
    size_t len = lean_sarray_size(bytes);
    if (off >= len) return lean_io_result_mk_ok(lean_box_uint64(0));
    ssize_t n;
    do {
        n = write((int)fd, lean_sarray_cptr(bytes) + off, len - off);
    } while (n < 0 && errno == EINTR);
    if (n < 0) {
        if (errno == EAGAIN || errno == EWOULDBLOCK)
            return lean_io_result_mk_ok(lean_box_uint64(0));
        if (errno == EPIPE || errno == ECONNRESET || errno == EIO)
            return lean_io_result_mk_ok(lean_box_uint64((uint64_t)(int64_t)-1));
        return io_err("write");
    }
    return lean_io_result_mk_ok(lean_box_uint64((uint64_t)(int64_t)n));
}

/* zmx_write_all : UInt32 -> @& ByteArray -> IO Unit
 * Blocking full write for fds we own end-to-end (client's stdout). */
LEAN_EXPORT lean_obj_res zmx_write_all(uint32_t fd, b_lean_obj_arg bytes,
                                       lean_obj_arg w) {
    (void)w;
    size_t len = lean_sarray_size(bytes), off = 0;
    while (off < len) {
        ssize_t n = write((int)fd, lean_sarray_cptr(bytes) + off, len - off);
        if (n < 0) {
            if (errno == EINTR) continue;
            return io_err("write_all");
        }
        off += (size_t)n;
    }
    return io_ok_unit();
}

/* -------------------------------------------------------------------- */
/* poll                                                                  */

/* zmx_poll : @& Array UInt32 -> @& Array UInt32 -> Int32 -> IO (Array UInt32)
 * fds and requested-events arrays (same length), timeout in ms (<0 =
 * infinite). Returns revents per fd; all-zero on EINTR or timeout. */
LEAN_EXPORT lean_obj_res zmx_poll(b_lean_obj_arg fds, b_lean_obj_arg events,
                                  int32_t timeout_ms, lean_obj_arg w) {
    (void)w;
    size_t n = lean_array_size(fds);
    if (n != lean_array_size(events))
        return lean_io_result_mk_error(
            lean_mk_io_user_error(lean_mk_string("poll: fds/events length mismatch")));
    if (n > 4096)
        return lean_io_result_mk_error(
            lean_mk_io_user_error(lean_mk_string("poll: too many fds")));
    struct pollfd pfds[4096];
    for (size_t i = 0; i < n; i++) {
        pfds[i].fd = (int)lean_unbox_uint32(lean_array_get_core(fds, i));
        pfds[i].events = (short)lean_unbox_uint32(lean_array_get_core(events, i));
        pfds[i].revents = 0;
    }
    int r = poll(pfds, (nfds_t)n, (int)timeout_ms);
    if (r < 0 && errno != EINTR) return io_err("poll");
    lean_object *out = lean_alloc_array(n, n);
    for (size_t i = 0; i < n; i++)
        lean_array_set_core(out, i,
                            lean_box_uint32(r < 0 ? 0 : (uint32_t)(uint16_t)pfds[i].revents));
    return lean_io_result_mk_ok(out);
}

/* -------------------------------------------------------------------- */
/* pty                                                                   */

/* zmx_spawn_pty : UInt32 -> UInt32 -> @& String -> @& String
 *                 -> @& Array String -> @& Array String -> IO UInt64
 * forkpty + execvp. Returns pid<<32 | masterFd. cwd "" = inherit.
 * extraEnv entries are "K=V" strings applied with putenv semantics.
 * Child resets SIGPIPE to default before exec; _exit(127) on failure. */
LEAN_EXPORT lean_obj_res zmx_spawn_pty(uint32_t cols, uint32_t rows,
                                       b_lean_obj_arg cwd, b_lean_obj_arg prog,
                                       b_lean_obj_arg args, b_lean_obj_arg extra_env,
                                       lean_obj_arg w) {
    (void)w;
    struct winsize ws;
    memset(&ws, 0, sizeof ws);
    ws.ws_col = (unsigned short)cols;
    ws.ws_row = (unsigned short)rows;

    /* argv/env must be materialized before fork: no allocation after. */
    size_t nargs = lean_array_size(args);
    char **argv = calloc(nargs + 2, sizeof(char *));
    if (!argv) return io_err("calloc");
    argv[0] = (char *)lean_string_cstr(prog);
    for (size_t i = 0; i < nargs; i++)
        argv[i + 1] = (char *)lean_string_cstr(lean_array_get_core(args, i));

    int master = -1;
    pid_t pid = forkpty(&master, NULL, NULL, &ws);
    if (pid < 0) {
        free(argv);
        return io_err("forkpty");
    }
    if (pid == 0) { /* child: slave pty is now stdin/stdout/stderr + ctty */
        signal(SIGPIPE, SIG_DFL);
        signal(SIGHUP, SIG_DFL);
        for (size_t i = 0; i < lean_array_size(extra_env); i++) {
            /* putenv keeps the pointer; the string outlives us via exec or _exit */
            putenv(strdup(lean_string_cstr(lean_array_get_core(extra_env, i))));
        }
        const char *dir = lean_string_cstr(cwd);
        if (dir[0] != '\0' && chdir(dir) != 0) {
            /* saved cwd may be gone after reboot; HOME beats dying */
            const char *home = getenv("HOME");
            if (home) { if (chdir(home) != 0) { /* keep inherited cwd */ } }
        }
        execvp(lean_string_cstr(prog), argv);
        dprintf(2, "lzmx: exec %s: %s\r\n", lean_string_cstr(prog), strerror(errno));
        _exit(127);
    }
    free(argv);
    return lean_io_result_mk_ok(
        lean_box_uint64(((uint64_t)(uint32_t)pid << 32) | (uint32_t)master));
}

/* zmx_winsize_get : UInt32 -> IO UInt64   (cols<<32 | rows) */
LEAN_EXPORT lean_obj_res zmx_winsize_get(uint32_t fd, lean_obj_arg w) {
    (void)w;
    struct winsize ws;
    if (ioctl((int)fd, TIOCGWINSZ, &ws) < 0) return io_err("TIOCGWINSZ");
    return lean_io_result_mk_ok(
        lean_box_uint64(((uint64_t)ws.ws_col << 32) | ws.ws_row));
}

/* zmx_winsize_set : UInt32 -> UInt32 -> UInt32 -> IO Unit
 * On a pty master this also delivers SIGWINCH to the foreground pgrp. */
LEAN_EXPORT lean_obj_res zmx_winsize_set(uint32_t fd, uint32_t cols, uint32_t rows,
                                         lean_obj_arg w) {
    (void)w;
    struct winsize ws;
    memset(&ws, 0, sizeof ws);
    ws.ws_col = (unsigned short)cols;
    ws.ws_row = (unsigned short)rows;
    if (ioctl((int)fd, TIOCSWINSZ, &ws) < 0) return io_err("TIOCSWINSZ");
    return io_ok_unit();
}

/* -------------------------------------------------------------------- */
/* termios                                                               */

/* zmx_term_raw : UInt32 -> IO ByteArray
 * cfmakeraw the fd; returns the prior termios as opaque bytes. */
LEAN_EXPORT lean_obj_res zmx_term_raw(uint32_t fd, lean_obj_arg w) {
    (void)w;
    struct termios old, raw;
    if (tcgetattr((int)fd, &old) < 0) return io_err("tcgetattr");
    raw = old;
    cfmakeraw(&raw);
    raw.c_cc[VMIN] = 1;
    raw.c_cc[VTIME] = 0;
    if (tcsetattr((int)fd, TCSANOW, &raw) < 0) return io_err("tcsetattr(raw)");
    lean_object *arr = lean_alloc_sarray(1, sizeof old, sizeof old);
    memcpy(lean_sarray_cptr(arr), &old, sizeof old);
    return lean_io_result_mk_ok(arr);
}

/* zmx_term_restore : UInt32 -> @& ByteArray -> IO Unit */
LEAN_EXPORT lean_obj_res zmx_term_restore(uint32_t fd, b_lean_obj_arg saved,
                                          lean_obj_arg w) {
    (void)w;
    if (lean_sarray_size(saved) != sizeof(struct termios))
        return lean_io_result_mk_error(
            lean_mk_io_user_error(lean_mk_string("term_restore: bad termios blob")));
    struct termios t;
    memcpy(&t, lean_sarray_cptr(saved), sizeof t);
    if (tcsetattr((int)fd, TCSANOW, &t) < 0) return io_err("tcsetattr(restore)");
    return io_ok_unit();
}

/* -------------------------------------------------------------------- */
/* unix sockets                                                          */

static int fill_sockaddr(const char *path, struct sockaddr_un *sa) {
    size_t len = strlen(path);
    if (len == 0 || len >= sizeof sa->sun_path) return -1;
    memset(sa, 0, sizeof *sa);
    sa->sun_family = AF_UNIX;
    memcpy(sa->sun_path, path, len + 1);
    return 0;
}

/* zmx_unix_listen : @& String -> IO UInt32  (caller unlinks stale paths) */
LEAN_EXPORT lean_obj_res zmx_unix_listen(b_lean_obj_arg path, lean_obj_arg w) {
    (void)w;
    struct sockaddr_un sa;
    if (fill_sockaddr(lean_string_cstr(path), &sa) < 0)
        return lean_io_result_mk_error(
            lean_mk_io_user_error(lean_mk_string("listen: socket path empty or too long")));
    int fd = socket(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0);
    if (fd < 0) return io_err("socket");
    if (bind(fd, (struct sockaddr *)&sa, sizeof sa) < 0) {
        close(fd);
        return io_err("bind");
    }
    if (listen(fd, 64) < 0) {
        close(fd);
        return io_err("listen");
    }
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)fd));
}

/* zmx_unix_connect : @& String -> IO Int64
 * >=0: fd. <0: -errno (ENOENT / ECONNREFUSED are normal: no daemon /
 * stale socket; the caller decides). */
LEAN_EXPORT lean_obj_res zmx_unix_connect(b_lean_obj_arg path, lean_obj_arg w) {
    (void)w;
    struct sockaddr_un sa;
    if (fill_sockaddr(lean_string_cstr(path), &sa) < 0)
        return lean_io_result_mk_ok(lean_box_uint64((uint64_t)(int64_t)-ENAMETOOLONG));
    int fd = socket(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0);
    if (fd < 0) return io_err("socket");
    int r;
    do { r = connect(fd, (struct sockaddr *)&sa, sizeof sa); }
    while (r < 0 && errno == EINTR);
    if (r < 0) {
        int e = errno;
        close(fd);
        return lean_io_result_mk_ok(lean_box_uint64((uint64_t)(int64_t)-e));
    }
    return lean_io_result_mk_ok(lean_box_uint64((uint64_t)(int64_t)fd));
}

/* zmx_accept : UInt32 -> IO Int64
 * >=0: connection fd. -1: nothing to accept (EAGAIN -- listen fd is
 * nonblocking to close the poll/accept race). EINTR retried. */
LEAN_EXPORT lean_obj_res zmx_accept(uint32_t fd, lean_obj_arg w) {
    (void)w;
    int c;
    do { c = accept4((int)fd, NULL, NULL, SOCK_CLOEXEC); }
    while (c < 0 && errno == EINTR);
    if (c < 0) {
        if (errno == EAGAIN || errno == EWOULDBLOCK || errno == ECONNABORTED)
            return lean_io_result_mk_ok(lean_box_uint64((uint64_t)(int64_t)-1));
        return io_err("accept");
    }
    return lean_io_result_mk_ok(lean_box_uint64((uint64_t)(int64_t)c));
}

/* zmx_flock : @& String -> IO Int64
 * Exclusive, non-blocking lock on `path` (created 0600). Returns the
 * held fd (>= 0) or -1 if someone else holds it.
 *
 * flock, not an O_EXCL/mkdir lock file: the kernel releases it when the
 * holder dies or the fd closes, so a SIGKILLed or power-cut daemon
 * leaves nothing stale behind and no staleness timeout has to be
 * invented. The caller must keep the fd open for as long as it wants
 * the lock, and must NOT unlink the lock file -- unlinking would let a
 * second process create a fresh inode and lock that while we still hold
 * the old one. */
LEAN_EXPORT lean_obj_res zmx_flock(b_lean_obj_arg path, lean_obj_arg w) {
    (void)w;
    int fd = open(lean_string_cstr(path), O_RDWR | O_CREAT | O_CLOEXEC, 0600);
    if (fd < 0) return io_err("open(lockfile)");
    int r;
    do { r = flock(fd, LOCK_EX | LOCK_NB); } while (r < 0 && errno == EINTR);
    if (r < 0) {
        int e = errno;
        close(fd);
        if (e == EWOULDBLOCK) return lean_io_result_mk_ok(lean_box_uint64((uint64_t)(int64_t)-1));
        errno = e;
        return io_err("flock");
    }
    return lean_io_result_mk_ok(lean_box_uint64((uint64_t)(int64_t)fd));
}

/* -------------------------------------------------------------------- */
/* processes                                                             */

/* zmx_spawn_detached : @& String -> @& Array String -> @& String -> IO Unit
 * Double-fork + setsid; grandchild execvp's with stdio on logPath
 * (append, 0600; /dev/null if logPath == ""). No zombie remains. */
LEAN_EXPORT lean_obj_res zmx_spawn_detached(b_lean_obj_arg prog, b_lean_obj_arg args,
                                            b_lean_obj_arg log_path, lean_obj_arg w) {
    (void)w;
    size_t nargs = lean_array_size(args);
    char **argv = calloc(nargs + 2, sizeof(char *));
    if (!argv) return io_err("calloc");
    argv[0] = (char *)lean_string_cstr(prog);
    for (size_t i = 0; i < nargs; i++)
        argv[i + 1] = (char *)lean_string_cstr(lean_array_get_core(args, i));
    const char *logp = lean_string_cstr(log_path);

    pid_t pid = fork();
    if (pid < 0) {
        free(argv);
        return io_err("fork");
    }
    if (pid == 0) { /* child */
        if (setsid() < 0) _exit(126);
        pid_t pid2 = fork();
        if (pid2 != 0) _exit(pid2 < 0 ? 126 : 0);
        /* grandchild: no ctty, own session */
        int fd = logp[0] ? open(logp, O_WRONLY | O_CREAT | O_APPEND, 0600)
                         : open("/dev/null", O_RDWR);
        int devnull = open("/dev/null", O_RDONLY);
        if (devnull >= 0) { dup2(devnull, 0); if (devnull > 0) close(devnull); }
        if (fd >= 0) {
            dup2(fd, 1);
            dup2(fd, 2);
            if (fd > 2) close(fd);
        }
        signal(SIGHUP, SIG_IGN);
        execvp(lean_string_cstr(prog), argv);
        _exit(127);
    }
    free(argv);
    int status;
    while (waitpid(pid, &status, 0) < 0 && errno == EINTR) {}
    return io_ok_unit();
}

/* zmx_exec : @& String -> @& Array String -> IO Unit  (replaces the process) */
LEAN_EXPORT lean_obj_res zmx_exec(b_lean_obj_arg prog, b_lean_obj_arg args,
                                  lean_obj_arg w) {
    (void)w;
    size_t nargs = lean_array_size(args);
    char **argv = calloc(nargs + 2, sizeof(char *));
    if (!argv) return io_err("calloc");
    argv[0] = (char *)lean_string_cstr(prog);
    for (size_t i = 0; i < nargs; i++)
        argv[i + 1] = (char *)lean_string_cstr(lean_array_get_core(args, i));
    execvp(lean_string_cstr(prog), argv);
    free(argv);
    return io_err("execvp");
}

/* zmx_kill : UInt32 -> UInt32 -> IO Unit  (ESRCH is not an error) */
LEAN_EXPORT lean_obj_res zmx_kill(uint32_t pid, uint32_t sig, lean_obj_arg w) {
    (void)w;
    if (kill((pid_t)pid, (int)sig) < 0 && errno != ESRCH) return io_err("kill");
    return io_ok_unit();
}

/* zmx_alive : UInt32 -> IO Bool  (kill(pid, 0)) */
LEAN_EXPORT lean_obj_res zmx_alive(uint32_t pid, lean_obj_arg w) {
    (void)w;
    int r = kill((pid_t)pid, 0);
    return lean_io_result_mk_ok(lean_box(r == 0 ? 1 : 0));
}

/* zmx_waitpid_nohang : UInt32 -> IO Int64
 * -1: still running (or not our child). >=0: exit status byte
 * (128+sig if signalled), reaping the zombie. */
LEAN_EXPORT lean_obj_res zmx_waitpid_nohang(uint32_t pid, lean_obj_arg w) {
    (void)w;
    int status;
    pid_t r;
    do { r = waitpid((pid_t)pid, &status, WNOHANG); }
    while (r < 0 && errno == EINTR);
    int64_t out = -1;
    if (r == (pid_t)pid) {
        if (WIFEXITED(status)) out = WEXITSTATUS(status);
        else if (WIFSIGNALED(status)) out = 128 + WTERMSIG(status);
        else out = -1;
    } else if (r < 0 && errno == ECHILD) {
        out = -2; /* not our child / already reaped: caller checks zmx_alive */
    }
    return lean_io_result_mk_ok(lean_box_uint64((uint64_t)out));
}

/* -------------------------------------------------------------------- */
/* misc                                                                  */

/* zmx_getpid : IO UInt32 */
LEAN_EXPORT lean_obj_res zmx_getpid(lean_obj_arg w) {
    (void)w;
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)getpid()));
}

/* zmx_getuid : IO UInt32 */
LEAN_EXPORT lean_obj_res zmx_getuid(lean_obj_arg w) {
    (void)w;
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)getuid()));
}

/* zmx_isatty : UInt32 -> IO Bool */
LEAN_EXPORT lean_obj_res zmx_isatty(uint32_t fd, lean_obj_arg w) {
    (void)w;
    return lean_io_result_mk_ok(lean_box(isatty((int)fd) == 1 ? 1 : 0));
}

/* zmx_chmod : @& String -> UInt32 -> IO Unit */
LEAN_EXPORT lean_obj_res zmx_chmod(b_lean_obj_arg path, uint32_t mode, lean_obj_arg w) {
    (void)w;
    if (chmod(lean_string_cstr(path), (mode_t)mode) < 0) return io_err("chmod");
    return io_ok_unit();
}

/* zmx_getcwd_of : UInt32 -> IO String
 * /proc/<pid>/cwd -- where the session's shell currently sits, for
 * checkpointing. Falls back to "" when unreadable. */
LEAN_EXPORT lean_obj_res zmx_getcwd_of(uint32_t pid, lean_obj_arg w) {
    (void)w;
    char link[64], buf[4096];
    snprintf(link, sizeof link, "/proc/%u/cwd", pid);
    ssize_t n = readlink(link, buf, sizeof buf - 1);
    if (n < 0) n = 0;
    buf[n] = '\0';
    return lean_io_result_mk_ok(lean_mk_string(buf));
}

/* zmx_gethostname : IO String */
LEAN_EXPORT lean_obj_res zmx_gethostname(lean_obj_arg w) {
    (void)w;
    char buf[256];
    if (gethostname(buf, sizeof buf) < 0) buf[0] = '\0';
    buf[sizeof buf - 1] = '\0';
    return lean_io_result_mk_ok(lean_mk_string(buf));
}

/* zmx_monotonic_ms : IO UInt64  (CLOCK_MONOTONIC, for checkpoint cadence) */
LEAN_EXPORT lean_obj_res zmx_monotonic_ms(lean_obj_arg w) {
    (void)w;
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return lean_io_result_mk_ok(
        lean_box_uint64((uint64_t)ts.tv_sec * 1000 + (uint64_t)ts.tv_nsec / 1000000));
}

/* zmx_realtime_s : IO UInt64  (unix epoch seconds, for labels/list) */
LEAN_EXPORT lean_obj_res zmx_realtime_s(lean_obj_arg w) {
    (void)w;
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    return lean_io_result_mk_ok(lean_box_uint64((uint64_t)ts.tv_sec));
}
