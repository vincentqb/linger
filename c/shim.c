/* linger C shim -- the raw POSIX operations missing from Lean's IO surface.
 *
 * Contract (AGENTS.md): syscall + errno only. No buffering, no retry
 * policy beyond EINTR, no session logic. Every function is a thin
 * wrapper whose behavior is stated in Linger/Posix.lean next to its
 * binding. All Lean object parameters are borrowed (@& on the Lean
 * side), so nothing here inc/decs references except allocations we
 * hand back.
 *
 * The pinned Lean compiler erases IO's world parameter and represents
 * Int32 arguments as uint32_t bits. Keep these signatures aligned with
 * the declarations generated from Linger/Posix.lean.
 */
/* accept4 needs _GNU_SOURCE on glibc */
#define _GNU_SOURCE
#include <lean/lean.h>

#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/file.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <sys/un.h>
#include <sys/wait.h>
#include <termios.h>
#include <unistd.h>
#ifdef __APPLE__
#include <libproc.h>   /* PROC_PIDVNODEPATHINFO: the /proc-less cwd read */
#endif

/* Hold the Lean poll bits to the ABI on each supported platform. */
_Static_assert(POLLIN == 0x001, "POLLIN");
_Static_assert(POLLOUT == 0x004, "POLLOUT");
_Static_assert(POLLERR == 0x008, "POLLERR");
_Static_assert(POLLHUP == 0x010, "POLLHUP");
_Static_assert(POLLNVAL == 0x020, "POLLNVAL");

static lean_obj_res io_err_code(const char *what, int code) {
    char buf[256];
    snprintf(buf, sizeof buf, "%s: %s (errno %d)", what, strerror(code), code);
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(buf)));
}

static lean_obj_res io_err(const char *what) { return io_err_code(what, errno); }

static lean_obj_res io_msg(const char *msg) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

static lean_obj_res io_ok_unit(void) { return lean_io_result_mk_ok(lean_box(0)); }

/* Child-side setup/exec failure reporting. The child writes one record to a
 * CLOEXEC pipe and _exits; a successful exec closes the pipe, so the parent
 * reads EOF. Without this, a failed setsid/dup2/execve is invisible: the
 * parent holds a pid that never became the requested program. */
struct spawn_err { char stage[24]; int code; };

static void release_stdio(unsigned held) {
    int e = errno;
    for (int fd = 0; fd <= STDERR_FILENO; fd++)
        if (held & (1u << fd)) close(fd);
    errno = e;
}

/* Reserve missing stdio slots until fork returns in the parent. Besides keeping
 * the report writer clear of dup2, this keeps libuv's pthread_atfork handler from
 * allocating its internal pipes below 3: its next fork aborts on such a pipe.
 * Returns the reserved-fd mask; the child replaces these with its own stdio. */
static int spawn_pipe(int fds[2]) {
    unsigned held = 0;
    for (int fd = 0; fd <= STDERR_FILENO; fd++) {
        if (fcntl(fd, F_GETFD) >= 0) continue;
        if (errno != EBADF) goto fail;
        int spare = open("/dev/null", O_RDWR | O_CLOEXEC);
        if (spare < 0) goto fail;
        if (spare != fd) { close(spare); errno = EBUSY; goto fail; }
        held |= 1u << fd;
    }
    if (pipe(fds) < 0) goto fail;
    if (fcntl(fds[1], F_SETFD, FD_CLOEXEC) < 0) {
        int e = errno;
        close(fds[0]); close(fds[1]);
        errno = e;
        goto fail;
    }
    return (int)held;
fail:
    release_stdio(held);
    return -1;
}

static void spawn_fail(int fd, const char *stage, int code) {
    struct spawn_err rec = { .code = code };
    /* No stdio formatting after fork; the last byte remains NUL. */
    strncpy(rec.stage, stage, sizeof rec.stage - 1);
    ssize_t n;
    do { n = write(fd, &rec, sizeof rec); } while (n < 0 && errno == EINTR);
    _exit(127);
}

/* 1 = the child reported a failure (record filled in); 0 = clean EOF. */
static int spawn_report(int fd, struct spawn_err *out) {
    size_t got = 0;
    while (got < sizeof *out) {
        ssize_t n = read(fd, (char *)out + got, sizeof *out - got);
        if (n == 0) break;
        if (n < 0) {
            if (errno == EINTR) continue;
            break;
        }
        got += (size_t)n;
    }
    return got == sizeof *out;
}

/* All argument vectors are built before fork; their strings remain borrowed. */
static char **exec_argv(b_lean_obj_arg prog, b_lean_obj_arg args) {
    size_t nargs = lean_array_size(args);
    char **argv = calloc(nargs + 2, sizeof(char *));
    if (!argv) return NULL;
    argv[0] = (char *)lean_string_cstr(prog);
    for (size_t i = 0; i < nargs; i++)
        argv[i + 1] = (char *)lean_string_cstr(lean_array_get_core(args, i));
    return argv;
}

static char **shell_argv(char **argv, size_t nargs) {
    char **out = calloc(nargs + 3, sizeof(char *));
    if (!out) return NULL;
    out[0] = (char *)"/bin/sh";
    for (size_t i = 0; i < nargs; i++) out[i + 2] = argv[i + 1];
    return out;
}

/* `key` includes '='. Resolve against the environment actually given to exec. */
static const char *env_value(char **envp, const char *key) {
    size_t n = strlen(key);
    for (size_t i = 0; envp[i]; i++)
        if (strncmp(envp[i], key, n) == 0) return envp[i] + n;
    return NULL;
}

/* execvp's PATH lookup and ENOEXEC shell fallback using only async-signal-safe
 * operations. In particular, a bare program is never tried outside PATH.
 * A failed shell fallback is final; only search misses and EACCES try another
 * candidate, with EACCES retained if no candidate succeeds. */
static void exec_search(char **argv, char **shargv, char **envp, const char *path) {
    const char *file = argv[0];
    if (!file[0]) { errno = ENOENT; return; }
    if (strchr(file, '/')) {
        execve(file, argv, envp);
        if (errno == ENOEXEC) {
            shargv[1] = argv[0];
            execve("/bin/sh", shargv, envp);
        }
        return;
    }
    char candidate[4096];
    size_t filelen = strlen(file);
    if (filelen >= sizeof candidate) { errno = ENAMETOOLONG; return; }
    int denied = 0;
    const char *seg = path ? path : "/usr/bin:/bin";
    for (;;) {
        const char *end = strchr(seg, ':');
        size_t len = end ? (size_t)(end - seg) : strlen(seg);
        if (len == 0 || len < sizeof candidate - filelen - 1) {
            size_t start = 0;
            if (len) {
                memcpy(candidate, seg, len);
                candidate[len] = '/';
                start = len + 1;
            }
            memcpy(candidate + start, file, filelen + 1);
            execve(candidate, argv, envp);
            if (errno == ENOEXEC) {
                shargv[1] = candidate;
                execve("/bin/sh", shargv, envp);
                return;
            }
            if (errno == EACCES) denied = 1;
            else if (errno != ENOENT && errno != ENOTDIR) return;
        }
        if (!end) break;
        seg = end + 1;  /* includes a final empty component */
    }
    errno = denied ? EACCES : ENOENT;
}

/* SOCK_CLOEXEC and accept4 set the close-on-exec flag atomically where they
 * exist (Linux, FreeBSD). macOS has neither, so there the flag is set after
 * socket()/accept(), and a fork inside that window inherits the descriptor.
 * Cli.cmdList creates local query sockets in tasks while it starts ssh with
 * IO.Process.spawn, which is fork plus execvp and closes no other
 * descriptors, so on macOS a socket created in that window can be inherited
 * by ssh until ssh exits. Not exported: no new syscall surface (SHIM_CAP). */
#ifdef SOCK_CLOEXEC
#define LINGER_HAVE_SOCK_CLOEXEC 1
#else
#define LINGER_HAVE_SOCK_CLOEXEC 0
#endif

static int unix_socket_cloexec(void) {
#if LINGER_HAVE_SOCK_CLOEXEC
    return socket(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0);
#else
    int fd = socket(AF_UNIX, SOCK_STREAM, 0);
    if (fd >= 0 && fcntl(fd, F_SETFD, FD_CLOEXEC) < 0) {
        int e = errno;
        close(fd);
        errno = e;
        return -1;
    }
    return fd;
#endif
}

static int accept_cloexec(int fd) {
#if LINGER_HAVE_SOCK_CLOEXEC
    return accept4(fd, NULL, NULL, SOCK_CLOEXEC);
#else
    int c = accept(fd, NULL, NULL);
    if (c >= 0 && fcntl(c, F_SETFD, FD_CLOEXEC) < 0) {
        int e = errno;
        close(c);
        errno = e;
        return -1;
    }
    return c;
#endif
}

/* -------------------------------------------------------------------- */
/* process-wide init                                                     */

/* linger_ignore_sighup : IO Unit  (daemon: survive controlling-tty death) */
LEAN_EXPORT lean_obj_res linger_ignore_sighup(void) {
    signal(SIGHUP, SIG_IGN);
    return io_ok_unit();
}

/* -------------------------------------------------------------------- */
/* fds                                                                   */

/* linger_close : UInt32 -> IO Unit */
LEAN_EXPORT lean_obj_res linger_close(uint32_t fd) {
    close((int)fd); /* errors on close are not actionable */
    return io_ok_unit();
}

static int set_nonblock(int fd) {
    int fl = fcntl(fd, F_GETFL, 0);
    return fl < 0 ? -1 : fcntl(fd, F_SETFL, fl | O_NONBLOCK);
}

/* linger_set_nonblock : UInt32 -> IO Unit */
LEAN_EXPORT lean_obj_res linger_set_nonblock(uint32_t fd) {
    if (set_nonblock((int)fd) < 0)
        return io_err("fcntl(O_NONBLOCK)");
    return io_ok_unit();
}

/* linger_read : UInt32 -> USize -> IO (Option ByteArray)
 * none          = EOF (incl. EIO from a pty master whose child died)
 * some #[]      = nothing available right now (EAGAIN on nonblocking fd)
 * some bytes    = data. EINTR is retried. */
LEAN_EXPORT lean_obj_res linger_read(uint32_t fd, size_t max) {
    if (max == 0) return io_msg("read: zero-length read cannot distinguish EOF");
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

/* linger_write : UInt32 -> @& ByteArray -> USize -> IO Int64
 * One write(2) attempt from offset `off`. >=0: bytes written (0 on
 * EAGAIN). -1: peer gone (EPIPE/ECONNRESET/EIO) -- a normal event for
 * daemons, not an exception. EINTR retried. */
LEAN_EXPORT lean_obj_res linger_write(uint32_t fd, b_lean_obj_arg bytes, size_t off) {
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

/* -------------------------------------------------------------------- */
/* poll                                                                  */

/* linger_poll : @& Array UInt32 -> @& Array UInt32 -> Int32 -> IO (Array UInt32)
 * fds and requested-events arrays (same length), timeout in ms (<0 =
 * infinite). Returns revents per fd; all-zero on EINTR or timeout. */
LEAN_EXPORT lean_obj_res linger_poll(b_lean_obj_arg fds, b_lean_obj_arg events,
                                  uint32_t timeout_ms) {
    size_t n = lean_array_size(fds);
    if (n != lean_array_size(events))
        return io_msg("poll: fds/events length mismatch");
    if (n > 4096)
        return io_msg("poll: too many fds");
    struct pollfd pfds[4096];
    for (size_t i = 0; i < n; i++) {
        pfds[i].fd = (int)lean_unbox_uint32(lean_array_get_core(fds, i));
        pfds[i].events = (short)lean_unbox_uint32(lean_array_get_core(events, i));
        pfds[i].revents = 0;
    }
    int r = poll(pfds, (nfds_t)n, (int32_t)timeout_ms);
    if (r < 0 && errno != EINTR) return io_err("poll");
    lean_object *out = lean_alloc_array(n, n);
    for (size_t i = 0; i < n; i++)
        lean_array_set_core(out, i,
                            lean_box_uint32(r < 0 ? 0 : (uint32_t)(uint16_t)pfds[i].revents));
    return lean_io_result_mk_ok(out);
}

/* -------------------------------------------------------------------- */
/* pty                                                                   */

/* linger_spawn_pty : UInt32 -> UInt32 -> @& String -> @& String
 *                 -> @& Array String -> @& Array String -> IO UInt64
 * open a pty and fork+execve a child on its slave, with PATH lookup. Returns
 * pid<<32 | masterFd. cwd "" = inherit. extraEnv entries are "K=V".
 * Child resets SIGPIPE/SIGHUP to default before exec; _exit(127) on fail.
 *
 * Uses the POSIX posix_openpt family rather than forkpty(3): forkpty
 * lives in libutil, which the Lean toolchain does not bundle and which
 * modern glibc (>= 2.34) folds into libc with no link stub — so
 * -lutil is unportable. posix_openpt/grantpt/unlockpt/ptsname/setsid/
 * TIOCSCTTY are all plain libc and do exactly what forkpty wraps. */
LEAN_EXPORT lean_obj_res linger_spawn_pty(uint32_t cols, uint32_t rows,
                                       b_lean_obj_arg cwd, b_lean_obj_arg prog,
                                       b_lean_obj_arg args, b_lean_obj_arg extra_env) {
    struct winsize ws;
    memset(&ws, 0, sizeof ws);
    ws.ws_col = (unsigned short)cols;
    ws.ws_row = (unsigned short)rows;

    /* argv/env must be materialized before fork: no allocation after. */
    size_t nargs = lean_array_size(args);
    char **argv = exec_argv(prog, args);
    if (!argv) return io_err("calloc");

    /* master pty, set up before fork so the slave name is known to the child */
    int master = posix_openpt(O_RDWR | O_NOCTTY);
    if (master < 0) { int e = errno; free(argv); return io_err_code("posix_openpt", e); }
    if (grantpt(master) < 0 || unlockpt(master) < 0) {
        int e = errno;
        close(master); free(argv);
        return io_err_code("grantpt/unlockpt", e);
    }
    /* ptsname's static buffer must be read before fork (async-signal-safe
     * territory after); copy it out. */
    char slavePath[128];
    const char *pn = ptsname(master);
    if (!pn) {
        int e = errno;
        close(master); free(argv);
        return io_err_code("ptsname", e);
    }
    if (strlen(pn) >= sizeof slavePath) {
        close(master); free(argv);
        return io_msg("spawn_pty: pty slave path too long");
    }
    memcpy(slavePath, pn, strlen(pn) + 1);
    if (fcntl(master, F_SETFD, FD_CLOEXEC) < 0) { /* child must not inherit the master */
        int e = errno;
        close(master); free(argv);
        return io_err_code("fcntl(master CLOEXEC)", e);
    }

    /* Pre-resolve everything the child would otherwise have to allocate for:
     * after fork it may only call async-signal-safe operations. */
    size_t nenv = lean_array_size(extra_env);
    char **envp = NULL;
    size_t envc = 0;
    {
        extern char **environ;
        size_t inherited = 0;
        while (environ[inherited]) inherited++;
        envp = calloc(inherited + nenv + 1, sizeof(char *));
        if (!envp) { int e = errno; close(master); free(argv); return io_err_code("calloc", e); }
        for (size_t i = 0; i < inherited; i++) envp[envc++] = environ[i];
        for (size_t i = 0; i < nenv; i++) {
            char *entry = (char *)lean_string_cstr(lean_array_get_core(extra_env, i));
            const char *eq = strchr(entry, '=');
            if (!eq) { close(master); free(argv); free(envp); return io_msg("spawn_pty: env entry is not K=V"); }
            size_t keylen = (size_t)(eq - entry) + 1;             /* include '=' */
            for (size_t j = 0; j < envc; j++)
                if (strncmp(envp[j], entry, keylen) == 0) { envp[j] = envp[--envc]; break; }
            envp[envc++] = entry;
        }
        envp[envc] = NULL;
    }
    const char *dir = lean_string_cstr(cwd);
    const char *home = env_value(envp, "HOME=");
    const char *path = env_value(envp, "PATH=");

    /* execvp's ENOEXEC fallback, pre-allocated: a file that is executable but not a
     * valid executable image (a script with no shebang) is handed to the shell. The
     * rewrite to execve dropped that silently, which narrowed `linger attach <name>
     * <cmd>` for exactly those files. Built here, not in the child, for the same
     * async-signal-safe reason as argv and envp; the child only fills in slot 1. */
    char **shargv = shell_argv(argv, nargs);
    if (!shargv) {
        int e = errno;
        close(master); free(argv); free(envp);
        return io_err_code("calloc", e);
    }

    int errPipe[2];
    int held = spawn_pipe(errPipe);
    if (held < 0) {
        int e = errno;
        close(master); free(argv); free(envp); free(shargv);
        return io_err_code("spawn_pipe", e);
    }

    pid_t pid = fork();
    if (pid != 0) release_stdio((unsigned)held);
    if (pid < 0) {
        int e = errno;
        close(errPipe[0]); close(errPipe[1]);
        close(master); free(argv); free(envp); free(shargv);
        return io_err_code("fork", e);
    }
    if (pid == 0) { /* child: make the slave our controlling tty + stdio */
        close(errPipe[0]);
        signal(SIGPIPE, SIG_DFL);
        signal(SIGHUP, SIG_DFL);
        if (setsid() < 0) spawn_fail(errPipe[1], "setsid", errno);
        int slave = open(slavePath, O_RDWR);
        if (slave < 0) spawn_fail(errPipe[1], "open(pty slave)", errno);
        if (ioctl(slave, TIOCSCTTY, 0) < 0) spawn_fail(errPipe[1], "TIOCSCTTY", errno);
        if (ioctl(slave, TIOCSWINSZ, &ws) < 0) spawn_fail(errPipe[1], "TIOCSWINSZ", errno);
        if (dup2(slave, 0) < 0 || dup2(slave, 1) < 0 || dup2(slave, 2) < 0)
            spawn_fail(errPipe[1], "dup2", errno);
        if (slave > 2) close(slave);
        if (dir[0] != '\0' && chdir(dir) != 0) {
            /* saved cwd may be gone after reboot; HOME beats dying */
            if (home && chdir(home) != 0) { /* keep inherited cwd */ }
        }
        exec_search(argv, shargv, envp, path);
        spawn_fail(errPipe[1], "execve", errno);
    }
    close(errPipe[1]);
    struct spawn_err rec;
    int failed = spawn_report(errPipe[0], &rec);
    close(errPipe[0]);
    free(argv);
    free(envp);
    free(shargv);
    if (failed) {
        int status;
        while (waitpid(pid, &status, 0) < 0 && errno == EINTR) {}
        close(master);
        char buf[128];
        snprintf(buf, sizeof buf, "spawn_pty: %s", rec.stage);
        return io_err_code(buf, rec.code);
    }
    return lean_io_result_mk_ok(
        lean_box_uint64(((uint64_t)(uint32_t)pid << 32) | (uint32_t)master));
}

/* linger_winsize_get : UInt32 -> IO UInt64   (cols<<32 | rows) */
LEAN_EXPORT lean_obj_res linger_winsize_get(uint32_t fd) {
    struct winsize ws;
    if (ioctl((int)fd, TIOCGWINSZ, &ws) < 0) return io_err("TIOCGWINSZ");
    return lean_io_result_mk_ok(
        lean_box_uint64(((uint64_t)ws.ws_col << 32) | ws.ws_row));
}

/* linger_winsize_set : UInt32 -> UInt32 -> UInt32 -> IO Unit
 * On a pty master this also delivers SIGWINCH to the foreground pgrp. */
LEAN_EXPORT lean_obj_res linger_winsize_set(uint32_t fd, uint32_t cols, uint32_t rows) {
    struct winsize ws;
    memset(&ws, 0, sizeof ws);
    ws.ws_col = (unsigned short)cols;
    ws.ws_row = (unsigned short)rows;
    if (ioctl((int)fd, TIOCSWINSZ, &ws) < 0) return io_err("TIOCSWINSZ");
    return io_ok_unit();
}

/* -------------------------------------------------------------------- */
/* termios                                                               */

/* linger_term_raw : UInt32 -> IO ByteArray
 * cfmakeraw the fd; returns the prior termios as opaque bytes. */
LEAN_EXPORT lean_obj_res linger_term_raw(uint32_t fd) {
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

/* linger_term_restore : UInt32 -> @& ByteArray -> IO Unit */
LEAN_EXPORT lean_obj_res linger_term_restore(uint32_t fd, b_lean_obj_arg saved) {
    if (lean_sarray_size(saved) != sizeof(struct termios))
        return io_msg("term_restore: bad termios blob");
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

/* linger_unix_listen : @& String -> IO UInt32  (caller unlinks stale paths) */
LEAN_EXPORT lean_obj_res linger_unix_listen(b_lean_obj_arg path) {
    struct sockaddr_un sa;
    if (fill_sockaddr(lean_string_cstr(path), &sa) < 0)
        return io_msg("listen: socket path empty or too long");
    int fd = unix_socket_cloexec();
    if (fd < 0) return io_err("socket");
    if (bind(fd, (struct sockaddr *)&sa, sizeof sa) < 0) {
        int e = errno;
        close(fd);
        return io_err_code("bind", e);
    }
    if (listen(fd, 64) < 0) {
        int e = errno;
        close(fd);
        return io_err_code("listen", e);
    }
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)fd));
}

/* linger_unix_connect : @& String -> Bool -> IO Int64
 * >=0: fd. <0: -errno (ENOENT / ECONNREFUSED are normal: no daemon /
 * stale socket; the caller decides). */
LEAN_EXPORT lean_obj_res linger_unix_connect(b_lean_obj_arg path, uint8_t nonblocking) {
    struct sockaddr_un sa;
    if (fill_sockaddr(lean_string_cstr(path), &sa) < 0)
        return lean_io_result_mk_ok(lean_box_uint64((uint64_t)(int64_t)-ENAMETOOLONG));
    int fd = unix_socket_cloexec();
    if (fd < 0) return io_err("socket");
    if (nonblocking && set_nonblock(fd) < 0) {
        int e = errno;
        close(fd);
        return io_err_code("fcntl(O_NONBLOCK)", e);
    }
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

/* linger_accept : UInt32 -> IO Int64
 * >=0: connection fd. -1: nothing to accept (EAGAIN -- listen fd is
 * nonblocking to close the poll/accept race). EINTR retried. */
LEAN_EXPORT lean_obj_res linger_accept(uint32_t fd) {
    int c;
    do { c = accept_cloexec((int)fd); }
    while (c < 0 && errno == EINTR);
    if (c < 0) {
        if (errno == EAGAIN || errno == EWOULDBLOCK || errno == ECONNABORTED)
            return lean_io_result_mk_ok(lean_box_uint64((uint64_t)(int64_t)-1));
        return io_err("accept");
    }
    return lean_io_result_mk_ok(lean_box_uint64((uint64_t)(int64_t)c));
}

/* linger_flock : @& String -> IO Int64
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
LEAN_EXPORT lean_obj_res linger_flock(b_lean_obj_arg path) {
    int fd = open(lean_string_cstr(path), O_RDWR | O_CREAT | O_CLOEXEC, 0600);
    if (fd < 0) return io_err("open(lockfile)");
    int r;
    do { r = flock(fd, LOCK_EX | LOCK_NB); } while (r < 0 && errno == EINTR);
    if (r < 0) {
        int e = errno;
        close(fd);
        if (e == EWOULDBLOCK) return lean_io_result_mk_ok(lean_box_uint64((uint64_t)(int64_t)-1));
        return io_err_code("flock", e);
    }
    return lean_io_result_mk_ok(lean_box_uint64((uint64_t)(int64_t)fd));
}

/* -------------------------------------------------------------------- */
/* processes                                                             */

/* linger_spawn_detached : @& String -> @& Array String -> @& String -> IO Unit
 * Double-fork + setsid; grandchild execve's with PATH lookup and stdio on logPath
 * (append, 0600; /dev/null if logPath == ""). No zombie remains. */
LEAN_EXPORT lean_obj_res linger_spawn_detached(b_lean_obj_arg prog, b_lean_obj_arg args,
                                            b_lean_obj_arg log_path) {
    size_t nargs = lean_array_size(args);
    char **argv = exec_argv(prog, args);
    if (!argv) return io_err("calloc");
    char **shargv = shell_argv(argv, nargs);
    if (!shargv) { int e = errno; free(argv); return io_err_code("calloc", e); }
    const char *logp = lean_string_cstr(log_path);
    extern char **environ;
    const char *path = env_value(environ, "PATH=");

    int errPipe[2];
    int held = spawn_pipe(errPipe);
    if (held < 0) {
        int e = errno;
        free(argv); free(shargv);
        return io_err_code("spawn_pipe", e);
    }

    pid_t pid = fork();
    if (pid != 0) release_stdio((unsigned)held);
    if (pid < 0) {
        int e = errno;
        close(errPipe[0]); close(errPipe[1]); free(argv); free(shargv);
        return io_err_code("fork", e);
    }
    if (pid == 0) { /* child */
        close(errPipe[0]);
        if (setsid() < 0) spawn_fail(errPipe[1], "setsid", errno);
        pid_t pid2 = fork();
        if (pid2 < 0) spawn_fail(errPipe[1], "fork", errno);
        if (pid2 != 0) _exit(0);
        /* grandchild: no ctty, own session. stdin first, so a closed fd 0
         * cannot alias the log descriptor. */
        int devnull = open("/dev/null", O_RDONLY);
        if (devnull < 0) spawn_fail(errPipe[1], "open(/dev/null)", errno);
        if (dup2(devnull, 0) < 0) spawn_fail(errPipe[1], "dup2(stdin)", errno);
        if (devnull > 0) close(devnull);
        int fd = logp[0] ? open(logp, O_WRONLY | O_CREAT | O_APPEND, 0600)
                         : open("/dev/null", O_WRONLY);
        if (fd < 0) spawn_fail(errPipe[1], "open(log)", errno);
        if (dup2(fd, 1) < 0 || dup2(fd, 2) < 0) spawn_fail(errPipe[1], "dup2(stdout)", errno);
        if (fd > 2) close(fd);
        signal(SIGHUP, SIG_IGN);
        exec_search(argv, shargv, environ, path);
        spawn_fail(errPipe[1], "execve", errno);
    }
    close(errPipe[1]);
    struct spawn_err rec;
    int failed = spawn_report(errPipe[0], &rec);
    close(errPipe[0]);
    int status;
    while (waitpid(pid, &status, 0) < 0 && errno == EINTR) {}
    free(argv);
    free(shargv);
    if (failed) {
        char buf[128];
        snprintf(buf, sizeof buf, "spawn_detached: %s", rec.stage);
        return io_err_code(buf, rec.code);
    }
    return io_ok_unit();
}

/* linger_kill : UInt32 -> UInt32 -> IO Unit  (ESRCH is not an error) */
LEAN_EXPORT lean_obj_res linger_kill(uint32_t pid, uint32_t sig) {
    if (kill((pid_t)pid, (int)sig) < 0 && errno != ESRCH) return io_err("kill");
    return io_ok_unit();
}

/* linger_alive : UInt32 -> IO Bool  (kill(pid, 0)) */
LEAN_EXPORT lean_obj_res linger_alive(uint32_t pid) {
    int r = kill((pid_t)pid, 0);
    return lean_io_result_mk_ok(lean_box(r == 0 ? 1 : 0));
}

/* linger_waitpid_nohang : UInt32 -> IO Int64
 * -1: the requested child is still running. -2: not our child or already
 * reaped (ECHILD -- the caller then asks linger_alive). >=0: exit status
 * byte (128+sig if signalled), reaping the zombie.
 *
 * There is no fourth outcome to report: the only other errno waitpid can
 * set here is EINVAL for bad options, and the options are the constant
 * WNOHANG. Selectors (pid 0, negative pid_t) never arrive -- Linger.Posix
 * .checkPid rejects them -- so a failure that is not ECHILD is answered
 * -2 rather than "running", which degrades to a liveness probe instead of
 * waiting forever on a child that cannot be reaped. */
LEAN_EXPORT lean_obj_res linger_waitpid_nohang(uint32_t pid) {
    int status;
    pid_t r;
    do { r = waitpid((pid_t)pid, &status, WNOHANG); }
    while (r < 0 && errno == EINTR);
    int64_t out;
    if (r == 0) {
        out = -1;
    } else if (r == (pid_t)pid) {
        if (WIFEXITED(status)) out = WEXITSTATUS(status);
        else if (WIFSIGNALED(status)) out = 128 + WTERMSIG(status);
        else out = -1; /* WNOHANG without WUNTRACED: not exited, so running */
    } else {
        out = -2;
    }
    return lean_io_result_mk_ok(lean_box_uint64((uint64_t)out));
}

/* -------------------------------------------------------------------- */
/* misc                                                                  */

/* getpid, chmod, both clocks, hostname, stdin tty detection, and the
 * full-write loop are Lean/core; see Linger/Posix.lean. */

/* linger_getuid : IO UInt32 */
LEAN_EXPORT lean_obj_res linger_getuid(void) {
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)getuid()));
}

/* linger_getcwd_of : UInt32 -> IO String
 * Where the session's shell currently sits, for checkpointing. Falls back
 * to "" when unreadable, and the caller then keeps the recorded start_dir.
 *
 * /proc/<pid>/cwd on Linux; macOS has no /proc, so there it is libproc's
 * PROC_PIDVNODEPATHINFO, which reports the same thing for a process of
 * our own uid (the session shell is our child). Returning "" on macOS
 * instead was silently wrong rather than broken: the resumed shell landed
 * in start_dir, so a reboot-resume reopened where the session was created
 * rather than where the user had cd'd to. libproc gives the resolved
 * vnode path (/private/tmp for /tmp) -- the point is the directory, and
 * the caller stores whatever string chdir will accept. */
LEAN_EXPORT lean_obj_res linger_getcwd_of(uint32_t pid) {
#ifdef __APPLE__
    struct proc_vnodepathinfo vpi;
    int n = proc_pidinfo((int)pid, PROC_PIDVNODEPATHINFO, 0, &vpi, sizeof vpi);
    if (n < (int)sizeof vpi) return lean_io_result_mk_ok(lean_mk_string(""));
    vpi.pvi_cdir.vip_path[sizeof vpi.pvi_cdir.vip_path - 1] = '\0';
    return lean_io_result_mk_ok(lean_mk_string(vpi.pvi_cdir.vip_path));
#else
    /* No truncation branch, and the mechanism is the kernel's, not readlink's:
     * readlink(2) does NOT signal a short buffer — it truncates and returns the byte
     * count. What protects us is that the kernel builds this link's target with
     * d_path into a PATH_MAX buffer and fails the whole call with ENAMETOOLONG when
     * the cwd does not fit, measured at exactly 4096 bytes and at ~4500. Asking for
     * sizeof buf - 1 (4095) then means a target that arrives at all arrives whole.
     * So `n < 0 -> ""` covers the over-long class. THIS IS WHY buf IS PATH_MAX: shrink
     * it and readlink starts truncating silently, with no error to notice.
     * lingertest's testDeepCwd pins the behaviour — a usable directory or nothing,
     * never a path naming somewhere else. */
    char link[64], buf[4096];
    snprintf(link, sizeof link, "/proc/%u/cwd", pid);
    ssize_t n = readlink(link, buf, sizeof buf - 1);
    if (n < 0) n = 0;
    buf[n] = '\0';
    return lean_io_result_mk_ok(lean_mk_string(buf));
#endif
}
