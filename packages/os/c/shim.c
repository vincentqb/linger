/* linger C shim -- the raw POSIX operations missing from Lean's IO surface.
 *
 * Contract (AGENTS.md): syscall + errno only. No buffering, no retry
 * policy beyond EINTR, no session logic. Every function is a thin
 * wrapper bound in packages/os/Os/WorldSpec.lean; its behavior is stated on
 * the Lean wrapper of the same name in packages/os/Os/WorldCode.lean. All Lean
 * object parameters are borrowed (@& on the Lean side), so nothing here
 * inc/decs references except allocations we hand back.
 *
 * The pinned Lean compiler erases IO's world parameter and represents
 * Int32 arguments as uint32_t bits. Keep these signatures aligned with
 * the declarations generated from packages/os/Os/WorldSpec.lean.
 */
/* accept4 needs _GNU_SOURCE on glibc */
#define _GNU_SOURCE
#include <lean/lean.h>

#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <poll.h>
#include <pthread.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/file.h>
#include <sys/resource.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/un.h>
#include <sys/wait.h>
#include <termios.h>
#include <unistd.h>
#ifdef __APPLE__
#include <libproc.h>   /* PROC_PIDVNODEPATHINFO: the /proc-less cwd read */
#include <sys/stat.h>  /* stat: check that path against the cwd vnode */
#include <sys/sysctl.h>  /* KERN_PROCARGS2: the /proc-less command line read */
#else
#include <dirent.h>       /* the /proc listing of linger_signal_session */
#include <sys/syscall.h>  /* pidfd_open, pidfd_send_signal and close_range, which glibc may not wrap */
#ifndef SYS_pidfd_open
#define SYS_pidfd_open 434 /* the same number on x86-64 and arm64 */
#endif
#ifndef SYS_pidfd_send_signal
#define SYS_pidfd_send_signal 424
#endif
#if defined(__linux__) && !defined(SYS_close_range)
#define SYS_close_range 436 /* Linux 5.9; the same number on x86-64 and arm64 */
#endif
#ifndef SYS_renameat2
#if defined(__x86_64__)
#define SYS_renameat2 316 /* Linux 3.15 */
#elif defined(__aarch64__)
#define SYS_renameat2 276
#endif
#endif
#ifndef RENAME_NOREPLACE
#define RENAME_NOREPLACE (1 << 0) /* <linux/fs.h>, which glibc before 2.28 does not pass on */
#endif
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

/* A started program (Except.ok) or why one did not start (Except.error): the
 * failure's kind and the OS's words for it. */
static lean_obj_res spawn_started(uint64_t packed) {
    lean_object *started = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(started, 0, lean_box_uint64(packed));
    return lean_io_result_mk_ok(started);
}

static lean_obj_res spawn_refused(uint8_t why, int code) {
    lean_object *pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, lean_box(why));
    lean_ctor_set(pair, 1, lean_mk_string(strerror(code)));
    lean_object *refused = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(refused, 0, pair);
    return lean_io_result_mk_ok(refused);
}

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

/* Read up to len bytes, retrying EINTR, until EOF or another error. Returns the
 * count read. */
static size_t read_full(int fd, void *buf, size_t len) {
    size_t got = 0;
    while (got < len) {
        ssize_t n = read(fd, (char *)buf + got, len - got);
        if (n == 0) break;
        if (n < 0) {
            if (errno == EINTR) continue;
            break;
        }
        got += (size_t)n;
    }
    return got;
}

/* 1 = the child reported a failure (record filled in); 0 = clean EOF. */
static int spawn_report(int fd, struct spawn_err *out) {
    return read_full(fd, out, sizeof *out) == sizeof *out;
}

/* One past the highest descriptor this process can hold, the soft RLIMIT_NOFILE, which bounds
 * the close loop where close_range is missing. Read before fork: getrlimit is not on POSIX's
 * async-signal-safe list. Linux and macOS both keep this limit finite. */
static int fd_limit(void) {
    struct rlimit rl;
    if (getrlimit(RLIMIT_NOFILE, &rl) < 0 || rl.rlim_cur >= (rlim_t)INT_MAX) return INT_MAX;
    return (int)rl.rlim_cur;
}

/* Close every descriptor from 3 up but `keep`, the exec-error report pipe, which closes on exec
 * by itself. close_range does it in at most two calls where the kernel has it (Linux 5.9);
 * elsewhere, as on macOS, and where it fails, each descriptor below `limit` is closed. */
static void close_from_3(int keep, int limit) {
#ifdef SYS_close_range
    unsigned low = 3;
    int ok = 1;
    if (keep >= 3) {
        if (keep > 3) ok = syscall(SYS_close_range, 3u, (unsigned)keep - 1, 0u) == 0;
        low = (unsigned)keep + 1;
    }
    if (ok && syscall(SYS_close_range, low, ~0u, 0u) == 0) return;
#endif
    for (int fd = 3; fd < limit; fd++)
        if (fd != keep) close(fd);
}

/* What a spawned program starts without, of the state this process would pass on: with
 * `dispositions`, every catchable signal goes back to its default action; with `mask`, no signal
 * stays blocked; with `descriptors`, no descriptor from 3 up stays open but `keep`. A handler
 * ends at exec by itself, but an ignored signal, the mask and every descriptor not marked
 * close-on-exec survive it. Runs after fork, with plain syscalls only. */
static void spawn_reset(int dispositions, int mask, int descriptors, int keep, int limit) {
    if (dispositions) {
        struct sigaction dfl;
        memset(&dfl, 0, sizeof dfl);
        dfl.sa_handler = SIG_DFL;
        sigemptyset(&dfl.sa_mask);
        /* SIGKILL and SIGSTOP have no other disposition, and glibc refuses the two it keeps for
         * itself, which nothing can have ignored: those calls fail and change nothing. */
        for (int sig = 1; sig < NSIG; sig++)
            if (sig != SIGKILL && sig != SIGSTOP) sigaction(sig, &dfl, NULL);
    }
    if (mask) {
        sigset_t none;
        sigemptyset(&none);
        sigprocmask(SIG_SETMASK, &none, NULL);
    }
    if (descriptors) close_from_3(keep, limit);
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
 * `linger ls` creates local query sockets in tasks while it starts ssh with
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
    /* BSD accept copies the listener's O_NONBLOCK, which accept4 never does: clear
     * it, so an accepted socket is blocking on every platform. */
    int c = accept(fd, NULL, NULL);
    int fl;
    if (c < 0) return -1;
    if (fcntl(c, F_SETFD, FD_CLOEXEC) < 0 || (fl = fcntl(c, F_GETFL, 0)) < 0 ||
        fcntl(c, F_SETFL, fl & ~O_NONBLOCK) < 0) {
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
 * One write(2) attempt from offset `off`, one value for each outcome.
 * >=0: bytes written (0 only when `off` is at or past the end, with no
 * write(2)). -EAGAIN: nothing written, the descriptor is nonblocking and
 * full (EWOULDBLOCK reported as EAGAIN). -1: nothing written, the reader is
 * gone: EPIPE, ECONNRESET, or EIO from a terminal, which is how a pty reports
 * that its other side closed; EIO from anything else is a device error. A
 * daemon meets the last two as normal events, not exceptions. EINTR retried;
 * other errors throw. */
LEAN_EXPORT lean_obj_res linger_write(uint32_t fd, b_lean_obj_arg bytes, size_t off) {
    size_t len = lean_sarray_size(bytes);
    if (off >= len) return lean_io_result_mk_ok(lean_box_uint64(0));
    ssize_t n;
    do {
        n = write((int)fd, lean_sarray_cptr(bytes) + off, len - off);
    } while (n < 0 && errno == EINTR);
    if (n < 0) {
        int e = errno;
        if (e == EAGAIN || e == EWOULDBLOCK)
            return lean_io_result_mk_ok(lean_box_uint64((uint64_t)(int64_t)-EAGAIN));
        if (e == EPIPE || e == ECONNRESET || (e == EIO && isatty((int)fd)))
            return lean_io_result_mk_ok(lean_box_uint64((uint64_t)(int64_t)-1));
        return io_err_code("write", e);
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
 *                 -> @& Array String -> @& Array String -> Bool -> Bool -> Bool
 *                 -> IO (Except (UInt8 × String) UInt64)
 * open a pty and fork+execve a child on its slave, with PATH lookup. Returns
 * pid<<32 | masterFd. cwd "" = inherit; a cwd the child cannot enter is a
 * failure, whatever $HOME is. extraEnv entries are
 * "K=V". Child resets SIGPIPE/SIGHUP to default before exec, and with
 * dispositions, mask and descriptors does what spawn_reset says.
 *
 * A program that cannot start is answered Except.error (why, the OS's words):
 * why 1 is its directory (125, as env -C), 2 no such program (127), 3 found
 * but not runnable (126). A started one is Except.ok (pid<<32 | masterFd).
 * The other setup failures throw.
 *
 * Uses the POSIX posix_openpt family rather than forkpty(3): forkpty
 * lives in libutil, which the Lean toolchain does not bundle and which
 * modern glibc (>= 2.34) folds into libc with no link stub — so
 * -lutil is unportable. posix_openpt/grantpt/unlockpt/ptsname/setsid/
 * TIOCSCTTY are all plain libc and do exactly what forkpty wraps. */
LEAN_EXPORT lean_obj_res linger_spawn_pty(uint32_t cols, uint32_t rows,
                                       b_lean_obj_arg cwd,
                                       b_lean_obj_arg prog, b_lean_obj_arg args,
                                       b_lean_obj_arg extra_env, uint8_t dispositions,
                                       uint8_t mask, uint8_t descriptors) {
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
        /* "K=V" sets K; a bare "K" unsets it */
        for (size_t i = 0; i < nenv; i++) {
            char *entry = (char *)lean_string_cstr(lean_array_get_core(extra_env, i));
            const char *eq = strchr(entry, '=');
            size_t keylen = eq ? (size_t)(eq - entry) : strlen(entry);
            if (keylen == 0) { close(master); free(argv); free(envp); return io_msg("spawn_pty: env entry has no name"); }
            for (size_t j = 0; j < envc; j++)
                if (strncmp(envp[j], entry, keylen) == 0 && envp[j][keylen] == '=') { envp[j] = envp[--envc]; break; }
            if (eq) envp[envc++] = entry;
        }
        envp[envc] = NULL;
    }
    const char *dir = lean_string_cstr(cwd);
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
    int limit = fd_limit();

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
        if (dir[0] != '\0' && chdir(dir) != 0) spawn_fail(errPipe[1], "chdir", errno);
        spawn_reset(dispositions, mask, descriptors, errPipe[1], limit);
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
        uint8_t why = 0;
        if (strcmp(rec.stage, "chdir") == 0) why = 1;
        else if (strcmp(rec.stage, "execve") == 0) why = rec.code == ENOENT ? 2 : 3;
        if (why != 0) return spawn_refused(why, rec.code);
        char buf[128];
        snprintf(buf, sizeof buf, "spawn_pty: %s", rec.stage);
        return io_err_code(buf, rec.code);
    }
    return spawn_started(((uint64_t)(uint32_t)pid << 32) | (uint32_t)master);
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
 * Exclusive, non-blocking lock on the file at `path` (created 0600). Returns
 * the held fd (>= 0) or -1 if someone else holds it.
 *
 * flock, not an O_EXCL/mkdir lock file: the kernel releases it when the
 * holder dies or the fd closes, so a SIGKILLed or power-cut daemon
 * leaves nothing stale behind and no staleness timeout has to be
 * invented. The caller must keep the fd open for as long as it wants
 * the lock. The lock is the inode's, not the path's: a holder may unlink
 * the file, after which another process creates and locks a fresh one, so
 * a caller that wants the path's lock checks, once it holds this one, that
 * the path still names the file it locked (linger_names_held). */
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

/* linger_names_held : UInt32 -> @& String -> IO Bool
 * Whether `path` names the file `fd` holds open: fstat(fd) and stat(path)
 * report the same device and inode. A path that names nothing (ENOENT,
 * ENOTDIR) names another file; any other failure is an error. */
LEAN_EXPORT lean_obj_res linger_names_held(uint32_t fd, b_lean_obj_arg path) {
    struct stat held, named;
    if (fstat((int)fd, &held) < 0) return io_err("fstat(lock)");
    if (stat(lean_string_cstr(path), &named) < 0) {
        if (errno == ENOENT || errno == ENOTDIR) return lean_io_result_mk_ok(lean_box(0));
        return io_err("stat(lock)");
    }
    int same = held.st_dev == named.st_dev && held.st_ino == named.st_ino;
    return lean_io_result_mk_ok(lean_box(same ? 1 : 0));
}

/* -------------------------------------------------------------------- */
/* durability                                                            */

/* linger_fsync_path : @& String -> Bool -> IO Bool
 * Open `path` read-only (with `directory`, as a directory: O_DIRECTORY),
 * flush it to the device and close it: true once flushed. O_NONBLOCK keeps
 * the open from waiting for a writer when the path is a FIFO, which fsync
 * then refuses (EINVAL). fsync(2) on macOS hands the data to the drive and
 * stops there, so the drive's own cache can still lose it on power loss;
 * fcntl(F_FULLFSYNC) asks the drive to write that cache too. A file system
 * that does not offer it (an SMB mount answers ENOTSUP) gets fsync. A file
 * system that cannot flush a directory at all answers EINVAL, as some
 * network and FUSE ones do: false, since nothing more can be asked of it.
 * EINTR is retried; any other flush error is reported, never retried, since
 * the kernel may drop the pages it failed to write. */
LEAN_EXPORT lean_obj_res linger_fsync_path(b_lean_obj_arg path, uint8_t directory) {
    int fd;
    do {
        fd = open(lean_string_cstr(path),
                  O_RDONLY | O_NONBLOCK | O_CLOEXEC | (directory ? O_DIRECTORY : 0));
    } while (fd < 0 && errno == EINTR);
    if (fd < 0) return io_err("open(fsync)");
    int r = -1;
#ifdef __APPLE__
    do { r = fcntl(fd, F_FULLFSYNC); } while (r < 0 && errno == EINTR);
    if (r < 0 && (errno == ENOTSUP || errno == ENOTTY))
#endif
    {
        do { r = fsync(fd); } while (r < 0 && errno == EINTR);
    }
    int e = errno;
    close(fd);
    if (r == 0) return lean_io_result_mk_ok(lean_box(1));
    if (directory && e == EINVAL) return lean_io_result_mk_ok(lean_box(0));
    return io_err_code("fsync", e);
}

/* -------------------------------------------------------------------- */
/* names placed without replacing                                        */

/* linger_link_new : @& String -> @& String -> IO Bool
 * link(2) the name `dst` to the file `src` names: true once linked, false
 * when `dst` already names something (EEXIST), which link never replaces. */
LEAN_EXPORT lean_obj_res linger_link_new(b_lean_obj_arg src, b_lean_obj_arg dst) {
    if (link(lean_string_cstr(src), lean_string_cstr(dst)) == 0)
        return lean_io_result_mk_ok(lean_box(1));
    if (errno == EEXIST) return lean_io_result_mk_ok(lean_box(0));
    return io_err("link");
}

/* linger_rename_new : @& String -> @& String -> IO Bool
 * Rename `src` to `dst` in one step, only while `dst` names nothing:
 * renameat2(RENAME_NOREPLACE) on Linux, renamex_np(RENAME_EXCL) on macOS.
 * true once renamed, false when `dst` already names something (EEXIST). A
 * file system that cannot rename without replacing answers EINVAL on Linux
 * and ENOTSUP on macOS, an error like any other, never a plain rename. */
LEAN_EXPORT lean_obj_res linger_rename_new(b_lean_obj_arg src, b_lean_obj_arg dst) {
#ifdef __APPLE__
    int r = renamex_np(lean_string_cstr(src), lean_string_cstr(dst), RENAME_EXCL);
#else
    long r = syscall(SYS_renameat2, AT_FDCWD, lean_string_cstr(src), AT_FDCWD,
                     lean_string_cstr(dst), RENAME_NOREPLACE);
#endif
    if (r == 0) return lean_io_result_mk_ok(lean_box(1));
    if (errno == EEXIST) return lean_io_result_mk_ok(lean_box(0));
    return io_err("rename(no replace)");
}

/* -------------------------------------------------------------------- */
/* processes                                                             */

/* linger_spawn_detached : @& String -> @& Array String -> @& String -> IO UInt32
 * Double-fork + setsid; grandchild execve's with PATH lookup and stdio on logPath
 * (append, 0600; /dev/null if logPath == ""), every signal at its default action but
 * SIGHUP, ignored, none blocked and no descriptor from 3 up (spawn_reset). No zombie
 * remains. Returns the grandchild's pid, which the intermediate child writes before it
 * exits. */
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
    /* fds 0-2 are occupied while `held`, so neither end can land on stdio. A failed
     * pipe leaves the array unmodified, so -1 marks that nothing was opened. */
    int pidPipe[2] = { -1, -1 };
    if (pipe(pidPipe) < 0 || fcntl(pidPipe[1], F_SETFD, FD_CLOEXEC) < 0) {
        int e = errno;
        release_stdio((unsigned)held);
        if (pidPipe[0] >= 0) { close(pidPipe[0]); close(pidPipe[1]); }
        close(errPipe[0]); close(errPipe[1]); free(argv); free(shargv);
        return io_err_code("pid pipe", e);
    }
    int limit = fd_limit();

    pid_t pid = fork();
    if (pid != 0) release_stdio((unsigned)held);
    if (pid < 0) {
        int e = errno;
        close(pidPipe[0]); close(pidPipe[1]);
        close(errPipe[0]); close(errPipe[1]); free(argv); free(shargv);
        return io_err_code("fork", e);
    }
    if (pid == 0) { /* child */
        close(errPipe[0]);
        close(pidPipe[0]);
        if (setsid() < 0) spawn_fail(errPipe[1], "setsid", errno);
        pid_t pid2 = fork();
        if (pid2 < 0) spawn_fail(errPipe[1], "fork", errno);
        if (pid2 != 0) {
            ssize_t n;
            do { n = write(pidPipe[1], &pid2, sizeof pid2); } while (n < 0 && errno == EINTR);
            _exit(0);
        }
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
        spawn_reset(1, 1, 1, errPipe[1], limit);
        signal(SIGHUP, SIG_IGN);
        exec_search(argv, shargv, environ, path);
        spawn_fail(errPipe[1], "execve", errno);
    }
    close(errPipe[1]);
    close(pidPipe[1]);
    pid_t grandchild = 0;
    size_t got = read_full(pidPipe[0], &grandchild, sizeof grandchild);
    close(pidPipe[0]);
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
    if (got != sizeof grandchild || grandchild <= 0)
        return io_msg("spawn_detached: no pid reported");
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)grandchild));
}

/* linger_kill : UInt32 -> UInt32 -> IO Unit  (ESRCH is not an error) */
LEAN_EXPORT lean_obj_res linger_kill(uint32_t pid, uint32_t sig) {
    if (kill((pid_t)pid, (int)sig) < 0 && errno != ESRCH) return io_err("kill");
    return io_ok_unit();
}

/* linger_kill_group : UInt32 -> UInt32 -> IO Bool
 * kill(-pgid, sig): sig to every process of the process group pgid. False when the group has
 * no process left (ESRCH). A pgid of 0 or 1 never arrives (Os.Shell.signalGroup): -1 would
 * signal every process the user may signal, and 0 the caller's own group. */
LEAN_EXPORT lean_obj_res linger_kill_group(uint32_t pgid, uint32_t sig) {
    if (pgid <= 1 || pgid > 0x7FFFFFFF) return io_msg("kill_group: not a process group");
    if (kill(-(pid_t)pgid, (int)sig) == 0) return lean_io_result_mk_ok(lean_box(1));
    if (errno == ESRCH) return lean_io_result_mk_ok(lean_box(0));
    return io_err("kill(-pgid)");
}

/* linger_environ_names : IO (Array String)  the names of this process's environment */
LEAN_EXPORT lean_obj_res linger_environ_names(void) {
    extern char **environ;
    lean_object *names = lean_mk_empty_array();
    for (size_t i = 0; environ[i]; i++) {
        const char *eq = strchr(environ[i], '=');
        size_t len = eq ? (size_t)(eq - environ[i]) : strlen(environ[i]);
        names = lean_array_push(names, lean_mk_string_from_bytes(environ[i], len));
    }
    return lean_io_result_mk_ok(names);
}

/* linger_alive : UInt32 -> IO Bool  (kill(pid, 0)) */
LEAN_EXPORT lean_obj_res linger_alive(uint32_t pid) {
    int r = kill((pid_t)pid, 0);
    return lean_io_result_mk_ok(lean_box(r == 0 ? 1 : 0));
}

/* linger_waitpid_nohang : UInt32 -> Bool -> IO Int64
 * -1: the requested child is still running. -2: not our child or already
 * reaped (ECHILD -- the caller then asks linger_alive). 0..255: the exit
 * code; 256+sig: killed by signal sig. The two ranges keep an exit code
 * apart from a signal (Os.Shell.reapNohang). An ended child is
 * reaped unless keep is set; with keep it stays waitable, so its zombie
 * holds its pid (WNOWAIT).
 *
 * waitid, not waitpid, because only waitid can leave the zombie. With
 * WNOHANG and nothing to report it returns 0 and leaves si_pid as the
 * caller set it, hence the zeroed siginfo. There is no fourth outcome to
 * report: the only other errno waitid can set here is EINVAL for bad
 * options, and the options are constant. Selectors (pid 0, negative pid_t)
 * never arrive -- Os.Shell.checkPid rejects them -- so a failure
 * that is not ECHILD is answered -2 rather than "running", which degrades
 * to a liveness probe instead of waiting forever on a child that cannot
 * be reaped. */
LEAN_EXPORT lean_obj_res linger_waitpid_nohang(uint32_t pid, uint8_t keep) {
    siginfo_t info;
    memset(&info, 0, sizeof info);
    int r;
    do { r = waitid(P_PID, (id_t)pid, &info, WEXITED | WNOHANG | (keep ? WNOWAIT : 0)); }
    while (r < 0 && errno == EINTR);
    int64_t out;
    if (r < 0) {
        out = -2;
    } else if (info.si_pid == 0) {
        out = -1;
    } else if (info.si_code == CLD_EXITED) {
        out = info.si_status & 0xFF;
    } else if (info.si_code == CLD_KILLED || info.si_code == CLD_DUMPED) {
        out = 256 + info.si_status;
    } else {
        out = -1; /* WEXITED only: no other state change is reported */
    }
    return lean_io_result_mk_ok(lean_box_uint64((uint64_t)out));
}

/* The write end of the pipe linger_signal_pipe makes, for its handler: set once, before the
 * handlers are installed, and never changed after. */
static volatile sig_atomic_t signal_write = -1;

/* The signals the pipe carries: a child's end, and the four the system stops a process with at
 * logout or shutdown. */
static const int piped_signals[] = { SIGCHLD, SIGHUP, SIGINT, SIGQUIT, SIGTERM };

/* Write one byte per signal, so that a poll() waiting on the read end wakes and learns which, in
 * the order they came: 0 for SIGCHLD, a child's end, and the signal's own number otherwise. A
 * full pipe already holds an unread wake-up, and a closed read end has no reader left (the Lean
 * runtime ignores SIGPIPE, so that write fails with EPIPE), so a write that fails loses nothing
 * a reader could still act on. The handler restores errno for the code the signal interrupted. */
static void on_signal(int sig) {
    int saved = errno;
    unsigned char byte = sig == SIGCHLD ? 0 : (unsigned char)sig;
    ssize_t n = write((int)signal_write, &byte, 1);
    (void)n;
    errno = saved;
}

/* Block or unblock, in the calling thread, the signals the pipe carries. */
static void mask_piped(int how) {
    sigset_t set;
    sigemptyset(&set);
    for (size_t i = 0; i < sizeof piped_signals / sizeof piped_signals[0]; i++)
        sigaddset(&set, piped_signals[i]);
    pthread_sigmask(how, &set, NULL);
}

/* linger_signal_pipe : UInt32 -> UInt32 -> IO UInt64
 * A pipe this process's handlers for SIGCHLD and for SIGHUP, SIGINT, SIGQUIT and SIGTERM write
 * one byte to per signal: 0 when a child ends, else the signal's number. Returns write<<32 | read.
 * With `adopt_read` and `adopt_write` both 0xFFFFFFFF it makes the pipe, both ends nonblocking
 * and close on exec, so a program the daemon starts inherits neither, and a handler ends at exec;
 * otherwise it adopts the pipe whose ends those are, as an image linger_exec_image started
 * inherits it, with the bytes the previous image's handlers wrote and nobody read. poll() cannot
 * wait for a process or a signal and Lean core has no pipe, so a daemon that sleeps until
 * something happens needs this to hear its program end and the system stop it. Call it once,
 * before starting the program: it installs the process's handlers for these five signals, then
 * unblocks them in the calling thread, where linger_exec_image blocked them, so one that came
 * meanwhile is delivered now. SA_NOCLDSTOP: a stop is no end; SA_RESTART: read and write resume
 * after a signal (poll still returns EINTR, which linger_poll reports as no event, and the next
 * poll sees the byte). When a handler cannot be installed, the ones already installed are put
 * back as they were, a pipe it made is closed, and it fails. */
LEAN_EXPORT lean_obj_res linger_signal_pipe(uint32_t adopt_read, uint32_t adopt_write) {
    int fds[2];
    int made = adopt_read == 0xFFFFFFFFu && adopt_write == 0xFFFFFFFFu;
    if (made) {
        if (pipe(fds) < 0) return io_err("pipe");
        for (int i = 0; i < 2; i++) {
            if (fcntl(fds[i], F_SETFD, FD_CLOEXEC) < 0 || set_nonblock(fds[i]) < 0) {
                int e = errno;
                close(fds[0]);
                close(fds[1]);
                return io_err_code("fcntl", e);
            }
        }
    } else {
        fds[0] = (int)adopt_read;
        fds[1] = (int)adopt_write;
        if (fcntl(fds[0], F_SETFD, FD_CLOEXEC) < 0 || fcntl(fds[1], F_SETFD, FD_CLOEXEC) < 0)
            return io_err("fcntl(adopted signal pipe)");
    }
    signal_write = fds[1];
    enum { count = sizeof piped_signals / sizeof piped_signals[0] };
    struct sigaction before[count];
    struct sigaction sa;
    memset(&sa, 0, sizeof sa);
    sa.sa_handler = on_signal;
    sigemptyset(&sa.sa_mask);
    for (int i = 0; i < count; i++) {
        int sig = piped_signals[i];
        sa.sa_flags = sig == SIGCHLD ? SA_RESTART | SA_NOCLDSTOP : SA_RESTART;
        if (sigaction(sig, &sa, &before[i]) < 0) {
            int e = errno;
            /* put back what this replaced before the pipe goes, so no handler writes to a
             * descriptor number the process reuses */
            while (i-- > 0) sigaction(piped_signals[i], &before[i], NULL);
            signal_write = -1;
            if (made) {
                close(fds[0]);
                close(fds[1]);
            }
            return io_err_code("sigaction", e);
        }
    }
    mask_piped(SIG_UNBLOCK);
    return lean_io_result_mk_ok(
        lean_box_uint64(((uint64_t)(uint32_t)fds[1] << 32) | (uint64_t)(uint32_t)fds[0]));
}

/* linger_exec_image : @& String -> @& Array String -> @& Array UInt32 -> IO Unit
 * Replace this process's image with the program at `prog`, by execve, with `args` after it as
 * its words and this process's environment. execve keeps the process's id, its children and
 * every descriptor not marked close-on-exec: each of `keep` is unmarked first, so it stays open
 * at its number. The signals the signal pipe carries are blocked in the calling thread first, so
 * one that comes before the new image installs its handlers waits for them, blocked, instead of
 * taking its default action (linger_signal_pipe unblocks them). Returns only when the exec
 * fails: it then marks close-on-exec again on each of `keep` it unmarked, unblocks the signals
 * if they were not blocked before, and fails with execve's errno, so the image carries on as it
 * was. */
LEAN_EXPORT lean_obj_res linger_exec_image(b_lean_obj_arg prog, b_lean_obj_arg args,
                                         b_lean_obj_arg keep) {
    char **argv = exec_argv(prog, args);
    if (!argv) return io_msg("exec: out of memory");
    size_t n = lean_array_size(keep);
    int *cleared = calloc(n + 1, sizeof(int));
    if (!cleared) {
        free(argv);
        return io_msg("exec: out of memory");
    }
    sigset_t before;
    pthread_sigmask(SIG_SETMASK, NULL, &before);
    mask_piped(SIG_BLOCK);
    int e = 0;
    size_t done = 0;
    for (; done < n; done++) {
        int fd = (int)lean_unbox_uint32(lean_array_get_core(keep, done));
        int flags = fcntl(fd, F_GETFD);
        if (flags < 0 || fcntl(fd, F_SETFD, flags & ~FD_CLOEXEC) < 0) {
            e = errno;
            break;
        }
        cleared[done] = flags & FD_CLOEXEC;
    }
    extern char **environ;
    if (!e) {
        execve(lean_string_cstr(prog), argv, environ);
        e = errno;
    }
    for (size_t i = 0; i < done; i++) {
        int fd = (int)lean_unbox_uint32(lean_array_get_core(keep, i));
        if (cleared[i]) fcntl(fd, F_SETFD, FD_CLOEXEC);
    }
    pthread_sigmask(SIG_SETMASK, &before, NULL);
    free(cleared);
    free(argv);
    return io_err_code("execve", e);
}

/* linger_signal_session : UInt32 -> UInt32 -> IO UInt32
 * Send sig (0 only tests) to every process whose session id is sid, other
 * than sid itself, and return how many it reached. Processes of another
 * user are not reached, and a failed listing throws.
 *
 * The caller keeps the session's leader, its child, unreaped meanwhile:
 * the zombie holds the pid that is the session's id, so no other session
 * can take that id. On Linux each process is pinned with a pidfd before
 * its session is read, so a pid that its process gave up and another took
 * between the read and the signal is never signalled; a kernel without
 * pidfds (before 5.3) falls back to getsid then kill, like macOS, where
 * that window remains. */
LEAN_EXPORT lean_obj_res linger_signal_session(uint32_t sid, uint32_t sig) {
    uint32_t reached = 0;
#ifdef __APPLE__
    int cap = proc_listallpids(NULL, 0);
    if (cap < 0) return io_err("proc_listallpids");
    cap += 64; /* room for processes started since the count */
    pid_t *pids = malloc((size_t)cap * sizeof *pids);
    if (pids == NULL) return io_err("malloc");
    int n = proc_listallpids(pids, cap * (int)sizeof *pids);
    if (n < 0) {
        free(pids);
        return io_err("proc_listallpids");
    }
    for (int i = 0; i < n; i++) {
        if (pids[i] <= 0 || pids[i] == (pid_t)sid || getsid(pids[i]) != (pid_t)sid) continue;
        if (kill(pids[i], (int)sig) == 0) reached++;
    }
    free(pids);
#else
    DIR *dir = opendir("/proc");
    if (dir == NULL) return io_err("opendir(/proc)");
    struct dirent *entry;
    while ((entry = readdir(dir)) != NULL) {
        char *end;
        long pid = strtol(entry->d_name, &end, 10);
        if (end == entry->d_name || *end != '\0' || pid <= 0 || pid == (long)sid) continue;
        /* getsid alone first: it is one cheap syscall per process on the host */
        if (getsid((pid_t)pid) != (pid_t)sid) continue;
        int fd = (int)syscall(SYS_pidfd_open, (pid_t)pid, 0);
        if (fd < 0 && errno == ESRCH) continue;
        /* read again once pinned: the pid may have changed hands since */
        if (fd >= 0 && getsid((pid_t)pid) != (pid_t)sid) {
            close(fd);
            continue;
        }
        long r = fd >= 0 ? syscall(SYS_pidfd_send_signal, fd, (int)sig, NULL, 0)
                         : (long)kill((pid_t)pid, (int)sig);
        if (r == 0) reached++;
        if (fd >= 0) close(fd);
    }
    closedir(dir);
#endif
    return lean_io_result_mk_ok(lean_box_uint32(reached));
}

/* -------------------------------------------------------------------- */
/* misc                                                                  */

/* getpid, chmod, both clocks, hostname, stdin tty detection, and the
 * full-write loop are Lean/core; see packages/os/Os/WorldCode.lean. */

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
 * the caller stores whatever string chdir will accept. A cwd longer than
 * MAXPATHLEN comes back cut short instead of failing, so the path is kept
 * only when it stats to the cwd vnode libproc reported beside it. */
LEAN_EXPORT lean_obj_res linger_getcwd_of(uint32_t pid) {
#ifdef __APPLE__
    struct proc_vnodepathinfo vpi;
    struct stat st;
    int n = proc_pidinfo((int)pid, PROC_PIDVNODEPATHINFO, 0, &vpi, sizeof vpi);
    if (n < (int)sizeof vpi) return lean_io_result_mk_ok(lean_mk_string(""));
    vpi.pvi_cdir.vip_path[sizeof vpi.pvi_cdir.vip_path - 1] = '\0';
    if (stat(vpi.pvi_cdir.vip_path, &st) != 0
        || (uint32_t)st.st_dev != vpi.pvi_cdir.vip_vi.vi_stat.vst_dev
        || (uint64_t)st.st_ino != vpi.pvi_cdir.vip_vi.vi_stat.vst_ino)
        return lean_io_result_mk_ok(lean_mk_string(""));
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

/* linger_tcgetpgrp : UInt32 -> IO Int64
 * The foreground process group of the terminal open on fd, the session's pty
 * master: tcgetpgrp(3), which reports the group of the terminal's foreground
 * job as the line discipline holds it, or -errno. */
LEAN_EXPORT lean_obj_res linger_tcgetpgrp(uint32_t fd) {
    pid_t g = tcgetpgrp((int)fd);
    int64_t r = g < 0 ? -(int64_t)errno : (int64_t)g;
    return lean_io_result_mk_ok(lean_box_uint64((uint64_t)r));
}

/* linger_cmdline_of : UInt32 -> IO ByteArray
 * The words pid runs with, each ended by NUL, as the process holds them,
 * at most CMDLINE_MAX bytes; empty when unreadable, as for a process that
 * has ended. /proc/<pid>/cmdline on Linux. macOS has no /proc: there it is
 * sysctl's KERN_PROCARGS2, argc then the executable's path, NUL padding and
 * the words, read for a process of our own uid. That path is untested here:
 * no macOS host runs the suites. */
#define CMDLINE_MAX 4096
LEAN_EXPORT lean_obj_res linger_cmdline_of(uint32_t pid) {
    char buf[CMDLINE_MAX];
    size_t n = 0;
#ifdef __APPLE__
    int mib[3] = { CTL_KERN, KERN_PROCARGS2, (int)pid };
    size_t size = 0;
    if (sysctl(mib, 3, NULL, &size, NULL, 0) == 0 && size > sizeof(int)) {
        char *all = malloc(size);
        if (all && sysctl(mib, 3, all, &size, NULL, 0) == 0 && size > sizeof(int)) {
            int argc;
            memcpy(&argc, all, sizeof argc);
            size_t i = sizeof argc;
            while (i < size && all[i] != '\0') i++;   /* the executable's path */
            while (i < size && all[i] == '\0') i++;   /* its padding */
            size_t start = i;
            for (int w = 0; w < argc && i < size; w++) {
                while (i < size && all[i] != '\0') i++;
                if (i < size) i++;
            }
            n = i - start;
            if (n > sizeof buf) n = sizeof buf;
            memcpy(buf, all + start, n);
        }
        free(all);
    }
#else
    char path[64];
    snprintf(path, sizeof path, "/proc/%u/cmdline", pid);
    int fd = open(path, O_RDONLY | O_CLOEXEC);
    if (fd >= 0) {
        while (n < sizeof buf) {
            ssize_t r = read(fd, buf + n, sizeof buf - n);
            if (r < 0 && errno == EINTR) continue;
            if (r <= 0) break;
            n += (size_t)r;
        }
        close(fd);
    }
#endif
    lean_object *arr = lean_alloc_sarray(1, n, n);
    memcpy(lean_sarray_cptr(arr), buf, n);
    return lean_io_result_mk_ok(arr);
}
