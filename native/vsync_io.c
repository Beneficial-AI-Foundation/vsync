/* Atomic, durable file replacement for vsync (unverified trusted shell; keep tiny).
 *
 * vsync_write_atomic(dst, mode_from, data):
 *   1. mkstemp "<dir of dst>/.vsync-XXXXXX"  (O_EXCL, mode 0600, random name: no symlink/race)
 *   2. write all bytes, fchmod to mode of `mode_from` (if it exists), fsync, close
 *   3. rename over dst (atomic), fsync the directory
 *   On any failure the temp file is unlinked and an IO error is returned.
 */
#include <lean/lean.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

static lean_obj_res fail(const char *what, const char *path) {
  char buf[PATH_MAX + 128];
  snprintf(buf, sizeof buf, "%s %s: %s", what, path, strerror(errno));
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(buf)));
}

LEAN_EXPORT lean_obj_res vsync_write_atomic(b_lean_obj_arg dst_o, b_lean_obj_arg from_o,
                                            b_lean_obj_arg data, lean_obj_arg w) {
  (void)w;
  const char *dst = lean_string_cstr(dst_o);
  const char *from = lean_string_cstr(from_o);
  char dir[PATH_MAX], tmpl[PATH_MAX];

  const char *slash = strrchr(dst, '/');
  if (slash == NULL) strcpy(dir, ".");
  else if (slash == dst) strcpy(dir, "/");
  else {
    size_t n = (size_t)(slash - dst);
    if (n >= sizeof dir) { errno = ENAMETOOLONG; return fail("path", dst); }
    memcpy(dir, dst, n); dir[n] = 0;
  }
  if (snprintf(tmpl, sizeof tmpl, "%s/.vsync-XXXXXX", dir) >= (int)sizeof tmpl) {
    errno = ENAMETOOLONG; return fail("path", dst);
  }

  int fd = mkstemp(tmpl);
  if (fd < 0) return fail("mkstemp in", dir);

  const uint8_t *p = lean_sarray_cptr(data);
  size_t left = lean_sarray_size(data);
  while (left > 0) {
    ssize_t k = write(fd, p, left);
    if (k < 0) { if (errno == EINTR) continue; goto err; }
    p += k; left -= (size_t)k;
  }
  struct stat st;
  if (from[0] != 0 && stat(from, &st) == 0 && fchmod(fd, st.st_mode & 07777) != 0) goto err;
  if (fsync(fd) != 0) goto err;
  if (close(fd) != 0) { fd = -1; goto err; }
  fd = -1;
  if (rename(tmpl, dst) != 0) goto err;

  int dfd = open(dir, O_RDONLY | O_CLOEXEC);
  if (dfd >= 0) { fsync(dfd); close(dfd); }
  return lean_io_result_mk_ok(lean_box(0));

err: {
    int e = errno;
    if (fd >= 0) close(fd);
    unlink(tmpl);
    errno = e;
    return fail("write", dst);
  }
}

/* ===================================================================================
 * Confined file access for `vsync serve` (and lstat for the sender).
 *
 * Every path below is relative to a root directory. The Lean side has already checked it
 * with `safeRel` (no "..", ".", empty components, NUL). On top of that, each directory
 * component is opened with openat(..., O_NOFOLLOW | O_DIRECTORY), so a symlink anywhere in
 * the path is refused by the kernel and the walk cannot leave the root.
 * Integers cross the FFI as uint64; multi-value results as big-endian u64 byte arrays.
 * =================================================================================== */
#include <sys/time.h>

static lean_obj_res fail_msg(const char *what) {
  char buf[256];
  snprintf(buf, sizeof buf, "%s: %s", what, strerror(errno));
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(buf)));
}

static lean_obj_res mk_u64s(const uint64_t *v, size_t n) {
  lean_object *a = lean_alloc_sarray(1, n * 8, n * 8);
  uint8_t *p = lean_sarray_cptr(a);
  for (size_t k = 0; k < n; k++)
    for (int b = 0; b < 8; b++) p[k * 8 + b] = (uint8_t)(v[k] >> (56 - 8 * b));
  return lean_io_result_mk_ok(a);
}

/* modification time in nanoseconds since the epoch */
static uint64_t mtime_of(const struct stat *st) {
#ifdef __APPLE__
  return (uint64_t)st->st_mtimespec.tv_sec * 1000000000ull + (uint64_t)st->st_mtimespec.tv_nsec;
#else
  return (uint64_t)st->st_mtim.tv_sec * 1000000000ull + (uint64_t)st->st_mtim.tv_nsec;
#endif
}

static void ts_of(uint64_t ns, struct timespec ts[2]) {
  ts[0].tv_sec = (time_t)(ns / 1000000000ull); ts[0].tv_nsec = (long)(ns % 1000000000ull); ts[1] = ts[0];
}

/* wall-clock time in nanoseconds */
LEAN_EXPORT lean_obj_res vsync_now_ns(lean_obj_arg w) {
  (void)w;
  struct timespec t;
  clock_gettime(CLOCK_REALTIME, &t);
  return lean_io_result_mk_ok(lean_box_uint64((uint64_t)t.tv_sec * 1000000000ull + (uint64_t)t.tv_nsec));
}

/* lstat(path) -> [type, size, mode, mtime]; type 0 missing, 1 file, 2 dir, 3 symlink, 4 other */
LEAN_EXPORT lean_obj_res vsync_lstat(b_lean_obj_arg path, lean_obj_arg w) {
  (void)w;
  struct stat st;
  uint64_t v[4] = {0, 0, 0, 0};
  if (lstat(lean_string_cstr(path), &st) != 0) {
    if (errno == ENOENT || errno == ENOTDIR) return mk_u64s(v, 4);
    return fail_msg("lstat");
  }
  v[0] = S_ISREG(st.st_mode) ? 1 : S_ISDIR(st.st_mode) ? 2 : S_ISLNK(st.st_mode) ? 3 : 4;
  v[1] = (uint64_t)st.st_size; v[2] = (uint64_t)(st.st_mode & 07777); v[3] = mtime_of(&st);
  return mk_u64s(v, 4);
}

/* Open the parent directory of root/rel without following symlinks.
 * On success returns a dirfd and points *name at the last component (inside buf). */
static int open_parent(const char *root, b_lean_obj_arg rel, char *buf, size_t bufsz, char **name) {
  size_t n = lean_sarray_size(rel);
  if (n == 0 || n >= bufsz) { errno = EINVAL; return -1; }
  memcpy(buf, lean_sarray_cptr(rel), n); buf[n] = 0;
  if (memchr(buf, 0, n) != NULL) { errno = EINVAL; return -1; }
  int dfd = open(root, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
  if (dfd < 0) return -1;
  char *comp = buf;
  for (;;) {
    char *slash = strchr(comp, '/');
    if (slash == NULL) { *name = comp; return dfd; }
    *slash = 0;
    int next = openat(dfd, comp, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
    int e = errno;
    close(dfd);
    if (next < 0) { errno = e; return -1; }
    dfd = next;
    comp = slash + 1;
  }
}

/* Open an existing regular file root/rel for reading. Returns fd+1, or 0 if it does not exist
 * or is not a regular file. Symlinks (anywhere) are not followed. */
LEAN_EXPORT lean_obj_res vsync_rd_open(b_lean_obj_arg root, b_lean_obj_arg rel, lean_obj_arg w) {
  (void)w;
  char buf[PATH_MAX], *name;
  int dfd = open_parent(lean_string_cstr(root), rel, buf, sizeof buf, &name);
  if (dfd < 0) {
    if (errno == ENOENT) return lean_io_result_mk_ok(lean_box_uint64(0));
    return fail_msg("open parent");
  }
  int fd = openat(dfd, name, O_RDONLY | O_NOFOLLOW | O_CLOEXEC);
  int e = errno;
  close(dfd);
  if (fd < 0) {
    if (e == ENOENT || e == ELOOP || e == EISDIR) return lean_io_result_mk_ok(lean_box_uint64(0));
    errno = e; return fail_msg("open");
  }
  struct stat st;
  if (fstat(fd, &st) != 0 || !S_ISREG(st.st_mode)) { close(fd); return lean_io_result_mk_ok(lean_box_uint64(0)); }
  return lean_io_result_mk_ok(lean_box_uint64((uint64_t)fd + 1));
}

/* fstat(fd) -> [size, mode, mtime] */
LEAN_EXPORT lean_obj_res vsync_fstat(uint64_t h, lean_obj_arg w) {
  (void)w;
  struct stat st;
  if (fstat((int)(h - 1), &st) != 0) return fail_msg("fstat");
  uint64_t v[3] = {(uint64_t)st.st_size, (uint64_t)(st.st_mode & 07777), mtime_of(&st)};
  return mk_u64s(v, 3);
}

/* Read up to len bytes at offset off (short only at end of file). */
LEAN_EXPORT lean_obj_res vsync_pread(uint64_t h, uint64_t off, uint64_t len, lean_obj_arg w) {
  (void)w;
  if (len > (1u << 30)) { errno = EINVAL; return fail_msg("pread"); }
  lean_object *a = lean_alloc_sarray(1, 0, len);
  uint8_t *p = lean_sarray_cptr(a);
  size_t got = 0;
  while (got < len) {
    ssize_t k = pread((int)(h - 1), p + got, len - got, (off_t)(off + got));
    if (k < 0) { if (errno == EINTR) continue; lean_dec(a); return fail_msg("pread"); }
    if (k == 0) break;
    got += (size_t)k;
  }
  lean_to_sarray(a)->m_size = got;
  return lean_io_result_mk_ok(a);
}

LEAN_EXPORT lean_obj_res vsync_close(uint64_t h, lean_obj_arg w) {
  (void)w;
  if (h > 0) close((int)(h - 1));
  return lean_io_result_mk_ok(lean_box(0));
}

/* ---- streaming writer: begin / write / commit | abort ---- */
#define MAXSLOTS 16
static struct { int used, dfd, fd; char tmp[64]; char name[PATH_MAX]; } slots[MAXSLOTS];

static void rand_name(char *out, size_t n) {
  unsigned char r[8] = {0};
  int u = open("/dev/urandom", O_RDONLY | O_CLOEXEC);
  if (u >= 0) { ssize_t k = read(u, r, sizeof r); (void)k; close(u); }
  snprintf(out, n, ".vsync-%02x%02x%02x%02x%02x%02x%02x%02x.tmp",
           r[0], r[1], r[2], r[3], r[4], r[5], r[6], r[7]);
}

LEAN_EXPORT lean_obj_res vsync_wr_begin(b_lean_obj_arg root, b_lean_obj_arg rel, lean_obj_arg w) {
  (void)w;
  int s = 0;
  while (s < MAXSLOTS && slots[s].used) s++;
  if (s == MAXSLOTS) { errno = EMFILE; return fail_msg("writer slots"); }
  char buf[PATH_MAX], *name;
  int dfd = open_parent(lean_string_cstr(root), rel, buf, sizeof buf, &name);
  if (dfd < 0) return fail_msg("open parent");
  int fd = -1;
  for (int tries = 0; tries < 16 && fd < 0; tries++) {
    rand_name(slots[s].tmp, sizeof slots[s].tmp);
    fd = openat(dfd, slots[s].tmp, O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_CLOEXEC, 0600);
    if (fd < 0 && errno != EEXIST) break;
  }
  if (fd < 0) { int e = errno; close(dfd); errno = e; return fail_msg("create temp"); }
  slots[s].used = 1; slots[s].dfd = dfd; slots[s].fd = fd;
  snprintf(slots[s].name, sizeof slots[s].name, "%s", name);
  return lean_io_result_mk_ok(lean_box_uint64((uint64_t)s));
}

LEAN_EXPORT lean_obj_res vsync_wr_write(uint64_t s, b_lean_obj_arg data, lean_obj_arg w) {
  (void)w;
  if (s >= MAXSLOTS || !slots[s].used) { errno = EBADF; return fail_msg("write"); }
  const uint8_t *p = lean_sarray_cptr(data);
  size_t left = lean_sarray_size(data);
  while (left > 0) {
    ssize_t k = write(slots[s].fd, p, left);
    if (k < 0) { if (errno == EINTR) continue; return fail_msg("write"); }
    p += k; left -= (size_t)k;
  }
  return lean_io_result_mk_ok(lean_box(0));
}

static void slot_free(int s, int unlink_tmp) {
  if (slots[s].fd >= 0) close(slots[s].fd);
  if (unlink_tmp) unlinkat(slots[s].dfd, slots[s].tmp, 0);
  close(slots[s].dfd);
  slots[s].used = 0;
}

LEAN_EXPORT lean_obj_res vsync_wr_commit(uint64_t s, uint64_t mode, uint64_t mtime, lean_obj_arg w) {
  (void)w;
  if (s >= MAXSLOTS || !slots[s].used) { errno = EBADF; return fail_msg("commit"); }
  int fd = slots[s].fd;
  struct timespec ts[2];
  ts_of(mtime, ts);
  if (fchmod(fd, (mode_t)(mode & 07777)) != 0 || fsync(fd) != 0 || futimens(fd, ts) != 0) {
    int e = errno; slot_free((int)s, 1); errno = e; return fail_msg("finish temp");
  }
  close(fd); slots[s].fd = -1;
  if (renameat(slots[s].dfd, slots[s].tmp, slots[s].dfd, slots[s].name) != 0) {
    int e = errno; slot_free((int)s, 1); errno = e; return fail_msg("rename");
  }
  fsync(slots[s].dfd);
  slot_free((int)s, 0);
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res vsync_wr_abort(uint64_t s, lean_obj_arg w) {
  (void)w;
  if (s < MAXSLOTS && slots[s].used) slot_free((int)s, 1);
  return lean_io_result_mk_ok(lean_box(0));
}

/* mkdir root/rel (parents must exist). An existing directory is fine; anything else is an error. */
LEAN_EXPORT lean_obj_res vsync_mkdir(b_lean_obj_arg root, b_lean_obj_arg rel, uint64_t mode, lean_obj_arg w) {
  (void)w;
  char buf[PATH_MAX], *name;
  int dfd = open_parent(lean_string_cstr(root), rel, buf, sizeof buf, &name);
  if (dfd < 0) return fail_msg("open parent");
  if (mkdirat(dfd, name, (mode_t)((mode & 07777) | 0700)) != 0) {
    struct stat st;
    if (errno != EEXIST || fstatat(dfd, name, &st, AT_SYMLINK_NOFOLLOW) != 0 || !S_ISDIR(st.st_mode)) {
      int e = (errno == EEXIST) ? ENOTDIR : errno; close(dfd); errno = e; return fail_msg("mkdir");
    }
  }
  close(dfd);
  return lean_io_result_mk_ok(lean_box(0));
}

/* Set permission bits and mtime on root/rel (file or directory; symlinks refused). */
LEAN_EXPORT lean_obj_res vsync_setmeta(b_lean_obj_arg root, b_lean_obj_arg rel, uint64_t mode,
                                       uint64_t mtime, lean_obj_arg w) {
  (void)w;
  char buf[PATH_MAX], *name;
  int dfd = open_parent(lean_string_cstr(root), rel, buf, sizeof buf, &name);
  if (dfd < 0) return fail_msg("open parent");
  int fd = openat(dfd, name, O_RDONLY | O_NOFOLLOW | O_CLOEXEC);
  int e = errno;
  close(dfd);
  if (fd < 0) { errno = e; return fail_msg("open for metadata"); }
  struct timespec ts[2];
  ts_of(mtime, ts);
  if (fchmod(fd, (mode_t)(mode & 07777)) != 0 || futimens(fd, ts) != 0) {
    e = errno; close(fd); errno = e; return fail_msg("set metadata");
  }
  close(fd);
  return lean_io_result_mk_ok(lean_box(0));
}
