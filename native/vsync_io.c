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
