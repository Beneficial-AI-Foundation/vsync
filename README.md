# vsync

A file-sync tool in the spirit of rsync, written in Lean 4 with its core **formally verified**,
compiled to C. It syncs single files or whole directory trees, locally or over `ssh`, streaming
large files instead of loading them into memory.

## Install

You need [elan](https://github.com/leanprover/elan) (the Lean toolchain manager) and a C compiler
(`cc`, `gcc` or `clang`).

```sh
# 1. Lean toolchain (skip if you already have elan)
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh

# 2. Build: checks every proof, then compiles the binary
git clone https://github.com/Beneficial-AI-Foundation/vsync.git
cd vsync
lake build

# 3. Put it on your PATH
install -m 755 .lake/build/bin/vsync ~/.local/bin/vsync     # or /usr/local/bin
vsync                                                       # prints usage
```

To sync **to another machine**, install `vsync` there the same way. `push` starts it over `ssh`
(`vsync serve`), just as rsync starts a remote rsync. If it is not on the remote `PATH`, pass
`--remote-vsync /path/to/vsync`.

## Usage

```sh
# Copy a directory tree into an existing directory (contents of src/ go into dest/)
vsync push src/ backup/

# The same, to another machine over ssh
vsync push src/ user@host:/srv/backup

# Custom ssh command / remote binary location
vsync push src/ host:/srv/backup --rsh "ssh -p 2222 -i ~/.ssh/key" --remote-vsync ~/bin/vsync

# Always compare contents instead of trusting size + mtime
vsync push src/ host:/srv/backup --checksum

# Push a single file into a directory
vsync push big.iso host:/srv/isos

# Update one local file in place (in memory; proven exact with no assumptions)
vsync sync new.bin old.bin [block-size]
```

Output is one summary line, e.g.
`files=1 unchanged=4 dirs=2 bytes=300000000 literal_bytes=17600 reused=299982400 symlinks_skipped=0 errors=0`.
The exit status is 0 only if there were no errors.

### What `push` does

- **Directories**: copied recursively. Destination directories are created as needed.
- **Unchanged files** are skipped when size, permissions and mtime (nanoseconds) all match.
  Files modified in the last 2 seconds are always checked, and `--checksum` disables skipping.
- **Changed files**: the receiver sends block checksums of its old copy, the sender sends only
  the differences, and the receiver rebuilds the file into a temporary file, then renames it
  into place atomically. An interrupted transfer never leaves a half-written file.
- **Metadata**: permission bits and modification time of files and directories.
- **Streaming**: the sender holds one segment (8 MiB) at a time and the receiver reads old blocks
  on demand, so memory use stays around 50–70 MB however large the files are.
- **Not copied**: symbolic links (skipped and counted), devices and sockets, ownership, ACLs and
  extended attributes. Files that exist only in the destination are **not deleted**.

## What is proven

Every guarantee is a theorem in [`VSync/Spec.lean`](VSync/Spec.lean), checked by `lake build`.
An axiom audit at the bottom fails the build if any of them uses `sorry` or a non-standard axiom.

| Spec | Guarantee |
|---|---|
| `sync_local_exact` | Local sync reproduces the source exactly, with no assumptions |
| `sync_remote_roundtrip` | Remote sync is exact unless SHA-256 collides on a block of the new file |
| `sync_segments`, `receiver_streaming` | Streaming (segments, on-demand reads) gives the same result |
| `receiver_checks_segment` | The receiver never writes a segment whose SHA-256 differs from the sender's |
| `wire_roundtrip`, `wire_signature` | Every protocol message decodes back to itself |
| `path_safe`, `path_rejects_*` | Paths from the peer can't contain `..`, `.`, empty components, `/` or NUL |
| `copies_in_range` | Every copy instruction refers to a real block of the old file |
| `skip_only_if_same`, `no_skip_when_racy` | A file is skipped only if size, mode and mtime match and it isn't freshly modified |
| `sync_self`, `sync_empty_src`, `no_copies_without_blocks` | Edge cases |
| `rolling_checksum`, `weak_fast_correct` | The O(1) rolling update and O(n) checksum equal the specification |
| `sha256_*` | SHA-256 matches NIST test vectors (checked by the Lean kernel) |
| `cli_*` | Argument parsing |

## Security model

- **Parsing is verified.** Every message goes through codecs with a proven round trip. Decoders
  are total, every read is bounds-checked, and lengths and counts from the peer are checked
  against the bytes actually received. Frames are capped at 64 MiB on the receiver.
- **The receiver is confined to its directory.** Paths are validated by `safeRel` (proven), and
  every directory component is opened with `openat(..., O_NOFOLLOW)`, so a symlink in the
  destination tree cannot redirect a write outside it.
- **Writes are atomic.** Files are written to a randomly named temp file created with `O_EXCL`,
  flushed with `fsync`, given their permissions and mtime, then `rename`d into place.
- **Transport** is `ssh` (or any command given with `--rsh`); vsync does no authentication or
  encryption of its own.
- **Trusted, unverified code**: `native/vsync_io.c` (~310 lines of file-system calls), the
  process plumbing in `Main.lean`, the Lean compiler, the C compiler and the runtime.

## Project layout

| Path | What |
|---|---|
| `VSync/Checksum.lean` | Rolling weak checksum and its proofs |
| `VSync/Sha256.lean` | SHA-256 |
| `VSync/Delta.lean` | Signature, delta, patch |
| `VSync/Wire.lean` | Verified codecs (varint, bytes, pairs, lists) |
| `VSync/Proto.lean` | Protocol messages, path safety, streaming model, quick check |
| `VSync/Proofs.lean` | Supporting lemmas |
| `VSync/Spec.lean` | **The test suite**: every guarantee, plus the axiom audit |
| `Main.lean` | Command line, `push` / `serve` / `sync` |
| `native/vsync_io.c` | Atomic writes, confined `openat` walks, `pread`, `lstat` |
| `pages/vsync.md` | The VeriLib page for this project |

Development workflow (proofs and C generation on a remote box, native build locally):
`./vd.sh all` then `./build-local.sh`. See `CLAUDE.md`.
