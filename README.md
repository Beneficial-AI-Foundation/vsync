# vsync

A formally verified implementation of the rsync delta algorithm, written in Lean 4 and compiled to C.

## Guarantees (all in [`VSync/Spec.lean`](VSync/Spec.lean), checked by `lake build`)

| Spec | Guarantee |
|---|---|
| `sync_local_exact` | Local sync reproduces the source **exactly, with no assumptions** (matches are confirmed byte-for-byte) |
| `sync_remote_roundtrip` | Signature-only (remote) mode is exact unless SHA-256 collides on a window of the new file |
| `copies_in_range` | Every copy instruction references a real block of the old file |
| `sync_self` | Unchanged files reuse every full block |
| `sync_empty_src`, `no_copies_without_blocks` | Edge cases: empty source, missing/tiny destination |
| `rolling_checksum`, `weak_fast_correct` | O(1) rolling update and O(n) checksum both equal the specification |
| `sha256_*` | SHA-256 matches the NIST test vectors (checked by the Lean kernel) |
| `cli_*` | Argument parsing: block size is always positive, defaults are bounded |

An axiom audit at the bottom of `Spec.lean` fails the build if any spec uses `sorry` or a
non-standard axiom.

## Compared with rsync

- **Memory safety**: Lean is bounds-checked; no hand-written parsing in C.
- **Strong hash**: SHA-256 (rsync historically used MD4/MD5).
- **Correctness proof**: the round trip is a theorem, not a test.
- **Safe writes** (`native/vsync_io.c`, ~80 lines, the only unverified C): random temp file
  created exclusively (`mkstemp`), permissions preserved, `fsync`, atomic `rename`, directory
  `fsync`, temp removed on failure. Unchanged files are not rewritten.
- **No quadratic blow-up** on duplicate blocks: candidates are indexed by (weak checksum, SHA-256).
- **Defense in depth**: output is compared with the source before writing, guarding the unverified
  toolchain (Lean compiler, C compiler, runtime).

Not yet: network protocol (remote mode is implemented and proven, but there is no transport),
directories/metadata beyond permissions, streaming for files larger than RAM.

## Build

```sh
lake build                                   # check every proof and build the binary
.lake/build/bin/vsync sync <src> <dst> [block-size]
```

Requires Lean 4.36.0 (via [elan](https://github.com/leanprover/elan)) and a C compiler.

Split workflow (proofs + C generation on a remote box, native compile locally):
`./vd.sh all` then `./build-local.sh`.
