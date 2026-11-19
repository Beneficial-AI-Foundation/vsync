# vsync: rsync, formally verified

**What it is.** A file-sync tool in the spirit of rsync, written in Lean 4 with its core proved correct and compiled to C. It syncs single files or directory trees, locally or over `ssh`, and streams large files instead of loading them into memory.

**The question behind it.** In January 2025, rsync 3.4.0 fixed six vulnerabilities, one rated CVSS 9.8. Which of those classes of bug does a verified rewrite actually remove, and what does it cost?

```stats
{
  "items": [
    { "value": "31", "label": "Specs", "hint": "theorems in VSync/Spec.lean, checked on every build" },
    { "value": "0", "label": "sorry", "hint": "an axiom audit fails the build if any spec gains one" },
    { "value": "3 of 6", "label": "rsync 2025 CVEs ruled out", "hint": "by proof or by the language; the other 3 by design or mitigation" },
    { "value": "54 MB", "label": "Memory for a 300 MB file", "hint": "streaming; the in-memory path needed 1.4 GB" }
  ]
}
```

```cards
{
  "repos": ["OWNER/vsync"],
  "variant": "green"
}
```

## The main theorem

```latex
\forall\, old\ new\ B,\quad \mathrm{patch}\big(old,\ B,\ \mathrm{delta}(\mathrm{sig}(old, B),\ \mathrm{confirm}_{\mathrm{local}},\ new)\big) = new
```

A local sync reproduces the source exactly, for every pair of files and every block size, with no assumption about hash collisions (`sync_local_exact`). Over the network the sender has only the receiver's checksums, so the remote version (`sync_remote_roundtrip`) states its one assumption: no SHA-256 collision on a block of the new file. The receiver also checks every segment's SHA-256 before writing it.

## rsync's 2025 CVEs, one by one

| CVE | What went wrong in rsync | vsync |
|---|---|---|
| **CVE-2024-12084** (CVSS 9.8) | Heap buffer overflow while parsing checksums from the peer | **Ruled out by proof.** Every message goes through codecs with a proven round trip (`wire_roundtrip`); decoders are total, every read is bounds-checked, and lengths from the peer are checked against the bytes received. |
| **CVE-2024-12085** | Uninitialized stack memory leaked through checksum comparison | **Ruled out by the language.** Lean has no uninitialized memory. |
| **CVE-2024-12087** | Path traversal via `--inc-recursive` | **Ruled out on the receiver.** Paths are validated by `safeRel` (`path_safe`: no `..`, `.`, empty components, `/` or NUL), and every directory is opened with `O_NOFOLLOW`, so a symlink can't redirect a write either. |
| **CVE-2024-12086** | A malicious server can read arbitrary client files | **Ruled out by design, not proven.** No message lets the receiver ask the sender for a path; the sender only reads the tree it was told to send. |
| **CVE-2024-12088** | `--safe-links` didn't check symlinks inside symlink targets | **Not applicable.** vsync never creates or follows symlinks; they are skipped and counted. |
| **CVE-2024-12747** | Symlink race while writing files | **Mitigated, not proven.** Temp files are created with `O_EXCL` and a random name inside a directory opened without following symlinks, then `renameat`'d into place. This is in the ~310 lines of unverified C. |

## Hostile client, tested

A small script spoke the wire format directly to `vsync serve` and tried to escape or corrupt the destination. Everything was refused and nothing outside the root changed.

| Attack | Result |
|---|---|
| `../escape`, `/tmp/abs`, `a/../../x` | Rejected by `safeRel` |
| Write through a symlinked directory in the destination | Refused by the kernel (`O_NOFOLLOW`) |
| Copy of block 999999 | Rejected, file left untouched |
| Segment with a wrong SHA-256 | Rejected, file left untouched |
| 4 GB frame header, garbage body, list count of 10¹² | Rejected before allocating |

## Design-level differences from rsync

| rsync | vsync |
|---|---|
| Strong block checksum went MD4, then MD5, and since 3.2 defaults to **xxHash (xxh128)**, which is not cryptographic. | **SHA-256**, checked against NIST vectors by the Lean kernel. Local syncs also compare bytes, so a collision can't corrupt a file. |
| Correctness rests on a whole-file checksum and a retry. | Correctness is a **theorem**, plus a per-segment SHA-256 check on the receiver. |
| Protocol parsing in C. | Protocol parsing in Lean, with proofs; the only C is file-system calls. |
| Behaviour checked by tests. | **31 specs** checked on every build. |

## How a sync works

1. **Signature.** The receiver reads its old copy block by block and sends a weak rolling checksum and a SHA-256 for each block.
2. **Scan.** The sender slides a window over its file, 8 MiB segment at a time. Updating the weak checksum by one byte costs O(1) (`rolling_checksum`).
3. **Match.** A weak hit is confirmed with SHA-256 (and, locally, byte for byte).
4. **Delta.** The sender emits `copy i` for matched blocks and literal runs for new data.
5. **Patch.** The receiver rebuilds each segment, reading old blocks with `pread` (`receiver_streaming`), checks its SHA-256, and appends it to a temp file.
6. **Commit.** Permissions and mtime are set, the file is flushed with `fsync` and renamed into place atomically.

Unchanged files are skipped when size, permissions and nanosecond mtime match. Testing found a bug here: two versions written in the same second looked identical. vsync now never skips a file modified in the last two seconds (`no_skip_when_racy`), the same fix git uses, and `--checksum` disables skipping.

## Speed and memory

```chart
{
  "id": "vsync-stream-mem",
  "type": "stacked-bar",
  "title": "Peak memory (MB), 300 MB file",
  "row": "perf",
  "width": "1/2",
  "height": 240,
  "x": { "type": "category", "field": "mode" },
  "legend": { "show": false },
  "series": [ { "key": "mb", "label": "MB", "color": "#01BB00" } ],
  "source": { "kind": "inline" },
  "data": [ { "mode": "in memory (sync)", "mb": 1475 }, { "mode": "streaming (push)", "mb": 54 } ]
}
```

```chart
{
  "id": "vsync-v1-v2",
  "type": "stacked-bar",
  "title": "Seconds to sync 20 MB, v1 vs v2",
  "row": "perf",
  "width": "1/2",
  "height": 240,
  "x": { "type": "category", "field": "version" },
  "legend": { "show": false },
  "series": [ { "key": "seconds", "label": "Seconds", "color": "#217ef0" } ],
  "source": { "kind": "inline" },
  "data": [ { "version": "v1", "seconds": 97 }, { "version": "v2", "seconds": 1.1 } ]
}
```

v1 ran the specification of the weak checksum directly, which recomputed a list length at every step. v2 runs a one-pass version proven equal to it (`weak_fast_correct`). A one-byte change in a 300 MB file sends 17,600 bytes and takes about 15 seconds; most of that is the pure-Lean SHA-256, so rsync is still much faster.

## Where vsync is weaker than rsync

- Files that exist only in the destination are not deleted (no `--delete`).
- Symlinks, ownership, ACLs and extended attributes are not copied.
- No compression, and both machines need vsync installed.
- Slower: SHA-256 is written in Lean, not optimized C.
- Trusted, unverified code remains: ~310 lines of C for file-system calls, the process plumbing, the Lean and C compilers, and the runtime.

## Try it

```
git clone https://github.com/Beneficial-AI-Foundation/vsync.git && cd vsync
lake build && install -m 755 .lake/build/bin/vsync ~/.local/bin/
vsync push src/ user@host:/srv/backup
```

Source and full install notes: [github.com/Beneficial-AI-Foundation/vsync](https://github.com/Beneficial-AI-Foundation/vsync)

## Sources

- [oss-security: rsync 3.4.0 security release](https://openwall.com/lists/oss-security/2025/01/14/3)
- [The Hacker News: Google Cloud researchers uncover flaws in rsync](https://thehackernews.com/2025/01/google-cloud-researchers-uncover-flaws.html)
- [Help Net Security: rsync vulnerabilities allow remote code execution](https://www.helpnetsecurity.com/2025/01/15/rsync-vulnerabilities-allow-remote-code-execution-on-servers-patch-quickly/)
- [rsync commit: checksum negotiation and xxHash (2020)](https://lists.samba.org/archive/rsync-cvs/2020-May/007538.html)
