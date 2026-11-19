import VSync

open VSync

/-- Atomic, durable replace of `dst` (see native/vsync_io.c). Permission bits are copied
from `modeFrom` when that path exists. -/
@[extern "vsync_write_atomic"]
opaque writeAtomic (dst : @& String) (modeFrom : @& String) (data : @& ByteArray) : IO Unit

def usage : String :=
  "usage: vsync sync <src> <dst> [block-size]\n" ++
  "  Updates <dst> to match <src> using the rsync delta algorithm\n" ++
  "  (signature of dst -> delta from src -> patch dst)."

def syncFiles (src dst : System.FilePath) (blk? : Option Nat) : IO UInt32 := do
  if (← src.isDir) then
    IO.eprintln s!"vsync: {src} is a directory"; return 1
  if (← dst.isDir) then
    IO.eprintln s!"vsync: {dst} is a directory"; return 1
  let new ← IO.FS.readBinFile src
  let dstExists ← dst.pathExists
  let old ← if dstExists then IO.FS.readBinFile dst else pure ByteArray.empty
  let B := blk?.getD (defaultBlock old.size)
  let ops := delta (signature old B) (confirmLocal old B) new
  let out := patch old B ops
  -- `Spec.sync_local_exact` proves out = new; this check only guards the unverified
  -- toolchain (Lean compiler, C compiler, runtime). Never write a wrong file.
  if out != new then
    IO.eprintln "vsync: internal error: patched output differs from source; nothing written"
    return 2
  let stats := s!"block={B} old={old.size}B new={new.size}B matched_blocks={numCopies ops} \
    literal_bytes={litBytes ops} reused={new.size - litBytes ops}B"
  if dstExists && old == new then
    IO.println s!"{stats} (unchanged, not rewritten)"
    return 0
  writeAtomic dst.toString (if dstExists then dst.toString else src.toString) out
  IO.println stats
  return 0

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | some (.sync src dst blk) =>
    try syncFiles src dst blk
    catch e => IO.eprintln s!"vsync: {e}"; return 1
  | none => IO.eprintln usage; return 1
