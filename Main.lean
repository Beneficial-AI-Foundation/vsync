import VSync

open VSync

def usage : String :=
  "usage: vsync sync <src> <dst> [block-size]\n" ++
  "  Updates <dst> to match <src> using the rsync delta algorithm\n" ++
  "  (signature of dst -> delta from src -> patch dst)."

def syncFiles (src dst : System.FilePath) (blk? : Option Nat) : IO UInt32 := do
  let new := (← IO.FS.readBinFile src).data
  let old ← if ← dst.pathExists then pure (← IO.FS.readBinFile dst).data else pure #[]
  let B := blk?.getD (defaultBlock old.size)
  let sig := signature old B
  let ops := delta sig new
  let out := patch old B ops
  let copies := numCopies ops
  let lits := numLits ops
  -- `patch_delta` proves out = new unless the strong hash collides; check anyway.
  if out != new then
    IO.eprintln "strong-hash collision detected; falling back to full copy"
  let result := if out == new then out else new
  let tmp := dst.toString ++ ".vsync-tmp"
  IO.FS.writeBinFile tmp ⟨result⟩
  IO.FS.rename tmp dst
  IO.println s!"block={B} old={old.size}B new={new.size}B matched_blocks={copies} \
    literal_bytes={lits} reused={copies * B}B ({if new.size = 0 then 100 else copies * B * 100 / new.size}%)"
  return 0

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | some (.sync src dst blk) => syncFiles src dst blk
  | none => IO.eprintln usage; return 1
