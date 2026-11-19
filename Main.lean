import VSync

open VSync

/-! ## Native helpers (native/vsync_io.c) -/

@[extern "vsync_write_atomic"]
opaque writeAtomic (dst : @& String) (modeFrom : @& String) (data : @& ByteArray) : IO Unit
@[extern "vsync_now_ns"] opaque nowNs : IO UInt64
@[extern "vsync_lstat"] opaque lstatRaw (path : @& String) : IO ByteArray
@[extern "vsync_rd_open"] opaque rdOpen (root : @& String) (rel : @& ByteArray) : IO UInt64
@[extern "vsync_fstat"] opaque fstatRaw (fd : UInt64) : IO ByteArray
@[extern "vsync_pread"] opaque pread (fd off len : UInt64) : IO ByteArray
@[extern "vsync_close"] opaque closeFd (fd : UInt64) : IO Unit
@[extern "vsync_wr_begin"] opaque wrBegin (root : @& String) (rel : @& ByteArray) : IO UInt64
@[extern "vsync_wr_write"] opaque wrWrite (slot : UInt64) (data : @& ByteArray) : IO Unit
@[extern "vsync_wr_commit"] opaque wrCommit (slot mode mtime : UInt64) : IO Unit
@[extern "vsync_wr_abort"] opaque wrAbort (slot : UInt64) : IO Unit
@[extern "vsync_mkdir"] opaque mkdirAt (root : @& String) (rel : @& ByteArray) (mode : UInt64) : IO Unit
@[extern "vsync_setmeta"]
opaque setMetaAt (root : @& String) (rel : @& ByteArray) (mode mtime : UInt64) : IO Unit

def u64At (a : ByteArray) (k : Nat) : Nat :=
  (List.range 8).foldl (fun acc b => acc * 256 + (a[8 * k + b]!).toNat) 0

structure FileStat where
  kind : Nat   -- 0 missing, 1 file, 2 dir, 3 symlink, 4 other
  size : Nat
  mode : Nat
  mtime : Nat

def lstat (p : String) : IO FileStat := do
  let a ← lstatRaw p
  return ⟨u64At a 0, u64At a 1, u64At a 2, u64At a 3⟩

/-! ## Framing: 4-byte big-endian length, then a `Msg` encoded with the verified codec -/

def readExact (s : IO.FS.Stream) (n : Nat) : IO ByteArray := do
  let mut buf := ByteArray.emptyWithCapacity n
  while buf.size < n do
    let chunk ← s.read (n - buf.size).toUSize
    if chunk.isEmpty then throw (IO.userError "connection closed")
    buf := buf ++ chunk
  return buf

def sendMsg (s : IO.FS.Stream) (m : Msg) : IO Unit := do
  let body := encodeMsg m
  let n := body.size
  s.write ⟨#[(n >>> 24).toUInt8, (n >>> 16).toUInt8, (n >>> 8).toUInt8, n.toUInt8]⟩
  s.write body
  s.flush

def recvMsg (s : IO.FS.Stream) (cap : Nat) : IO Msg := do
  let h ← readExact s 4
  let n := h[0]!.toNat * 16777216 + h[1]!.toNat * 65536 + h[2]!.toNat * 256 + h[3]!.toNat
  if n > cap then throw (IO.userError s!"message too large ({n} bytes)")
  match decodeMsg (← readExact s n) with
  | some m => return m
  | none => throw (IO.userError "malformed message")

def errText (e : ByteArray) : String := (String.fromUTF8? e).getD "<binary error>"

/-! ## `sync`: single local file, in memory, exact (Spec.sync_local_exact) -/

def syncFiles (src dst : System.FilePath) (blk? : Option Nat) : IO UInt32 := do
  if (← src.isDir) then
    IO.eprintln s!"vsync: {src} is a directory (use `vsync push` for trees)"; return 1
  if (← dst.isDir) then
    IO.eprintln s!"vsync: {dst} is a directory"; return 1
  let new ← IO.FS.readBinFile src
  let dstExists ← dst.pathExists
  let old ← if dstExists then IO.FS.readBinFile dst else pure ByteArray.empty
  let B := blk?.getD (defaultBlock old.size)
  let ops := delta (signature old B) (confirmLocal old B) new
  let out := patch old B ops
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

/-! ## `serve`: receiving side -/

structure Recv where
  slot : UInt64
  oldFd : UInt64
  B : Nat
  nBlocks : Nat
  mode : Nat
  mtime : Nat
  failed : Option String

def serverCap : Nat := 64 * 1024 * 1024

/-- Apply one segment's ops, reading old blocks with `pread` (`patchWith` in Proto.lean). -/
def applySeg (r : Recv) (ops : List Op) : IO (Except String ByteArray) := do
  let mut out := ByteArray.empty
  for op in ops do
    match op with
    | .lits b => out := out ++ b
    | .copy i =>
      if i < r.nBlocks then out := out ++ (← pread r.oldFd (i * r.B).toUInt64 r.B.toUInt64)
      else return .error s!"copy of block {i} out of range"
  return .ok out

def serve (root : String) : IO UInt32 := do
  let inp ← IO.getStdin
  let out ← IO.getStdout
  unless (← System.FilePath.isDir root) do
    sendMsg out (.err s!"destination {root} is not a directory".toUTF8); return 1
  let mut cur : Option Recv := none
  repeat
    let m ← recvMsg inp serverCap
    match m with
    | .hello v =>
      sendMsg out (if v = 1 then .ok else .err "protocol version mismatch".toUTF8)
    | .quit => break
    | .mkdir p mode =>
      match safeRel p with
      | none => sendMsg out (.err "unsafe path".toUTF8)
      | some _ =>
        try mkdirAt root p mode.toUInt64; sendMsg out .ok
        catch e => sendMsg out (.err (toString e).toUTF8)
    | .setMeta p mode mtime =>
      match safeRel p with
      | none => sendMsg out (.err "unsafe path".toUTF8)
      | some _ =>
        try setMetaAt root p mode.toUInt64 mtime.toUInt64; sendMsg out .ok
        catch e => sendMsg out (.err (toString e).toUTF8)
    | .file p mode mtime size allowSkip =>
      match safeRel p with
      | none => sendMsg out (.err "unsafe path".toUTF8)
      | some _ =>
        try
          let fd ← rdOpen root p
          let (oldSize, same) ← if fd == 0 then pure (0, false) else do
            let st ← fstatRaw fd
            pure (u64At st 0,
              quickSkip allowSkip size mode mtime (u64At st 0) (u64At st 1) (u64At st 2))
          if same then
            closeFd fd; sendMsg out .skip
          else
            let B := defaultBlock oldSize
            let n := if fd == 0 then 0 else oldSize / B
            -- signature, streamed block by block (sigData in Delta.lean)
            let mut blocks : Array (Weak × ByteArray) := Array.mkEmpty n
            for i in [0:n] do
              blocks := blocks.push (blockInfo (← pread fd (i * B).toUInt64 B.toUInt64))
            let slot ← wrBegin root p
            cur := some ⟨slot, fd, B, n, mode, mtime, none⟩
            sendMsg out (.sig ⟨B, blocks⟩)
        catch e => sendMsg out (.err (toString e).toUTF8)
    | .seg ops sha =>
      match cur with
      | none => pure ()
      | some r =>
        if r.failed.isNone then
          match ← applySeg r ops with
          | .error msg => cur := some { r with failed := some msg }
          | .ok seg =>
            match acceptSeg seg sha with
            | none => cur := some { r with failed := some "segment checksum mismatch" }
            | some good =>
              try wrWrite r.slot good
              catch e => cur := some { r with failed := some (toString e) }
    | .endFile =>
      match cur with
      | none => sendMsg out (.err "no file in progress".toUTF8)
      | some r =>
        closeFd r.oldFd
        cur := none
        match r.failed with
        | some msg => wrAbort r.slot; sendMsg out (.err msg.toUTF8)
        | none =>
          try wrCommit r.slot r.mode.toUInt64 r.mtime.toUInt64; sendMsg out .ok
          catch e => wrAbort r.slot; sendMsg out (.err (toString e).toUTF8)
    | _ => sendMsg out (.err "unexpected message".toUTF8)
  if let some r := cur then wrAbort r.slot; closeFd r.oldFd
  return 0

/-! ## `push`: sending side -/

structure Stats where
  files : Nat := 0
  skipped : Nat := 0
  dirs : Nat := 0
  literal : Nat := 0
  total : Nat := 0
  errors : Nat := 0
  symlinks : Nat := 0

def clientCap : Nat := 1024 * 1024 * 1024

/-- Read up to `n` bytes (fewer only at end of file). -/
def readUpTo (h : IO.FS.Handle) (n : Nat) : IO ByteArray := do
  let mut buf := ByteArray.emptyWithCapacity n
  while buf.size < n do
    let chunk ← h.read (n - buf.size).toUSize
    if chunk.isEmpty then break
    buf := buf ++ chunk
  return buf

def sendFile (inp out : IO.FS.Stream) (chk : Bool) (path : System.FilePath) (rel : String)
    (st : FileStat) (stats : Stats) : IO Stats := do
  let now := (← nowNs).toNat
  sendMsg out (.file rel.toUTF8 st.mode st.mtime st.size (maySkip chk st.mtime now))
  match ← recvMsg inp clientCap with
  | .skip => return { stats with skipped := stats.skipped + 1 }
  | .err e =>
    IO.eprintln s!"vsync: {rel}: {errText e}"
    return { stats with errors := stats.errors + 1 }
  | .sig d =>
    let sig := Sig.build d
    let h ← IO.FS.Handle.mk path .read
    let mut lit := 0
    -- segments are a whole number of blocks, so block alignment is kept across segments
    let segLen := if 0 < sig.B then max sig.B (segmentSize / sig.B * sig.B) else segmentSize
    repeat
      let seg ← readUpTo h segLen
      if seg.isEmpty then break
      let ops := if 0 < sig.B then delta sig confirmRemote seg else #[.lits seg]
      lit := lit + litBytes ops
      sendMsg out (.seg ops.toList (sha256 seg))
      if seg.size < segLen then break
    sendMsg out .endFile
    match ← recvMsg inp clientCap with
    | .ok => return { stats with files := stats.files + 1, literal := stats.literal + lit,
                                 total := stats.total + st.size }
    | .err e =>
      IO.eprintln s!"vsync: {rel}: {errText e}"
      return { stats with errors := stats.errors + 1 }
    | _ => throw (IO.userError "protocol error")
  | _ => throw (IO.userError "protocol error")

def expectOk (inp : IO.FS.Stream) (what : String) (stats : Stats) : IO Stats := do
  match ← recvMsg inp clientCap with
  | .ok => return stats
  | .err e => IO.eprintln s!"vsync: {what}: {errText e}"; return { stats with errors := stats.errors + 1 }
  | _ => throw (IO.userError "protocol error")

partial def walk (inp out : IO.FS.Stream) (chk : Bool) (dir : System.FilePath) (relDir : String)
    (stats : Stats) : IO Stats := do
  let entries := (← dir.readDir).qsort (fun a b => a.fileName < b.fileName)
  let mut stats := stats
  for e in entries do
    let rel := if relDir.isEmpty then e.fileName else relDir ++ "/" ++ e.fileName
    if (safeRel rel.toUTF8).isNone then
      IO.eprintln s!"vsync: skipping {rel}: name not allowed"; continue
    let st ← lstat e.path.toString
    match st.kind with
    | 1 => stats ← sendFile inp out chk e.path rel st stats
    | 2 =>
      sendMsg out (.mkdir rel.toUTF8 st.mode)
      stats ← expectOk inp rel stats
      stats ← walk inp out chk e.path rel { stats with dirs := stats.dirs + 1 }
      sendMsg out (.setMeta rel.toUTF8 st.mode st.mtime)
      stats ← expectOk inp rel stats
    | 3 => stats := { stats with symlinks := stats.symlinks + 1 }
    | _ => IO.eprintln s!"vsync: skipping {rel}: not a regular file or directory"
  return stats

def push (src dest rsh remoteBin : String) (chk : Bool) : IO UInt32 := do
  let st ← lstat src
  if st.kind != 1 && st.kind != 2 then
    IO.eprintln s!"vsync: {src}: not a regular file or directory"; return 1
  let (cmd, args) ← match splitRemote dest with
    | some (host, path) =>
      let parts := (rsh.splitOn " ").filter (· ≠ "")
      pure (parts.headD "ssh", (parts.drop 1 ++ [host, remoteBin, "serve", path]).toArray)
    | none => do pure ((← IO.appPath).toString, #["serve", dest])
  let child ← IO.Process.spawn { cmd, args, stdin := .piped, stdout := .piped, stderr := .inherit }
  let out := IO.FS.Stream.ofHandle child.stdin
  let inp := IO.FS.Stream.ofHandle child.stdout
  sendMsg out (.hello 1)
  match ← recvMsg inp clientCap with
  | .ok => pure ()
  | .err e => IO.eprintln s!"vsync: {errText e}"; return 1
  | _ => IO.eprintln "vsync: protocol error"; return 1
  let stats ← if st.kind == 1 then
      let name := (System.FilePath.mk src).fileName.getD src
      sendFile inp out chk src name st {}
    else walk inp out chk src "" {}
  sendMsg out .quit
  let (_, child) ← child.takeStdin
  let _ ← child.wait
  IO.println s!"files={stats.files} unchanged={stats.skipped} dirs={stats.dirs} \
    bytes={stats.total} literal_bytes={stats.literal} \
    reused={stats.total - min stats.total stats.literal} symlinks_skipped={stats.symlinks} \
    errors={stats.errors}"
  return if stats.errors == 0 then 0 else 1

/-! ## main -/

def usage : String :=
  "usage:\n" ++
  "  vsync sync <src-file> <dst-file> [block-size]\n" ++
  "      update one local file in place (exact, byte-confirmed)\n" ++
  "  vsync push <src> <dest-dir> [--checksum] [--rsh CMD] [--remote-vsync PATH]\n" ++
  "      stream a file or directory tree into <dest-dir>; <dest-dir> may be host:dir (over ssh)\n" ++
  "  vsync serve <dir>\n" ++
  "      receiving side (started by push; speaks the protocol on stdin/stdout)"

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | some (.sync src dst blk) =>
    try syncFiles src dst blk catch e => IO.eprintln s!"vsync: {e}"; return 1
  | some (.push src dest rsh bin chk) =>
    try push src dest rsh bin chk catch e => IO.eprintln s!"vsync: {e}"; return 1
  | some (.serve root) =>
    try serve root catch e => IO.eprintln s!"vsync serve: {e}"; return 1
  | none => IO.eprintln usage; return 1
