/-! Pure part of the command line: argument parsing and block-size choice. -/

namespace VSync

inductive Cmd where
  /-- Update one local file in place (in memory, unconditionally exact). -/
  | sync (src dst : String) (block : Option Nat)
  /-- Stream a file or directory tree to `dest` (local dir or `host:dir`). -/
  | push (src dest : String) (rsh : String) (remoteBin : String) (checksum : Bool)
  /-- Receiving side, speaks the protocol on stdin/stdout, confined to `root`. -/
  | serve (root : String)
  deriving Repr, DecidableEq

/-- Parse `push` options after the two positional arguments. -/
def parsePushOpts (src dest : String) : List String → String → String → Bool → Option Cmd
  | [], rsh, bin, chk => some (.push src dest rsh bin chk)
  | "--rsh" :: r :: rest, _, bin, chk => parsePushOpts src dest rest r bin chk
  | "--remote-vsync" :: b :: rest, rsh, _, chk => parsePushOpts src dest rest rsh b chk
  | "--checksum" :: rest, rsh, bin, _ => parsePushOpts src dest rest rsh bin true
  | _, _, _, _ => none

theorem parsePushOpts_push (src dest : String) (opts : List String) (rsh bin : String) (chk : Bool)
    (c : Cmd) : parsePushOpts src dest opts rsh bin chk = some c →
      ∃ r b k, c = .push src dest r b k := by
  fun_induction parsePushOpts src dest opts rsh bin chk <;> intro h
  all_goals first
    | (cases h; exact ⟨_, _, _, rfl⟩)
    | (simp at h)
    | solve_by_elim

def parseArgs : List String → Option Cmd
  | ["sync", src, dst] => some (.sync src dst none)
  | ["sync", src, dst, b] =>
    match b.toNat? with
    | some n => if n = 0 then none else some (.sync src dst (some n))
    | none => none
  | "push" :: src :: dest :: opts => parsePushOpts src dest opts "ssh" "vsync" false
  | ["serve", root] => some (.serve root)
  | _ => none

/-- rsync-ish default: ~sqrt(size), clamped to [700, 131072]. -/
def defaultBlock (n : Nat) : Nat := max 700 (min 131072 (Nat.sqrt n))

/-- Split `host:path` (a colon before any slash) from a local path. -/
def splitRemote (dest : String) : Option (String × String) :=
  match dest.splitOn ":" with
  | host :: rest@(_ :: _) =>
    if host.isEmpty || host.contains '/' then none else some (host, ":".intercalate rest)
  | _ => none

/-- Segment size for streaming: the sender holds at most this much of a file at once. -/
def segmentSize : Nat := 8 * 1024 * 1024

end VSync
