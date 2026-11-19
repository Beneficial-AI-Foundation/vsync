/-! Pure part of the command line: argument parsing and block-size choice. -/

namespace VSync

inductive Cmd where
  | sync (src dst : String) (block : Option Nat)
  deriving Repr, DecidableEq

def parseArgs : List String → Option Cmd
  | ["sync", src, dst] => some (.sync src dst none)
  | ["sync", src, dst, b] =>
    match b.toNat? with
    | some n => if n = 0 then none else some (.sync src dst (some n))
    | none => none
  | _ => none

/-- rsync-ish default: ~sqrt(size), clamped to [700, 131072]. -/
def defaultBlock (n : Nat) : Nat := max 700 (min 131072 (Nat.sqrt n))

end VSync
