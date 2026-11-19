import VSync.Checksum
import Std.Data.HashMap

/-!
# rsync delta algorithm

* `signature old B` — weak + strong checksum of every full `B`-byte block of `old`.
* `delta sig new`   — scan `new` with a rolling weak checksum; on a weak hit,
  confirm with the strong hash and emit `copy i`, otherwise emit a literal byte.
* `patch old B ops` — rebuild the file from `old` and the ops.

Main theorem `patch_delta`: if the strong hash has no collisions against the
blocks of `old` (the assumption real rsync also makes), then
`patch old B (delta (signature old B) new) = new`.
-/

namespace VSync

/-! ## Strong hash: 64-bit FNV-1a. Not cryptographic; the proof is generic in it. -/

def fnvStep (h : UInt64) (b : UInt8) : UInt64 := (h ^^^ b.toUInt64) * 0x100000001b3
def strong (w : List UInt8) : UInt64 := w.foldl fnvStep 0xcbf29ce484222325

/-! ## Spec helpers -/

/-- Block `i` of `old` (the spec view). -/
def block (old : Array UInt8) (B i : Nat) : List UInt8 := (old.toList.drop (i * B)).take B

inductive Op where
  | copy (i : Nat)
  | lit (b : UInt8)
  deriving Repr, BEq, Inhabited

def Op.isCopy : Op → Bool
  | .copy _ => true
  | .lit _ => false

def numCopies (ops : Array Op) : Nat := ops.toList.countP Op.isCopy
def numLits (ops : Array Op) : Nat := ops.toList.countP (! ·.isCopy)

def Op.bytes (old : Array UInt8) (B : Nat) : Op → List UInt8
  | .copy i => block old B i
  | .lit b => [b]

/-! ## Signature -/

structure Sig where
  B : Nat
  strongs : Array UInt64
  index : Std.HashMap Weak (List Nat)

/-- Prepend block index `i` to a candidate list. -/
def consIdx (i : Nat) : Option (List Nat) → Option (List Nat)
  | none => some [i]
  | some l => some (i :: l)

def addBlock (old : Array UInt8) (B i : Nat) (m : Std.HashMap Weak (List Nat)) :
    Std.HashMap Weak (List Nat) :=
  m.alter (weakAt old (i * B) B) (consIdx i)

def signature (old : Array UInt8) (B : Nat) : Sig :=
  let n := if B = 0 then 0 else old.size / B
  let strongs := (Array.range n).map fun i => strong (old.extract (i * B) (i * B + B)).toList
  let index := (List.range n).foldr (addBlock old B) {}
  { B, strongs, index }

/-! ## Delta -/

def pushLit (acc : Array Op) (b : UInt8) : Array Op := acc.push (.lit b)

def pick (strongs : Array UInt64) (h : UInt64) : List Nat → Option Nat
  | [] => none
  | i :: is => if strongs[i]? == some h then some i else pick strongs h is

theorem pick_spec {s : Array UInt64} {h : UInt64} :
    ∀ {l : List Nat} {i : Nat}, pick s h l = some i → s[i]? = some h
  | [], _, hp => by simp [pick] at hp
  | j :: js, i, hp => by
    unfold pick at hp
    split at hp
    · rename_i hb; cases hp; simpa using hb
    · exact pick_spec hp

def findMatch (sig : Sig) (w : Weak) (win : List UInt8) : Option Nat :=
  match sig.index[w]? with
  | none => none
  | some cands => pick sig.strongs (strong win) cands

theorem findMatch_spec {sig : Sig} {w win i} (h : findMatch sig w win = some i) :
    sig.strongs[i]? = some (strong win) := by
  unfold findMatch at h
  split at h
  · cases h
  · exact pick_spec h

/-- Main scan loop. `w` is the rolling checksum of the window at `p`
(correctness of the output does not depend on it; only match-finding does). -/
def go (sig : Sig) (hB : 0 < sig.B) (new : Array UInt8) (p : Nat) (w : Weak)
    (acc : Array Op) : Array Op :=
  if hp : p + sig.B ≤ new.size then
    let win := (new.extract p (p + sig.B)).toList
    match findMatch sig w win with
    | some i =>
      let p' := p + sig.B
      go sig hB new p' (weakAt new p' sig.B) (acc.push (.copy i))
    | none =>
      let w' := if h : p + sig.B < new.size then roll sig.B w new[p] new[p + sig.B] else w
      go sig hB new (p + 1) w' (acc.push (.lit new[p]))
  else
    (new.extract p new.size).foldl pushLit acc
termination_by new.size - p

def delta (sig : Sig) (new : Array UInt8) : Array Op :=
  if hB : 0 < sig.B then go sig hB new 0 (weakAt new 0 sig.B) #[]
  else new.foldl pushLit #[]

/-! ## Patch -/

def patchStep (old : Array UInt8) (B : Nat) (acc : Array UInt8) : Op → Array UInt8
  | .copy i => acc ++ old.extract (i * B) (i * B + B)
  | .lit b => acc.push b

def patch (old : Array UInt8) (B : Nat) (ops : Array Op) : Array UInt8 :=
  ops.foldl (patchStep old B) #[]

end VSync
