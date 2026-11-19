import VSync.Checksum
import VSync.Sha256
import Std.Data.HashMap

/-!
# rsync delta algorithm (hardened)

* `signature old B` — for every full `B`-byte block of `old`: weak rolling checksum and
  SHA-256. Indexed by weak checksum (cheap filter) and by (weak, SHA-256) (exact lookup),
  so a position costs O(1) map lookups however many duplicate blocks `old` has.
* `delta sig confirm new` — scan `new` with the rolling weak checksum; on a hit, look up
  (weak, SHA-256) and take the first candidate block that `confirm` accepts.
  - `confirmLocal old B` compares the bytes: correctness is **unconditional**.
  - `confirmRemote` trusts SHA-256 (the sender doesn't have `old`).
  Consecutive literal bytes are emitted as one `lits` op.
* `patch old B ops` — rebuild the file.
-/

namespace VSync

/-! ## Blocks and ops -/

def strong (w : ByteArray) : ByteArray := sha256 w

/-- Block `i` of `old`. -/
def block (old : ByteArray) (B i : Nat) : ByteArray := old.extract (i * B) (i * B + B)

inductive Op where
  | copy (i : Nat)
  | lits (bytes : ByteArray)
  deriving Inhabited

def Op.bytes (old : ByteArray) (B : Nat) : Op → List UInt8
  | .copy i => (block old B i).data.toList
  | .lits b => b.data.toList

def Op.isCopy : Op → Bool
  | .copy _ => true
  | .lits _ => false

def Op.litLen : Op → Nat
  | .copy _ => 0
  | .lits b => b.size

def numCopies (ops : Array Op) : Nat := ops.toList.countP Op.isCopy
def litBytes (ops : Array Op) : Nat := (ops.toList.map Op.litLen).sum

/-! ## Signature -/

structure Key where
  w : Weak
  d : ByteArray
  deriving DecidableEq, Hashable

structure Sig where
  B : Nat
  strongs : Array ByteArray
  weaks : Std.HashMap Weak Unit
  index : Std.HashMap Key (List Nat)

/-- Prepend block index `i` to a candidate list. -/
def consIdx (i : Nat) : Option (List Nat) → Option (List Nat)
  | none => some [i]
  | some l => some (i :: l)

/-- Per-block data sent over the wire: (weak checksum, SHA-256). -/
def blockInfo (blk : ByteArray) : Weak × ByteArray := (weakFast blk.data.toList, strong blk)

/-- Everything a sender needs about `old`, as plain data (no hash maps). -/
structure SigData where
  B : Nat
  blocks : Array (Weak × ByteArray)

def numBlocks (old : ByteArray) (B : Nat) : Nat := if B = 0 then 0 else old.size / B

def sigData (old : ByteArray) (B : Nat) : SigData :=
  { B, blocks := (Array.range (numBlocks old B)).map fun i => blockInfo (block old B i) }

def addBlock (d : SigData) (i : Nat) (m : Std.HashMap Key (List Nat)) : Std.HashMap Key (List Nat) :=
  m.alter ⟨d.blocks[i]!.1, d.blocks[i]!.2⟩ (consIdx i)

def addWeak (d : SigData) (i : Nat) (m : Std.HashMap Weak Unit) : Std.HashMap Weak Unit :=
  m.insert d.blocks[i]!.1 ()

/-- Build the lookup structure from plain signature data (sender side). -/
def Sig.build (d : SigData) : Sig :=
  { B := d.B
    strongs := d.blocks.map (·.2)
    weaks := (List.range d.blocks.size).foldr (addWeak d) {}
    index := (List.range d.blocks.size).foldr (addBlock d) {} }

def signature (old : ByteArray) (B : Nat) : Sig := Sig.build (sigData old B)

/-! ## Match confirmation -/

/-- Local mode: confirm a candidate by comparing bytes with the real block. -/
def confirmLocal (old : ByteArray) (B : Nat) (i : Nat) (win : ByteArray) : Bool :=
  decide (win = block old B i)

/-- Remote mode: the sender has only the signature, so it trusts SHA-256. -/
def confirmRemote (_ : Nat) (_ : ByteArray) : Bool := true

/-! ## Delta -/

def pick (sig : Sig) (confirm : Nat → ByteArray → Bool) (win d : ByteArray) :
    List Nat → Option Nat
  | [] => none
  | i :: is => if sig.strongs[i]? = some d ∧ confirm i win = true then some i
               else pick sig confirm win d is

def findMatch (sig : Sig) (confirm : Nat → ByteArray → Bool) (w : Weak) (win : ByteArray) :
    Option Nat :=
  if sig.weaks.contains w then
    match sig.index[(⟨w, strong win⟩ : Key)]? with
    | none => none
    | some l => pick sig confirm win (strong win) l
  else none

/-- Emit the pending literal run `new[s, p)`, if non-empty. -/
def flush (new : ByteArray) (s p : Nat) (acc : Array Op) : Array Op :=
  if s < p then acc.push (.lits (new.extract s p)) else acc

/-- Main scan loop. `s` = start of the pending literal run, `p` = window position,
`w` = rolling weak checksum of the window (affects only which matches are found). -/
def go (sig : Sig) (confirm : Nat → ByteArray → Bool) (hB : 0 < sig.B) (new : ByteArray)
    (s p : Nat) (w : Weak) (acc : Array Op) : Array Op :=
  if hp : p + sig.B ≤ new.size then
    match findMatch sig confirm w (new.extract p (p + sig.B)) with
    | some i =>
      go sig confirm hB new (p + sig.B) (p + sig.B) (weakAt new (p + sig.B) sig.B)
        ((flush new s p acc).push (.copy i))
    | none =>
      let w' := if h : p + sig.B < new.size then roll sig.B w new[p] new[p + sig.B] else w
      go sig confirm hB new s (p + 1) w' acc
  else
    flush new s new.size acc
termination_by new.size - p

def delta (sig : Sig) (confirm : Nat → ByteArray → Bool) (new : ByteArray) : Array Op :=
  if hB : 0 < sig.B then go sig confirm hB new 0 0 (weakAt new 0 sig.B) #[]
  else flush new 0 new.size #[]

/-! ## Patch -/

def patchStep (old : ByteArray) (B : Nat) (acc : ByteArray) : Op → ByteArray
  | .copy i => acc ++ block old B i
  | .lits b => acc ++ b

def patch (old : ByteArray) (B : Nat) (ops : Array Op) : ByteArray :=
  ops.foldl (patchStep old B) ByteArray.empty

end VSync
