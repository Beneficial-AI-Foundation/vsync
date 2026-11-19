import VSync.Wire
import VSync.Proofs

/-!
# Protocol: messages, path safety, streaming

* `Msg` and its codec `msgC` (built from the proven codecs in `Wire`).
* `safeRel` — validation of relative paths received from the peer.
* `patchWith` / segment lemmas — the model of what the streaming receiver does.
-/

namespace VSync

open Wire

/-! ## Messages -/

inductive Msg where
  | hello (version : Nat)
  | file (path : ByteArray) (mode mtime size : Nat) (maySkip : Bool)
  | seg (ops : List Op) (sha : ByteArray)
  | endFile
  | mkdir (path : ByteArray) (mode : Nat)
  | setMeta (path : ByteArray) (mode mtime : Nat)
  | quit
  | ok
  | skip
  | err (msg : ByteArray)
  | sig (d : SigData)

def opC : Codec Op :=
  iso (pair varint (pair varint bytes))
    (fun (t, i, b) => if t = 0 then .copy i else .lits b)
    (fun | .copy i => (0, i, ByteArray.empty) | .lits b => (1, 0, b))
    (fun y => by cases y <;> rfl)

def sigC : Codec SigData :=
  iso (pair varint (list (pair (pair varint varint) bytes)))
    (fun (B, l) => ⟨B, (l.map fun ((a, b), s) => (⟨a, b⟩, s)).toArray⟩)
    (fun d => (d.B, d.blocks.toList.map fun (w, s) => ((w.a, w.b), s)))
    (fun d => by
      have e : ∀ x : Weak × ByteArray, ((⟨x.1.a, x.1.b⟩ : Weak), x.2) = x := fun ⟨⟨_, _⟩, _⟩ => rfl
      cases d; simp [Function.comp_def, e])

abbrev MsgRec := Nat × ByteArray × List Nat × List Op × ByteArray × SigData

def Msg.toRec : Msg → MsgRec
  | .hello v => (0, .empty, [v], [], .empty, ⟨0, #[]⟩)
  | .file p m t s q => (1, p, [m, t, s, if q then 1 else 0], [], .empty, ⟨0, #[]⟩)
  | .seg ops h => (2, .empty, [], ops, h, ⟨0, #[]⟩)
  | .endFile => (3, .empty, [], [], .empty, ⟨0, #[]⟩)
  | .mkdir p m => (4, p, [m], [], .empty, ⟨0, #[]⟩)
  | .setMeta p m t => (5, p, [m, t], [], .empty, ⟨0, #[]⟩)
  | .quit => (6, .empty, [], [], .empty, ⟨0, #[]⟩)
  | .ok => (7, .empty, [], [], .empty, ⟨0, #[]⟩)
  | .skip => (8, .empty, [], [], .empty, ⟨0, #[]⟩)
  | .err e => (9, .empty, [], [], e, ⟨0, #[]⟩)
  | .sig d => (10, .empty, [], [], .empty, d)

def Msg.ofRec : MsgRec → Msg
  | (0, _, ns, _, _, _) => .hello (ns.getD 0 0)
  | (1, p, ns, _, _, _) => .file p (ns.getD 0 0) (ns.getD 1 0) (ns.getD 2 0) (ns.getD 3 0 == 1)
  | (2, _, _, ops, h, _) => .seg ops h
  | (3, _, _, _, _, _) => .endFile
  | (4, p, ns, _, _, _) => .mkdir p (ns.getD 0 0)
  | (5, p, ns, _, _, _) => .setMeta p (ns.getD 0 0) (ns.getD 1 0)
  | (6, _, _, _, _, _) => .quit
  | (7, _, _, _, _, _) => .ok
  | (8, _, _, _, _, _) => .skip
  | (9, _, _, _, e, _) => .err e
  | (_, _, _, _, _, d) => .sig d

theorem Msg.ofRec_toRec (m : Msg) : Msg.ofRec m.toRec = m := by
  cases m with
  | file p m t s q => cases q <;> rfl
  | _ => rfl

def msgC : Codec Msg :=
  iso (pair varint (pair bytes (pair (list varint) (pair (list opC) (pair bytes sigC)))))
    Msg.ofRec Msg.toRec Msg.ofRec_toRec

def encodeMsg (m : Msg) : ByteArray := msgC.encTo ByteArray.empty m
def decodeMsg (a : ByteArray) : Option Msg := decodeAll msgC a

theorem decodeMsg_encodeMsg (m : Msg) (h : msgC.valid m) : decodeMsg (encodeMsg m) = some m := by
  unfold encodeMsg decodeMsg
  rw [msgC.encTo_eq]
  have : ByteArray.empty ++ msgC.enc m = msgC.enc m := ba_ext (by simp)
  rw [this]
  exact decodeAll_enc msgC m h

/-! ## Path safety -/

/-- A path component is a plain name: non-empty, not `.` or `..`, no `/` and no NUL. -/
def validComp (c : List UInt8) : Bool :=
  !c.isEmpty && c != [46] && c != [46, 46] && !c.contains 0 && !c.contains 47

/-- Validate a relative path from the peer (bytes, `/`-separated). Absolute paths, empty
components (`a//b`), `.` and `..` are all rejected. -/
def safeRel (p : ByteArray) : Option (List (List UInt8)) :=
  let cs := (L p).splitOn 47
  if cs.all validComp then some cs else none

theorem safeRel_sound {p : ByteArray} {cs : List (List UInt8)} (h : safeRel p = some cs) :
    ∀ c ∈ cs, c ≠ [] ∧ c ≠ [46] ∧ c ≠ [46, 46] ∧ (0 : UInt8) ∉ c ∧ (47 : UInt8) ∉ c := by
  simp only [safeRel] at h
  split at h
  · rename_i hall
    cases h
    intro c hc
    have := List.all_eq_true.mp hall c hc
    simp [validComp] at this
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := this
    exact ⟨h1, h2, h3, h4, h5⟩
  · cases h

/-! ## Quick check -/

/-- Files modified less than this long ago are never skipped (their mtime may not yet
distinguish them from an older version: the "racy" case). -/
def racyWindowNs : Nat := 2000000000

/-- Sender side: may the receiver skip this file if size, mode and mtime match? -/
def maySkip (checksum : Bool) (mtimeNs nowNs : Nat) : Bool :=
  !checksum && mtimeNs + racyWindowNs ≤ nowNs

/-- Receiver side: skip only if allowed and size, mode and mtime (ns) all match. -/
def quickSkip (allowed : Bool) (srcSize srcMode srcMtime dstSize dstMode dstMtime : Nat) : Bool :=
  allowed && srcSize == dstSize && srcMode == dstMode && srcMtime == dstMtime

theorem quickSkip_sound {a b c d e f : Nat} {allowed : Bool}
    (h : quickSkip allowed a b c d e f = true) : allowed = true ∧ a = d ∧ b = e ∧ c = f := by
  simp only [quickSkip, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem maySkip_not_racy {chk : Bool} {m now : Nat} (h : maySkip chk m now = true) :
    chk = false ∧ m + racyWindowNs ≤ now := by
  simp [maySkip] at h; exact h

/-! ## Streaming receiver model -/

def patchStepWith (get : Nat → ByteArray) (acc : ByteArray) : Op → ByteArray
  | .copy i => acc ++ get i
  | .lits b => acc ++ b

/-- What the receiver computes for one segment, reading old blocks through `get`
(at run time: `pread` at offset `i * B`). -/
def patchWith (get : Nat → ByteArray) (ops : List Op) : ByteArray :=
  ops.foldl (patchStepWith get) ByteArray.empty

theorem foldl_with_eq (old : ByteArray) (B : Nat) (get : Nat → ByteArray)
    (hget : ∀ i < numBlocks old B, get i = block old B i) :
    ∀ (l : List Op), (∀ op ∈ l, ValidOp old B op) → ∀ acc,
      l.foldl (patchStepWith get) acc = l.foldl (patchStep old B) acc
  | [], _, _ => rfl
  | op :: l, hl, acc => by
    simp only [List.foldl_cons]
    have hop := hl op (by simp)
    have e : patchStepWith get acc op = patchStep old B acc op := by
      cases op with
      | copy i => simp only [ValidOp] at hop; simp [patchStepWith, patchStep, hget i hop]
      | lits b => rfl
    rw [e]
    exact foldl_with_eq old B get hget l (fun o ho => hl o (by simp [ho])) _

theorem patchWith_eq (old : ByteArray) (B : Nat) (get : Nat → ByteArray)
    (hget : ∀ i < numBlocks old B, get i = block old B i) (ops : Array Op)
    (hv : AllValid old B ops) : patchWith get ops.toList = patch old B ops := by
  unfold patchWith patch
  rw [← Array.foldl_toList]
  exact foldl_with_eq old B get hget ops.toList hv _

/-- Receiver check for a segment: keep it only if its SHA-256 matches the sender's claim. -/
def acceptSeg (out sha : ByteArray) : Option ByteArray := if sha256 out = sha then some out else none

theorem acceptSeg_sound {out sha x : ByteArray} (h : acceptSeg out sha = some x) :
    x = out ∧ sha256 x = sha := by
  unfold acceptSeg at h
  split at h
  · cases h; exact ⟨rfl, ‹_›⟩
  · cases h

end VSync
