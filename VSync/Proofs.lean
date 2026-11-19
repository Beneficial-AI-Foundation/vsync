import VSync.Delta

/-!
# Correctness of delta / patch

`patch_delta` : under `NoCollision old new B`,
  `patch old B (delta (signature old B) new) = new`.

`NoCollision` only quantifies over windows that actually occur in `new`,
so it is a satisfiable assumption (the same one rsync relies on), not a
vacuous "the hash is injective" axiom.
-/

namespace VSync

/-- Window of `new` starting at `p` (spec view). -/
def window (new : Array UInt8) (B p : Nat) : List UInt8 := (new.toList.drop p).take B

/-- No `B`-byte window of `new` collides (under `strong`) with a different block of `old`. -/
def NoCollision (old new : Array UInt8) (B : Nat) : Prop :=
  ∀ i, i < old.size / B → ∀ p, p + B ≤ new.size →
    strong (window new B p) = strong (block old B i) → window new B p = block old B i

def bytesOf (old : Array UInt8) (B : Nat) (ops : Array Op) : List UInt8 :=
  ops.toList.flatMap (Op.bytes old B)

theorem extract_toList (a : Array α) (s e : Nat) :
    (a.extract s e).toList = (a.toList.drop s).take (e - s) := by
  simp

theorem bytesOf_push (old : Array UInt8) (B : Nat) (acc : Array Op) (op : Op) :
    bytesOf old B (acc.push op) = bytesOf old B acc ++ op.bytes old B := by
  simp [bytesOf]

/-! ## patch -/

theorem foldl_patchStep (old : Array UInt8) (B : Nat) :
    ∀ (l : List Op) (acc : Array UInt8),
      (l.foldl (patchStep old B) acc).toList = acc.toList ++ l.flatMap (Op.bytes old B)
  | [], acc => by simp
  | op :: l, acc => by
    cases op <;> simp [foldl_patchStep old B l, patchStep, Op.bytes, block]

theorem patch_toList (old : Array UInt8) (B : Nat) (ops : Array Op) :
    (patch old B ops).toList = bytesOf old B ops := by
  unfold patch bytesOf
  rw [← Array.foldl_toList, foldl_patchStep]
  simp

/-! ## literal runs -/

theorem foldl_pushLit (old : Array UInt8) (B : Nat) :
    ∀ (l : List UInt8) (acc : Array Op),
      bytesOf old B (l.foldl pushLit acc) = bytesOf old B acc ++ l
  | [], acc => by simp
  | b :: l, acc => by
    simp only [List.foldl_cons, foldl_pushLit old B l, pushLit, bytesOf_push, Op.bytes]
    simp

theorem bytesOf_lits (old : Array UInt8) (B : Nat) (xs : Array UInt8) (acc : Array Op) :
    bytesOf old B (xs.foldl pushLit acc) = bytesOf old B acc ++ xs.toList := by
  rw [← Array.foldl_toList, foldl_pushLit]

/-! ## signature -/

theorem strongs_spec {old : Array UInt8} {B i : Nat} {s : UInt64} (hB : 0 < B)
    (h : (signature old B).strongs[i]? = some s) :
    i < old.size / B ∧ s = strong (block old B i) := by
  have hB' : B ≠ 0 := by omega
  simp [signature, hB'] at h
  obtain ⟨j, hj, rfl⟩ := h
  simp [Array.getElem?_range] at hj
  obtain ⟨hi, rfl⟩ := hj
  exact ⟨hi, rfl⟩

/-! ## delta -/

theorem go_spec (old new : Array UInt8) (B : Nat) (hB : 0 < (signature old B).B)
    (hNC : NoCollision old new B) :
    ∀ p w acc, p ≤ new.size →
      bytesOf old B (go (signature old B) hB new p w acc)
        = bytesOf old B acc ++ new.toList.drop p := by
  have hBB : (signature old B).B = B := rfl
  intro p
  induction h : new.size - p using Nat.strongRecOn generalizing p with
  | _ k ih =>
    intro w acc hp
    rw [go]
    split
    · rename_i hpB
      have hB0 : 0 < B := hBB ▸ hB
      have hpB' : p + B ≤ new.size := hBB ▸ hpB
      dsimp only
      have hwin : (new.extract p (p + (signature old B).B)).toList = window new B p := by
        simp [window, hBB]
      cases hm : findMatch (signature old B) w (new.extract p (p + (signature old B).B)).toList with
      | some i =>
        have hs := findMatch_spec hm
        obtain ⟨hi, hstr⟩ := strongs_spec (hBB ▸ hB) hs
        rw [hwin] at hstr
        have heq := hNC i hi p hpB' hstr
        dsimp only
        rw [ih (new.size - (p + (signature old B).B)) (by omega) _ rfl _ _ (by omega),
          bytesOf_push]
        simp only [Op.bytes, hBB, ← heq, window, List.append_assoc]
        congr 1
        have := List.take_append_drop B (new.toList.drop p)
        simpa [List.drop_drop, Nat.add_comm] using this
      | none =>
        dsimp only
        rw [ih (new.size - (p + 1)) (by omega) _ rfl _ _ (by omega), bytesOf_push]
        simp only [Op.bytes, List.append_assoc]
        congr 1
        rw [List.drop_eq_getElem_cons (show p < new.toList.length by simp; omega)]
        simp
    · rw [bytesOf_lits]
      simp only [extract_toList]
      rw [List.take_of_length_le (by simp)]

/-- **Main theorem.** Applying the delta of `new` against the signature of `old`
reconstructs `new` exactly (given no strong-hash collisions on `new`'s windows). -/
theorem patch_delta (old new : Array UInt8) (B : Nat) (hNC : NoCollision old new B) :
    patch old B (delta (signature old B) new) = new := by
  apply Array.toList_inj.mp
  rw [patch_toList]
  unfold delta
  split
  · rename_i hB
    rw [go_spec old new B hB hNC 0 _ _ (Nat.zero_le _)]
    simp [bytesOf]
  · rw [bytesOf_lits]
    simp [bytesOf]

/-! ## Safety: copies only reference blocks that exist in `old` -/

def ValidOp (old : Array UInt8) (B : Nat) : Op → Prop
  | .copy i => i < old.size / B
  | .lit _ => True

theorem lits_valid (old : Array UInt8) (B : Nat) :
    ∀ (l : List UInt8) (acc : Array Op), (∀ op ∈ acc.toList, ValidOp old B op) →
      ∀ op ∈ (l.foldl pushLit acc).toList, ValidOp old B op
  | [], acc, h => by simpa using h
  | b :: l, acc, h => by
    simp only [List.foldl_cons]
    apply lits_valid old B l
    intro op hop
    simp [pushLit] at hop
    rcases hop with hop | rfl
    · exact h op (by simpa using hop)
    · trivial

theorem go_valid (old new : Array UInt8) (B : Nat) (hB : 0 < (signature old B).B) :
    ∀ p w acc, (∀ op ∈ acc.toList, ValidOp old B op) →
      ∀ op ∈ (go (signature old B) hB new p w acc).toList, ValidOp old B op := by
  have hBB : (signature old B).B = B := rfl
  intro p
  induction h : new.size - p using Nat.strongRecOn generalizing p with
  | _ k ih =>
    intro w acc hacc
    rw [go]
    split
    · rename_i hpB
      have hB0 : 0 < B := hBB ▸ hB
      dsimp only
      cases hm : findMatch (signature old B) w (new.extract p (p + (signature old B).B)).toList with
      | some i =>
        obtain ⟨hi, -⟩ := strongs_spec hB0 (findMatch_spec hm)
        dsimp only
        apply ih (new.size - (p + (signature old B).B)) (by omega) _ rfl
        intro op hop
        simp at hop
        rcases hop with hop | rfl
        · exact hacc op (by simpa using hop)
        · exact hi
      | none =>
        dsimp only
        apply ih (new.size - (p + 1)) (by omega) _ rfl
        intro op hop
        simp at hop
        rcases hop with hop | rfl
        · exact hacc op (by simpa using hop)
        · trivial
    · rw [← Array.foldl_toList]
      exact lits_valid old B _ acc hacc

theorem delta_valid (old new : Array UInt8) (B : Nat) :
    ∀ op ∈ (delta (signature old B) new).toList, ValidOp old B op := by
  unfold delta
  split
  · exact go_valid old new B _ 0 _ _ (by simp)
  · rw [← Array.foldl_toList]
    exact lits_valid old B _ _ (by simp)

/-! ## Counting copies and literals -/

theorem numCopies_push (acc : Array Op) (op : Op) :
    numCopies (acc.push op) = numCopies acc + (if op.isCopy then 1 else 0) := by
  simp [numCopies, List.countP_append]

theorem numLits_push (acc : Array Op) (op : Op) :
    numLits (acc.push op) = numLits acc + (if op.isCopy then 0 else 1) := by
  cases op <;> simp [numLits, List.countP_append, Op.isCopy]

theorem lits_counts : ∀ (l : List UInt8) (acc : Array Op),
    numCopies (l.foldl pushLit acc) = numCopies acc ∧
    numLits (l.foldl pushLit acc) = numLits acc + l.length
  | [], acc => by simp
  | b :: l, acc => by
    have ih := lits_counts l (pushLit acc b)
    simp only [List.foldl_cons]
    rw [ih.1, ih.2]
    simp only [pushLit, numCopies_push, numLits_push, Op.isCopy, List.length_cons]
    simp; omega

/-! ## Completeness on unchanged data: every full block is found -/

theorem pick_complete {s : Array UInt64} {h : UInt64} :
    ∀ {l : List Nat} {k : Nat}, k ∈ l → s[k]? = some h → (pick s h l).isSome
  | [], _, hk, _ => by simp at hk
  | j :: js, k, hk, hs => by
    unfold pick
    split
    · rfl
    · rename_i hne
      rcases List.mem_cons.mp hk with rfl | hk
      · simp [hs] at hne
      · exact pick_complete hk hs

theorem index_complete (old : Array UInt8) (B : Nat) :
    ∀ (L : List Nat) (k : Nat), k ∈ L →
      ∃ l, (L.foldr (addBlock old B) {})[weakAt old (k * B) B]? = some l ∧ k ∈ l
  | [], _, hk => by simp at hk
  | j :: L, k, hk => by
    simp only [List.foldr_cons, addBlock, Std.HashMap.getElem?_alter]
    by_cases hj : j = k
    · subst hj
      simp only [beq_self_eq_true, ite_true]
      cases (L.foldr (addBlock old B) {})[weakAt old (j * B) B]? <;> simp [consIdx]
    · have hk' : k ∈ L := by
        rcases List.mem_cons.mp hk with h | h
        · exact absurd h.symm hj
        · exact h
      obtain ⟨l, hl, hkl⟩ := index_complete old B L k hk'
      split
      · rename_i heq
        have : weakAt old (j * B) B = weakAt old (k * B) B := by simpa using heq
        rw [this, hl]
        exact ⟨k :: l |>.tail.cons j, by simp [consIdx], by simp [hkl]⟩
      · exact ⟨l, hl, hkl⟩

theorem findMatch_self (x : Array UInt8) (B k : Nat) (hB : 0 < B) (hk : k < x.size / B) :
    (findMatch (signature x B) (weakAt x (k * B) B)
      (x.extract (k * B) (k * B + B)).toList).isSome := by
  have hB' : B ≠ 0 := by omega
  obtain ⟨l, hl, hkl⟩ := index_complete x B (List.range (x.size / B)) k (by simpa using hk)
  unfold findMatch
  have hidx : (signature x B).index[weakAt x (k * B) B]? = some l := by
    simpa [signature, hB'] using hl
  rw [hidx]
  apply pick_complete hkl
  simp [signature, hB', hk]

theorem go_self (x : Array UInt8) (B : Nat) (hB : 0 < (signature x B).B) :
    ∀ k, k ≤ x.size / B → ∀ acc,
      numCopies (go (signature x B) hB x (k * B) (weakAt x (k * B) (signature x B).B) acc)
          = numCopies acc + (x.size / B - k) ∧
      numLits (go (signature x B) hB x (k * B) (weakAt x (k * B) (signature x B).B) acc)
          = numLits acc + x.size % B := by
  have hBB : (signature x B).B = B := rfl
  have hB0 : 0 < B := hBB ▸ hB
  intro k
  induction h : x.size / B - k using Nat.strongRecOn generalizing k with
  | _ j ih =>
    intro hk acc
    rw [go]
    split
    · rename_i hpB
      have hlt : k + 1 ≤ x.size / B := by
        apply (Nat.le_div_iff_mul_le hB0).mpr
        rw [Nat.succ_mul]; exact hBB ▸ hpB
      dsimp only
      have hfm : (findMatch (signature x B) (weakAt x (k * B) (signature x B).B)
          (x.extract (k * B) (k * B + (signature x B).B)).toList).isSome :=
        findMatch_self x B k hB0 hlt
      cases hm : findMatch (signature x B) (weakAt x (k * B) (signature x B).B)
          (x.extract (k * B) (k * B + (signature x B).B)).toList with
      | none => rw [hm] at hfm; cases hfm
      | some i =>
        dsimp only
        have hgo : go (signature x B) hB x (k * B + (signature x B).B)
              (weakAt x (k * B + (signature x B).B) (signature x B).B) (acc.push (.copy i))
            = go (signature x B) hB x ((k + 1) * B) (weakAt x ((k + 1) * B) (signature x B).B)
              (acc.push (.copy i)) := by
          rw [Nat.succ_mul, hBB]
        rw [hgo]
        obtain ⟨h1, h2⟩ := ih (x.size / B - (k + 1)) (by omega) (k + 1) rfl hlt (acc.push (.copy i))
        rw [h1, h2, numCopies_push, numLits_push]
        simp [Op.isCopy]; omega
    · rename_i hpB
      have hk' : x.size / B = k := by
        have : ¬ (k + 1 ≤ x.size / B) := fun h => hpB (by
          have := (Nat.le_div_iff_mul_le hB0).mp h
          rw [Nat.succ_mul] at this; exact hBB ▸ this)
        omega
      rw [← Array.foldl_toList]
      obtain ⟨h1, h2⟩ := lits_counts (x.extract (k * B) x.size).toList acc
      rw [h1, h2]
      have hmod := Nat.mod_add_div x.size B
      rw [hk', Nat.mul_comm] at hmod
      simp
      omega

theorem delta_self (x : Array UInt8) (B : Nat) (hB : 0 < B) :
    numCopies (delta (signature x B) x) = x.size / B ∧
    numLits (delta (signature x B) x) = x.size % B := by
  unfold delta
  rw [dite_cond_eq_true (eq_true (show 0 < (signature x B).B from hB))]
  have := go_self x B hB 0 (Nat.zero_le _) #[]
  simpa [numCopies, numLits] using this

end VSync
