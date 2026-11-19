import VSync.Delta

/-!
# Proofs for `VSync.Delta`

Everything is stated over `ByteArray.data.toList`. The main results:
* `delta_correct`  — round trip for any `confirm` that is sound (`MatchSound`).
* `matchSound_local` — byte-comparison confirmation is sound unconditionally.
* `matchSound_remote` — SHA-256 confirmation is sound under `NoCollision`.
* `delta_valid`, `delta_self`, `delta_empty` — safety, completeness, edge cases.
-/

namespace VSync

/-! ## ByteArray / list plumbing -/

theorem L_extract (a : ByteArray) (s e : Nat) :
    (a.extract s e).data.toList = (a.data.toList.drop s).take (e - s) := by
  simp [ByteArray.data_extract]

theorem L_append (a b : ByteArray) :
    (a ++ b).data.toList = a.data.toList ++ b.data.toList := by
  simp [ByteArray.data_append]

theorem drop_split (l : List α) (a b : Nat) :
    l.drop a = (l.drop a).take b ++ l.drop (a + b) := by
  have h := List.take_append_drop b (l.drop a)
  rw [List.drop_drop] at h
  rw [Nat.add_comm] at h ⊢
  exact h.symm

/-! ## bytesOf / patch -/

def bytesOf (old : ByteArray) (B : Nat) (ops : Array Op) : List UInt8 :=
  ops.toList.flatMap (Op.bytes old B)

theorem bytesOf_push (old : ByteArray) (B : Nat) (acc : Array Op) (op : Op) :
    bytesOf old B (acc.push op) = bytesOf old B acc ++ op.bytes old B := by
  simp [bytesOf]

theorem foldl_patchStep (old : ByteArray) (B : Nat) :
    ∀ (l : List Op) (acc : ByteArray),
      (l.foldl (patchStep old B) acc).data.toList = acc.data.toList ++ l.flatMap (Op.bytes old B)
  | [], acc => by simp
  | op :: l, acc => by
    cases op <;> simp [foldl_patchStep old B l, patchStep, Op.bytes, L_append]

theorem patch_toList (old : ByteArray) (B : Nat) (ops : Array Op) :
    (patch old B ops).data.toList = bytesOf old B ops := by
  unfold patch bytesOf
  rw [← Array.foldl_toList, foldl_patchStep]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity] <;> rfl

theorem flush_bytes (old new : ByteArray) (B s p : Nat) (acc : Array Op) :
    bytesOf old B (flush new s p acc)
      = bytesOf old B acc ++ (new.data.toList.drop s).take (p - s) := by
  unfold flush
  split
  · simp [bytesOf_push, Op.bytes]
  · have : p - s = 0 := by omega
    simp [this]

/-! ## signature -/

theorem strongs_spec {old : ByteArray} {B i : Nat} {d : ByteArray}
    (h : (signature old B).strongs[i]? = some d) :
    i < numBlocks old B ∧ d = strong (block old B i) := by
  simp [signature] at h
  obtain ⟨j, hj, rfl⟩ := h
  simp [Array.getElem?_range] at hj
  obtain ⟨hi, rfl⟩ := hj
  exact ⟨hi, rfl⟩

theorem numBlocks_pos {old : ByteArray} {B : Nat} (hB : 0 < B) :
    numBlocks old B = old.size / B := by
  simp [numBlocks]; omega

/-! ## Match confirmation -/

theorem pick_spec {sig : Sig} {confirm} {win d : ByteArray} :
    ∀ {l : List Nat} {i : Nat}, pick sig confirm win d l = some i →
      sig.strongs[i]? = some d ∧ confirm i win = true
  | [], _, hp => by simp [pick] at hp
  | j :: js, i, hp => by
    unfold pick at hp
    split at hp
    · rename_i hc; cases hp; exact hc
    · exact pick_spec hp

theorem findMatch_spec {sig : Sig} {confirm} {w : Weak} {win : ByteArray} {i : Nat}
    (h : findMatch sig confirm w win = some i) :
    sig.strongs[i]? = some (strong win) ∧ confirm i win = true := by
  unfold findMatch at h
  split at h
  · split at h
    · cases h
    · exact pick_spec h
  · cases h

/-- A confirmation function is sound if every window it accepts really equals the block. -/
def MatchSound (old new : ByteArray) (B : Nat) (confirm : Nat → ByteArray → Bool) : Prop :=
  ∀ i p, p + B ≤ new.size →
    (signature old B).strongs[i]? = some (strong (new.extract p (p + B))) →
    confirm i (new.extract p (p + B)) = true → new.extract p (p + B) = block old B i

/-- No `B`-byte window of `new` has the same SHA-256 as a *different* block of `old`. -/
def NoCollision (old new : ByteArray) (B : Nat) : Prop :=
  ∀ i, i < numBlocks old B → ∀ p, p + B ≤ new.size →
    strong (new.extract p (p + B)) = strong (block old B i) →
    new.extract p (p + B) = block old B i

theorem matchSound_local (old new : ByteArray) (B : Nat) :
    MatchSound old new B (confirmLocal old B) := by
  intro i p _ _ hc
  simpa [confirmLocal] using hc

theorem matchSound_remote (old new : ByteArray) (B : Nat) (h : NoCollision old new B) :
    MatchSound old new B confirmRemote := by
  intro i p hp hs _
  obtain ⟨hi, hd⟩ := strongs_spec hs
  exact h i hi p hp hd

/-! ## Round trip -/

theorem go_spec (old new : ByteArray) (B : Nat) (confirm : Nat → ByteArray → Bool)
    (hB : 0 < (signature old B).B) (hS : MatchSound old new B confirm) :
    ∀ p s w acc, s ≤ p → p ≤ new.size →
      bytesOf old B (go (signature old B) confirm hB new s p w acc)
        = bytesOf old B acc ++ new.data.toList.drop s := by
  have hBB : (signature old B).B = B := rfl
  intro p
  induction h : new.size - p using Nat.strongRecOn generalizing p with
  | _ k ih =>
    intro s w acc hsp hp
    rw [go]
    split
    · rename_i hpB
      have hB0 : 0 < B := hBB ▸ hB
      have hpB' : p + B ≤ new.size := hBB ▸ hpB
      cases hm : findMatch (signature old B) confirm w (new.extract p (p + (signature old B).B)) with
      | some i =>
        obtain ⟨hs, hc⟩ := findMatch_spec hm
        have heq := hS i p hpB' hs hc
        dsimp only
        rw [ih (new.size - (p + (signature old B).B)) (by omega) _ rfl _ _ _ (by omega) (by omega),
          bytesOf_push, flush_bytes]
        simp only [Op.bytes, hBB, ← heq, L_extract, List.append_assoc]
        congr 1
        rw [Nat.add_sub_cancel_left, ← drop_split]
        have hsplit := drop_split new.data.toList s (p - s)
        rw [Nat.add_sub_cancel' hsp] at hsplit
        exact hsplit.symm
      | none =>
        dsimp only
        rw [ih (new.size - (p + 1)) (by omega) _ rfl _ _ _ (by omega) (by omega)]
    · rw [flush_bytes, List.take_of_length_le (by simp)]

theorem delta_correct (old new : ByteArray) (B : Nat) (confirm : Nat → ByteArray → Bool)
    (hS : MatchSound old new B confirm) :
    patch old B (delta (signature old B) confirm new) = new := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [patch_toList]
  unfold delta
  split
  · rename_i hB
    rw [go_spec old new B confirm hB hS 0 0 _ _ (Nat.le_refl _) (Nat.zero_le _)]
    simp [bytesOf]
  · rw [flush_bytes, List.take_of_length_le (by simp)]
    simp [bytesOf]

/-! ## Safety: copies only reference real blocks -/

def ValidOp (old : ByteArray) (B : Nat) : Op → Prop
  | .copy i => i < numBlocks old B
  | .lits _ => True

def AllValid (old : ByteArray) (B : Nat) (ops : Array Op) : Prop :=
  ∀ op ∈ ops.toList, ValidOp old B op

theorem allValid_push {old B acc op} (h : AllValid old B acc) (hop : ValidOp old B op) :
    AllValid old B (acc.push op) := by
  intro o ho
  simp at ho
  rcases ho with ho | rfl
  · exact h o (by simpa using ho)
  · exact hop

theorem allValid_flush {old B new s p acc} (h : AllValid old B acc) :
    AllValid old B (flush new s p acc) := by
  unfold flush; split
  · exact allValid_push h trivial
  · exact h

theorem go_valid (old new : ByteArray) (B : Nat) (confirm) (hB : 0 < (signature old B).B) :
    ∀ p s w acc, AllValid old B acc →
      AllValid old B (go (signature old B) confirm hB new s p w acc) := by
  intro p
  induction h : new.size - p using Nat.strongRecOn generalizing p with
  | _ k ih =>
    intro s w acc hacc
    rw [go]
    split
    · cases hm : findMatch (signature old B) confirm w (new.extract p (p + (signature old B).B)) with
      | some i =>
        obtain ⟨hi, -⟩ := strongs_spec (findMatch_spec hm).1
        exact ih _ (by omega) _ rfl _ _ _ (allValid_push (allValid_flush hacc) hi)
      | none =>
        exact ih _ (by omega) _ rfl _ _ _ hacc
    · exact allValid_flush hacc

theorem delta_valid (old new : ByteArray) (B : Nat) (confirm) :
    AllValid old B (delta (signature old B) confirm new) := by
  unfold delta
  split
  · exact go_valid old new B confirm _ 0 0 _ _ (by simp [AllValid])
  · exact allValid_flush (by simp [AllValid])

/-! ## Edge case: empty input -/

theorem delta_empty (old : ByteArray) (B : Nat) (confirm) :
    delta (signature old B) confirm ByteArray.empty = #[] := by
  unfold delta
  split
  · rw [go, dif_neg (by simp; omega)]
    simp [flush]
  · simp [flush]

/-! ## Counting -/

theorem numCopies_push (acc : Array Op) (op : Op) :
    numCopies (acc.push op) = numCopies acc + (if op.isCopy then 1 else 0) := by
  simp [numCopies, List.countP_append]

theorem litBytes_push (acc : Array Op) (op : Op) :
    litBytes (acc.push op) = litBytes acc + op.litLen := by
  simp [litBytes]

theorem flush_counts (new : ByteArray) (s p : Nat) (acc : Array Op) (hp : p ≤ new.size) :
    numCopies (flush new s p acc) = numCopies acc ∧
    litBytes (flush new s p acc) = litBytes acc + (p - s) := by
  unfold flush
  split
  · simp only [numCopies_push, litBytes_push, Op.isCopy, Op.litLen]
    simp [ByteArray.size_extract]; omega
  · simp; omega

/-! ## Completeness on unchanged data (local mode) -/

theorem pick_complete {sig : Sig} {confirm} {win d : ByteArray} :
    ∀ {l : List Nat} {k : Nat}, k ∈ l → sig.strongs[k]? = some d → confirm k win = true →
      (pick sig confirm win d l).isSome
  | [], _, hk, _, _ => by simp at hk
  | j :: js, k, hk, hs, hc => by
    unfold pick
    split
    · rfl
    · rename_i hne
      rcases List.mem_cons.mp hk with rfl | hk
      · exact absurd ⟨hs, hc⟩ hne
      · exact pick_complete hk hs hc

theorem index_complete (old : ByteArray) (B : Nat) :
    ∀ (L : List Nat) (k : Nat), k ∈ L →
      ∃ l, (L.foldr (addBlock old B) {})[(⟨weakAt old (k * B) B, strong (block old B k)⟩ : Key)]?
        = some l ∧ k ∈ l
  | [], _, hk => by simp at hk
  | j :: L, k, hk => by
    simp only [List.foldr_cons, addBlock, Std.HashMap.getElem?_alter]
    by_cases hj : j = k
    · subst hj
      simp only [beq_self_eq_true, ite_true]
      cases (L.foldr (addBlock old B) {})[(⟨weakAt old (j * B) B, strong (block old B j)⟩ : Key)]?
        <;> simp [consIdx]
    · have hk' : k ∈ L := by
        rcases List.mem_cons.mp hk with h | h
        · exact absurd h.symm hj
        · exact h
      obtain ⟨l, hl, hkl⟩ := index_complete old B L k hk'
      split
      · rename_i heq
        have e : (⟨weakAt old (j * B) B, strong (block old B j)⟩ : Key)
            = ⟨weakAt old (k * B) B, strong (block old B k)⟩ := by simpa using heq
        rw [e, hl]
        exact ⟨j :: l, by simp [consIdx], by simp [hkl]⟩
      · exact ⟨l, hl, hkl⟩

theorem weaks_complete (old : ByteArray) (B : Nat) :
    ∀ (L : List Nat) (k : Nat), k ∈ L →
      (L.foldr (addWeak old B) {}).contains (weakAt old (k * B) B) = true
  | [], _, hk => by simp at hk
  | j :: L, k, hk => by
    simp only [List.foldr_cons, addWeak, Std.HashMap.contains_insert]
    by_cases hj : j = k
    · subst hj; simp
    · have hk' : k ∈ L := by
        rcases List.mem_cons.mp hk with h | h
        · exact absurd h.symm hj
        · exact h
      simp [weaks_complete old B L k hk']

theorem findMatch_self (x : ByteArray) (B k : Nat) (hB : 0 < B) (hk : k < x.size / B) :
    (findMatch (signature x B) (confirmLocal x B) (weakAt x (k * B) B) (block x B k)).isSome := by
  have hn : numBlocks x B = x.size / B := numBlocks_pos hB
  have hmem : k ∈ List.range (numBlocks x B) := by simp [hn, hk]
  obtain ⟨l, hl, hkl⟩ := index_complete x B _ k hmem
  have hw := weaks_complete x B _ k hmem
  unfold findMatch
  rw [if_pos (by simpa [signature] using hw)]
  have hidx : (signature x B).index[(⟨weakAt x (k * B) B, strong (block x B k)⟩ : Key)]? = some l := by
    simpa [signature] using hl
  rw [hidx]
  apply pick_complete hkl
  · simp [signature, hn, hk]
  · simp [confirmLocal]

theorem go_self (x : ByteArray) (B : Nat) (hB : 0 < (signature x B).B) :
    ∀ k, k ≤ x.size / B → ∀ acc,
      numCopies (go (signature x B) (confirmLocal x B) hB x (k * B) (k * B)
          (weakAt x (k * B) (signature x B).B) acc) = numCopies acc + (x.size / B - k) ∧
      litBytes (go (signature x B) (confirmLocal x B) hB x (k * B) (k * B)
          (weakAt x (k * B) (signature x B).B) acc) = litBytes acc + x.size % B := by
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
      have hfm : (findMatch (signature x B) (confirmLocal x B) (weakAt x (k * B) (signature x B).B)
          (x.extract (k * B) (k * B + (signature x B).B))).isSome :=
        findMatch_self x B k hB0 hlt
      cases hm : findMatch (signature x B) (confirmLocal x B) (weakAt x (k * B) (signature x B).B)
          (x.extract (k * B) (k * B + (signature x B).B)) with
      | none => rw [hm] at hfm; cases hfm
      | some i =>
        dsimp only
        have hgo : go (signature x B) (confirmLocal x B) hB x (k * B + (signature x B).B)
              (k * B + (signature x B).B)
              (weakAt x (k * B + (signature x B).B) (signature x B).B)
              ((flush x (k * B) (k * B) acc).push (.copy i))
            = go (signature x B) (confirmLocal x B) hB x ((k + 1) * B) ((k + 1) * B)
              (weakAt x ((k + 1) * B) (signature x B).B) (acc.push (.copy i)) := by
          rw [Nat.succ_mul, hBB]; simp [flush]
        rw [hgo]
        obtain ⟨h1, h2⟩ := ih (x.size / B - (k + 1)) (by omega) (k + 1) rfl hlt (acc.push (.copy i))
        rw [h1, h2, numCopies_push, litBytes_push]
        simp [Op.isCopy, Op.litLen]; omega
    · rename_i hpB
      have hk' : x.size / B = k := by
        have : ¬ (k + 1 ≤ x.size / B) := fun h => hpB (by
          have := (Nat.le_div_iff_mul_le hB0).mp h
          rw [Nat.succ_mul] at this; exact hBB ▸ this)
        omega
      have hkB : k * B ≤ x.size := by
        rw [← hk']; exact Nat.div_mul_le_self _ _
      obtain ⟨h1, h2⟩ := flush_counts x (k * B) x.size acc (Nat.le_refl _)
      rw [h1, h2]
      have hmod := Nat.mod_add_div x.size B
      rw [hk', Nat.mul_comm] at hmod
      constructor <;> omega

theorem delta_self (x : ByteArray) (B : Nat) (hB : 0 < B) :
    numCopies (delta (signature x B) (confirmLocal x B) x) = x.size / B ∧
    litBytes (delta (signature x B) (confirmLocal x B) x) = x.size % B := by
  unfold delta
  rw [dite_cond_eq_true (eq_true (show 0 < (signature x B).B from hB))]
  have := go_self x B hB 0 (Nat.zero_le _) #[]
  simpa [numCopies, litBytes] using this

end VSync
