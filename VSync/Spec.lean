import VSync.Proofs
import VSync.Cli

/-!
# vsync specification

This file is the test suite. Every behaviour we care about is a theorem here,
checked by `lake build`; there are no runtime unit tests.

Rules (see CLAUDE.md):
* New behaviour ⇒ new spec in this file, in the matching section.
* A spec states a property for *all* inputs; a concrete example is only added
  when it is kernel-checkable (`rfl` / `decide`), never `native_decide`.
* Every spec is listed in the axiom audit at the bottom (`#guard_msgs` + `#print axioms`);
  the build fails if a spec gains `sorry` or any non-standard axiom.
-/

namespace VSync.Spec

open VSync

/-! ## 1. Round trip  (was: "2 MB file with insert / edit / append", "16-byte blocks") -/

/-- For every old file, new file and block size: patching old with the delta of new
reproduces new, provided no window of new collides with a different block of old. -/
theorem sync_roundtrip (old new : Array UInt8) (B : Nat) (h : NoCollision old new B) :
    patch old B (delta (signature old B) new) = new :=
  patch_delta old new B h

/-! ## 2. Missing / tiny destination  (was: "dst missing") -/

/-- If old has no full block (e.g. dst missing, so old is empty), the round trip holds
with no collision assumption at all. -/
theorem sync_roundtrip_no_blocks (old new : Array UInt8) (B : Nat) (h : old.size < B) :
    patch old B (delta (signature old B) new) = new :=
  patch_delta old new B fun i hi => by
    have : old.size / B = 0 := Nat.div_eq_of_lt h
    omega

/-- …and the delta is literals only: no block can be copied from a file without blocks. -/
theorem no_copies_without_blocks (old new : Array UInt8) (B : Nat) (h : old.size < B) :
    numCopies (delta (signature old B) new) = 0 := by
  unfold numCopies
  rw [List.countP_eq_zero]
  intro op hop
  have hv := delta_valid old new B op hop
  have : old.size / B = 0 := Nat.div_eq_of_lt h
  cases op with
  | copy i => simp [ValidOp] at hv; omega
  | lit _ => simp [Op.isCopy]

/-! ## 3. Empty source  (was: "empty src") -/

/-- Syncing an empty source produces no ops and an empty file, unconditionally. -/
theorem sync_empty_src (old : Array UInt8) (B : Nat) :
    delta (signature old B) #[] = #[] ∧ patch old B (delta (signature old B) #[]) = #[] := by
  have hd : delta (signature old B) #[] = #[] := by
    unfold delta
    split
    · rename_i hB
      rw [go]
      simp only [List.size_toArray, List.length_nil]
      rw [dif_neg (by omega)]
      rfl
    · rfl
  exact ⟨hd, by rw [hd]; rfl⟩

/-! ## 4. Unchanged file  (was: "second run, no changes") -/

/-- Syncing a file against itself reuses every full block and sends only the trailing
partial block as literals. (Documents the current limitation: the tail is never reused.) -/
theorem sync_self (x : Array UInt8) (B : Nat) (hB : 0 < B) :
    numCopies (delta (signature x B) x) = x.size / B ∧
    numLits (delta (signature x B) x) = x.size % B :=
  delta_self x B hB

/-! ## 5. Safety -/

/-- Every `copy i` in a delta refers to an existing full block of old,
so `patch` never reads outside old. -/
theorem copies_in_range (old new : Array UInt8) (B i : Nat)
    (h : Op.copy i ∈ (delta (signature old B) new).toList) : i < old.size / B :=
  delta_valid old new B _ h

/-! ## 6. Rolling checksum -/

/-- The O(1) rolling update equals recomputing the weak checksum of the shifted window. -/
theorem rolling_checksum (x y : UInt8) (r : List UInt8) :
    roll (r.length + 1) (weak (x :: r)) x y = weak (r ++ [y]) :=
  roll_correct x y r

/-! ## 7. Command line  (was: "no args prints usage", "block size 0 rejected") -/

theorem cli_block_pos (args : List String) (s d : String) (n : Nat)
    (h : parseArgs args = some (.sync s d (some n))) : 0 < n := by
  unfold parseArgs at h
  split at h <;> try simp at h
  rename_i b
  split at h
  · split at h
    · simp at h
    · simp at h; omega
  · simp at h

theorem cli_no_args : parseArgs [] = none := rfl

theorem cli_sync_default (s d : String) : parseArgs ["sync", s, d] = some (.sync s d none) := rfl

theorem cli_default_block_bounds (n : Nat) : 700 ≤ defaultBlock n ∧ defaultBlock n ≤ 131072 := by
  unfold defaultBlock; omega

/-! ## Axiom audit — add every new spec here -/

/-- info: 'VSync.Spec.sync_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sync_roundtrip

/-- info: 'VSync.Spec.sync_roundtrip_no_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sync_roundtrip_no_blocks

/-- info: 'VSync.Spec.no_copies_without_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms no_copies_without_blocks

/-- info: 'VSync.Spec.sync_empty_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sync_empty_src

/-- info: 'VSync.Spec.sync_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sync_self

/-- info: 'VSync.Spec.copies_in_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms copies_in_range

/-- info: 'VSync.Spec.cli_block_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cli_block_pos

/-- info: 'VSync.Spec.cli_no_args' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cli_no_args

/-- info: 'VSync.Spec.cli_sync_default' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cli_sync_default

/-- info: 'VSync.Spec.cli_default_block_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cli_default_block_bounds

/-- info: 'VSync.Spec.rolling_checksum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms rolling_checksum

end VSync.Spec
