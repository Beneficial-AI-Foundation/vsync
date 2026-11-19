import VSync.Proofs
import VSync.Cli

/-!
# vsync specification

This file is the test suite. Every behaviour we care about is a theorem here,
checked by `lake build`; there are no runtime unit tests.

Rules (see CLAUDE.md):
* New behaviour ⇒ new spec in this file, in the matching section.
* A spec states a property for *all* inputs; a concrete example is only added
  when it is kernel-checkable (`rfl` / `decide` / `decide +kernel`), never `native_decide`.
* Every spec is listed in the axiom audit at the bottom (`#guard_msgs` + `#print axioms`);
  the build fails if a spec gains `sorry` or any non-standard axiom.
-/

namespace VSync.Spec

open VSync

/-! ## 1. Round trip -/

/-- **Local sync is exact, with no assumptions.** For every old file, new file and block
size, patching old with the (byte-confirmed) delta of new reproduces new. -/
theorem sync_local_exact (old new : ByteArray) (B : Nat) :
    patch old B (delta (signature old B) (confirmLocal old B) new) = new :=
  delta_correct old new B _ (matchSound_local old new B)

/-- **Remote sync** (sender has only the signature, matches on SHA-256): exact unless a
window of new has the same SHA-256 as a *different* block of old. -/
theorem sync_remote_roundtrip (old new : ByteArray) (B : Nat) (h : NoCollision old new B) :
    patch old B (delta (signature old B) confirmRemote new) = new :=
  delta_correct old new B _ (matchSound_remote old new B h)

/-! ## 2. Missing / tiny destination  (was: "dst missing") -/

/-- If old has no full block (e.g. dst missing), the delta contains no copies. -/
theorem no_copies_without_blocks (old new : ByteArray) (B : Nat) (confirm)
    (h : old.size < B) : numCopies (delta (signature old B) confirm new) = 0 := by
  unfold numCopies
  rw [List.countP_eq_zero]
  intro op hop
  have hv := delta_valid old new B confirm op hop
  have : numBlocks old B = 0 := by
    unfold numBlocks; split
    · rfl
    · exact Nat.div_eq_of_lt h
  cases op with
  | copy i => simp [ValidOp] at hv; omega
  | lits _ => simp [Op.isCopy]

/-! ## 3. Empty source  (was: "empty src") -/

/-- Syncing an empty source produces no ops and an empty file. -/
theorem sync_empty_src (old : ByteArray) (B : Nat) (confirm) :
    delta (signature old B) confirm ByteArray.empty = #[] ∧
    patch old B (delta (signature old B) confirm ByteArray.empty) = ByteArray.empty := by
  have hd := delta_empty old B confirm
  exact ⟨hd, by rw [hd]; rfl⟩

/-! ## 4. Unchanged file  (was: "second run, no changes") -/

/-- Syncing a file against itself reuses every full block; only the trailing partial
block (`size % B` bytes) is sent as literals. -/
theorem sync_self (x : ByteArray) (B : Nat) (hB : 0 < B) :
    numCopies (delta (signature x B) (confirmLocal x B) x) = x.size / B ∧
    litBytes (delta (signature x B) (confirmLocal x B) x) = x.size % B :=
  delta_self x B hB

/-! ## 5. Safety -/

/-- Every `copy i` in a delta refers to an existing full block of old. -/
theorem copies_in_range (old new : ByteArray) (B i : Nat) (confirm)
    (h : Op.copy i ∈ (delta (signature old B) confirm new).toList) : i < numBlocks old B :=
  delta_valid old new B confirm _ h

/-! ## 6. Rolling checksum -/

/-- The O(1) rolling update equals recomputing the weak checksum of the shifted window. -/
theorem rolling_checksum (x y : UInt8) (r : List UInt8) :
    roll (r.length + 1) (weak (x :: r)) x y = weak (r ++ [y]) :=
  roll_correct x y r

/-- The O(n) checksum used at run time equals the specification `weak`. -/
theorem weak_fast_correct (l : List UInt8) : weakFast l = weak l := weakFast_eq l

/-! ## 7. SHA-256 test vectors (FIPS 180-4 / NIST), checked by the kernel -/

theorem sha256_empty : sha256 ByteArray.empty = ByteArray.mk #[
    0xe3,0xb0,0xc4,0x42,0x98,0xfc,0x1c,0x14,0x9a,0xfb,0xf4,0xc8,0x99,0x6f,0xb9,0x24,
    0x27,0xae,0x41,0xe4,0x64,0x9b,0x93,0x4c,0xa4,0x95,0x99,0x1b,0x78,0x52,0xb8,0x55] := by
  decide +kernel

theorem sha256_abc : sha256 "abc".toUTF8 = ByteArray.mk #[
    0xba,0x78,0x16,0xbf,0x8f,0x01,0xcf,0xea,0x41,0x41,0x40,0xde,0x5d,0xae,0x22,0x23,
    0xb0,0x03,0x61,0xa3,0x96,0x17,0x7a,0x9c,0xb4,0x10,0xff,0x61,0xf2,0x00,0x15,0xad] := by
  decide +kernel

/-- Two-block message (448 bits). -/
theorem sha256_two_blocks :
    sha256 "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8 = ByteArray.mk #[
    0x24,0x8d,0x6a,0x61,0xd2,0x06,0x38,0xb8,0xe5,0xc0,0x26,0x93,0x0c,0x3e,0x60,0x39,
    0xa3,0x3c,0xe4,0x59,0x64,0xff,0x21,0x67,0xf6,0xec,0xed,0xd4,0x19,0xdb,0x06,0xc1] := by
  decide +kernel

/-! ## 8. Command line  (was: "no args prints usage", "block size 0 rejected") -/

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

/-- info: 'VSync.Spec.sync_local_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sync_local_exact

/-- info: 'VSync.Spec.sync_remote_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sync_remote_roundtrip

/-- info: 'VSync.Spec.no_copies_without_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms no_copies_without_blocks

/-- info: 'VSync.Spec.sync_empty_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sync_empty_src

/-- info: 'VSync.Spec.sync_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sync_self

/-- info: 'VSync.Spec.copies_in_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms copies_in_range

/-- info: 'VSync.Spec.rolling_checksum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms rolling_checksum

/-- info: 'VSync.Spec.weak_fast_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms weak_fast_correct

/-- info: 'VSync.Spec.sha256_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sha256_empty

/-- info: 'VSync.Spec.sha256_abc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sha256_abc

/-- info: 'VSync.Spec.sha256_two_blocks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sha256_two_blocks

/-- info: 'VSync.Spec.cli_block_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cli_block_pos

/-- info: 'VSync.Spec.cli_no_args' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cli_no_args

/-- info: 'VSync.Spec.cli_sync_default' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cli_sync_default

/-- info: 'VSync.Spec.cli_default_block_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cli_default_block_bounds

end VSync.Spec
