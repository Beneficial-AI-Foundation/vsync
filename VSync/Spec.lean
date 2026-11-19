import VSync.Proofs
import VSync.Cli
import VSync.Proto

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
  split at h
  · simp at h
  · rename_i b
    split at h
    · split at h
      · simp at h
      · simp at h; omega
    · simp at h
  · obtain ⟨r, b, k, hc⟩ := parsePushOpts_push _ _ _ _ _ _ _ h
    cases hc
  · simp at h
  · simp at h

theorem cli_serve (root : String) : parseArgs ["serve", root] = some (.serve root) := rfl

theorem cli_push_default (s d : String) :
    parseArgs ["push", s, d] = some (.push s d "ssh" "vsync" false) := rfl

theorem cli_no_args : parseArgs [] = none := rfl

theorem cli_sync_default (s d : String) : parseArgs ["sync", s, d] = some (.sync s d none) := rfl

theorem cli_default_block_bounds (n : Nat) : 700 ≤ defaultBlock n ∧ defaultBlock n ≤ 131072 := by
  unfold defaultBlock; omega


/-! ## 9. Wire format (the class of bug behind rsync's CVE-2024-12084) -/

/-- Every protocol message decodes back to itself. The decoder is a total function with
bounds-checked reads; lengths from the peer are checked against the bytes actually received. -/
theorem wire_roundtrip (m : Msg) (h : msgC.valid m) : decodeMsg (encodeMsg m) = some m :=
  decodeMsg_encodeMsg m h

/-- The signature survives the trip to the sender, and the sender's lookup structure built
from it is exactly `signature old B`. -/
theorem wire_signature (old : ByteArray) (B : Nat) (h : sigC.valid (sigData old B)) :
    (Wire.decodeAll sigC (sigC.enc (sigData old B))).map Sig.build = some (signature old B) := by
  rw [Wire.decodeAll_enc sigC _ h]; rfl

/-! ## 10. Path safety (the class of bug behind rsync's CVE-2024-12087) -/

/-- An accepted path is a list of plain names: no empty component, no `.`, no `..`,
no `/` and no NUL inside a component. The receiver therefore cannot be steered outside
its root by the path itself (symlinks are refused separately, by the kernel, via O_NOFOLLOW). -/
theorem path_safe (p : ByteArray) (cs : List (List UInt8)) (h : safeRel p = some cs) :
    ∀ c ∈ cs, c ≠ [] ∧ c ≠ [46] ∧ c ≠ [46, 46] ∧ (0 : UInt8) ∉ c ∧ (47 : UInt8) ∉ c :=
  safeRel_sound h

theorem path_rejects_parent : safeRel "../etc/passwd".toUTF8 = none := by decide +kernel
theorem path_rejects_inner_parent : safeRel "a/../../b".toUTF8 = none := by decide +kernel
theorem path_rejects_absolute : safeRel "/etc/passwd".toUTF8 = none := by decide +kernel
theorem path_rejects_dot : safeRel "a/./b".toUTF8 = none := by decide +kernel
theorem path_rejects_empty : safeRel "a//b".toUTF8 = none := by decide +kernel
theorem path_accepts_plain : (safeRel "docs/a.txt".toUTF8).isSome = true := by decide +kernel

/-! ## 11. Streaming -/

/-- The sender works on one segment at a time; syncing segment by segment reproduces each
segment exactly, so the concatenation is the whole file. -/
theorem sync_segments (old : ByteArray) (B : Nat) (segs : List ByteArray) :
    segs.map (fun s => patch old B (delta (signature old B) (confirmLocal old B) s)) = segs := by
  conv => rhs; rw [← List.map_id segs]
  apply List.map_congr_left
  intro s _
  exact sync_local_exact old s B

/-- The streaming receiver reads old blocks on demand (`pread`) instead of holding the old
file in memory. If those reads return the real blocks, its output equals `patch`. -/
theorem receiver_streaming (old seg : ByteArray) (B : Nat) (get : Nat → ByteArray)
    (hget : ∀ i < numBlocks old B, get i = block old B i) (hNC : NoCollision old seg B) :
    patchWith get (delta (signature old B) confirmRemote seg).toList = seg := by
  rw [patchWith_eq old B get hget _ (delta_valid old seg B confirmRemote)]
  exact sync_remote_roundtrip old seg B hNC

/-- The receiver never writes a segment whose SHA-256 differs from the sender's. -/
theorem receiver_checks_segment (out sha x : ByteArray) (h : acceptSeg out sha = some x) :
    x = out ∧ sha256 x = sha :=
  acceptSeg_sound h

/-! ## 12. Quick check (skipping unchanged files) -/

/-- A file is skipped only when the sender allowed it and size, permissions and mtime
(nanoseconds) all match. -/
theorem skip_only_if_same (allowed : Bool) (a b c d e f : Nat)
    (h : quickSkip allowed a b c d e f = true) : allowed = true ∧ a = d ∧ b = e ∧ c = f :=
  quickSkip_sound h

/-- The sender never allows skipping with `--checksum`, nor for a file modified in the last
two seconds (whose mtime could still collide with an older version's). -/
theorem no_skip_when_racy (chk : Bool) (m now : Nat) (h : maySkip chk m now = true) :
    chk = false ∧ m + racyWindowNs ≤ now :=
  maySkip_not_racy h

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

/-- info: 'VSync.Spec.wire_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wire_roundtrip

/-- info: 'VSync.Spec.wire_signature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wire_signature

/-- info: 'VSync.Spec.path_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms path_safe

/-- info: 'VSync.Spec.path_rejects_parent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms path_rejects_parent

/-- info: 'VSync.Spec.path_rejects_inner_parent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms path_rejects_inner_parent

/-- info: 'VSync.Spec.path_rejects_absolute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms path_rejects_absolute

/-- info: 'VSync.Spec.path_rejects_dot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms path_rejects_dot

/-- info: 'VSync.Spec.path_rejects_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms path_rejects_empty

/-- info: 'VSync.Spec.path_accepts_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms path_accepts_plain

/-- info: 'VSync.Spec.sync_segments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sync_segments

/-- info: 'VSync.Spec.receiver_streaming' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms receiver_streaming

/-- info: 'VSync.Spec.receiver_checks_segment' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms receiver_checks_segment

/-- info: 'VSync.Spec.cli_serve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cli_serve

/-- info: 'VSync.Spec.cli_push_default' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cli_push_default

/-- info: 'VSync.Spec.skip_only_if_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms skip_only_if_same

/-- info: 'VSync.Spec.no_skip_when_racy' depends on axioms: [propext] -/
#guard_msgs in #print axioms no_skip_when_racy

end VSync.Spec
