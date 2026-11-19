import VSync.Delta

/-!
# Wire format

Codecs with a proven round trip. A `Codec α` has
* `enc`   : the specification encoder,
* `encTo` : the runtime encoder, appending to an accumulator (`encTo_eq` proves it equals `enc`),
* `dec`   : a decoder reading a buffer at a position; total, and every read is bounds-checked,
* `law`   : if the bytes from position `i` on start with `enc x`, the decoder returns `x`
            and the position just after it, whatever bytes follow.

Decoders never trust a length without checking it against the remaining input, so a
hostile peer cannot make them read past what it sent.
-/

namespace VSync.Wire

/-! ## ByteArray views -/

/-- The list view of a byte buffer. -/
abbrev L (a : ByteArray) : List UInt8 := a.data.toList

theorem ba_ext {a b : ByteArray} (h : L a = L b) : a = b :=
  ByteArray.ext (Array.toList_inj.mp h)

theorem size_eq_len (a : ByteArray) : a.size = (L a).length := by
  rw [L, Array.length_toList, ByteArray.size_data]

@[simp] theorem L_append (a b : ByteArray) : L (a ++ b) = L a ++ L b := by
  simp [L, ByteArray.data_append]

@[simp] theorem L_push (a : ByteArray) (b : UInt8) : L (a.push b) = L a ++ [b] := by
  simp [L, ByteArray.data_push]

@[simp] theorem L_mk (l : List UInt8) : L ⟨l.toArray⟩ = l := by simp [L]

@[simp] theorem L_empty : L ByteArray.empty = [] := by
  simp [L, ByteArray.empty, ByteArray.emptyWithCapacity] <;> rfl

theorem L_extract (a : ByteArray) (s e : Nat) :
    L (a.extract s e) = ((L a).drop s).take (e - s) := by
  simp [L, ByteArray.data_extract]

/-- Bounds-checked read. -/
def byteAt (a : ByteArray) (i : Nat) : Option UInt8 := if h : i < a.size then some a[i] else none

theorem byteAt_of_drop {a : ByteArray} {i : Nat} {b : UInt8} {R : List UInt8}
    (h : (L a).drop i = b :: R) : byteAt a i = some b := by
  have hlen : i < a.size := by
    have := congrArg List.length h
    rw [List.length_drop, List.length_cons] at this
    rw [size_eq_len]; omega
  have hget : (L a)[i]? = some b := by
    rw [← List.head?_drop, h]; rfl
  unfold byteAt
  rw [dif_pos hlen]
  simp only [L] at hget
  rw [Array.getElem?_toList] at hget
  simp only [ByteArray.getElem_eq_getElem_data]
  rw [Array.getElem?_eq_getElem (by simpa using hlen)] at hget
  exact congrArg some (Option.some.inj hget)

theorem drop_succ_of_drop {l : List UInt8} {i : Nat} {b : UInt8} {R : List UInt8}
    (h : l.drop i = b :: R) : l.drop (i + 1) = R := by
  rw [← List.drop_drop, h]; rfl

/-! ## Codecs -/

abbrev Dec (α : Type) := ByteArray → Nat → Option (α × Nat)

structure Codec (α : Type) where
  enc : α → ByteArray
  encTo : ByteArray → α → ByteArray
  dec : Dec α
  valid : α → Prop
  encTo_eq : ∀ acc x, encTo acc x = acc ++ enc x
  pos : ∀ x, 0 < (L (enc x)).length
  law : ∀ x, valid x → ∀ (a : ByteArray) (i : Nat) (R : List UInt8),
    (L a).drop i = L (enc x) ++ R → dec a i = some (x, i + (L (enc x)).length)

/-! ## Unsigned varint (LEB128), at most 10 bytes -/

def encVarL (n : Nat) : List UInt8 :=
  if n < 128 then [n.toUInt8] else (n % 128 + 128).toUInt8 :: encVarL (n / 128)
termination_by n
decreasing_by omega

theorem encVarL_ne (n : Nat) : encVarL n ≠ [] := by
  rw [encVarL]; split <;> simp

def decVar (a : ByteArray) (i : Nat) : Nat → Option (Nat × Nat)
  | 0 => none
  | f + 1 =>
    match byteAt a i with
    | none => none
    | some b =>
      if b.toNat < 128 then some (b.toNat, i + 1)
      else match decVar a (i + 1) f with
        | none => none
        | some (m, j) => some (b.toNat - 128 + 128 * m, j)

theorem decVar_law : ∀ (f n : Nat), n < 128 ^ (f + 1) → ∀ (a : ByteArray) (i : Nat) (R : List UInt8),
    (L a).drop i = encVarL n ++ R → decVar a i (f + 1) = some (n, i + (encVarL n).length)
  | f, n, h, a, i, R, hd => by
    by_cases hn : n < 128
    · have e : encVarL n = [n.toUInt8] := by rw [encVarL]; simp [hn]
      rw [e] at hd ⊢
      have hb : (n.toUInt8).toNat = n := by simp; omega
      simp only [decVar, byteAt_of_drop hd, hb, if_pos hn]
      rfl
    · have e : encVarL n = (n % 128 + 128).toUInt8 :: encVarL (n / 128) := by
        rw [encVarL]; simp [hn]
      rw [e] at hd ⊢
      have hb : ((n % 128 + 128).toUInt8).toNat = n % 128 + 128 := by simp; omega
      match f with
      | 0 => simp at h; omega
      | f' + 1 =>
        have ih := decVar_law f' (n / 128) (by rw [Nat.pow_succ] at h; omega) a (i + 1) R
          (drop_succ_of_drop hd)
        simp only [decVar, byteAt_of_drop hd, hb, if_neg (by omega : ¬ n % 128 + 128 < 128)]
        rw [show f' + 1 = f' + 1 from rfl] at ih
        simp only [decVar] at ih
        simp only [ih, List.length_cons, Option.some.injEq, Prod.mk.injEq]
        constructor <;> omega

def varint : Codec Nat where
  enc n := ⟨(encVarL n).toArray⟩
  encTo acc n := (encVarL n).foldl ByteArray.push acc
  dec a i := decVar a i 10
  valid n := n < 128 ^ 10
  encTo_eq acc n := by
    apply ba_ext
    simp only [L_append, L_mk]
    generalize encVarL n = l
    induction l generalizing acc with
    | nil => simp
    | cons x xs ih => simp [ih]
  pos n := by simp; exact List.length_pos_iff.mpr (encVarL_ne n)
  law n hv a i R hd := by
    simp only [L_mk] at hd ⊢
    exact decVar_law 9 n hv a i R hd

/-! ## Length-prefixed bytes -/

def bytes : Codec ByteArray where
  enc b := varint.enc b.size ++ b
  encTo acc b := varint.encTo acc b.size ++ b
  dec a i :=
    match varint.dec a i with
    | none => none
    | some (n, j) => if j + n ≤ a.size then some (a.extract j (j + n), j + n) else none
  valid b := b.size < 128 ^ 10
  encTo_eq acc b := by rw [varint.encTo_eq]; exact ba_ext (by simp)
  pos b := by simp only [L_append, List.length_append]; have := varint.pos b.size; omega
  law b hv a i R hd := by
    simp only [L_append, List.append_assoc] at hd
    have h1 := varint.law b.size hv a i (L b ++ R) hd
    simp only [h1]
    have hlenA := congrArg List.length hd
    rw [List.length_drop, List.length_append, List.length_append] at hlenA
    have hpos := varint.pos b.size
    generalize hj : i + (L (varint.enc b.size)).length = j at hd ⊢
    have hdj : (L a).drop j = L b ++ R := by
      rw [← hj, ← List.drop_drop, hd, List.drop_append_of_le_length (Nat.le_refl _)]
      simp
    have hlen : j + b.size ≤ a.size := by
      have := congrArg List.length hdj
      simp only [List.length_drop, List.length_append] at this
      rw [size_eq_len a, size_eq_len b]; omega
    rw [if_pos hlen]
    have hx : a.extract j (j + b.size) = b := by
      apply ba_ext
      rw [L_extract, hdj, Nat.add_sub_cancel_left, size_eq_len, List.take_left' rfl]
    rw [hx]
    simp only [L_append, List.length_append, ← hj, size_eq_len b]
    congr 2; omega

/-! ## Pairs -/

def pair (A : Codec α) (B : Codec β) : Codec (α × β) where
  enc p := A.enc p.1 ++ B.enc p.2
  encTo acc p := B.encTo (A.encTo acc p.1) p.2
  dec a i :=
    match A.dec a i with
    | none => none
    | some (x, j) =>
      match B.dec a j with
      | none => none
      | some (y, k) => some ((x, y), k)
  valid p := A.valid p.1 ∧ B.valid p.2
  encTo_eq acc p := by rw [B.encTo_eq, A.encTo_eq]; exact ba_ext (by simp)
  pos p := by simp only [L_append, List.length_append]; have := A.pos p.1; omega
  law p hv a i R hd := by
    simp only [L_append, List.append_assoc] at hd
    have h1 := A.law p.1 hv.1 a i _ hd
    have hdj : (L a).drop (i + (L (A.enc p.1)).length) = L (B.enc p.2) ++ R := by
      rw [← List.drop_drop, hd, List.drop_append_of_le_length (Nat.le_refl _)]
      simp
    have h2 := B.law p.2 hv.2 a _ R hdj
    simp only [h1, h2, L_append, List.length_append, Nat.add_assoc]

/-! ## Lists (count-prefixed; the count is checked against the remaining input) -/

def encItems (A : Codec α) : List α → ByteArray
  | [] => ByteArray.empty
  | x :: xs => A.enc x ++ encItems A xs

theorem encItems_len (A : Codec α) : ∀ l : List α, l.length ≤ (L (encItems A l)).length
  | [] => by simp [encItems]
  | x :: xs => by
    simp only [encItems, L_append, List.length_append, List.length_cons]
    have := A.pos x; have := encItems_len A xs; omega

/-- Tail-recursive: decodes `k` items, accumulating into `acc`. -/
def decItems (A : Codec α) (a : ByteArray) : Nat → Nat → Array α → Option (List α × Nat)
  | 0, j, acc => some (acc.toList, j)
  | k + 1, j, acc =>
    match A.dec a j with
    | none => none
    | some (x, j') => decItems A a k j' (acc.push x)

theorem decItems_law (A : Codec α) : ∀ (l : List α), (∀ x ∈ l, A.valid x) →
    ∀ (a : ByteArray) (j : Nat) (acc : Array α) (R : List UInt8),
      (L a).drop j = L (encItems A l) ++ R →
      decItems A a l.length j acc = some (acc.toList ++ l, j + (L (encItems A l)).length)
  | [], _, a, j, acc, R, _ => by simp [decItems, encItems]
  | x :: xs, hv, a, j, acc, R, hd => by
    simp only [encItems, L_append, List.append_assoc] at hd
    have h1 := A.law x (hv x (by simp)) a j _ hd
    have hdj : (L a).drop (j + (L (A.enc x)).length) = L (encItems A xs) ++ R := by
      rw [← List.drop_drop, hd, List.drop_append_of_le_length (Nat.le_refl _)]
      simp
    have ih := decItems_law A xs (fun y hy => hv y (by simp [hy])) a _ (acc.push x) R hdj
    simp only [List.length_cons, decItems, h1, ih, encItems, L_append, List.length_append]
    simp [Nat.add_assoc]

theorem foldl_encTo (A : Codec α) : ∀ (l : List α) (acc : ByteArray),
    l.foldl A.encTo acc = acc ++ encItems A l
  | [], acc => ba_ext (by simp [encItems])
  | x :: xs, acc => by
    simp only [List.foldl_cons, A.encTo_eq, foldl_encTo A xs]
    exact ba_ext (by simp [encItems])

def list (A : Codec α) : Codec (List α) where
  enc l := varint.enc l.length ++ encItems A l
  encTo acc l := l.foldl A.encTo (varint.encTo acc l.length)
  dec a i :=
    match varint.dec a i with
    | none => none
    | some (n, j) => if n ≤ a.size - j then decItems A a n j #[] else none
  valid l := l.length < 128 ^ 10 ∧ ∀ x ∈ l, A.valid x
  encTo_eq acc l := by
    rw [foldl_encTo, varint.encTo_eq]
    exact ba_ext (by simp)
  pos l := by simp only [L_append, List.length_append]; have := varint.pos l.length; omega
  law l hv a i R hd := by
    simp only [L_append, List.append_assoc] at hd
    have h1 := varint.law l.length hv.1 a i _ hd
    simp only [h1]
    generalize hj : i + (L (varint.enc l.length)).length = j at hd ⊢
    have hdj : (L a).drop j = L (encItems A l) ++ R := by
      rw [← hj, ← List.drop_drop, hd, List.drop_append_of_le_length (Nat.le_refl _)]
      simp
    have hcount : l.length ≤ a.size - j := by
      have := congrArg List.length hdj
      simp only [List.length_drop, List.length_append] at this
      have := encItems_len A l
      rw [size_eq_len]; omega
    rw [if_pos hcount, decItems_law A l hv.2 a j #[] R hdj]
    simp [← hj, Nat.add_assoc]

/-! ## Isomorphic types -/

def iso (A : Codec α) (f : α → β) (g : β → α) (fg : ∀ y, f (g y) = y) : Codec β where
  enc y := A.enc (g y)
  encTo acc y := A.encTo acc (g y)
  dec a i :=
    match A.dec a i with
    | none => none
    | some (x, j) => some (f x, j)
  valid y := A.valid (g y)
  encTo_eq acc y := A.encTo_eq acc (g y)
  pos y := A.pos (g y)
  law y hv a i R hd := by
    simp only [A.law (g y) hv a i R hd, fg]

/-! ## Whole messages -/

/-- Decode a complete message: the buffer must be exactly one encoded value. -/
def decodeAll (A : Codec α) (a : ByteArray) : Option α :=
  match A.dec a 0 with
  | some (x, j) => if j = a.size then some x else none
  | none => none

theorem decodeAll_enc (A : Codec α) (x : α) (hv : A.valid x) :
    decodeAll A (A.enc x) = some x := by
  unfold decodeAll
  rw [A.law x hv (A.enc x) 0 [] (by simp)]
  simp only [Nat.zero_add, size_eq_len (A.enc x)]
  simp

end VSync.Wire
