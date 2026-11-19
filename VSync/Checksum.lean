/-!
# Weak rolling checksum (rsync / Adler-32 style)

For a window `w = [x₀, …, x_{n-1}]`:
* `a = Σ xᵢ                 (mod 2¹⁶)`
* `b = Σ (n - i) · xᵢ       (mod 2¹⁶)`

The point of the checksum is that sliding the window one byte to the right
(drop `x₀`, append `y`) can be done in O(1) via `roll`. `roll_correct`
proves this equals recomputing the checksum from scratch.
-/

namespace VSync

def M : Nat := 65536

def sumA : List UInt8 → Nat
  | [] => 0
  | x :: r => x.toNat + sumA r

def sumB : List UInt8 → Nat
  | [] => 0
  | x :: r => (r.length + 1) * x.toNat + sumB r

structure Weak where
  a : Nat
  b : Nat
  deriving DecidableEq, Hashable, Repr

/-- Specification: checksum of a window computed from scratch. -/
def weak (w : List UInt8) : Weak := ⟨sumA w % M, sumB w % M⟩

/-- O(1) update: window of length `n` loses `x` at the front, gains `y` at the back. -/
def roll (n : Nat) (s : Weak) (x y : UInt8) : Weak :=
  let a' := (s.a + M - x.toNat + y.toNat) % M
  let b' := (s.b + n * M - n * x.toNat + a') % M
  ⟨a', b'⟩

theorem sumA_append_single (r : List UInt8) (y : UInt8) :
    sumA (r ++ [y]) = sumA r + y.toNat := by
  induction r with
  | nil => simp [sumA]
  | cons x r ih => simp [sumA, ih]; omega

theorem sumB_append_single (r : List UInt8) (y : UInt8) :
    sumB (r ++ [y]) = sumB r + sumA r + y.toNat := by
  induction r with
  | nil => simp [sumB, sumA]
  | cons x r ih =>
    have hl : (r ++ [y]).length = r.length + 1 := by simp
    simp only [List.cons_append, sumB, sumA, ih, hl, Nat.add_mul, Nat.one_mul]
    omega

theorem roll_correct (x y : UInt8) (r : List UInt8) :
    roll (r.length + 1) (weak (x :: r)) x y = weak (r ++ [y]) := by
  have hx : x.toNat < 256 := x.toNat_lt
  have hP : (r.length + 1) * x.toNat ≤ (r.length + 1) * M :=
    Nat.mul_le_mul_left _ (by unfold M; omega)
  simp only [roll, weak, sumA, sumB, sumA_append_single, sumB_append_single, Weak.mk.injEq]
  generalize r.length + 1 = n at *
  generalize n * x.toNat = P at *
  unfold M at *
  constructor <;> omega

/-! ## Implementation over arrays -/

/-- Weak checksum of `data[p, p+n)`, computed directly. -/
def weakAt (data : Array UInt8) (p n : Nat) : Weak :=
  weak (data.extract p (p + n)).toList

end VSync
