/-!
# SHA-256 (FIPS 180-4)

Straightforward pure-Lean implementation. Correctness against the standard is
checked by test-vector specs in `VSync/Spec.lean` (kernel-evaluated with `decide`).
-/

namespace VSync.Sha256

def K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def H0 : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

@[inline] def rotr (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- Message padding: 0x80, zeros, 64-bit big-endian bit length; result is a multiple of 64 bytes. -/
def pad (msg : ByteArray) : ByteArray :=
  let z := (119 - msg.size % 64) % 64
  let m := (List.replicate z (0 : UInt8)).foldl ByteArray.push (msg.push 0x80)
  let bits := msg.size * 8
  (List.range 8).foldl (fun m i => m.push (UInt8.ofNat (bits >>> (8 * (7 - i))))) m

@[inline] def word (m : ByteArray) (i : Nat) : UInt32 :=
  (m[i]!).toUInt32 <<< 24 ||| (m[i+1]!).toUInt32 <<< 16 |||
  (m[i+2]!).toUInt32 <<< 8 ||| (m[i+3]!).toUInt32

def schedule (m : ByteArray) (off : Nat) : Array UInt32 :=
  let w := (List.range 16).foldl (fun w t => w.push (word m (off + 4 * t))) (Array.mkEmpty 64)
  (List.range 48).foldl (fun w t =>
    let t := t + 16
    let x := w[t - 15]!
    let y := w[t - 2]!
    let s0 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
    let s1 := rotr y 17 ^^^ rotr y 19 ^^^ (y >>> 10)
    w.push (w[t - 16]! + s0 + w[t - 7]! + s1)) w

/-- Working variables a..h (a structure of scalars, so the compiled code doesn't box them). -/
structure St where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32
  f : UInt32
  g : UInt32
  h : UInt32

@[inline] def round (w : Array UInt32) (st : St) (t : Nat) : St :=
  let S1 := rotr st.e 6 ^^^ rotr st.e 11 ^^^ rotr st.e 25
  let ch := (st.e &&& st.f) ^^^ ((~~~st.e) &&& st.g)
  let t1 := st.h + S1 + ch + K[t]! + w[t]!
  let S0 := rotr st.a 2 ^^^ rotr st.a 13 ^^^ rotr st.a 22
  let maj := (st.a &&& st.b) ^^^ (st.a &&& st.c) ^^^ (st.b &&& st.c)
  ⟨t1 + S0 + maj, st.a, st.b, st.c, st.d + t1, st.e, st.f, st.g⟩

/-- Rounds `t, t+1, …, 63`. -/
def rounds (w : Array UInt32) (st : St) (t : Nat) : St :=
  if t < 64 then rounds w (round w st t) (t + 1) else st
termination_by 64 - t

def compress (hs w : Array UInt32) : Array UInt32 :=
  let r := rounds w ⟨hs[0]!, hs[1]!, hs[2]!, hs[3]!, hs[4]!, hs[5]!, hs[6]!, hs[7]!⟩ 0
  #[hs[0]! + r.a, hs[1]! + r.b, hs[2]! + r.c, hs[3]! + r.d,
    hs[4]! + r.e, hs[5]! + r.f, hs[6]! + r.g, hs[7]! + r.h]

def hash (msg : ByteArray) : ByteArray :=
  let m := pad msg
  let hs := (List.range (m.size / 64)).foldl (fun hs i => compress hs (schedule m (64 * i))) H0
  hs.foldl (fun out (x : UInt32) =>
    ((out.push (x >>> 24).toUInt8).push (x >>> 16).toUInt8 |>.push (x >>> 8).toUInt8).push x.toUInt8)
    ByteArray.empty

end VSync.Sha256

namespace VSync
def sha256 (msg : ByteArray) : ByteArray := Sha256.hash msg
end VSync
