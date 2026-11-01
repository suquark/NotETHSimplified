import OAI.Algorithms.SubexponentialSAT.CounterWidth
import OAI.Algorithms.SubexponentialSAT.ModularArithmetic

/-!
# Words on Boolean stacks

`wordOf W x` is the little-endian word of exactly `W` bits. A list of length `W` with value `x` is equal
to `wordOf W x`, so the outputs of the library routines become canonical words without further work.
-/

namespace TransposeBase.Machine

open OAI.Algorithms.SubexponentialSAT
open BinaryArithmetic

/-- The `W`-bit little-endian word of `x` (the bits above `W` are dropped). -/
def wordOf : ℕ → ℕ → List Bool
  | 0, _ => []
  | W + 1, x => decide (x % 2 = 1) :: wordOf W (x / 2)

@[simp] theorem length_wordOf (W x : ℕ) : (wordOf W x).length = W := by
  induction W generalizing x with
  | zero => rfl
  | succ W ih => simp [wordOf, ih]

private theorem bitVal_decide (x : ℕ) : bitVal (decide (x % 2 = 1)) = x % 2 := by
  by_cases h : x % 2 = 1
  · simp [h, bitVal]
  · simp [h, bitVal]
    omega

theorem toNat_wordOf {W x : ℕ} (h : x < 2 ^ W) : toNat (wordOf W x) = x := by
  induction W generalizing x with
  | zero =>
    simp only [pow_zero] at h
    simp only [wordOf, toNat]
    omega
  | succ W ih =>
    have h2 : x / 2 < 2 ^ W := by
      rw [pow_succ] at h
      omega
    simp only [wordOf, toNat, bitVal_decide, ih h2]
    omega

/-- A list of length `W` and value `x` is the word of `x`. -/
theorem eq_wordOf {xs : List Bool} {W x : ℕ} (hl : xs.length = W) (hv : toNat xs = x) :
    xs = wordOf W x := by
  induction xs generalizing W x with
  | nil =>
    subst hl
    rfl
  | cons b xs ih =>
    subst hl
    simp only [toNat] at hv
    have hb : b = decide (x % 2 = 1) := by
      cases b <;> simp [bitVal] at hv ⊢ <;> omega
    have hx : toNat xs = x / 2 := by
      cases b <;> simp [bitVal] at hv <;> omega
    simp only [List.length_cons, wordOf]
    rw [← hb]
    exact congrArg _ (ih rfl hx)

theorem wordOf_zero (W : ℕ) : wordOf W 0 = List.replicate W false := by
  induction W with
  | zero => rfl
  | succ W ih => simp [wordOf, ih, List.replicate_succ]

theorem toNat_lt (xs : List Bool) : toNat xs < 2 ^ xs.length :=
  ModularArithmetic.toNat_lt_pow_length xs

theorem toNat_replicate_false (a : ℕ) : toNat (List.replicate a false) = 0 := by
  induction a with
  | zero => rfl
  | succ a ih => simp [List.replicate_succ, ih, bitVal]

theorem toNat_replicate_append (a : ℕ) (xs : List Bool) :
    toNat (List.replicate a false ++ xs) = 2 ^ a * toNat xs := by
  induction a with
  | zero => simp
  | succ a ih =>
    simp only [List.replicate_succ, List.cons_append, toNat, ih, bitVal_false]
    rw [pow_succ]
    ring

/-- The word of a power of two: one bit at position `a`. -/
theorem wordOf_two_pow {W a : ℕ} (h : a < W) :
    List.replicate a false ++ true :: List.replicate (W - a - 1) false = wordOf W (2 ^ a) := by
  apply eq_wordOf
  · simp
    omega
  · simp [toNat_replicate_append, toNat, toNat_replicate_false, bitVal]

/-- `padTo` keeps the low bits: truncation and padding at the same time. -/
theorem toNat_padTo (shape xs : List Bool) :
    toNat (ModularArithmetic.padTo shape xs) = toNat xs % 2 ^ shape.length := by
  induction shape generalizing xs with
  | nil => simp [ModularArithmetic.padTo, Nat.mod_one]
  | cons a shape ih =>
    cases xs with
    | nil => simp [ModularArithmetic.padTo, ih, toNat, bitVal]
    | cons b bs =>
      simp only [ModularArithmetic.padTo, toNat, ih, List.length_cons, pow_succ]
      have hb : bitVal b < 2 := by cases b <;> simp [bitVal]
      have hpos : 0 < 2 ^ shape.length := by positivity
      generalize 2 ^ shape.length = p at *
      generalize toNat bs = y at *
      have hy := Nat.div_add_mod y p
      have hr := Nat.mod_lt y hpos
      have : bitVal b + 2 * y = (bitVal b + 2 * (y % p)) + (p * 2) * (y / p) := by nlinarith
      have hlt : bitVal b + 2 * (y % p) < p * 2 := by omega
      rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

end TransposeBase.Machine
