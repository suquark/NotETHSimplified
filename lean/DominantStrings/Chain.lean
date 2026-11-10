import DominantStrings.Potential

/-!
# The chain of steps

`Ktow L h` is the number of words at height `h`: `L` at height `0`, and the square at each height above. A code of a
chain holds the bits of the steps, the top step in the low bits.
-/

namespace DominantStrings

open Finset

/-- The number of words at height `h`. -/
def Ktow (L : ℕ) : ℕ → ℕ
  | 0 => L
  | h + 1 => Ktow L h * Ktow L h

/-- The number of bits of a code of a chain from height `h`. -/
def chainBits (L : ℕ) : ℕ → ℕ
  | 0 => 0
  | h + 1 => Ktow L h ^ 4 + chainBits L h

/-- The power of two of a chain from height `h`. -/
def scaleTot (L scale : ℕ) : ℕ → ℕ
  | 0 => 0
  | h + 1 => scale * nRect (Ktow L h) + scaleTot L scale h

/-- The level after one step, for the low bits of the code. -/
def levOf (L scale h : ℕ) (w : ℕ → ℕ → ℕ) (c : ℕ) : Lev :=
  ⟨Ktow L h, w, c, dirOf (Ktow L h) w scale c, scale⟩

/-- The value at height `0`, for a code, from height `h`. -/
noncomputable def chainVal (L scale : ℕ) :
    (h : ℕ) → (w : ℕ → ℕ → ℕ) → (F : ℕ → (ℕ → ℕ) → ℤ) → (c : ℕ) → ℤ
  | 0, w, F, _ => val L w F
  | h + 1, w, F, c =>
    if validCode (Ktow L h) (c % 2 ^ Ktow L h ^ 4) then
      chainVal L scale h (levOf L scale h w (c % 2 ^ Ktow L h ^ 4)).newW
        ((levOf L scale h w (c % 2 ^ Ktow L h ^ 4)).stepF F) (c / 2 ^ Ktow L h ^ 4)
    else 0

/-- The number of words is positive at each height. -/
theorem Ktow_pos {L : ℕ} (hL : 0 < L) : ∀ h, 0 < Ktow L h
  | 0 => hL
  | h + 1 => Nat.mul_pos (Ktow_pos hL h) (Ktow_pos hL h)

/-- The value of a code of a chain, for its low and its high bits. -/
theorem chainVal_split (L scale h : ℕ) (w : ℕ → ℕ → ℕ) (F : ℕ → (ℕ → ℕ) → ℤ) {x : ℕ}
    (hx : x < 2 ^ Ktow L h ^ 4) (y : ℕ) :
    chainVal L scale (h + 1) w F (x + 2 ^ Ktow L h ^ 4 * y) =
      if validCode (Ktow L h) x then
        chainVal L scale h (levOf L scale h w x).newW ((levOf L scale h w x).stepF F) y
      else 0 := by
  have hmod : (x + 2 ^ Ktow L h ^ 4 * y) % 2 ^ Ktow L h ^ 4 = x := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  have hdiv : (x + 2 ^ Ktow L h ^ 4 * y) / 2 ^ Ktow L h ^ 4 = y := by
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hx, zero_add]
  rw [chainVal, hmod, hdiv]

/-- **The chain.** The value at height `h` is a sum over the codes of the value at height `0`. -/
theorem chain_val (L scale : ℕ) (hL : 0 < L) (h : ℕ) (w : ℕ → ℕ → ℕ) (hsym : ∀ x y, w x y = w y x)
    (htot : ∑ x ∈ range (Ktow L h), ∑ y ∈ range (Ktow L h), w x y ≤ scale) (F : ℕ → (ℕ → ℕ) → ℤ) :
    2 ^ scaleTot L scale h * val (Ktow L h) w F =
      ∑ c ∈ range (2 ^ chainBits L h), chainVal L scale h w F c := by
  induction h generalizing w F with
  | zero => simp [scaleTot, chainBits, Ktow, chainVal]
  | succ h ih =>
    have htot' : ∑ x ∈ range (Ktow L h * Ktow L h), ∑ y ∈ range (Ktow L h * Ktow L h), w x y ≤ scale := htot
    have hscale : ∀ x < Ktow L h * Ktow L h, ∀ y < Ktow L h * Ktow L h, w x y ≤ scale :=
      fun x hx y hy => (le_total hx hy).trans htot'
    have hstep := step_val (Ktow L h) w hsym scale hscale (dirOf (Ktow L h) w scale) F
    have hx : ∀ x ∈ range (2 ^ Ktow L h ^ 4),
        ∑ y ∈ range (2 ^ chainBits L h), chainVal L scale (h + 1) w F (x + 2 ^ Ktow L h ^ 4 * y) =
          2 ^ scaleTot L scale h *
            if validCode (Ktow L h) x then
              val (Ktow L h) (Lev.newW ⟨Ktow L h, w, x, dirOf (Ktow L h) w scale x, scale⟩)
                (Lev.stepF ⟨Ktow L h, w, x, dirOf (Ktow L h) w scale x, scale⟩ F)
            else 0 := by
      intro x hx
      simp only [chainVal_split L scale h w F (mem_range.mp hx)]
      by_cases hv : validCode (Ktow L h) x
      · simp only [if_pos hv]
        exact (ih (levOf L scale h w x).newW (newW_symm (levOf L scale h w x) hsym)
          ((newW_total_le (levOf L scale h w x) (Ktow_pos hL h) hsym).trans htot') _).symm
      · simp [if_neg hv]
    calc 2 ^ scaleTot L scale (h + 1) * val (Ktow L (h + 1)) w F
        = 2 ^ scaleTot L scale h * (2 ^ (scale * nRect (Ktow L h)) * val (Ktow L h * Ktow L h) w F) := by
          rw [scaleTot, pow_add]
          change _ * val (Ktow L h * Ktow L h) w F = _
          ring
      _ = ∑ x ∈ range (2 ^ Ktow L h ^ 4), ∑ y ∈ range (2 ^ chainBits L h),
            chainVal L scale (h + 1) w F (x + 2 ^ Ktow L h ^ 4 * y) := by
          rw [hstep, mul_sum]
          exact sum_congr rfl fun x hx' => (hx x hx').symm
      _ = ∑ c ∈ range (2 ^ chainBits L (h + 1)), chainVal L scale (h + 1) w F c := by
          rw [chainBits, sum_split, sum_comm]

end DominantStrings
