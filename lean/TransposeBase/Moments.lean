import TransposeBase.Limits

/-!
# The cost for digit partitions is about `N / √Q`

The cost for digit partitions is about `N / √Q`.

Let `σ` be a balanced `±1` function on the alphabet and `s(u) = ∑ t, σ (u t)`. For the set
`W = {(u, w) : s(u) > s(w)}`, the difference `p_t - q_t` is the same for all `t`, and
`Q * (p_t - q_t) = (1 / 4) * ∑ u w, |s(u) - s(w)|`.

Relation to the note. The note computes this sum exactly and gets `D ≥ N / (4 √Q)`. Here the sum is
bounded below by moments, using `|x| ≥ (3 x² t² - x⁴) / (2 t³)`, which gives `D ≥ N / (5 √Q)`. The
proof needs only the second and fourth moments of a sum of independent terms.

* `moments`: the first, second and fourth moments.
* `sum_abs_ge`: the lower bound for the sum of absolute values.
* `digit_cost`: the conclusion `2 ^ D ≤ ∑ t, r t` for `D ≤ N / (5 √Q)`.
-/

set_option linter.unusedSectionVars false

namespace TransposeBase
namespace Moments

open scoped BigOperators
open Finset

section Sum

variable {B : Type*} [Fintype B] [DecidableEq B]

/-- The sum of independent terms. -/
def sumS {Q : ℕ} (x : B → ℝ) (z : Fin Q → B) : ℝ := ∑ t, x (z t)

theorem sum_cons {Q : ℕ} (F : (Fin (Q + 1) → B) → ℝ) :
    ∑ z, F z = ∑ b, ∑ z' : Fin Q → B, F (Fin.cons b z') := by
  rw [← Fintype.sum_prod_type']
  exact ((Fin.consEquiv (fun _ : Fin (Q + 1) => B)).sum_comp F).symm

theorem sumS_cons {Q : ℕ} (x : B → ℝ) (b : B) (z : Fin Q → B) :
    sumS x (Fin.cons b z : Fin (Q + 1) → B) = x b + sumS x z := by
  simp [sumS, Fin.sum_univ_succ]

/-- **The moments of a sum of independent terms with mean zero.** -/
theorem moments (x : B → ℝ) {m₂ m₄ : ℝ} (h1 : ∑ b, x b = 0)
    (h2 : ∑ b, x b ^ 2 = m₂ * Fintype.card B) (h4 : ∑ b, x b ^ 4 = m₄ * Fintype.card B) (Q : ℕ) :
    ∑ z : Fin Q → B, sumS x z = 0 ∧
    ∑ z : Fin Q → B, sumS x z ^ 2 = (Fintype.card B : ℝ) ^ Q * (Q * m₂) ∧
    ∑ z : Fin Q → B, sumS x z ^ 4 =
      (Fintype.card B : ℝ) ^ Q * (Q * m₄ + 3 * Q * (Q - 1) * m₂ ^ 2) := by
  induction Q with
  | zero => simp [sumS]
  | succ Q ih =>
      obtain ⟨i1, i2, i4⟩ := ih
      set C : ℝ := ((Fintype.card B : ℕ) : ℝ) with hC
      have hA : ∀ (a : B → ℝ) (g : (Fin Q → B) → ℝ),
          ∑ b, ∑ z, a b * g z = (∑ b, a b) * ∑ z, g z := by
        intro a g
        rw [sum_mul_sum]
      have hone : ∑ _z : Fin Q → B, (1 : ℝ) = C ^ Q := by
        simp [hC]
      have hb1 : ∑ _b : B, (1 : ℝ) = C := by
        simp [hC]
      have hx2 : ∑ b, 2 * x b = 0 := by rw [← mul_sum, h1, mul_zero]
      have hx4 : ∑ b, 4 * x b = 0 := by rw [← mul_sum, h1, mul_zero]
      have hx6 : ∑ b, 6 * x b ^ 2 = 6 * (m₂ * C) := by rw [← mul_sum, h2]
      refine ⟨?_, ?_, ?_⟩
      · rw [sum_cons]
        simp_rw [sumS_cons]
        have hexp : ∀ b (z : Fin Q → B), x b + sumS x z = x b * 1 + 1 * sumS x z := fun b z => by ring
        simp_rw [hexp, sum_add_distrib, hA, h1, i1]
        ring
      · rw [sum_cons]
        simp_rw [sumS_cons]
        have hexp : ∀ b (z : Fin Q → B), (x b + sumS x z) ^ 2 =
            x b ^ 2 * 1 + (2 * x b) * sumS x z + 1 * sumS x z ^ 2 := fun b z => by ring
        simp_rw [hexp, sum_add_distrib, hA, h2, hone, hx2, hb1, i2]
        push_cast
        ring
      · rw [sum_cons]
        simp_rw [sumS_cons]
        have hexp : ∀ b (z : Fin Q → B), (x b + sumS x z) ^ 4 =
            x b ^ 4 * 1 + (4 * x b ^ 3) * sumS x z + (6 * x b ^ 2) * sumS x z ^ 2 +
              (4 * x b) * sumS x z ^ 3 + 1 * sumS x z ^ 4 := fun b z => by ring
        simp_rw [hexp, sum_add_distrib, hA, h4, hone, i1, hx6, i2, hx4, hb1, i4]
        push_cast
        ring

/-- The inequality behind the lower bound. -/
theorem abs_ge_of_moments (x : ℝ) {t : ℝ} (ht : 0 < t) :
    (3 * x ^ 2 * t ^ 2 - x ^ 4) / (2 * t ^ 3) ≤ |x| := by
  rw [div_le_iff₀ (by positivity)]
  have hsq : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have h4 : x ^ 4 = |x| ^ 4 := by rw [show x ^ 4 = (x ^ 2) ^ 2 by ring, hsq]; ring
  rw [h4, hsq]
  have ha := abs_nonneg x
  have : 0 ≤ |x| * ((|x| - t) ^ 2 * (|x| + 2 * t)) := by positivity
  nlinarith

/-- **The lower bound for the sum of absolute values**, when `m₂ = 2` and `m₄ = 8`. -/
theorem sum_abs_ge (x : B → ℝ) (h1 : ∑ b, x b = 0)
    (h2 : ∑ b, x b ^ 2 = 2 * Fintype.card B) (h4 : ∑ b, x b ^ 4 = 8 * Fintype.card B)
    {Q : ℕ} (hQ : 0 < Q) :
    (Fintype.card B : ℝ) ^ Q * (2 * Real.sqrt Q / Real.sqrt 6) ≤ ∑ z : Fin Q → B, |sumS x z| := by
  obtain ⟨-, i2, i4⟩ := moments x h1 h2 h4 Q
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  set t : ℝ := Real.sqrt (6 * Q) with ht
  have ht0 : 0 < t := Real.sqrt_pos.mpr (by positivity)
  have ht2 : t ^ 2 = 6 * Q := Real.sq_sqrt (by positivity)
  have hC : (0 : ℝ) ≤ (Fintype.card B : ℝ) ^ Q := by positivity
  have hsum : ∑ z : Fin Q → B, (3 * sumS x z ^ 2 * t ^ 2 - sumS x z ^ 4) / (2 * t ^ 3) ≤
      ∑ z : Fin Q → B, |sumS x z| := sum_le_sum fun z _ => abs_ge_of_moments _ ht0
  have hexp : ∑ z : Fin Q → B, (3 * sumS x z ^ 2 * t ^ 2 - sumS x z ^ 4) / (2 * t ^ 3) =
      ((Fintype.card B : ℝ) ^ Q) * (3 * (Q * 2) * t ^ 2 - (Q * 8 + 3 * Q * (Q - 1) * 2 ^ 2)) /
        (2 * t ^ 3) := by
    rw [← sum_div, sum_sub_distrib]
    have : ∑ z : Fin Q → B, 3 * sumS x z ^ 2 * t ^ 2 =
        3 * t ^ 2 * ∑ z : Fin Q → B, sumS x z ^ 2 := by
      rw [mul_sum]
      exact sum_congr rfl fun z _ => by ring
    rw [this, i2, i4]
    ring
  have hval : 2 * Real.sqrt Q / Real.sqrt 6 ≤
      (3 * (Q * 2) * t ^ 2 - (Q * 8 + 3 * Q * (Q - 1) * 2 ^ 2)) / (2 * t ^ 3) := by
    have hnum : 3 * ((Q : ℝ) * 2) * t ^ 2 - (Q * 8 + 3 * Q * (Q - 1) * 2 ^ 2) ≥ 24 * (Q : ℝ) ^ 2 := by
      rw [ht2]
      nlinarith
    have ht3 : t ^ 3 = 6 * Q * t := by rw [pow_succ, ht2]
    have htval : t = Real.sqrt 6 * Real.sqrt Q := Real.sqrt_mul (by norm_num) _
    have hs6 : 0 < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
    have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQr
    have hsQ2 : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQr.le
    rw [le_div_iff₀ (by positivity), ht3, htval]
    have : 2 * Real.sqrt Q / Real.sqrt 6 * (2 * (6 * ↑Q * (Real.sqrt 6 * Real.sqrt Q))) =
        24 * (Q : ℝ) ^ 2 := by
      field_simp
      nlinarith [hsQ2]
    rw [this, ← htval]
    exact hnum
  calc _ ≤ ((Fintype.card B : ℝ) ^ Q) * ((3 * (Q * 2) * t ^ 2 - (Q * 8 + 3 * Q * (Q - 1) * 2 ^ 2)) /
        (2 * t ^ 3)) := mul_le_mul_of_nonneg_left hval hC
    _ = _ := by rw [mul_div_assoc']
    _ = _ := hexp.symm
    _ ≤ _ := hsum

end Sum

/-! ## The digit partitions -/

section Digit

variable {Q : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

/-- The `±1` function of a merging of the alphabet. -/
def sgn (c : A → Bool) (a : A) : ℝ := if c a then 1 else -1

/-- The sum of the signs of a word. -/
def wordS (c : A → Bool) (u : Word Q A) : ℝ := ∑ t, sgn c (u t)

/-- The difference of signs on a pair of letters. -/
def pairX (c : A → Bool) (b : A × A) : ℝ := sgn c b.1 - sgn c b.2

theorem sgn_sq (c : A → Bool) (a : A) : sgn c a ^ 2 = 1 := by
  unfold sgn
  split <;> norm_num

theorem pairX_sum (c : A → Bool) : ∑ b, pairX c b = 0 := by
  rw [Fintype.sum_prod_type]
  simp only [pairX]
  simp_rw [sum_sub_distrib]
  simp only [sum_const, card_univ, nsmul_eq_mul]
  rw [← mul_sum]
  ring

theorem pairX_sq_sum (c : A → Bool) (hbal : ∑ a, sgn c a = 0) :
    ∑ b, pairX c b ^ 2 = 2 * Fintype.card (A × A) := by
  rw [Fintype.sum_prod_type, Fintype.card_prod]
  have hexp : ∀ a a' : A, pairX c (a, a') ^ 2 = 2 - 2 * (sgn c a * sgn c a') := by
    intro a a'
    simp only [pairX]
    have h1 := sgn_sq c a
    have h2 := sgn_sq c a'
    nlinarith
  have hinner : ∀ a : A, ∑ a' : A, pairX c (a, a') ^ 2 = 2 * (Fintype.card A : ℝ) := by
    intro a
    simp_rw [hexp]
    rw [sum_sub_distrib]
    have h0 : ∑ a' : A, 2 * (sgn c a * sgn c a') = 0 := by
      rw [← mul_sum, ← mul_sum, hbal]
      ring
    rw [h0]
    simp
    ring
  simp_rw [hinner]
  simp
  ring

theorem pairX_four_sum (c : A → Bool) (hbal : ∑ a, sgn c a = 0) :
    ∑ b, pairX c b ^ 4 = 8 * Fintype.card (A × A) := by
  have h4 : ∀ b, pairX c b ^ 4 = 4 * pairX c b ^ 2 := by
    intro b
    simp only [pairX, sgn]
    split <;> split <;> norm_num
  simp_rw [h4]
  rw [← mul_sum, pairX_sq_sum c hbal]
  ring

/-- Pairs of words as words of pairs. -/
def pairEquiv : Cell Q A ≃ (Fin Q → A × A) :=
  (Equiv.arrowProdEquivProdArrow _ _ _).symm

theorem sumS_pairEquiv (c : A → Bool) (ω : Cell Q A) :
    sumS (pairX c) (pairEquiv ω) = wordS c ω.1 - wordS c ω.2 := by
  simp [sumS, pairEquiv, pairX, wordS, sum_sub_distrib]

/-- `∑ u w, |s(u) - s(w)|` is at least `N * 2 √Q / √6`. -/
theorem sum_abs_cells (c : A → Bool) (hbal : ∑ a, sgn c a = 0) (hQ : 0 < Q) :
    (Fintype.card (Cell Q A) : ℝ) * (2 * Real.sqrt Q / Real.sqrt 6) ≤
      ∑ ω : Cell Q A, |wordS c ω.1 - wordS c ω.2| := by
  have h := sum_abs_ge (pairX c) (pairX_sum c) (pairX_sq_sum c hbal) (pairX_four_sum c hbal) hQ
  have hcard : (Fintype.card (Cell Q A) : ℝ) = (Fintype.card (A × A) : ℝ) ^ Q := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    push_cast
    ring
  rw [hcard]
  refine h.trans (le_of_eq ?_)
  rw [← (pairEquiv (Q := Q) (A := A)).sum_comp]
  simp_rw [sumS_pairEquiv]

open Classical in
/-- The set `W` of cells with `s(u) > s(w)`. -/
noncomputable def setW (c : A → Bool) : Finset (Cell Q A) :=
  univ.filter fun ω => wordS c ω.2 < wordS c ω.1

/-- `p_t - q_t`, written as the number of wires in `W` whose row digit is `true`, minus those whose
column digit is `true`. -/
noncomputable def diffT (c : A → Bool) (t : Fin Q) : ℝ :=
  ∑ ω ∈ setW (Q := Q) c, ((if c (ω.1 t) then (1 : ℝ) else 0) - if c (ω.2 t) then 1 else 0)

/-- The sum over `W` is half of the sum of absolute values. -/
theorem sum_setW (c : A → Bool) :
    ∑ ω ∈ setW (Q := Q) c, (wordS c ω.1 - wordS c ω.2) =
      (1 / 2) * ∑ ω : Cell Q A, |wordS c ω.1 - wordS c ω.2| := by
  classical
  have hswap : ∑ ω ∈ setW (Q := Q) c, (wordS c ω.1 - wordS c ω.2) =
      ∑ ω ∈ (univ.filter fun ω : Cell Q A => wordS c ω.1 < wordS c ω.2),
        |wordS c ω.1 - wordS c ω.2| := by
    refine sum_nbij' (fun ω => (ω.2, ω.1)) (fun ω => (ω.2, ω.1)) ?_ ?_ ?_ ?_ ?_
    · intro ω hω
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hω).2⟩
    · intro ω hω
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hω).2⟩
    · intro ω _; rfl
    · intro ω _; rfl
    · intro ω hω
      have h := (mem_filter.mp hω).2
      simp only
      rw [abs_sub_comm, abs_of_pos (by linarith)]
  have hself : ∑ ω ∈ setW (Q := Q) c, (wordS c ω.1 - wordS c ω.2) =
      ∑ ω ∈ setW (Q := Q) c, |wordS c ω.1 - wordS c ω.2| := by
    refine sum_congr rfl fun ω hω => ?_
    have h := (mem_filter.mp hω).2
    rw [abs_of_pos (by linarith)]
  have hall : ∑ ω : Cell Q A, |wordS c ω.1 - wordS c ω.2| =
      ∑ ω ∈ setW (Q := Q) c, |wordS c ω.1 - wordS c ω.2| +
        ∑ ω ∈ (univ.filter fun ω : Cell Q A => wordS c ω.1 < wordS c ω.2),
          |wordS c ω.1 - wordS c ω.2| := by
    rw [← sum_filter_add_sum_filter_not univ fun ω : Cell Q A => wordS c ω.2 < wordS c ω.1]
    congr 1
    refine (sum_subset (fun ω hω => ?_) (fun ω hω hn => ?_)).symm
    · have h := (mem_filter.mp hω).2
      exact mem_filter.mpr ⟨mem_univ _, not_lt.mpr h.le⟩
    · have h1 := (mem_filter.mp hω).2
      have h2 : ¬ wordS c ω.1 < wordS c ω.2 := fun h => hn (mem_filter.mpr ⟨mem_univ _, h⟩)
      have : wordS c ω.1 = wordS c ω.2 := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
      rw [this, sub_self, abs_zero]
  rw [hall, ← hself, ← hswap]
  ring

/-- The differences add up to half of the sum over `W`. -/
theorem sum_diffT (c : A → Bool) :
    ∑ t, diffT (Q := Q) c t = (1 / 2) * ∑ ω ∈ setW (Q := Q) c, (wordS c ω.1 - wordS c ω.2) := by
  unfold diffT
  rw [Finset.sum_comm, mul_sum]
  refine sum_congr rfl fun ω _ => ?_
  rw [sum_sub_distrib]
  have hind : ∀ u : Word Q A, ∑ t, (if c (u t) then (1 : ℝ) else 0) = (wordS c u + Q) / 2 := by
    intro u
    have : ∀ t, (if c (u t) then (1 : ℝ) else 0) = (sgn c (u t) + 1) / 2 := by
      intro t
      unfold sgn
      split <;> norm_num
    simp_rw [this]
    rw [← sum_div, sum_add_distrib]
    simp [wordS]
  rw [hind, hind]
  ring

/-- Permuting the digits fixes `W`, so all differences are equal. -/
theorem diffT_eq (c : A → Bool) (s t : Fin Q) : diffT (Q := Q) c s = diffT (Q := Q) c t := by
  classical
  let π : Equiv.Perm (Fin Q) := Equiv.swap s t
  have hw : ∀ u : Word Q A, wordS c (u ∘ π) = wordS c u := by
    intro u
    simp only [wordS, Function.comp]
    exact Equiv.sum_comp π fun i => sgn c (u i)
  unfold diffT
  refine sum_nbij' (fun ω => (ω.1 ∘ π, ω.2 ∘ π)) (fun ω => (ω.1 ∘ π, ω.2 ∘ π)) ?_ ?_ ?_ ?_ ?_
  · intro ω hω
    have h := (mem_filter.mp hω).2
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    simp only [hw]
    exact h
  · intro ω hω
    have h := (mem_filter.mp hω).2
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    simp only [hw]
    exact h
  · intro ω _
    ext i <;> simp [π, Function.comp]
  · intro ω _
    ext i <;> simp [π, Function.comp]
  · intro ω _
    simp [π, Function.comp]

/-- `p_t - q_t` is at least `N / (5 √Q)`. -/
theorem diffT_ge (c : A → Bool) (hbal : ∑ a, sgn c a = 0) (hQ : 0 < Q) (t : Fin Q) :
    (Fintype.card (Cell Q A) : ℝ) / (5 * Real.sqrt Q) ≤ diffT (Q := Q) c t := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hsum : (Q : ℝ) * diffT (Q := Q) c t =
      (1 / 4) * ∑ ω : Cell Q A, |wordS c ω.1 - wordS c ω.2| := by
    have h1 := sum_diffT (Q := Q) c
    simp_rw [diffT_eq c _ t] at h1
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    rw [h1, sum_setW]
    ring
  have hlow := sum_abs_cells (Q := Q) c hbal hQ
  set N : ℝ := (Fintype.card (Cell Q A) : ℝ) with hN
  have hN0 : 0 ≤ N := by positivity
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQr
  have hsQ2 : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQr.le
  have hs6 : 0 < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have hs6le : Real.sqrt 6 ≤ 2.5 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hkey : (Q : ℝ) * (N / (5 * Real.sqrt Q)) ≤ (Q : ℝ) * diffT (Q := Q) c t := by
    rw [hsum]
    have h1 : (Q : ℝ) * (N / (5 * Real.sqrt Q)) = N * Real.sqrt Q / 5 := by
      field_simp
      nlinarith [hsQ2]
    have h2 : N * Real.sqrt Q / 5 ≤ 1 / 4 * (N * (2 * Real.sqrt Q / Real.sqrt 6)) := by
      have h3 : (1 : ℝ) / 5 ≤ 1 / (2 * Real.sqrt 6) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        linarith
      have h4 : 0 ≤ N * Real.sqrt Q := by positivity
      calc N * Real.sqrt Q / 5 = (N * Real.sqrt Q) * (1 / 5) := by ring
        _ ≤ (N * Real.sqrt Q) * (1 / (2 * Real.sqrt 6)) := mul_le_mul_of_nonneg_left h3 h4
        _ = _ := by field_simp; ring
    rw [h1]
    exact h2.trans (by linarith)
  exact le_of_mul_le_mul_left hkey hQr

/-- **The proposition "The cost is about `N / √Q`".** Let `c` merge the alphabet into two parts of
equal size, and let `k` be a field. If `∑ t, T t` is the indicator of `Y = Xᵀ` on bit matrices, with `T t` a
linear combination of `r t` products over the blocks of `P_t`, then `2 ^ D ≤ ∑ t, r t` for each natural `D ≤ N / (5 √Q)`. This holds for every
decomposition, however it was found. -/
theorem digit_cost {k : Type*} [Field k] (c : A → Bool) (hbal : ∑ a, sgn c a = 0) (hQ : 0 < Q)
    (r : Fin Q → ℕ) (T : Fin Q → (Cell Q A → k) → (Cell Q A → k) → k)
    (hT : ∀ t, IsBlockSum t (r t) (T t))
    (hsum : IsTransposeIndicator fun X Y : Cell Q A → k => ∑ t, T t X Y)
    {D : ℕ} (hD : (D : ℝ) ≤ (Fintype.card (Cell Q A) : ℝ) / (5 * Real.sqrt Q)) :
    2 ^ D ≤ ∑ t, r t := by
  classical
  refine Limits.digit_lower_bound (fun _ => c) (setW (Q := Q) c) r T hT hsum ?_
  intro t
  have hdiff := hD.trans (diffT_ge c hbal hQ t)
  set W := setW (Q := Q) c with hW
  have hu : (W.filter fun ω => c (ω.1 t) = false).card + (W.filter fun ω => c (ω.1 t) = true).card =
      W.card := by
    rw [add_comm]
    have := card_filter_add_card_filter_not (s := W) (fun ω : Cell Q A => c (ω.1 t) = true)
    simpa using this
  have hexp : diffT (Q := Q) c t = ((W.filter fun ω => c (ω.1 t) = true).card : ℝ) -
      ((W.filter fun ω => c (ω.2 t) = true).card : ℝ) := by
    unfold diffT
    rw [sum_sub_distrib, sum_boole, sum_boole]
  rw [hexp] at hdiff
  have hreal : (((W.filter fun ω => c (ω.2 t) = true).card + D : ℕ) : ℝ) ≤
      ((W.filter fun ω => c (ω.1 t) = true).card : ℝ) := by
    push_cast
    linarith
  have hnat : (W.filter fun ω => c (ω.2 t) = true).card + D ≤
      (W.filter fun ω => c (ω.1 t) = true).card := by exact_mod_cast hreal
  omega

end Digit

end Moments
end TransposeBase
