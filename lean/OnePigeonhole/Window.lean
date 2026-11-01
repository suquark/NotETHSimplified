import OnePigeonhole.Wires

/-!
# The window matrix and the row space

Lemma 1 of `papers/one-pigeonhole/proof.tex`, on the wires, and the row space of Section 3.

* `Bmat W κ R`: the matrix with `B i j = ∑_{|E| ≤ R} κ_{|E|} [τ_E (c i) = d j]`.
* `Bmat_sub_one_eq`: with `κ = kappa Q R`, the matrix `B - 1` is the sum over the keys and the exceptional sign vectors of `alpha k σ i * beta k σ j`.
* `rank_Bmat_sub_one_le`: `rank (B - 1) ≤ rankBound Q L h R`, where `rankBound Q L h R = #keys * #exc`.
* `eqv a b`: the test `[a = b]`, as the polynomial `a b + (1 - a) (1 - b)`. On bits it is the indicator.
* `Aval`, `Dval`, `spanVec`, `row_mem_span`, `exists_row_space`: all rows of `A - D` lie in a space of dimension at most `2 * rankBound Q L h R`, for all rationals `x`, `y`.
* `card_exc_mul_sq_le_two_pow`, `card_exc_le_div`, `rankBound_mul_sq_le`, `rankBound_le_div`, `hypotheses_of_numbers`: the numbers for `Q = m ^ 4`, `R = m ^ 3`.
-/

set_option linter.unusedSectionVars false

namespace OnePigeonhole

open Finset

variable {Q L h M : ℕ}

/-! ### The matrix `B` -/

/-- The window matrix on the wires. -/
def Bmat (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) : Matrix (Fin M) (Fin M) ℚ :=
  Matrix.of fun i j => ∑ E ∈ shortSets Q R, if tau E (W.c i) = W.d j then κ E.card else 0

/-- The number `ρ_σ = ∑_{|E| ≤ R} κ_{|E|} σ ^ E - σ ^ [Q]` of the proof of Lemma 1. It vanishes off the exceptional sign vectors. -/
noncomputable def excGap (Q R : ℕ) (σ : Finset (Fin Q)) : ℚ :=
  ∑ E ∈ shortSets Q R, kappa Q R E.card * chi σ E - chi σ univ

theorem excGap_eq_zero {R : ℕ} {σ : Finset (Fin Q)} (h : σ ∉ exc Q R) : excGap Q R σ = 0 := by
  rw [excGap, sum_kappa_chi_of_notMem_exc h, sub_self]

/-- The left factor of a term of `B - 1`. -/
def alpha (W : Wires Q L h M) (k : Key Q L h) (σ : Finset (Fin Q)) (i : Fin M) : ℚ :=
  if W.key i = k then chi σ (W.F i) else 0

/-- The right factor of a term of `B - 1`. -/
noncomputable def beta (W : Wires Q L h M) (R : ℕ) (k : Key Q L h) (σ : Finset (Fin Q)) (j : Fin M) : ℚ :=
  if W.key j = k then (2 ^ Q)⁻¹ * excGap Q R σ * chi σ (W.F j)ᶜ else 0

/-- The bound on the rank of `B - 1`: the keys times the exceptional sign vectors. -/
def rankBound (Q L h R : ℕ) : ℕ := (keys Q L h).card * (exc Q R).card

theorem two_pow_inv_mul_sum_chi (E A : Finset (Fin Q)) :
    ((2 : ℚ) ^ Q)⁻¹ * ∑ σ, chi σ E * chi σ A = if E = A then 1 else 0 := by
  rw [sum_chi_mul_chi]
  split_ifs
  · exact inv_mul_cancel₀ (by positivity)
  · simp

/-- `B - 1` on two wires of one cube. -/
theorem Bmat_sub_one_same_key (W : Wires Q L h M) (R : ℕ) {i j : Fin M} (hk : W.key i = W.key j) :
    Bmat W (kappa Q R) R i j - (if i = j then 1 else 0) =
      ((2 : ℚ) ^ Q)⁻¹ * ∑ σ ∈ exc Q R, excGap Q R σ * chi σ (W.F i) * chi σ (W.F j)ᶜ := by
  classical
  set A := symmDiff (W.F i) (W.F j)ᶜ with hA
  have hrel : ∀ E, tau E (W.c i) = W.d j ↔ E = A := by
    intro E
    rw [W.tau_c_eq_d_iff]
    simp [hk, hA]
  have h1 : Bmat W (kappa Q R) R i j =
      ((2 : ℚ) ^ Q)⁻¹ * ∑ σ, (∑ E ∈ shortSets Q R, kappa Q R E.card * chi σ E) * chi σ A := by
    have h2 : ∀ E ∈ shortSets Q R, (if tau E (W.c i) = W.d j then kappa Q R E.card else 0) =
        kappa Q R E.card * (((2 : ℚ) ^ Q)⁻¹ * ∑ σ, chi σ E * chi σ A) := by
      intro E _
      rw [two_pow_inv_mul_sum_chi]
      simp only [hrel]
      split_ifs <;> simp
    simp only [Bmat, Matrix.of_apply]
    rw [Finset.sum_congr rfl h2]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun E _ => ?_
    ring
  have h3 : (if i = j then (1 : ℚ) else 0) = ((2 : ℚ) ^ Q)⁻¹ * ∑ σ, chi σ univ * chi σ A := by
    rw [two_pow_inv_mul_sum_chi]
    have : i = j ↔ univ = A := by
      rw [← W.tau_univ_c_eq_d_iff, hrel]
    simp only [this]
  rw [h1, h3, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  have h4 : ∀ σ : Finset (Fin Q), (∑ E ∈ shortSets Q R, kappa Q R E.card * chi σ E) * chi σ A -
      chi σ univ * chi σ A = excGap Q R σ * chi σ (W.F i) * chi σ (W.F j)ᶜ := by
    intro σ
    rw [hA, chi_symmDiff, excGap]
    ring
  simp_rw [h4]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun σ _ hσ => ?_
  rw [excGap_eq_zero hσ]
  ring

/-- **Lemma 1, on the wires.** The decomposition of `B - 1`. -/
theorem Bmat_sub_one_eq (W : Wires Q L h M) (R : ℕ) (i j : Fin M) :
    Bmat W (kappa Q R) R i j - (if i = j then 1 else 0) =
      ∑ p ∈ keys Q L h ×ˢ exc Q R, alpha W p.1 p.2 i * beta W R p.1 p.2 j := by
  classical
  rw [Finset.sum_product]
  by_cases hk : W.key i = W.key j
  · rw [Bmat_sub_one_same_key W R hk]
    rw [Finset.sum_eq_single (a := W.key i)]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      simp only [alpha, beta, if_true, ← hk]
      ring
    · intro k _ hne
      refine Finset.sum_eq_zero fun σ _ => ?_
      simp [alpha, hne.symm]
    · intro hmem
      exact absurd (W.key_mem_keys i) hmem
  · have h0 : Bmat W (kappa Q R) R i j = 0 := by
      simp only [Bmat, Matrix.of_apply]
      refine Finset.sum_eq_zero fun E _ => ?_
      rw [if_neg]
      intro he
      exact hk ((W.tau_c_eq_d_iff E i j).mp he).1
    have hij : i ≠ j := fun he => hk (by rw [he])
    rw [h0, if_neg hij, sub_zero]
    symm
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun σ _ => ?_
    by_cases hi : W.key i = k
    · have hj : W.key j ≠ k := fun hj => hk (hi.trans hj.symm)
      simp [beta, hj]
    · simp [alpha, hi]

/-- `B - 1` as a matrix. -/
theorem Bmat_sub_one_apply (W : Wires Q L h M) (R : ℕ) (i j : Fin M) :
    (Bmat W (kappa Q R) R - 1) i j =
      ∑ p ∈ keys Q L h ×ˢ exc Q R, alpha W p.1 p.2 i * beta W R p.1 p.2 j := by
  rw [Matrix.sub_apply, Matrix.one_apply, Bmat_sub_one_eq]

/-- The index set of the decomposition. -/
abbrev BIndex (Q L h R : ℕ) := {p // p ∈ keys Q L h ×ˢ exc Q R}

theorem card_BIndex (Q L h R : ℕ) : Fintype.card (BIndex Q L h R) = rankBound Q L h R := by
  rw [Fintype.card_coe, Finset.card_product, rankBound]

/-- **The rank bound.** -/
theorem rank_Bmat_sub_one_le (W : Wires Q L h M) (R : ℕ) :
    (Bmat W (kappa Q R) R - 1).rank ≤ rankBound Q L h R := by
  classical
  let f : BIndex Q L h R → Fin M → ℚ := fun p => beta W R p.1.1 p.1.2
  have hrow : ∀ i, (Bmat W (kappa Q R) R - 1).row i ∈ Submodule.span ℚ (Set.range f) := by
    intro i
    have : (Bmat W (kappa Q R) R - 1).row i = ∑ p : BIndex Q L h R, alpha W p.1.1 p.1.2 i • f p := by
      funext j
      simp only [Matrix.row_apply, Bmat_sub_one_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, f]
      exact (Finset.sum_coe_sort (keys Q L h ×ˢ exc Q R)
        (fun p => alpha W p.1 p.2 i * beta W R p.1 p.2 j)).symm
    rw [this]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
  rw [Matrix.rank_eq_finrank_span_row]
  calc Module.finrank ℚ (Submodule.span ℚ (Set.range (Bmat W (kappa Q R) R - 1).row))
      ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range f)) := by
        refine Submodule.finrank_mono (Submodule.span_le.mpr ?_)
        rintro _ ⟨i, rfl⟩
        exact hrow i
    _ ≤ Fintype.card (BIndex Q L h R) := finrank_range_le_card f
    _ = rankBound Q L h R := card_BIndex Q L h R

/-! ### The test `[a = b]` -/

/-- The test `[a = b]`, written as a polynomial in `a` and `b`. On bits it is the indicator, by `eqv_of_bits`. -/
def eqv (a b : ℚ) : ℚ := a * b + (1 - a) * (1 - b)

@[simp] theorem eqv_one_left (b : ℚ) : eqv 1 b = b := by simp [eqv]

@[simp] theorem eqv_zero_left (b : ℚ) : eqv 0 b = 1 - b := by simp [eqv]

@[simp] theorem eqv_one_right (a : ℚ) : eqv a 1 = a := by simp [eqv]

@[simp] theorem eqv_zero_right (a : ℚ) : eqv a 0 = 1 - a := by simp [eqv]

/-- The test against a bit of the first argument: `[a = b] = [a = 1] [1 = b] + [a = 0] [0 = b]`, for all rationals. -/
theorem eqv_split (a b : ℚ) : eqv a b = eqv a 1 * eqv 1 b + eqv a 0 * eqv 0 b := by
  simp [eqv]

theorem eqv_of_bits {a b : ℚ} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    eqv a b = if a = b then 1 else 0 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp

/-! ### The matrices `A` and `D` -/

/-- The matrix `A` of Section 3: `A i j = B i j [x_i = y_j]`. -/
def Aval (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (x y : Fin M → ℚ) : Matrix (Fin M) (Fin M) ℚ :=
  Matrix.of fun i j => Bmat W κ R i j * eqv (x i) (y j)

/-- The matrix `D` of Section 3: `D i j = [τ_{[Q]} c_i = d_j] [x_i = y_j]`. -/
def Dval (W : Wires Q L h M) (x y : Fin M → ℚ) : Matrix (Fin M) (Fin M) ℚ :=
  Matrix.of fun i j => (if tau univ (W.c i) = W.d j then 1 else 0) * eqv (x i) (y j)

/-- `D` is diagonal, since `τ_{[Q]} c_i = d_i` and the cells `d_j` are different. -/
theorem Dval_eq_diagonal (W : Wires Q L h M) (x y : Fin M → ℚ) :
    Dval W x y = Matrix.diagonal fun j => eqv (x j) (y j) := by
  ext i j
  simp only [Dval, Matrix.of_apply, Matrix.diagonal_apply, W.tau_univ_c_eq_d_iff]
  split_ifs with hij
  · rw [hij, one_mul]
  · rw [zero_mul]

theorem det_Dval (W : Wires Q L h M) (x y : Fin M → ℚ) :
    (Dval W x y).det = ∏ j, eqv (x j) (y j) := by
  rw [Dval_eq_diagonal, Matrix.det_diagonal]

theorem Aval_sub_Dval_apply (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (x y : Fin M → ℚ) (i j : Fin M) :
    (Aval W κ R x y - Dval W x y) i j = (Bmat W κ R - 1) i j * eqv (x i) (y j) := by
  simp only [Matrix.sub_apply, Aval, Dval, Matrix.of_apply, Matrix.one_apply, W.tau_univ_c_eq_d_iff]
  ring

/-- The vectors that span the rows of `A - D`, as in Section 3: `β_l j * y j` for the bit `true`, and `β_l j * (1 - y j)` for
the bit `false`. The index `l` is a key and an exceptional sign vector. -/
noncomputable def spanVec (W : Wires Q L h M) (R : ℕ) (y : Fin M → ℚ) (p : BIndex Q L h R × Bool) (j : Fin M) : ℚ :=
  beta W R p.1.1.1 p.1.1.2 j * (if p.2 then y j else 1 - y j)

/-- **The row space.** Every row of `A - D` lies in the span of `spanVec`. This holds for all rationals `x`, `y`. -/
theorem row_mem_span (W : Wires Q L h M) (R : ℕ) (x y : Fin M → ℚ) (i : Fin M) :
    (Aval W (kappa Q R) R x y - Dval W x y) i ∈ Submodule.span ℚ (Set.range (spanVec W R y)) := by
  classical
  have hrow : (Aval W (kappa Q R) R x y - Dval W x y) i =
      ∑ p : BIndex Q L h R, ((alpha W p.1.1 p.1.2 i * x i) • spanVec W R y (p, true) +
        (alpha W p.1.1 p.1.2 i * (1 - x i)) • spanVec W R y (p, false)) := by
    funext j
    rw [Aval_sub_Dval_apply, Bmat_sub_one_apply, Finset.sum_mul]
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.sum_coe_sort (keys Q L h ×ˢ exc Q R)]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [spanVec, eqv, if_true, Bool.false_eq_true, if_false]
    ring
  rw [hrow]
  refine Submodule.sum_mem _ fun p _ => Submodule.add_mem _ ?_ ?_
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(p, true), rfl⟩)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(p, false), rfl⟩)

/-- There are at most `2 * rankBound Q L h R` spanning vectors. -/
theorem finrank_span_spanVec_le (W : Wires Q L h M) (R : ℕ) (y : Fin M → ℚ) :
    Module.finrank ℚ (Submodule.span ℚ (Set.range (spanVec W R y))) ≤ 2 * rankBound Q L h R := by
  have hc := finrank_range_le_card (R := ℚ) (spanVec W R y)
  simp only [Fintype.card_prod, card_BIndex, Fintype.card_bool] at hc
  rw [mul_comm]
  exact hc

/-- All rows of `A - D` lie in a space of dimension at most `2 * rankBound Q L h R`. -/
theorem exists_row_space (W : Wires Q L h M) (R : ℕ) (x y : Fin M → ℚ) :
    ∃ V : Submodule ℚ (Fin M → ℚ), Module.finrank ℚ V ≤ 2 * rankBound Q L h R ∧
      ∀ i, (Aval W (kappa Q R) R x y - Dval W x y) i ∈ V :=
  ⟨_, finrank_span_spanVec_le W R y, row_mem_span W R x y⟩

/-! ### The numbers for `Q = m ^ 4`, `R = m ^ 3` -/

/-- `#exc * m ^ 2 ≤ 2 ^ Q`. -/
theorem card_exc_mul_sq_le_two_pow {m : ℕ} (hm : 0 < m) :
    (exc (m ^ 4) (m ^ 3)).card * m ^ 2 ≤ 2 ^ m ^ 4 := by
  have h := card_exc_mul_sq_le (m ^ 4) (m ^ 3)
  have hp : 0 < m ^ 4 := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hp
  calc (exc (m ^ 4) (m ^ 3)).card * m ^ 2 * m ^ 4 = (exc (m ^ 4) (m ^ 3)).card * (m ^ 3) ^ 2 := by ring
    _ ≤ 2 ^ m ^ 4 * m ^ 4 := h

/-- `#exc ≤ 2 ^ Q / m ^ 2`. -/
theorem card_exc_le_div {m : ℕ} (hm : 0 < m) :
    (exc (m ^ 4) (m ^ 3)).card ≤ 2 ^ m ^ 4 / m ^ 2 :=
  (Nat.le_div_iff_mul_le (by positivity)).mpr (card_exc_mul_sq_le_two_pow hm)

/-- `rankBound * m ^ 2 ≤ K ^ 2 * h`, with `K = L ^ Q`. -/
theorem rankBound_mul_sq_le {m : ℕ} (hm : 0 < m) (L h : ℕ) :
    rankBound (m ^ 4) L h (m ^ 3) * m ^ 2 ≤ (L ^ m ^ 4) ^ 2 * h := by
  calc rankBound (m ^ 4) L h (m ^ 3) * m ^ 2
      = (keys (m ^ 4) L h).card * ((exc (m ^ 4) (m ^ 3)).card * m ^ 2) := by
        rw [rankBound, mul_assoc]
    _ ≤ (keys (m ^ 4) L h).card * 2 ^ m ^ 4 := Nat.mul_le_mul_left _ (card_exc_mul_sq_le_two_pow hm)
    _ ≤ (L ^ m ^ 4) ^ 2 * h := card_keys_mul_le _ _ _

/-- `rank ≤ K ^ 2 * h / m ^ 2`. -/
theorem rankBound_le_div {m : ℕ} (hm : 0 < m) (L h : ℕ) :
    rankBound (m ^ 4) L h (m ^ 3) ≤ (L ^ m ^ 4) ^ 2 * h / m ^ 2 :=
  (Nat.le_div_iff_mul_le (by positivity)).mpr (rankBound_mul_sq_le hm L h)

/-- The rank of `B - 1` for `Q = m ^ 4`, `R = m ^ 3`. -/
theorem rank_Bmat_sub_one_le_div {m : ℕ} (hm : 0 < m) (W : Wires (m ^ 4) L h M) :
    (Bmat W (kappa (m ^ 4) (m ^ 3)) (m ^ 3) - 1).rank ≤ (L ^ m ^ 4) ^ 2 * h / m ^ 2 :=
  (rank_Bmat_sub_one_le W (m ^ 3)).trans (rankBound_le_div hm L h)

/-- With `r` at least the floor of `2 K ^ 2 h / m ^ 2`, the row space has dimension at most `r`. -/
theorem two_mul_rankBound_le {m : ℕ} (hm : 0 < m) (L h : ℕ) :
    2 * rankBound (m ^ 4) L h (m ^ 3) ≤ 2 * (L ^ m ^ 4) ^ 2 * h / m ^ 2 := by
  refine (Nat.le_div_iff_mul_le (by positivity)).mpr ?_
  calc 2 * rankBound (m ^ 4) L h (m ^ 3) * m ^ 2 = 2 * (rankBound (m ^ 4) L h (m ^ 3) * m ^ 2) := by ring
    _ ≤ 2 * ((L ^ m ^ 4) ^ 2 * h) := Nat.mul_le_mul_left _ (rankBound_mul_sq_le hm L h)
    _ = 2 * (L ^ m ^ 4) ^ 2 * h := by ring

/-- With `J = M / m + r + 1`, the pigeonhole inequality holds for `Q = m ^ 4`, `R = m ^ 3`. -/
theorem pigeon_ineq {m : ℕ} (hm : 0 < m) (M r : ℕ) :
    M * m ^ 3 + r * m ^ 4 < m ^ 4 * (M / m + r + 1) := by
  have h1 : M < m * (M / m + 1) := Nat.lt_mul_div_succ M hm
  have h2 : M * m ^ 3 < m * (M / m + 1) * m ^ 3 := Nat.mul_lt_mul_of_pos_right h1 (by positivity)
  calc M * m ^ 3 + r * m ^ 4 < m * (M / m + 1) * m ^ 3 + r * m ^ 4 := by omega
    _ = m ^ 4 * (M / m + r + 1) := by ring

/-- With `M / m ≤ r` and `J = 2 r + 1`, the pigeonhole inequality holds for `Q = m ^ 4`, `R = m ^ 3`. These are the numbers of
Section 3, where `r` is the floor of `Δ n / m` and `M ≤ Δ n`. -/
theorem pigeon_ineq_two {m M r : ℕ} (hm : 0 < m) (hr : M / m ≤ r) :
    M * m ^ 3 + r * m ^ 4 < m ^ 4 * (2 * r + 1) := by
  have h := pigeon_ineq hm M r
  have hle : M / m + r + 1 ≤ 2 * r + 1 := by omega
  exact h.trans_le (Nat.mul_le_mul_left _ hle)

/-- The bound of Section 3 on the row space: `2 * rankBound ≤ A / m`, when `2 K ^ 2 h ≤ m A`, with `K = L ^ Q`. In the text, `A = Δ n`
and `K ^ 2 h ≤ 14 A`, so this holds for `m ≥ 28`. -/
theorem two_mul_rankBound_le_div {m A L h : ℕ} (hm : 0 < m) (hN : 2 * ((L ^ m ^ 4) ^ 2 * h) ≤ m * A) :
    2 * rankBound (m ^ 4) L h (m ^ 3) ≤ A / m := by
  rw [Nat.le_div_iff_mul_le hm]
  refine Nat.le_of_mul_le_mul_right ?_ hm
  calc 2 * rankBound (m ^ 4) L h (m ^ 3) * m * m = 2 * (rankBound (m ^ 4) L h (m ^ 3) * m ^ 2) := by ring
    _ ≤ 2 * ((L ^ m ^ 4) ^ 2 * h) := Nat.mul_le_mul_left _ (rankBound_mul_sq_le hm L h)
    _ ≤ m * A := hN
    _ = A * m := mul_comm _ _

/-- **The numbers of Section 3.** If `M ≤ A` and `2 K ^ 2 h ≤ m A`, then `r = A / m` and `J = 2 r + 1` satisfy the two hypotheses
of the decomposition in `Theorem.lean`, for `Q = m ^ 4` and `R = m ^ 3`. -/
theorem hypotheses_of_numbers {m A L h M : ℕ} (hm : 0 < m) (hN : 2 * ((L ^ m ^ 4) ^ 2 * h) ≤ m * A) (hM : M ≤ A) :
    2 * rankBound (m ^ 4) L h (m ^ 3) ≤ A / m ∧
      M * m ^ 3 + A / m * m ^ 4 < m ^ 4 * (2 * (A / m) + 1) :=
  ⟨two_mul_rankBound_le_div hm hN, pigeon_ineq_two hm (Nat.div_le_div_right hM)⟩

end OnePigeonhole
