import TransposeBase.Short

/-!
# Walsh functions, the window polynomial, and the numbers `κ`

The part of Section 2 of `papers/one-pigeonhole/proof.tex` that does not mention wires. A sign vector is given by the set `σ`
of its digits with a minus sign.

* `chi σ F` is `σ ^ F = ∏_{t ∈ F} σ_t`. `sum_chi`: `∑ σ, σ ^ F = 2 ^ Q [F = ∅]`.
* `exc Q R`: the sign vectors with `|∑ t, σ_t| > R`. `card_exc_mul_sq_le`: `#exc * R ^ 2 ≤ 2 ^ Q * Q`.
* `window Q R`: the integers `k ≤ Q` with `|Q - 2 k| ≤ R`. `windowPoly Q R`: the Lagrange interpolation of `(-1) ^ k` on the window.
* `kappa Q R e`: the coefficient of a set of size `e`.
* `sum_kappa_chi`: `∑_{|E| ≤ R} κ_{|E|} σ ^ E = p(|σ|)`, and `sum_kappa_chi_of_notMem_exc`: this is `σ ^ [Q]` off `exc Q R`.
-/

set_option linter.unusedSectionVars false

namespace OnePigeonhole

open Finset

variable {Q : ℕ}

/-! ### Walsh functions -/

/-- The Walsh function `σ ^ F = ∏_{t ∈ F} σ_t`, where `σ` is the set of the digits with a minus sign. -/
def chi (σ F : Finset (Fin Q)) : ℚ := (-1) ^ (σ ∩ F).card

theorem chi_eq_prod (σ F : Finset (Fin Q)) :
    chi σ F = ∏ t, if t ∈ σ ∧ t ∈ F then (-1 : ℚ) else 1 := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, chi]
  congr 2
  ext t
  simp

theorem chi_comm (σ F : Finset (Fin Q)) : chi σ F = chi F σ := by
  rw [chi, chi, Finset.inter_comm]

/-- The product rule in the second argument: `σ ^ (E ∆ F) = σ ^ E * σ ^ F`. -/
theorem chi_symmDiff (σ E F : Finset (Fin Q)) : chi σ (symmDiff E F) = chi σ E * chi σ F := by
  simp only [chi_eq_prod]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun t _ => ?_
  by_cases h1 : t ∈ σ <;> by_cases h2 : t ∈ E <;> by_cases h3 : t ∈ F <;>
    simp [Finset.mem_symmDiff, h1, h2, h3]

/-- The product rule in the first argument. -/
theorem chi_symmDiff_left (σ σ' F : Finset (Fin Q)) : chi (symmDiff σ σ') F = chi σ F * chi σ' F := by
  rw [chi_comm, chi_symmDiff, chi_comm F σ, chi_comm F σ']

theorem chi_empty (σ : Finset (Fin Q)) : chi σ ∅ = 1 := by simp [chi]

theorem chi_mul_self (σ F : Finset (Fin Q)) : chi σ F * chi σ F = 1 := by
  rw [← chi_symmDiff, symmDiff_self]
  exact chi_empty σ

theorem chi_univ (σ : Finset (Fin Q)) : chi σ univ = (-1) ^ σ.card := by simp [chi]

theorem chi_singleton (σ : Finset (Fin Q)) (t : Fin Q) : chi σ {t} = if t ∈ σ then -1 else 1 := by
  rw [chi_eq_prod, Finset.prod_eq_single t]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/-- `∑ σ, σ ^ F = 2 ^ Q [F = ∅]`. -/
theorem sum_chi (F : Finset (Fin Q)) :
    ∑ σ, chi σ F = if F = ∅ then 2 ^ Q else 0 := by
  classical
  split_ifs with hF
  · subst hF
    simp [chi_empty]
  · obtain ⟨t, ht⟩ := Finset.nonempty_iff_ne_empty.mpr hF
    have hinv : Function.Involutive fun σ : Finset (Fin Q) => symmDiff σ {t} := by
      intro σ
      simp
    have h1 : ∑ σ, chi (symmDiff σ {t}) F = ∑ σ, chi σ F :=
      Equiv.sum_comp hinv.toPerm (fun σ => chi σ F)
    have h2 : ∀ σ, chi (symmDiff σ {t}) F = -chi σ F := by
      intro σ
      rw [chi_symmDiff_left, chi_comm {t} F, chi_singleton]
      simp [ht]
    simp only [h2, Finset.sum_neg_distrib] at h1
    linarith

/-- The dual form: `∑ E, σ ^ E = 2 ^ Q [σ = ∅]`. -/
theorem sum_chi_right (σ : Finset (Fin Q)) :
    ∑ E, chi σ E = if σ = ∅ then 2 ^ Q else 0 := by
  simp_rw [chi_comm σ]
  exact sum_chi σ

/-- The indicator of `E = A` as a sum over the sign vectors. -/
theorem sum_chi_mul_chi (E A : Finset (Fin Q)) :
    ∑ σ, chi σ E * chi σ A = if E = A then 2 ^ Q else 0 := by
  simp_rw [← chi_symmDiff]
  rw [sum_chi]
  simp

/-! ### The exceptional sign vectors -/

/-- `∑ t, σ_t`. -/
def sgnSum (σ : Finset (Fin Q)) : ℤ := (Q : ℤ) - 2 * σ.card

/-- The exceptional sign vectors: `|∑ t, σ_t| > R`. -/
def exc (Q R : ℕ) : Finset (Finset (Fin Q)) := univ.filter fun σ => (R : ℤ) < |sgnSum σ|

theorem sgnSum_eq_sum (σ : Finset (Fin Q)) : ((sgnSum σ : ℤ) : ℚ) = ∑ t, chi σ {t} := by
  simp_rw [chi_singleton]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one, sgnSum]
  have h1 : (univ.filter fun t => t ∈ σ) = σ := by
    ext t
    simp
  have h2 : ((univ.filter fun t => t ∉ σ).card : ℚ) = (Q : ℚ) - σ.card := by
    have h3 : (univ.filter fun t => t ∉ σ) = σᶜ := by
      ext t
      simp
    rw [h3, Finset.card_compl, Fintype.card_fin, Nat.cast_sub]
    calc σ.card ≤ (univ : Finset (Fin Q)).card := Finset.card_le_univ _
      _ = Q := by simp
  rw [h1, h2]
  push_cast
  ring

/-- `∑ σ, (∑ t, σ_t) ^ 2 = 2 ^ Q * Q`. -/
theorem sum_sgnSum_sq : ∑ σ : Finset (Fin Q), ((sgnSum σ : ℤ) : ℚ) ^ 2 = 2 ^ Q * Q := by
  classical
  have h1 : ∀ σ : Finset (Fin Q), ((sgnSum σ : ℤ) : ℚ) ^ 2 =
      ∑ t : Fin Q, ∑ t' : Fin Q, chi σ {t} * chi σ {t'} := by
    intro σ
    rw [sgnSum_eq_sum, sq, Finset.sum_mul_sum]
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ t : Fin Q, ∑ σ : Finset (Fin Q), ∑ t' : Fin Q, chi σ {t} * chi σ {t'} = 2 ^ Q := by
    intro t
    rw [Finset.sum_comm]
    simp_rw [sum_chi_mul_chi]
    simp [Finset.singleton_inj]
  simp_rw [h2]
  simp [mul_comm]

/-- `#exc * R ^ 2 ≤ 2 ^ Q * Q`. -/
theorem card_exc_mul_sq_le (Q R : ℕ) : (exc Q R).card * R ^ 2 ≤ 2 ^ Q * Q := by
  have h : ((exc Q R).card : ℚ) * (R : ℚ) ^ 2 ≤ 2 ^ Q * Q := by
    rw [← sum_sgnSum_sq]
    calc ((exc Q R).card : ℚ) * (R : ℚ) ^ 2 = ∑ _σ ∈ exc Q R, (R : ℚ) ^ 2 := by simp
      _ ≤ ∑ σ ∈ exc Q R, ((sgnSum σ : ℤ) : ℚ) ^ 2 := by
          refine Finset.sum_le_sum fun σ hσ => ?_
          have h1 : (R : ℤ) < |sgnSum σ| := (Finset.mem_filter.mp hσ).2
          have h2 : ((R : ℤ)) ^ 2 ≤ (sgnSum σ) ^ 2 := by
            rw [← sq_abs (sgnSum σ)]
            exact pow_le_pow_left₀ (by positivity) h1.le 2
          exact_mod_cast h2
      _ ≤ ∑ σ, ((sgnSum σ : ℤ) : ℚ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun σ _ _ => sq_nonneg _
  exact_mod_cast h

/-! ### The window polynomial -/

/-- The window: the integers `k ≤ Q` with `|Q - 2 k| ≤ R`. -/
def window (Q R : ℕ) : Finset ℕ := (range (Q + 1)).filter fun k => Q ≤ 2 * k + R ∧ 2 * k ≤ Q + R

theorem card_window_le (Q R : ℕ) : (window Q R).card ≤ R + 1 := by
  have hsub : window Q R ⊆ Finset.Ico ((Q - R + 1) / 2) ((Q - R + 1) / 2 + R + 1) := by
    intro k hk
    have h := (Finset.mem_filter.mp hk).2
    rw [Finset.mem_Ico]
    omega
  calc (window Q R).card ≤ _ := Finset.card_le_card hsub
    _ = R + 1 := by
      rw [Nat.card_Ico]
      omega

/-- A sign vector off the exceptional set has its number of minus signs in the window. -/
theorem card_mem_window {σ : Finset (Fin Q)} {R : ℕ} (h : σ ∉ exc Q R) : σ.card ∈ window Q R := by
  have h1 : ¬ (R : ℤ) < |sgnSum σ| := fun h' => h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩)
  have h2 := not_lt.mp h1
  have h3 := abs_le.mp h2
  have h4 : σ.card ≤ Q := by
    calc σ.card ≤ (univ : Finset (Fin Q)).card := Finset.card_le_univ _
      _ = Q := by simp
  simp only [sgnSum] at h3
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_, ?_⟩ <;> omega

/-- The Lagrange interpolation of `(-1) ^ k` on the window. -/
noncomputable def windowPoly (Q R : ℕ) : Polynomial ℚ :=
  Lagrange.interpolate (window Q R) (fun k : ℕ => (k : ℚ)) (fun k => (-1) ^ k)

theorem natDegree_windowPoly_le (Q R : ℕ) : (windowPoly Q R).natDegree ≤ R := by
  have hinj : Set.InjOn (fun k : ℕ => (k : ℚ)) (window Q R : Set ℕ) :=
    fun a _ b _ h => Nat.cast_injective h
  by_cases h0 : windowPoly Q R = 0
  · rw [h0]
    simp
  · have hd := Lagrange.degree_interpolate_lt (s := window Q R) (v := fun k : ℕ => (k : ℚ))
      (fun k => ((-1) ^ k : ℚ)) hinj
    have h1 := (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hd
    have h2 := card_window_le Q R
    omega

theorem eval_windowPoly {Q R k : ℕ} (hk : k ∈ window Q R) :
    (windowPoly Q R).eval (k : ℚ) = (-1) ^ k := by
  have hinj : Set.InjOn (fun k : ℕ => (k : ℚ)) (window Q R : Set ℕ) :=
    fun a _ b _ h => Nat.cast_injective h
  exact Lagrange.eval_interpolate_at_node (fun k => ((-1) ^ k : ℚ)) hinj hk

/-- The value of the window polynomial at an integer. -/
noncomputable def windowVal (Q R k : ℕ) : ℚ := (windowPoly Q R).eval (k : ℚ)

/-- A difference of order above the degree of the window polynomial vanishes. -/
theorem sum_choose_windowVal_eq_zero {Q R e : ℕ} (he : R < e) (a : ℕ) :
    ∑ j ∈ range (e + 1), (e.choose j : ℚ) * (-1) ^ j * windowVal Q R (a + j) = 0 := by
  have h0 := Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (P := windowPoly Q R) (n := e)
    (lt_of_le_of_lt (natDegree_windowPoly_le Q R) he)
  have h1 := congrFun h0 (a : ℚ)
  rw [fwdDiff_iter_eq_sum_shift] at h1
  have h2 : ∑ j ∈ range (e + 1), (e.choose j : ℚ) * (-1) ^ j * windowVal Q R (a + j) =
      (-1) ^ e * ∑ k ∈ range (e + 1),
        ((-1 : ℤ) ^ (e - k) * (e.choose k : ℤ)) • (windowPoly Q R).eval ((a : ℚ) + k • (1 : ℚ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hje : j ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hsign : (-1 : ℚ) ^ e * (-1) ^ (e - j) = (-1) ^ j := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hje
      rw [Nat.add_sub_cancel_left, pow_add, mul_assoc, ← pow_add, ← two_mul, pow_mul]
      simp
    simp only [windowVal, zsmul_eq_mul, nsmul_eq_mul, mul_one]
    push_cast
    linear_combination (-(e.choose j : ℚ) * (windowPoly Q R).eval ((a : ℚ) + j)) * hsign
  rw [h2]
  simp only [Pi.zero_apply] at h1
  rw [h1, mul_zero]

/-! ### The numbers `κ` -/

/-- The coefficient of a set of size `e`: `2 ^ (-Q)` times the sum over the sign vectors of `p(|σ|) σ ^ E`, for `|E| = e`. -/
noncomputable def kappa (Q R e : ℕ) : ℚ :=
  (2 ^ Q)⁻¹ * ∑ a ∈ range (Q - e + 1), ((Q - e).choose a : ℚ) *
    ∑ j ∈ range (e + 1), (e.choose j : ℚ) * (-1) ^ j * windowVal Q R (a + j)

/-- Split a sign vector into its part off `E` and its part on `E`. -/
theorem sum_card_mul_chi (f : ℕ → ℚ) (E : Finset (Fin Q)) :
    ∑ σ : Finset (Fin Q), f σ.card * chi σ E =
      ∑ a ∈ range (Q - E.card + 1), ((Q - E.card).choose a : ℚ) *
        ∑ j ∈ range (E.card + 1), (E.card.choose j : ℚ) * (-1) ^ j * f (a + j) := by
  classical
  have hsplit : ∑ σ : Finset (Fin Q), f σ.card * chi σ E =
      ∑ A ∈ (Eᶜ).powerset, ∑ B ∈ E.powerset, f (A.card + B.card) * (-1) ^ B.card := by
    rw [← Finset.sum_product']
    refine Finset.sum_nbij' (fun σ => (σ \ E, σ ∩ E)) (fun p => p.1 ∪ p.2) ?_ ?_ ?_ ?_ ?_
    · intro σ _
      simp only [Finset.mem_product, Finset.mem_powerset]
      refine ⟨fun t ht => ?_, Finset.inter_subset_right⟩
      simpa using (Finset.mem_sdiff.mp ht).2
    · intro _ _
      exact Finset.mem_univ _
    · intro σ _
      simp [Finset.sdiff_union_inter]
    · intro p hp
      obtain ⟨hA, hB⟩ := Finset.mem_product.mp hp
      have hA' := Finset.mem_powerset.mp hA
      have hB' := Finset.mem_powerset.mp hB
      have hd : Disjoint p.1 E := by
        rw [Finset.disjoint_left]
        intro t ht
        simpa using hA' ht
      refine Prod.ext ?_ ?_
      · ext t
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨h1 | h1, h2⟩
          · exact h1
          · exact absurd (hB' h1) h2
        · intro h
          exact ⟨Or.inl h, Finset.disjoint_left.mp hd h⟩
      · ext t
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨h1 | h1, h2⟩
          · exact absurd h2 (Finset.disjoint_left.mp hd h1)
          · exact h1
        · intro h
          exact ⟨Or.inr h, hB' h⟩
    · intro σ _
      have hd : Disjoint (σ \ E) (σ ∩ E) := Finset.disjoint_left.mpr fun t h1 h2 =>
        (Finset.mem_sdiff.mp h1).2 (Finset.mem_inter.mp h2).2
      simp only
      rw [← Finset.card_union_of_disjoint hd, Finset.sdiff_union_inter, chi]
  rw [hsplit]
  have hcard : (Eᶜ).card = Q - E.card := by rw [Finset.card_compl, Fintype.card_fin]
  rw [Finset.sum_powerset_apply_card
    (fun n => ∑ B ∈ E.powerset, f (n + B.card) * (-1) ^ B.card) (x := Eᶜ), hcard]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [nsmul_eq_mul, Finset.sum_powerset_apply_card (fun n => f (a + n) * (-1) ^ n) (x := E)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [nsmul_eq_mul]
  ring

/-- The number `κ` is the Fourier coefficient of the window polynomial at any set of its size. -/
theorem kappa_card_eq (R : ℕ) (E : Finset (Fin Q)) :
    kappa Q R E.card = (2 ^ Q)⁻¹ * ∑ σ : Finset (Fin Q), windowVal Q R σ.card * chi σ E := by
  rw [sum_card_mul_chi]
  rfl

/-- A set of more than `R` digits has coefficient `0`. -/
theorem kappa_eq_zero {Q R e : ℕ} (he : R < e) : kappa Q R e = 0 := by
  unfold kappa
  rw [Finset.sum_eq_zero, mul_zero]
  intro a _
  rw [sum_choose_windowVal_eq_zero he, mul_zero]

/-- The sets of at most `R` digits. -/
abbrev shortSets (Q R : ℕ) : Finset (Finset (Fin Q)) := TransposeBase.reads Q R

theorem mem_shortSets {R : ℕ} {E : Finset (Fin Q)} : E ∈ shortSets Q R ↔ E.card ≤ R := by
  simp [shortSets, TransposeBase.reads]

/-- Fourier inversion, with the sets of more than `R` digits dropped. -/
theorem sum_kappa_chi (R : ℕ) (σ : Finset (Fin Q)) :
    ∑ E ∈ shortSets Q R, kappa Q R E.card * chi σ E = windowVal Q R σ.card := by
  classical
  have h1 : ∑ E ∈ shortSets Q R, kappa Q R E.card * chi σ E =
      ∑ E, kappa Q R E.card * chi σ E := by
    refine Finset.sum_subset (Finset.subset_univ _) fun E _ hE => ?_
    have : R < E.card := by
      by_contra h
      exact hE (mem_shortSets.mpr (not_lt.mp h))
    rw [kappa_eq_zero this, zero_mul]
  rw [h1]
  simp_rw [kappa_card_eq, mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have h2 : ∀ σ' : Finset (Fin Q),
      ∑ E, windowVal Q R σ'.card * chi σ' E * chi σ E =
        if σ' = σ then 2 ^ Q * windowVal Q R σ'.card else 0 := by
    intro σ'
    simp_rw [mul_assoc, ← chi_symmDiff_left]
    rw [← Finset.mul_sum, sum_chi_right]
    by_cases h : σ' = σ
    · subst h
      simp [mul_comm]
    · have : symmDiff σ' σ ≠ ∅ := by
        intro h'
        exact h (symmDiff_eq_bot.mp h')
      simp [h, this]
  simp_rw [h2]
  rw [Finset.sum_ite_eq' univ σ]
  simp

/-- Off the exceptional sign vectors the window sum is the product of all signs. -/
theorem sum_kappa_chi_of_notMem_exc {R : ℕ} {σ : Finset (Fin Q)} (h : σ ∉ exc Q R) :
    ∑ E ∈ shortSets Q R, kappa Q R E.card * chi σ E = chi σ univ := by
  rw [sum_kappa_chi, windowVal, eval_windowPoly (card_mem_window h), chi_univ]

end OnePigeonhole
