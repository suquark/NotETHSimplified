import TransposeBase.Defs

/-! Formal monomials of reads, and coefficients of polynomials as fixed combinations of values on a grid. -/
set_option linter.unusedSectionVars false

namespace TransposeBase
open scoped BigOperators
open MvPolynomial hiding X

variable {Q : ℕ} {A : Type*} [Fintype A] [DecidableEq A] {k : Type*} [Field k] [CharZero k]

/-- The sets `E` with `|E| ≤ R`. -/
def reads (Q R : ℕ) : Finset (Finset (Fin Q)) :=
  (Finset.univ : Finset (Finset (Fin Q))).filter (fun E => E.card ≤ R)

section Grid
variable {N : ℕ}

/-- The grid points of one variable: `0, ..., N` in `k`. -/
def gridPt (N : ℕ) (b : Fin (N + 1)) : k := ((b : ℕ) : k)

theorem gridPt_inj (N : ℕ) : Function.Injective (gridPt (k := k) N) := by
  intro a b h
  apply Fin.ext
  unfold gridPt at h
  exact_mod_cast h

/-- The weight of the grid point `b` when extracting the exponent `e` of one variable. -/
noncomputable def lagCoeff (N e : ℕ) (b : Fin (N + 1)) : k :=
  (Lagrange.basis Finset.univ (gridPt (k := k) N) b).coeff e

/-- One variable: the weights extract the exponent `e` from `y^f` for `f ≤ N`. -/
theorem sum_lagCoeff_pow (e : ℕ) {f : ℕ} (hf : f ≤ N) :
    ∑ b, lagCoeff (k := k) N e b * gridPt N b ^ f = if e = f then 1 else 0 := by
  classical
  have hdeg : (Polynomial.X ^ f : Polynomial k).degree < (Finset.univ : Finset (Fin (N + 1))).card := by
    simp only [Polynomial.degree_X_pow, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast Nat.lt_succ_of_le hf
  have hint := Lagrange.eq_interpolate (s := Finset.univ) (v := gridPt (k := k) N)
    (fun a _ b _ h => gridPt_inj N h) hdeg
  have hc : (Polynomial.X ^ f : Polynomial k).coeff e = if e = f then 1 else 0 := by
    simp [Polynomial.coeff_X_pow]
  rw [← hc, hint]
  simp only [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.coeff_C_mul, lagCoeff]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The exponent vector with coordinates `a i`. -/
noncomputable def expOf (a : Fin Q → Fin (N + 1)) : Fin Q →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (a i : ℕ))

@[simp] theorem expOf_apply (a : Fin Q → Fin (N + 1)) (i : Fin Q) : expOf a i = (a i : ℕ) := rfl

theorem expOf_inj : Function.Injective (expOf (Q := Q) (N := N)) := by
  intro a b h
  funext i
  exact Fin.ext (DFunLike.congr_fun h i)

/-- A coefficient of a polynomial of degree at most `N` in each variable is a fixed combination
of its values on the grid. -/
theorem coeff_eq_grid (p : MvPolynomial (Fin Q) k) (hp : ∀ c ∈ p.support, ∀ i, c i ≤ N)
    (a : Fin Q → Fin (N + 1)) :
    coeff (expOf a) p =
      ∑ y : Fin Q → Fin (N + 1), (∏ i, lagCoeff N (a i) (y i)) *
        eval (fun i => gridPt N (y i)) p := by
  classical
  simp_rw [eval_eq', Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm : ∀ c ∈ p.support,
      ∑ y : Fin Q → Fin (N + 1), (∏ i, lagCoeff N (a i) (y i)) *
        (coeff c p * ∏ i, gridPt N (y i) ^ c i) =
      if c = expOf a then coeff c p else 0 := by
    intro c hc
    have hprod : ∑ y : Fin Q → Fin (N + 1),
        ∏ i, (lagCoeff (k := k) N (a i) (y i) * gridPt N (y i) ^ c i) =
        ∏ i, ∑ b, lagCoeff (k := k) N (a i) b * gridPt N b ^ c i :=
      (Fintype.prod_sum (fun i b => lagCoeff (k := k) N (a i) b * gridPt N b ^ c i)).symm
    have hval : (∏ i, ∑ b, lagCoeff (k := k) N (a i) b * gridPt N b ^ c i) =
        if c = expOf a then 1 else 0 := by
      simp_rw [fun i => sum_lagCoeff_pow (k := k) (N := N) (a i) (hp c hc i)]
      rw [Finset.prod_ite_zero]
      have : (∀ i, ((a i : ℕ)) = c i) ↔ c = expOf a := by
        constructor
        · intro h
          ext i
          simp [h i]
        · rintro rfl i
          rfl
      simp only [Finset.mem_univ, true_imp_iff, this, Finset.prod_const_one]
    have hrew : ∀ y : Fin Q → Fin (N + 1), (∏ i, lagCoeff N (a i) (y i)) *
        (coeff c p * ∏ i, gridPt N (y i) ^ c i) =
        coeff c p * ∏ i, (lagCoeff (k := k) N (a i) (y i) * gridPt N (y i) ^ c i) := by
      intro y
      rw [Finset.prod_mul_distrib]
      ring
    simp_rw [hrew]
    rw [← Finset.mul_sum, hprod, hval]
    split <;> simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  split
  · rfl
  · exact notMem_support_iff.mp ‹_›

end Grid

section Poly
variable (R : ℕ) (γ : Cell Q A → k) (m : Cell Q A → Finset (Fin Q) → k) (X Y : Cell Q A → k)

/-- `y^E = ∏_{i ∈ E} y_i`. -/
noncomputable def yMono (E : Finset (Fin Q)) : MvPolynomial (Fin Q) k :=
  ∏ i ∈ E, MvPolynomial.X i

theorem eval_yMono (E : Finset (Fin Q)) : eval (fun _ => (1 : k)) (yMono E) = 1 := by
  simp [yMono]

/-! ### Degrees -/

theorem degreeOf_yMono_le (i : Fin Q) (E : Finset (Fin Q)) :
    degreeOf i (yMono E : MvPolynomial (Fin Q) k) ≤ 1 := by
  classical
  unfold yMono
  refine (degreeOf_prod_le _ _ _).trans ?_
  calc ∑ j ∈ E, degreeOf i (MvPolynomial.X j : MvPolynomial (Fin Q) k)
      ≤ ∑ j ∈ E, if i = j then 1 else 0 := by
        apply Finset.sum_le_sum
        intro j _
        rw [degreeOf_X]
    _ ≤ 1 := by
        rw [Finset.sum_ite_eq]
        split <;> simp

theorem degreeOf_C_mul_le {p : MvPolynomial (Fin Q) k} {d : ℕ} (i : Fin Q) (a : k)
    (hp : degreeOf i p ≤ d) : degreeOf i (C a * p) ≤ d := by
  refine (degreeOf_mul_le _ _ _).trans ?_
  rw [degreeOf_C, zero_add]
  exact hp

theorem totalDegree_yMono_le {E : Finset (Fin Q)} (hE : E ∈ reads Q R) :
    (yMono E : MvPolynomial (Fin Q) k).totalDegree ≤ R := by
  unfold yMono
  refine (totalDegree_finsetProd _ _).trans ?_
  simpa using (Finset.mem_filter.mp hE).2

end Poly

section Partition
variable {N : ℕ}

/-- `t` is the first digit whose exponent in `a` is below `J`. -/
def IsFirst (J : ℕ) (a : Fin Q → Fin (N + 1)) (t : Fin Q) : Prop :=
  (a t : ℕ) < J ∧ ∀ s, s < t → J ≤ (a s : ℕ)

open Classical in
/-- The exponent vectors whose first digit below `J` is `t`: the product set with `a i ≥ J` for `i < t`,
`a t < J`, and `a i` free for `i > t`. -/
noncomputable def digitBox (N J : ℕ) (t : Fin Q) : Finset (Fin Q → Fin (N + 1)) :=
  Finset.univ.filter (fun a => IsFirst J a t)

/-- The weight of a grid point for digit `t`. -/
noncomputable def digitWeight (N J : ℕ) (t : Fin Q) (y : Fin Q → Fin (N + 1)) : k :=
  ∑ a ∈ digitBox N J t, ∏ i, lagCoeff N (a i) (y i)

/-- The condition of `digitBox` on the exponent `e` of coordinate `i`. -/
def digitTest (J : ℕ) (t i : Fin Q) (e : ℕ) : Prop :=
  ((i : ℕ) < t → J ≤ e) ∧ ((i : ℕ) = t → e < J)

instance (J : ℕ) (t i : Fin Q) (e : ℕ) : Decidable (digitTest J t i e) := by
  unfold digitTest
  infer_instance

/-- The exponents allowed by `digitTest` at coordinate `i`. -/
def digitSet (N J : ℕ) (t i : Fin Q) : Finset (Fin (N + 1)) :=
  Finset.univ.filter (fun e => digitTest J t i e)

theorem digitBox_eq_pi (J : ℕ) (t : Fin Q) :
    digitBox N J t = Fintype.piFinset (digitSet N J t) := by
  classical
  ext a
  rw [Fintype.mem_piFinset]
  constructor
  · intro ha i
    have h : IsFirst J a t := (Finset.mem_filter.mp ha).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h' => h.2 i (Fin.lt_def.mpr h'),
      fun h' => (Fin.ext h' : i = t) ▸ h.1⟩
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp (h t)).2.2 rfl,
      fun s hs => (Finset.mem_filter.mp (h s)).2.1 (Fin.lt_def.mp hs)⟩

/-- The weight is a product over the coordinates of sums over the allowed exponents. -/
theorem digitWeight_eq_prod (J : ℕ) (t : Fin Q) (y : Fin Q → Fin (N + 1)) :
    digitWeight (k := k) N J t y = ∏ i, ∑ e ∈ digitSet N J t i, lagCoeff (k := k) N e (y i) := by
  rw [Finset.prod_univ_sum, digitWeight, digitBox_eq_pi]

/-- The sum of the coefficients in `digitBox` is a fixed combination of grid values. -/
theorem sum_coeff_digitBox (J : ℕ) (t : Fin Q) (p : MvPolynomial (Fin Q) k)
    (hp : ∀ c ∈ p.support, ∀ i, c i ≤ N) :
    ∑ a ∈ digitBox N J t, coeff (expOf a) p =
      ∑ y : Fin Q → Fin (N + 1), digitWeight N J t y * eval (fun i => gridPt N (y i)) p := by
  unfold digitWeight
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  exact coeff_eq_grid p hp a

end Partition

end TransposeBase
