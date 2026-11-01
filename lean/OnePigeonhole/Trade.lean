import OnePigeonhole.Helpers
import OnePigeonhole.Window

/-!
# The trade

Equation (2) of `papers/one-pigeonhole/proof.tex`, in Section 3. The bits have fixed values here. `rowMix T (A - D) A` is the
matrix `⟨T⟩`: its rows in `T` come from `A - D`, and its other rows from `A`.

* `det_eq_sum_rowMix_all`: `det D = ∑ T, (-1) ^ |T| det ⟨T⟩`, by linearity in the rows of `D = A - (A - D)`.
* `det_eq_sum_rowMix`: the sum needs only `|T| ≤ r`, when the rows of `A - D` lie in a space of dimension at most `r`.
* `prod_eqv_eq_sum_rowMix`: equation (2) for the wires.
-/

set_option linter.unusedSectionVars false

namespace OnePigeonhole

open Finset

section Line

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- `det D = ∑ T, (-1) ^ |T| det ⟨T⟩`, by linearity in the rows of `D = A - (A - D)`. -/
theorem det_eq_sum_rowMix_all (A D : Matrix n n K) :
    D.det = ∑ T : Finset n, (-1) ^ T.card * (rowMix T (A - D) A).det := by
  classical
  have hsum : D = -(A - D) + A := by
    ext i j
    simp
  conv_lhs => rw [hsum, det_add_eq_sum_rowMix]
  refine Finset.sum_congr rfl fun T _ => ?_
  have hmat : rowMix T (-(A - D)) A =
      Matrix.of fun i j => (if i ∈ T then (-1 : K) else 1) * rowMix T (A - D) A i j := by
    ext i j
    by_cases hi : i ∈ T <;> simp [hi]
  rw [hmat, Matrix.det_mul_column, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

/-- A term with more rows than the dimension of the row space vanishes. -/
theorem det_rowMix_sub_eq_zero {A D : Matrix n n K} {V : Submodule K (n → K)} {r : ℕ}
    (hV : ∀ i, (A - D) i ∈ V) (hr : Module.finrank K V ≤ r) {T : Finset n} (hT : r < T.card) :
    (rowMix T (A - D) A).det = 0 :=
  det_rowMix_eq_zero T (A - D) A V (fun i _ => hV i) (by omega)

/-- **The trade.** `det D = ∑_{|T| ≤ r} (-1) ^ |T| det ⟨T⟩`, when the rows of `A - D` lie in a space of dimension at most `r`. -/
theorem det_eq_sum_rowMix {A D : Matrix n n K} {V : Submodule K (n → K)} {r : ℕ}
    (hV : ∀ i, (A - D) i ∈ V) (hr : Module.finrank K V ≤ r) :
    D.det = ∑ T ∈ (univ : Finset (Finset n)).filter (fun T => T.card ≤ r),
      (-1) ^ T.card * (rowMix T (A - D) A).det := by
  classical
  rw [det_eq_sum_rowMix_all A D, Finset.sum_filter]
  refine Finset.sum_congr rfl fun T _ => ?_
  split_ifs with hT
  · rfl
  · rw [det_rowMix_sub_eq_zero hV hr (not_le.mp hT), mul_zero]

end Line

section Wires

variable {Q L h M : ℕ}

/-- **Equation (2).** `∏ [x_j = y_j] = ∑_{|T| ≤ r} (-1) ^ |T| det ⟨T⟩`, when `2 * rankBound Q L h R ≤ r`. -/
theorem prod_eqv_eq_sum_rowMix (W : Wires Q L h M) {R r : ℕ} (hr : 2 * rankBound Q L h R ≤ r)
    (x y : Fin M → ℚ) :
    ∏ j, eqv (x j) (y j) =
      ∑ T ∈ (univ : Finset (Finset (Fin M))).filter (fun T => T.card ≤ r),
        (-1) ^ T.card * (rowMix T (Aval W (kappa Q R) R x y - Dval W x y) (Aval W (kappa Q R) R x y)).det := by
  obtain ⟨V, hdim, hV⟩ := exists_row_space W R x y
  rw [← det_Dval W]
  exact det_eq_sum_rowMix hV (hdim.trans hr)

end Wires

end OnePigeonhole
