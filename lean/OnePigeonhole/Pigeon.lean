import OnePigeonhole.Helpers
import OnePigeonhole.Trade

/-!
# The pigeonhole on the digits

Section 3 of `papers/one-pigeonhole/proof.tex`, from equation (2) to equation (3). The polynomials `Pz Q` have the variables
`z_1, ..., z_Q`, and `zMono E` is `z ^ E = ∏_{t ∈ E} z_t`.

* `gamE κ R T i E`: the number of the exchange `E` in the row `i` of `⟨T⟩`.
* `coefT`, `Tz`: the matrix `⟨T⟩_z`. `Tz_apply`: its entry `(i, j)` is the entry of `⟨T⟩` times `z ^ E_ij`. `det_rowMix_eq_eval`: at `z = 1` it is `⟨T⟩`.
* `coefH`, `Hz`: the matrix `H_{T,t,S}`, which keeps in the rows of `S` the entries with `t ∈ E_ij`, and in the other rows the entries with `t ∉ E_ij`. `det_Tz_eq_sum_Hz`: `det ⟨T⟩_z = ∑ S, det H_{T,t,S}`.
* `sum_exp_le`: every monomial `z ^ c` of `det ⟨T⟩_z` has `∑ t, c t ≤ M * R + |T| * Q`.
* `sumT J t f`: the sum `Sum_t f` of the coefficients of `f` at the monomials `z ^ c` with `c t < J`, and `c s ≥ J` for `s < t`.
* `sum_sumT_eq_eval`: if all monomials of `f` have total degree below `Q * J`, then the sum of `Sum_t f` over `t` is the sum of all coefficients of `f`.
* `sumT_eq_grid`: `Sum_t f` is a fixed combination of values of `f` on the grid, when the exponents of `f` are at most `M`.
* `prod_eqv_eq_sum_sumT`: equation (3). `prod_eqv_eq_grid`: equation (3) on the grid.
-/

set_option linter.unusedSectionVars false

namespace OnePigeonhole

open Finset TransposeBase MvPolynomial

variable {Q L h M : ℕ}

/-! ### The formal variables -/

/-- Polynomials in `z_1, ..., z_Q`. -/
abbrev Pz (Q : ℕ) := MvPolynomial (Fin Q) ℚ

/-- `z ^ E = ∏_{t ∈ E} z_t`. -/
noncomputable abbrev zMono (E : Finset (Fin Q)) : Pz Q := yMono E

/-- The number of the exchange `E` in the row `i`: `κ_{|E|}` if `|E| ≤ R`, minus `1` if `i ∈ T` and `E = [Q]`. A row is a
wire here, and a corner of a cube in `Cube.lean`. -/
def gamE {ι : Type*} [DecidableEq ι] (κ : ℕ → ℚ) (R : ℕ) (T : Finset ι) (i : ι) (E : Finset (Fin Q)) : ℚ :=
  (if E.card ≤ R then κ E.card else 0) - (if i ∈ T ∧ E = univ then 1 else 0)

/-- A nonzero number has `|E| ≤ R` outside `T`, and `|E| ≤ R` or `E = [Q]` in `T`. -/
theorem card_le_of_gamE_ne_zero {ι : Type*} [DecidableEq ι] {κ : ℕ → ℚ} {R : ℕ} {T : Finset ι} {i : ι}
    {E : Finset (Fin Q)} (hg : gamE κ R T i E ≠ 0) : E.card ≤ R + if i ∈ T then Q else 0 := by
  by_contra hc
  apply hg
  have h1 : ¬ E.card ≤ R := fun h2 => hc (h2.trans (Nat.le_add_right _ _))
  have h2 : ¬ (i ∈ T ∧ E = univ) := by
    rintro ⟨hi, rfl⟩
    apply hc
    simp [hi]
  simp [gamE, h1, h2]

/-- The coefficient of the entry `(i, j)` of `⟨T⟩_z`. -/
noncomputable def coefT (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (T : Finset (Fin M)) (i j : Fin M) : Pz Q :=
  if W.key i = W.key j then C (gamE κ R T i (W.Eij i j)) * zMono (W.Eij i j) else 0

/-- The matrix `⟨T⟩_z`. -/
noncomputable def Tz (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (T : Finset (Fin M)) (x y : Fin M → ℚ) :
    Matrix (Fin M) (Fin M) (Pz Q) :=
  Matrix.of fun i j => coefT W κ R T i j * C (eqv (x i) (y j))

/-- The coefficient `γ_ij` of the entry `(i, j)` of `H_{T,t,S}`: the rows in `S` keep the entries with `t ∈ E_ij`, and the
other rows the entries with `t ∉ E_ij`. It does not depend on the bits. -/
noncomputable def coefH (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (T : Finset (Fin M)) (t : Fin Q)
    (S : Finset (Fin M)) (i j : Fin M) : Pz Q :=
  if t ∈ W.Eij i j ↔ i ∈ S then coefT W κ R T i j else 0

/-- The matrix `H_{T,t,S}`. -/
noncomputable def Hz (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (T : Finset (Fin M)) (t : Fin Q)
    (S : Finset (Fin M)) (x y : Fin M → ℚ) : Matrix (Fin M) (Fin M) (Pz Q) :=
  Matrix.of fun i j => coefH W κ R T t S i j * C (eqv (x i) (y j))

/-- The sets of fewer than `J` rows. So `|T| ≤ r` is `T ∈ fewW M (r + 1)`. -/
def fewW (M J : ℕ) : Finset (Finset (Fin M)) := univ.filter fun S => S.card < J

theorem mem_fewW {J : ℕ} {S : Finset (Fin M)} : S ∈ fewW M J ↔ S.card < J := by simp [fewW]

theorem filter_card_le_eq_fewW (M r : ℕ) :
    (univ : Finset (Finset (Fin M))).filter (fun T => T.card ≤ r) = fewW M (r + 1) := by
  ext T
  simp [fewW]

/-! ### The value at `z = 1` -/

theorem Bmat_apply (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (i j : Fin M) :
    Bmat W κ R i j =
      if W.key i = W.key j then (if (W.Eij i j).card ≤ R then κ (W.Eij i j).card else 0) else 0 := by
  classical
  simp only [Bmat, Matrix.of_apply, W.tau_c_eq_d_iff_Eij]
  by_cases hk : W.key i = W.key j
  · simp only [hk, true_and, if_true]
    rw [Finset.sum_ite_eq']
    simp only [mem_shortSets]
  · simp [hk]

/-- An entry of `⟨T⟩_z` at `z = 1` is the entry of `⟨T⟩`. -/
theorem eval_one_Tz_apply (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (T : Finset (Fin M)) (x y : Fin M → ℚ)
    (i j : Fin M) :
    eval (fun _ => (1 : ℚ)) (Tz W κ R T x y i j) =
      rowMix T (Aval W κ R x y - Dval W x y) (Aval W κ R x y) i j := by
  classical
  have hiff : tau univ (W.c i) = W.d j ↔ W.key i = W.key j ∧ univ = W.Eij i j :=
    W.tau_c_eq_d_iff_Eij univ i j
  have hone : eval (fun _ : Fin Q => (1 : ℚ)) (zMono (W.Eij i j)) = 1 := eval_yMono _
  by_cases hk : W.key i = W.key j
  · by_cases hT : i ∈ T
    · simp only [Tz, Matrix.of_apply, coefT, hk, if_true, map_mul, eval_C, hone, rowMix_apply, hT,
        Matrix.sub_apply, Aval, Dval, Bmat_apply, hiff, true_and, gamE, mul_one]
      by_cases hE : W.Eij i j = univ
      · simp only [hE, if_true]
        ring
      · have hE' : ¬ univ = W.Eij i j := fun h => hE h.symm
        simp only [hE, hE', if_false]
        ring
    · simp [Tz, coefT, hk, hone, hT, Aval, Bmat_apply, gamE]
  · by_cases hT : i ∈ T
    · simp [Tz, coefT, hk, hT, Aval, Dval, Bmat_apply, hiff]
    · simp [Tz, coefT, hk, hT, Aval, Bmat_apply]

/-- The entry `(i, j)` of `⟨T⟩_z` is the entry of `⟨T⟩` times `z ^ E_ij`. -/
theorem Tz_apply (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (T : Finset (Fin M)) (x y : Fin M → ℚ) (i j : Fin M) :
    Tz W κ R T x y i j =
      C (rowMix T (Aval W κ R x y - Dval W x y) (Aval W κ R x y) i j) * zMono (W.Eij i j) := by
  rw [← eval_one_Tz_apply]
  have hone : eval (fun _ : Fin Q => (1 : ℚ)) (zMono (W.Eij i j)) = 1 := eval_yMono _
  by_cases hk : W.key i = W.key j
  · simp only [Tz, Matrix.of_apply, coefT, hk, if_true, map_mul, eval_C, hone, mul_one]
    ring
  · simp [Tz, coefT, hk]

/-- `det ⟨T⟩` is the value of `det ⟨T⟩_z` at `z = 1`. -/
theorem det_rowMix_eq_eval (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (T : Finset (Fin M)) (x y : Fin M → ℚ) :
    (rowMix T (Aval W κ R x y - Dval W x y) (Aval W κ R x y)).det =
      eval (fun _ => (1 : ℚ)) (Tz W κ R T x y).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  exact (eval_one_Tz_apply W κ R T x y i j).symm

/-! ### The split at a digit -/

/-- `det ⟨T⟩_z = ∑ S, det H_{T,t,S}`, by linearity in the rows. -/
theorem det_Tz_eq_sum_Hz (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (T : Finset (Fin M)) (t : Fin Q)
    (x y : Fin M → ℚ) :
    (Tz W κ R T x y).det = ∑ S : Finset (Fin M), (Hz W κ R T t S x y).det := by
  classical
  let Av : Matrix (Fin M) (Fin M) (Pz Q) :=
    Matrix.of fun i j => if t ∈ W.Eij i j then Tz W κ R T x y i j else 0
  let An : Matrix (Fin M) (Fin M) (Pz Q) :=
    Matrix.of fun i j => if t ∈ W.Eij i j then 0 else Tz W κ R T x y i j
  have h1 : Tz W κ R T x y = Av + An := by
    ext1 i j
    simp only [Av, An, Matrix.add_apply, Matrix.of_apply]
    split_ifs <;> simp
  rw [h1, det_add_eq_sum_rowMix]
  refine Finset.sum_congr rfl fun S _ => ?_
  congr 1
  ext1 i j
  by_cases hi : i ∈ S <;> by_cases ht : t ∈ W.Eij i j <;>
    simp [Av, An, Hz, Tz, coefH, hi, ht]

/-- `z_t ^ |S|` divides `det H_{T,t,S}`: every monomial has `a_t ≥ |S|`. -/
theorem pow_card_dvd_det_Hz (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (T : Finset (Fin M)) (t : Fin Q)
    (S : Finset (Fin M)) (x y : Fin M → ℚ) :
    (MvPolynomial.X t : Pz Q) ^ S.card ∣ (Hz W κ R T t S x y).det := by
  refine pow_card_dvd_det _ S _ fun i hi j => ?_
  simp only [Hz, Matrix.of_apply, coefH, coefT]
  refine Dvd.dvd.mul_right ?_ _
  split_ifs with h1 h2
  · exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (h1.mpr hi)) _
  · exact dvd_zero _
  · exact dvd_zero _

/-! ### Degrees -/

theorem totalDegree_zMono_le (E : Finset (Fin Q)) : (zMono E : Pz Q).totalDegree ≤ E.card :=
  totalDegree_yMono_le E.card (by simp [reads])

theorem totalDegree_coefT_le (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (T : Finset (Fin M)) (i j : Fin M) :
    (coefT W κ R T i j).totalDegree ≤ R + if i ∈ T then Q else 0 := by
  unfold coefT
  by_cases hk : W.key i = W.key j
  · rw [if_pos hk]
    by_cases hg : gamE κ R T i (W.Eij i j) = 0
    · simp [hg]
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      exact (totalDegree_zMono_le _).trans (card_le_of_gamE_ne_zero hg)
  · simp [hk]

/-- **The bound on the digits exchanged.** Every monomial `z ^ c` of `det ⟨T⟩_z` has `∑ t, c t ≤ M * R + |T| * Q`. -/
theorem sum_exp_le (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (T : Finset (Fin M)) (x y : Fin M → ℚ)
    {c : Fin Q →₀ ℕ} (hc : c ∈ (Tz W κ R T x y).det.support) :
    ∑ t, c t ≤ M * R + T.card * Q := by
  classical
  have h1 := le_totalDegree hc
  rw [Finsupp.sum_fintype _ _ (by simp)] at h1
  refine h1.trans ((totalDegree_det_le _ (fun i => R + if i ∈ T then Q else 0) fun i j => ?_).trans ?_)
  · simp only [Tz, Matrix.of_apply]
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, add_zero]
    exact totalDegree_coefT_le W κ R T i j
  · simp [Finset.sum_add_distrib, Finset.sum_ite_mem]

theorem degreeOf_coefT_le (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (T : Finset (Fin M)) (v : Fin Q)
    (i j : Fin M) : degreeOf v (coefT W κ R T i j) ≤ 1 := by
  unfold coefT
  split_ifs
  · exact degreeOf_C_mul_le' v _ (degreeOf_yMono_le' v _)
  · simp

theorem degreeOf_coefH_le (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (T : Finset (Fin M)) (t v : Fin Q)
    (S : Finset (Fin M)) (i j : Fin M) : degreeOf v (coefH W κ R T t S i j) ≤ 1 := by
  unfold coefH
  split_ifs
  · exact degreeOf_coefT_le W κ R T v i j
  · simp

/-- **The exponents.** The exponents of `det H_{T,t,S}` are at most `M`. -/
theorem det_Hz_exp_le (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (T : Finset (Fin M)) (t : Fin Q)
    (S : Finset (Fin M)) (x y : Fin M → ℚ) :
    ∀ c ∈ (Hz W κ R T t S x y).det.support, ∀ v, c v ≤ M := fun c hc v => by
  have h1 := degreeOf_det_le (Hz W κ R T t S x y) v fun i j =>
    OnePigeonhole.degreeOf_mul_C_le v _ (degreeOf_coefH_le W κ R T t v S i j)
  rw [Fintype.card_fin] at h1
  exact (degreeOf_le_iff.mp h1) c hc

/-! ### The sum `Sum_t` -/

/-- The monomial `z ^ c` is counted for the digit `t`: `c t < J`, and `c s ≥ J` for `s < t`. -/
def LowFirst (J : ℕ) (t : Fin Q) (c : Fin Q →₀ ℕ) : Prop := c t < J ∧ ∀ s, s < t → J ≤ c s

instance (J : ℕ) (t : Fin Q) (c : Fin Q →₀ ℕ) : Decidable (LowFirst J t c) := by
  unfold LowFirst
  infer_instance

/-- `Sum_t f`: the sum of the coefficients of `f` at the monomials counted for the digit `t`. -/
noncomputable def sumT (J : ℕ) (t : Fin Q) (f : Pz Q) : ℚ :=
  ∑ c ∈ f.support, if LowFirst J t c then coeff c f else 0

/-- A monomial of total degree below `Q * J` has a digit with an exponent below `J`, so it is counted for some digit. -/
theorem exists_lowFirst {J : ℕ} {c : Fin Q →₀ ℕ} (hc : ∑ t, c t < Q * J) : ∃ t, LowFirst J t c := by
  classical
  have hex : (univ.filter fun t : Fin Q => c t < J).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hne
    have : Q * J ≤ ∑ t, c t := by
      calc Q * J = ∑ _t : Fin Q, J := by simp
        _ ≤ _ := Finset.sum_le_sum fun t _ => not_lt.mp (hne (Finset.mem_univ t))
    omega
  obtain ⟨t, ht, hmin⟩ := Finset.exists_min_image _ id hex
  refine ⟨t, (Finset.mem_filter.mp ht).2, fun s hs => ?_⟩
  by_contra hlt
  have hle : t ≤ s := hmin s (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_le.mp hlt⟩)
  exact absurd hs (not_lt.mpr hle)

/-- A monomial is counted for at most one digit. -/
theorem lowFirst_unique {J : ℕ} {c : Fin Q →₀ ℕ} {s t : Fin Q} (hs : LowFirst J s c) (ht : LowFirst J t c) :
    s = t := by
  rcases lt_trichotomy s t with h | h | h
  · exact absurd hs.1 (not_lt.mpr (ht.2 s h))
  · exact h
  · exact absurd ht.1 (not_lt.mpr (hs.2 t h))

/-- If all monomials of `f` have total degree below `Q * J`, then the sum of `Sum_t f` over `t` is the sum of all
coefficients of `f`. -/
theorem sum_sumT_eq_eval {J : ℕ} {f : Pz Q} (hf : ∀ c ∈ f.support, ∑ t, c t < Q * J) :
    ∑ t, sumT J t f = eval (fun _ => (1 : ℚ)) f := by
  classical
  unfold sumT
  rw [Finset.sum_comm, eval_eq']
  refine Finset.sum_congr rfl fun c hc => ?_
  obtain ⟨t, ht⟩ := exists_lowFirst (hf c hc)
  rw [Finset.sum_eq_single t]
  · simp [ht]
  · intro s _ hs
    rw [if_neg]
    exact fun h => hs (lowFirst_unique h ht)
  · simp

theorem sumT_eq_of_subset {J : ℕ} {t : Fin Q} {f : Pz Q} {s : Finset (Fin Q →₀ ℕ)} (hs : f.support ⊆ s) :
    sumT J t f = ∑ c ∈ s, if LowFirst J t c then coeff c f else 0 := by
  refine Finset.sum_subset hs fun c _ hc => ?_
  rw [notMem_support_iff.mp hc, ite_self]

theorem sumT_zero (J : ℕ) (t : Fin Q) : sumT J t (0 : Pz Q) = 0 := by
  simp [sumT]

theorem sumT_add (J : ℕ) (t : Fin Q) (f g : Pz Q) : sumT J t (f + g) = sumT J t f + sumT J t g := by
  classical
  rw [sumT_eq_of_subset (s := f.support ∪ g.support) support_add,
    sumT_eq_of_subset (f := f) (s := f.support ∪ g.support) subset_union_left,
    sumT_eq_of_subset (f := g) (s := f.support ∪ g.support) subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [coeff_add]
  split_ifs <;> simp

/-- `Sum_t` is linear. -/
theorem sumT_sum {ι : Type*} (J : ℕ) (t : Fin Q) (s : Finset ι) (f : ι → Pz Q) :
    sumT J t (∑ i ∈ s, f i) = ∑ i ∈ s, sumT J t (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sumT_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, sumT_add, ih]

/-- If `z_t ^ J` divides `f`, then `Sum_t f = 0`. -/
theorem sumT_eq_zero_of_dvd {J : ℕ} {t : Fin Q} {f : Pz Q} (hd : (MvPolynomial.X t : Pz Q) ^ J ∣ f) :
    sumT J t f = 0 := by
  obtain ⟨q, rfl⟩ := hd
  refine Finset.sum_eq_zero fun c _ => ?_
  split_ifs with hc
  · rw [X_pow_eq_monomial, coeff_monomial_mul', if_neg]
    intro hle
    have h1 := hle t
    have h2 := hc.1
    simp at h1
    omega
  · rfl

/-- `Sum_t f` is the sum over `digitBox`, when the exponents of `f` are at most `M`. -/
theorem sumT_eq_box {J : ℕ} {t : Fin Q} (f : Pz Q) (hf : ∀ c ∈ f.support, ∀ i, c i ≤ M) :
    sumT J t f = ∑ a ∈ digitBox M J t, coeff (expOf a) f := by
  classical
  unfold sumT
  rw [← Finset.sum_filter, ← Finset.sum_image (f := fun c => coeff c f) (g := expOf)
    (fun a _ b _ he => expOf_inj he)]
  apply Finset.sum_subset
  · intro c hc
    obtain ⟨hs, hl⟩ := Finset.mem_filter.mp hc
    refine Finset.mem_image.mpr ⟨fun i => ⟨c i, Nat.lt_succ_of_le (hf c hs i)⟩, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl.1, fun s hs' => hl.2 s hs'⟩
    · ext i
      rfl
  · intro c hc hnot
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
    by_contra hne
    apply hnot
    have hfirst := (Finset.mem_filter.mp ha).2
    exact Finset.mem_filter.mpr ⟨mem_support_iff.mpr hne, hfirst.1, fun s hs' => hfirst.2 s hs'⟩

/-- `Sum_t f` is a fixed combination of values of `f` on the grid, when the exponents of `f` are at most `M`. -/
theorem sumT_eq_grid {J : ℕ} {t : Fin Q} (f : Pz Q) (hf : ∀ c ∈ f.support, ∀ i, c i ≤ M) :
    sumT J t f = ∑ p : Fin Q → Fin (M + 1),
      digitWeight (k := ℚ) M J t p * eval (fun i => gridPt (k := ℚ) M (p i)) f := by
  rw [sumT_eq_box f hf, sum_coeff_digitBox J t f hf]

/-! ### The identities -/

/-- For `|T| ≤ r`: `det ⟨T⟩ = ∑ t, ∑_{|S| < J} Sum_t (det H_{T,t,S})`. -/
theorem det_rowMix_eq_sum (W : Wires Q L h M) (κ : ℕ → ℚ) {R r J : ℕ} (hJ : M * R + r * Q < Q * J)
    {T : Finset (Fin M)} (hT : T.card ≤ r) (x y : Fin M → ℚ) :
    (rowMix T (Aval W κ R x y - Dval W x y) (Aval W κ R x y)).det =
      ∑ t, ∑ S ∈ fewW M J, sumT J t (Hz W κ R T t S x y).det := by
  classical
  have hdeg : ∀ c ∈ (Tz W κ R T x y).det.support, ∑ t, c t < Q * J := by
    intro c hc
    have h1 := sum_exp_le W κ R T x y hc
    have h2 : T.card * Q ≤ r * Q := Nat.mul_le_mul_right Q hT
    omega
  rw [det_rowMix_eq_eval, ← sum_sumT_eq_eval hdeg]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [det_Tz_eq_sum_Hz W κ R T t x y, sumT_sum]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun S _ hS => ?_
  have hS' : J ≤ S.card := not_lt.mp fun h => hS (mem_fewW.mpr h)
  exact sumT_eq_zero_of_dvd ((pow_dvd_pow _ hS').trans (pow_card_dvd_det_Hz W κ R T t S x y))

/-- **Equation (3).** `∏ [x_j = y_j] = ∑_{|T| ≤ r} (-1) ^ |T| ∑ t, ∑_{|S| < J} Sum_t (det H_{T,t,S})`, when
`2 * rankBound Q L h R ≤ r` and `M * R + r * Q < Q * J`. It holds for all rationals `x`, `y`. -/
theorem prod_eqv_eq_sum_sumT (W : Wires Q L h M) {R r J : ℕ} (hr : 2 * rankBound Q L h R ≤ r)
    (hJ : M * R + r * Q < Q * J) (x y : Fin M → ℚ) :
    ∏ j, eqv (x j) (y j) =
      ∑ T ∈ fewW M (r + 1), (-1) ^ T.card *
        ∑ t, ∑ S ∈ fewW M J, sumT J t (Hz W (kappa Q R) R T t S x y).det := by
  rw [prod_eqv_eq_sum_rowMix W hr x y, filter_card_le_eq_fewW]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [det_rowMix_eq_sum W _ hJ (Nat.lt_succ_iff.mp (mem_fewW.mp hT)) x y]

/-- **Equation (3) on the grid.** The weights `digitWeight` depend only on `M`, `J`, `t` and the grid point. -/
theorem prod_eqv_eq_grid (W : Wires Q L h M) {R r J : ℕ} (hr : 2 * rankBound Q L h R ≤ r)
    (hJ : M * R + r * Q < Q * J) (x y : Fin M → ℚ) :
    ∏ j, eqv (x j) (y j) =
      ∑ T ∈ fewW M (r + 1), (-1) ^ T.card *
        ∑ t, ∑ p : Fin Q → Fin (M + 1), ∑ S ∈ fewW M J,
          digitWeight (k := ℚ) M J t p *
            eval (fun i => gridPt (k := ℚ) M (p i)) (Hz W (kappa Q R) R T t S x y).det := by
  rw [prod_eqv_eq_sum_sumT W hr hJ x y]
  refine Finset.sum_congr rfl fun T _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  simp_rw [sumT_eq_grid _ (det_Hz_exp_le W _ R T t _ x y)]
  rw [Finset.sum_comm]

end OnePigeonhole
