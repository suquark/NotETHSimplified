import Mathlib

/-! **Limits of each ingredient.** Lower bounds from the section of the same name in the note:
the degree bound (Proposition `exact`), the rank of the error on one orbit (Proposition `ball`),
(Proposition `far`). This file imports only Mathlib. -/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace TransposeBase.Exact
open scoped BigOperators
open Finset

section Exact
open MvPolynomial
variable {F : Type*} [Field F] [Infinite F] {Q : ℕ}

/-- Setting `y_t=0`, as a substitution. -/
noncomputable def killVar (t : Fin Q) (D : MvPolynomial (Fin Q) F) : MvPolynomial (Fin Q) F :=
  bind₁ (fun i => if i = t then (0 : MvPolynomial (Fin Q) F) else X i) D

/-- Setting `y_t=0` keeps the coefficient of a monomial that does not contain `y_t`. -/
theorem coeff_killVar (t : Fin Q) (m : Fin Q →₀ ℕ) (hm : m t = 0) (D : MvPolynomial (Fin Q) F) :
    coeff m (killVar t D) = coeff m D := by
  classical
  unfold killVar
  induction D using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [bind₁_monomial]
    by_cases hd : d t = 0
    · have : (∏ i ∈ d.support, (if i = t then (0 : MvPolynomial (Fin Q) F) else X i) ^ d i)
          = ∏ i ∈ d.support, (X i : MvPolynomial (Fin Q) F) ^ d i := by
        apply Finset.prod_congr rfl
        intro i hi
        have : i ≠ t := by
          rintro rfl
          exact (Finsupp.mem_support_iff.mp hi) hd
        simp [this]
      rw [this, MvPolynomial.monomial_eq (s := d) (a := c), Finsupp.prod]
    · have ht : t ∈ d.support := Finsupp.mem_support_iff.mpr hd
      have h0 : (∏ i ∈ d.support, (if i = t then (0 : MvPolynomial (Fin Q) F) else X i) ^ d i)
          = 0 := by
        apply Finset.prod_eq_zero ht
        simp [hd]
      have hne : d ≠ m := by
        rintro rfl
        exact hd hm
      rw [h0, mul_zero, coeff_zero, coeff_monomial, if_neg hne]
  | add p q hp hq => rw [map_add, coeff_add, hp, hq, coeff_add]

theorem eval_killVar (t : Fin Q) (y : Fin Q → F) (D : MvPolynomial (Fin Q) F) :
    eval y (killVar t D) = eval (fun i => if i = t then 0 else y i) D := by
  unfold killVar
  induction D using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, bind₁_X_right, eval_X]
    by_cases h : i = t <;> simp [h]

/-- If `D` vanishes on `y_t=0`, then each monomial of `D` contains `y_t`. -/
theorem one_le_of_mem_support (D : MvPolynomial (Fin Q) F)
    (h0 : ∀ t (y : Fin Q → F), y t = 0 → eval y D = 0)
    {m : Fin Q →₀ ℕ} (hm : m ∈ D.support) (t : Fin Q) : 1 ≤ m t := by
  by_contra hlt
  have hmt : m t = 0 := by omega
  have hz : killVar t D = 0 := by
    apply MvPolynomial.funext
    intro y
    rw [eval_killVar, h0 t _ (by simp), map_zero]
  have := coeff_killVar t m hmt D
  rw [hz, coeff_zero] at this
  exact (mem_support_iff.mp hm) this.symm

/-- **The difference argument of Proposition `exact`.** A polynomial `D` with `D(1,…,1)=1` that
vanishes on every hyperplane `y_t=0` has total degree at least `Q`. -/
theorem totalDegree_ge_of_vanishing (D : MvPolynomial (Fin Q) F)
    (h1 : eval (fun _ => (1 : F)) D = 1)
    (h0 : ∀ t (y : Fin Q → F), y t = 0 → eval y D = 0) :
    Q ≤ D.totalDegree := by
  have hne : D ≠ 0 := by
    rintro rfl
    simp at h1
  obtain ⟨m, hm⟩ := (support_nonempty.mpr hne)
  refine le_trans ?_ (le_totalDegree hm)
  rw [Finsupp.sum_fintype _ _ (by simp)]
  calc Q = ∑ _t : Fin Q, 1 := by simp
    _ ≤ ∑ t, m t := Finset.sum_le_sum (fun t _ => one_le_of_mem_support D h0 hm t)

/-- **Proposition `exact`.** `Z` is a family of polynomials in `y` indexed by the bits `X`. If
`Z(1,X)` is the entry `X e`, and on each hyperplane `y_t=0` the value of `Z` does not depend on
`X e`, then for each setting of the other entries one of the two polynomials has total degree at
least `Q`. -/
theorem exact_degree {ι : Type*} [DecidableEq ι] (Z : (ι → Bool) → MvPolynomial (Fin Q) F) (e : ι)
    (h1 : ∀ X, eval (fun _ => (1 : F)) (Z X) = if X e then 1 else 0)
    (h0 : ∀ (t : Fin Q) (y : Fin Q → F), y t = 0 → ∀ (X : ι → Bool) (b : Bool),
      eval y (Z (Function.update X e b)) = eval y (Z X)) (X : ι → Bool) :
    Q ≤ (Z (Function.update X e true)).totalDegree ∨
      Q ≤ (Z (Function.update X e false)).totalDegree := by
  have key := totalDegree_ge_of_vanishing
    (Z (Function.update X e true) - Z (Function.update X e false))
    (by simp [h1]) (by
      intro t y hy
      simp [h0 t y hy])
  have := key.trans (totalDegree_sub _ _)
  rcases le_max_iff.mp this with h | h
  · exact Or.inl h
  · exact Or.inr h

end Exact

section RankTools
variable {𝕜 : Type*} [Field 𝕜]

theorem rank_add_le' {m n : Type*} [Fintype m] [Fintype n] (A B : Matrix m n 𝕜) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  refine le_trans (Submodule.finrank_mono (LinearMap.range_add_le _ _)) ?_
  exact Submodule.finrank_add_le_finrank_add_finrank _ _

/-- The rank is subadditive over finite sums. -/
theorem rank_sum_le {m n J : Type*} [Fintype m] [Fintype n] (s : Finset J)
    (A : J → Matrix m n 𝕜) : (∑ j ∈ s, A j).rank ≤ ∑ j ∈ s, (A j).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (rank_add_le' _ _).trans (by omega)

/-- A matrix that factors through an index type `L` has rank at most the size of `L`. -/
theorem rank_le_of_factor {m n L : Type*} [Fintype m] [Fintype n] [Fintype L]
    (M : Matrix m n 𝕜) (U : m → L → 𝕜) (V : L → n → 𝕜)
    (h : ∀ i j, M i j = ∑ k, U i k * V k j) : M.rank ≤ Fintype.card L := by
  have : M = Matrix.of U * Matrix.of V := by
    ext i j
    simp [Matrix.mul_apply, h]
  rw [this]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)

end RankTools

section Ball

/-- The number of coordinates of a bit vector equal to `true`. -/
def wt {α : Type*} [Fintype α] (a : α → Bool) : ℕ := (univ.filter (fun i => a i = true)).card

/-- The antipodal map of the cube. -/
def antipode {α : Type*} (a : α → Bool) : α → Bool := fun i => !a i

/-- The number of bit vectors of a given weight. -/
theorem card_wt_eq {α : Type*} [Fintype α] [DecidableEq α] (k : ℕ) :
    (univ.filter (fun a : α → Bool => wt a = k)).card = (Fintype.card α).choose k := by
  rw [← Finset.card_univ, ← Finset.card_powersetCard k (univ : Finset α)]
  apply Finset.card_bij (fun a _ => univ.filter (fun i => a i = true))
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    simp only [mem_powersetCard, subset_univ, true_and]
    exact ha
  · intro a _ b _ h
    funext i
    have := congrArg (fun S => i ∈ S) h
    simp only [mem_filter, mem_univ, true_and, eq_iff_iff] at this
    cases ha : a i <;> cases hb : b i <;> simp_all
  · intro S hS
    simp only [mem_powersetCard, subset_univ, true_and] at hS
    refine ⟨fun i => decide (i ∈ S), ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]
      simpa [wt] using hS
    · ext i
      simp

/-- A sum over the cube of a function of the weight. -/
theorem sum_wt {α R : Type*} [Fintype α] [DecidableEq α] [Semiring R] (φ : ℕ → R) :
    ∑ a : α → Bool, φ (wt a) = ∑ k ∈ range (Fintype.card α + 1),
      ((Fintype.card α).choose k : R) * φ k := by
  have hmaps : ∀ a ∈ (univ : Finset (α → Bool)), wt a ∈ range (Fintype.card α + 1) := by
    intro a _
    have : wt a ≤ Fintype.card α := Finset.card_le_univ _
    simp only [mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_congr rfl (g := fun _ => φ k)]
  · rw [Finset.sum_const, card_wt_eq, nsmul_eq_mul]
  · intro a ha
    rw [(mem_filter.mp ha).2]

variable {Q : ℕ}

end Ball

section CutRank
variable {W : Type*} [Fintype W] [DecidableEq W] {𝕜 : Type*} [Field 𝕜]

/-- The wires `w : W` carry one bit `X w` and one bit `Y w`. The bit `X w` lies in part `sx w`, and
the bit `Y w` lies in part `sy w`. `PartFun sx sy b f` says that `f` reads only the bits of
part `b`. -/
def PartFun (sx sy : W → Bool) (b : Bool) (f : (W → Bool) → (W → Bool) → 𝕜) : Prop :=
  ∀ X X' Y Y', (∀ w, sx w = b → X w = X' w) → (∀ w, sy w = b → Y w = Y' w) → f X Y = f X' Y'

/-- `p`: wires with `Y` in the first part (`true`) and `X` in the second. -/
def pCount (sx sy : W → Bool) : ℕ := (univ.filter (fun w => sy w = true ∧ sx w = false)).card

/-- `q`: wires with `Y` in the second part and `X` in the first. -/
def qCount (sx sy : W → Bool) : ℕ := (univ.filter (fun w => sy w = false ∧ sx w = true)).card

/-- With `e=|W|-p-q`, the bits counted here are `(q+e')+(q+e'')=2q+e`, written without `e`. -/
theorem count_identity (sx sy : W → Bool) :
    (univ.filter (fun w => sx w = true)).card + (univ.filter (fun w => sy w = false)).card
        + pCount sx sy = Fintype.card W + qCount sx sy := by
  unfold pCount qCount
  have hW : Fintype.card W = ∑ _w : W, 1 := by simp
  rw [hW]
  simp only [card_filter, ← sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  cases sx w <;> cases sy w <;> simp

/-- A product over a two-part partition has rank at most the number of `X` bits of the first part
and `Y` bits of the second part, as an exponent of `2`. -/
theorem rank_part_product_le (sx sy : W → Bool) (f g : (W → Bool) → (W → Bool) → 𝕜)
    (hf : PartFun sx sy true f) (hg : PartFun sx sy false g) :
    (Matrix.of fun X Y : W → Bool => f X Y * g X Y).rank ≤
      2 ^ ((univ.filter (fun w => sx w = true)).card + (univ.filter (fun w => sy w = false)).card) := by
  classical
  let L := ({w // sx w = true} → Bool) × ({w // sy w = false} → Bool)
  let extX : ({w // sx w = true} → Bool) → W → Bool :=
    fun k w => if h : sx w = true then k ⟨w, h⟩ else false
  let extY : ({w // sy w = false} → Bool) → W → Bool :=
    fun k w => if h : sy w = false then k ⟨w, h⟩ else false
  let U : (W → Bool) → L → 𝕜 := fun X k =>
    (if (fun w : {w // sx w = true} => X w.1) = k.1 then 1 else 0) * g X (extY k.2)
  let V : L → (W → Bool) → 𝕜 := fun k Y =>
    (if (fun w : {w // sy w = false} => Y w.1) = k.2 then 1 else 0) * f (extX k.1) Y
  have hcard : Fintype.card L =
      2 ^ ((univ.filter (fun w => sx w = true)).card + (univ.filter (fun w => sy w = false)).card) := by
    simp only [L, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype,
      pow_add]
  rw [← hcard]
  apply rank_le_of_factor _ U V
  intro X Y
  let k0 : L := (fun w => X w.1, fun w => Y w.1)
  rw [Finset.sum_eq_single k0]
  · have h1 : g X (extY k0.2) = g X Y := by
      apply hg
      · intro w _
        rfl
      · intro w hw
        simp [extY, k0, hw]
    have h2 : f (extX k0.1) Y = f X Y := by
      apply hf
      · intro w hw
        simp [extX, k0, hw]
      · intro w _
        rfl
    simp only [Matrix.of_apply, U, V, h1, h2, k0, if_true]
    simp [mul_comm]
  · intro k _ hk
    have : (fun w : {w // sx w = true} => X w.1) ≠ k.1 ∨
        (fun w : {w // sy w = false} => Y w.1) ≠ k.2 := by
      by_contra hcon
      push Not at hcon
      exact hk (Prod.ext hcon.1.symm hcon.2.symm)
    rcases this with h | h
    · simp [U, h]
    · simp [V, h]
  · simp

/-- **The rank of one product.** `2^(|W|-|p-q|)`. -/
theorem rank_product_le (sx sy : W → Bool) (f g : (W → Bool) → (W → Bool) → 𝕜)
    (hf : PartFun sx sy true f) (hg : PartFun sx sy false g) :
    (Matrix.of fun X Y : W → Bool => f X Y * g X Y).rank ≤
      2 ^ (Fintype.card W - ((pCount sx sy : ℤ) - qCount sx sy).natAbs) := by
  have h1 := rank_part_product_le sx sy f g hf hg
  have hf' : PartFun (fun w => !sx w) (fun w => !sy w) false f := by
    intro X X' Y Y' hX hY
    exact hf X X' Y Y' (fun w hw => hX w (by simp [hw])) (fun w hw => hY w (by simp [hw]))
  have hg' : PartFun (fun w => !sx w) (fun w => !sy w) true g := by
    intro X X' Y Y' hX hY
    exact hg X X' Y Y' (fun w hw => hX w (by simp [hw])) (fun w hw => hY w (by simp [hw]))
  have h2 := rank_part_product_le (fun w => !sx w) (fun w => !sy w) g f hg' hf'
  have hcomm : (Matrix.of fun X Y : W → Bool => g X Y * f X Y)
      = Matrix.of fun X Y : W → Bool => f X Y * g X Y := by
    ext X Y
    simp [mul_comm]
  rw [hcomm] at h2
  have c1 := count_identity sx sy
  have c2 := count_identity (fun w => !sx w) (fun w => !sy w)
  have hpq : pCount (fun w => !sx w) (fun w => !sy w) = qCount sx sy := by
    unfold pCount qCount
    congr 1
    ext w
    cases sx w <;> cases sy w <;> simp
  have hqp : qCount (fun w => !sx w) (fun w => !sy w) = pCount sx sy := by
    unfold pCount qCount
    congr 1
    ext w
    cases sx w <;> cases sy w <;> simp
  rw [hpq, hqp] at c2
  rcases le_total (pCount sx sy) (qCount sx sy) with hle | hle
  · refine h2.trans (Nat.pow_le_pow_right (by norm_num) ?_)
    omega
  · refine h1.trans (Nat.pow_le_pow_right (by norm_num) ?_)
    omega

/-- **The rank bound of Proposition `cut`, for several partitions.** The identity matrix between
the bits `X w` and `Y w` is a combination of products over two-part partitions; the `t`-th partition
carries `r t` products. Each product costs `2^(|W|-|p_t-q_t|)`. -/
theorem cut_rank_multi {T : Type*} [Fintype T] (sx sy : T → W → Bool) (r : T → ℕ)
    (a : ∀ t, Fin (r t) → 𝕜) (f g : ∀ t, Fin (r t) → (W → Bool) → (W → Bool) → 𝕜)
    (hf : ∀ t j, PartFun (sx t) (sy t) true (f t j))
    (hg : ∀ t j, PartFun (sx t) (sy t) false (g t j))
    (h : ∀ X Y : W → Bool, (if X = Y then (1 : 𝕜) else 0)
      = ∑ t, ∑ j, a t j * (f t j X Y * g t j X Y)) :
    2 ^ Fintype.card W ≤
      ∑ t, r t * 2 ^ (Fintype.card W - ((pCount (sx t) (sy t) : ℤ) - qCount (sx t) (sy t)).natAbs) := by
  have hM : (1 : Matrix (W → Bool) (W → Bool) 𝕜)
      = ∑ t, ∑ j, Matrix.of fun X Y : W → Bool => (a t j * f t j X Y) * g t j X Y := by
    ext X Y
    simp only [Matrix.one_apply, Matrix.sum_apply, Matrix.of_apply, h X Y, mul_assoc]
  have hrank : (1 : Matrix (W → Bool) (W → Bool) 𝕜).rank = 2 ^ Fintype.card W := by
    rw [Matrix.rank_one]
    simp
  rw [← hrank, hM]
  refine (rank_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro t _
  refine (rank_sum_le _ _).trans ?_
  calc _ ≤ ∑ _j : Fin (r t), 2 ^ (Fintype.card W
        - ((pCount (sx t) (sy t) : ℤ) - qCount (sx t) (sy t)).natAbs) := by
        apply Finset.sum_le_sum
        intro j _
        apply rank_product_le (sx t) (sy t)
        · intro X X' Y Y' hX hY
          simp only
          rw [hf t j X X' Y Y' hX hY]
        · exact hg t j
    _ = _ := by simp

end CutRank

section Rows
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝕜 : Type*} [Field 𝕜]

/-- The indicator `T(X,Y)=1[Y=Xᵀ]`. -/
def TT (𝕜 : Type*) [Zero 𝕜] [One 𝕜] (X Y : ι × ι → Bool) : 𝕜 :=
  open Classical in if ∀ ω, Y ω = X ω.swap then 1 else 0

/-- `f` reads only the entries of `X` and `Y` in rows of part `b` of the cut `c`. -/
def RowFun (c : ι → Bool) (b : Bool) (f : (ι × ι → Bool) → (ι × ι → Bool) → 𝕜) : Prop :=
  ∀ X X' Y Y', (∀ v, c v.1 = b → X v = X' v) → (∀ v, c v.1 = b → Y v = Y' v) → f X Y = f X' Y'

/-- `p`: wires `(u,w)` of `W` with `Y_(u,w)` in the first part and `X_(w,u)` in the second. -/
def pW (W : Finset (ι × ι)) (c : ι → Bool) : ℕ :=
  (W.filter (fun ω => c ω.1 = true ∧ c ω.2 = false)).card

/-- `q`: wires `(u,w)` of `W` with `Y_(u,w)` in the second part and `X_(w,u)` in the first. -/
def qW (W : Finset (ι × ι)) (c : ι → Bool) : ℕ :=
  (W.filter (fun ω => c ω.1 = false ∧ c ω.2 = true)).card

/-- Extend bits on `W` by `false`. -/
def extW (W : Finset (ι × ι)) (x : {ω // ω ∈ W} → Bool) (ω : ι × ι) : Bool :=
  if h : ω ∈ W then x ⟨ω, h⟩ else false

/-- **The bound for cuts of the rows.** Suppose `T` is a combination of products over the cuts
`c t`, with `r t` products for cut `t`. If `|p_t-q_t| ≥ D` for a wire set `W` and all `t`, then
`∑ r_t ≥ 2^D`. -/
theorem cut_rows {T : Type*} [Fintype T] (c : T → ι → Bool) (r : T → ℕ)
    (a : ∀ t, Fin (r t) → 𝕜) (f g : ∀ t, Fin (r t) → (ι × ι → Bool) → (ι × ι → Bool) → 𝕜)
    (hf : ∀ t j, RowFun (c t) true (f t j)) (hg : ∀ t j, RowFun (c t) false (g t j))
    (hT : ∀ X Y, TT 𝕜 X Y = ∑ t, ∑ j, a t j * (f t j X Y * g t j X Y))
    (W : Finset (ι × ι)) (D : ℕ)
    (hD : ∀ t, D ≤ ((pW W (c t) : ℤ) - qW W (c t)).natAbs) :
    2 ^ D ≤ ∑ t, r t := by
  classical
  let sx : T → {ω // ω ∈ W} → Bool := fun t ω => c t ω.1.2
  let sy : T → {ω // ω ∈ W} → Bool := fun t ω => c t ω.1.1
  have part : ∀ (F : (ι × ι → Bool) → (ι × ι → Bool) → 𝕜) (t : T) (b : Bool), RowFun (c t) b F →
      PartFun (sx t) (sy t) b (fun x y => F (fun v => extW W x v.swap) (extW W y)) := by
    intro F t b hF x x' y y' hx hy
    apply hF
    · intro v hv
      unfold extW
      by_cases h : v.swap ∈ W
      · simp only [dif_pos h]
        exact hx ⟨v.swap, h⟩ hv
      · simp only [dif_neg h]
    · intro v hv
      unfold extW
      by_cases h : v ∈ W
      · simp only [dif_pos h]
        exact hy ⟨v, h⟩ hv
      · simp only [dif_neg h]
  have hmain := cut_rank_multi sx sy r a
    (fun t j x y => f t j (fun v => extW W x v.swap) (extW W y))
    (fun t j x y => g t j (fun v => extW W x v.swap) (extW W y))
    (fun t j => part _ t true (hf t j)) (fun t j => part _ t false (hg t j))
    (by
      intro x y
      rw [← hT]
      unfold TT
      by_cases hxy : x = y
      · subst hxy
        simp
      · have : ¬ ∀ ω, extW W y ω = (fun v => extW W x v.swap) ω.swap := by
          intro hall
          apply hxy
          funext ω
          have := hall ω.1
          simp only [extW, Prod.swap_swap, ω.2, dif_pos] at this
          exact this.symm
        exact (if_neg hxy).trans (if_neg this).symm)
  have hcnt : ∀ (P : ι × ι → Prop) [DecidablePred P],
      (univ.filter (fun ω : {ω // ω ∈ W} => P ω.1)).card = (W.filter P).card := by
    intro P _
    simp only [card_filter]
    exact Finset.sum_coe_sort W (fun ω => if P ω then 1 else 0)
  have hp : ∀ t, pCount (sx t) (sy t) = pW W (c t) := fun t =>
    hcnt (fun ω => c t ω.1 = true ∧ c t ω.2 = false)
  have hq : ∀ t, qCount (sx t) (sy t) = qW W (c t) := fun t =>
    hcnt (fun ω => c t ω.1 = false ∧ c t ω.2 = true)
  simp only [hp, hq] at hmain
  set n := Fintype.card {ω // ω ∈ W} with hn
  have hbound : 2 ^ n ≤ (∑ t, r t) * 2 ^ (n - D) := by
    refine hmain.trans ?_
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro t _
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by have := hD t; omega))
  have hle : ∀ t, ((pW W (c t) : ℤ) - qW W (c t)).natAbs ≤ n := by
    intro t
    have h1 : pW W (c t) ≤ n := by
      rw [hn, ← hp]
      exact Finset.card_le_univ _
    have h2 : qW W (c t) ≤ n := by
      rw [hn, ← hq]
      exact Finset.card_le_univ _
    omega
  have hpos : (∑ t, r t) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hbound
    have : 0 < 2 ^ n := by positivity
    omega
  obtain ⟨t, ht, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos
  have hDn : D ≤ n := (hD t).trans (hle t)
  have h2 : 2 ^ D * 2 ^ (n - D) ≤ (∑ t, r t) * 2 ^ (n - D) := by
    rw [← pow_add, Nat.add_sub_cancel' hDn]
    exact hbound
  exact Nat.le_of_mul_le_mul_right h2 (by positivity)

end Rows

section Binomial

/-- A partial sum of `C(2n,k)(n-k)` for `n=m+1` telescopes. -/
theorem partial_choose (m j : ℕ) :
    ∑ k ∈ range (j + 1), (((2 * m + 2).choose k : ℕ) : ℤ) * ((m : ℤ) + 1 - k)
      = ((m : ℤ) + 1) * ((2 * m + 1).choose j : ℕ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : (((2 * m + 2).choose (j + 1) : ℕ) : ℤ)
        = ((2 * m + 1).choose j : ℕ) + ((2 * m + 1).choose (j + 1) : ℕ) := by
      have := Nat.choose_succ_succ (2 * m + 1) j
      exact_mod_cast this
    have h2 : (2 * (m : ℤ) + 2) * ((2 * m + 1).choose j : ℕ)
        = ((2 * m + 2).choose (j + 1) : ℕ) * ((j : ℤ) + 1) := by
      have := Nat.add_one_mul_choose_eq (2 * m + 1) j
      have h3 : (((2 * m + 1 + 1 : ℕ) : ℤ)) * ((2 * m + 1).choose j : ℕ)
          = ((2 * m + 1 + 1).choose (j + 1) : ℕ) * ((j + 1 : ℕ) : ℤ) := by
        exact_mod_cast this
      push_cast at h3
      linear_combination h3
    push_cast
    linear_combination (((m : ℤ) + 1)) * h1 + h2

/-- `∑_k C(2n,k)|n-k| = n C(2n,n)`. Dividing by `4^n` and multiplying by `2`, this says that the
expected absolute value of a sum of `2n` independent signs is `2n C(2n,n)/4^n`. -/
theorem sum_choose_abs (n : ℕ) :
    ∑ k ∈ range (2 * n + 1), (((2 * n).choose k : ℕ) : ℤ) * |(n : ℤ) - k|
      = (n : ℤ) * ((2 * n).choose n : ℕ) := by
  cases n with
  | zero => simp
  | succ m =>
    have hsplit : 2 * (m + 1) + 1 = (m + 2) + (m + 1) := by ring
    rw [hsplit, Finset.sum_range_add]
    have h2m : 2 * (m + 1) = 2 * m + 2 := by ring
    have hfirst : ∑ k ∈ range (m + 2), (((2 * (m + 1)).choose k : ℕ) : ℤ) * |((m + 1 : ℕ) : ℤ) - k|
        = ((m : ℤ) + 1) * ((2 * m + 1).choose (m + 1) : ℕ) := by
      rw [← partial_choose m (m + 1), h2m]
      apply Finset.sum_congr rfl
      intro k hk
      rw [mem_range] at hk
      have : |((m + 1 : ℕ) : ℤ) - k| = (m : ℤ) + 1 - k := by
        rw [abs_of_nonneg] <;> push_cast <;> omega
      rw [this]
    have hsecond : ∑ x ∈ range (m + 1), (((2 * (m + 1)).choose (m + 2 + x) : ℕ) : ℤ)
          * |((m + 1 : ℕ) : ℤ) - ((m + 2 + x : ℕ) : ℤ)|
        = ((m : ℤ) + 1) * ((2 * m + 1).choose m : ℕ) := by
      rw [← partial_choose m m, ← Finset.sum_range_reflect, h2m]
      apply Finset.sum_congr rfl
      intro k hk
      rw [mem_range] at hk
      have hk' : m + 1 - 1 - k + (m + 2) = 2 * m + 2 - k := by omega
      have hk2 : m + 2 + (m + 1 - 1 - k) = 2 * m + 2 - k := by omega
      rw [hk2, Nat.choose_symm (by omega)]
      have : |((m + 1 : ℕ) : ℤ) - ((2 * m + 2 - k : ℕ) : ℤ)| = (m : ℤ) + 1 - k := by
        rw [abs_sub_comm, abs_of_nonneg] <;> push_cast [Nat.cast_sub (show k ≤ 2 * m + 2 by omega)] <;> omega
      rw [this]
    rw [hfirst, hsecond, h2m]
    have hc : ((2 * m + 2).choose (m + 1) : ℕ) = (2 * m + 1).choose m + (2 * m + 1).choose (m + 1) :=
      Nat.choose_succ_succ _ _
    have hs : (2 * m + 1).choose (m + 1) = (2 * m + 1).choose m := Nat.choose_symm_half m
    rw [hc, hs]
    push_cast
    ring

/-- The central binomial bound, in squared form: `16^n ≤ 4n C(2n,n)²` for `n ≥ 1`. -/
theorem sixteen_pow_le (n : ℕ) (hn : 0 < n) :
    (16 : ℤ) ^ n ≤ 4 * n * (Nat.centralBinom n : ℤ) ^ 2 := by
  induction n, hn using Nat.le_induction with
  | base => simp [Nat.centralBinom]
  | succ n hn ih =>
    have h := Nat.succ_mul_centralBinom_succ n
    have h' : ((n : ℤ) + 1) * (Nat.centralBinom (n + 1) : ℤ)
        = 2 * (2 * (n : ℤ) + 1) * (Nat.centralBinom n : ℤ) := by
      exact_mod_cast h
    have hn0 : (0 : ℤ) < n := by exact_mod_cast hn
    set C : ℤ := (Nat.centralBinom n : ℤ)
    set C' : ℤ := (Nat.centralBinom (n + 1) : ℤ)
    have hkey : ((n : ℤ) + 1) * (4 * ((n : ℤ) + 1) * C' ^ 2)
        = 16 * (2 * (n : ℤ) + 1) ^ 2 * C ^ 2 := by
      linear_combination (4 * (((n : ℤ) + 1) * C' + 2 * (2 * (n : ℤ) + 1) * C)) * h'
    have h16 : (0 : ℤ) ≤ 16 ^ n := by positivity
    have hC : 0 ≤ C ^ 2 := by positivity
    have hgoal : ((n : ℤ) * ((n : ℤ) + 1)) * (16 ^ (n + 1) : ℤ)
        ≤ ((n : ℤ) * ((n : ℤ) + 1)) * (4 * ((n : ℤ) + 1) * C' ^ 2) := by
      have e1 : ((n : ℤ) * ((n : ℤ) + 1)) * (4 * ((n : ℤ) + 1) * C' ^ 2)
          = (n : ℤ) * (16 * (2 * (n : ℤ) + 1) ^ 2 * C ^ 2) := by
        rw [← hkey]
        ring
      rw [e1]
      have e2 : (n : ℤ) * (16 * (2 * (n : ℤ) + 1) ^ 2 * C ^ 2)
          = 4 * (2 * (n : ℤ) + 1) ^ 2 * (4 * n * C ^ 2) := by ring
      rw [e2, pow_succ]
      have e3 : 4 * (2 * (n : ℤ) + 1) ^ 2 * (16 ^ n) ≤ 4 * (2 * (n : ℤ) + 1) ^ 2 * (4 * n * C ^ 2) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      refine le_trans ?_ e3
      have e4 : ((n : ℤ) * ((n : ℤ) + 1)) * 16 ≤ 4 * (2 * (n : ℤ) + 1) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right e4 h16]
    have hpos : 0 < (n : ℤ) * ((n : ℤ) + 1) := by positivity
    exact_mod_cast le_of_mul_le_mul_left hgoal hpos

/-- `C(2Q,Q)/4^Q ≥ 1/(2√Q)`. -/
theorem central_ge (Q : ℕ) (hQ : 0 < Q) :
    1 / (2 * Real.sqrt Q) ≤ (Nat.centralBinom Q : ℝ) / 4 ^ Q := by
  have h := sixteen_pow_le Q hQ
  have hR : (16 : ℝ) ^ Q ≤ 4 * Q * (Nat.centralBinom Q : ℝ) ^ 2 := by exact_mod_cast h
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hs : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ'
  have h4 : (0 : ℝ) < 4 ^ Q := by positivity
  rw [div_le_div_iff₀ (by positivity) h4, one_mul]
  apply abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
  have e : ((4 : ℝ) ^ Q) ^ 2 = 16 ^ Q := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [e]
  have e2 : ((Nat.centralBinom Q : ℝ) * (2 * Real.sqrt Q)) ^ 2
      = 4 * Q * (Nat.centralBinom Q : ℝ) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hQ'.le]
    ring
  rw [e2]
  exact hR

end Binomial

section Signs

/-- The sign `c_t(u)` as an integer. -/
def sg (b : Bool) : ℤ := if b then 1 else -1

/-- `2(p-q)` is the sum of `c(u)-c(w)` over the wires `(u,w)`. -/
theorem two_pW_sub_qW {ι : Type*} [DecidableEq ι] (W : Finset (ι × ι)) (c : ι → Bool) :
    2 * ((pW W c : ℤ) - qW W c) = ∑ ω ∈ W, (sg (c ω.1) - sg (c ω.2)) := by
  unfold pW qW
  simp only [card_filter]
  push_cast
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  cases c ω.1 <;> cases c ω.2 <;> simp [sg]

/-- The sum `s(u)=∑_t c_t(u)`. -/
def sSum {ι : Type*} {T : Type*} [Fintype T] (c : T → ι → Bool) (u : ι) : ℤ := ∑ t, sg (c t u)

/-- The wires with `s(u)>s(w)`. -/
def upWires {ι : Type*} [Fintype ι] [DecidableEq ι] {T : Type*} [Fintype T]
    (c : T → ι → Bool) : Finset (ι × ι) :=
  univ.filter (fun ω => sSum c ω.2 < sSum c ω.1)

/-- The sum over the wires with `s(u)>s(w)` takes half of the pairs. -/
theorem two_sum_upWires {ι : Type*} [Fintype ι] [DecidableEq ι] {T : Type*} [Fintype T]
    (c : T → ι → Bool) :
    2 * ∑ ω ∈ upWires c, (sSum c ω.1 - sSum c ω.2) = ∑ ω : ι × ι, |sSum c ω.1 - sSum c ω.2| := by
  let F : ι × ι → ℤ := fun ω => if sSum c ω.2 < sSum c ω.1 then sSum c ω.1 - sSum c ω.2 else 0
  have h1 : ∑ ω ∈ upWires c, (sSum c ω.1 - sSum c ω.2) = ∑ ω, F ω := by
    unfold upWires
    rw [Finset.sum_filter]
  have h2 : ∑ ω : ι × ι, F ω.swap = ∑ ω, F ω := Equiv.sum_comp (Equiv.prodComm ι ι) F
  have h3 : ∑ ω : ι × ι, |sSum c ω.1 - sSum c ω.2| = ∑ ω, F ω + ∑ ω : ι × ι, F ω.swap := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    simp only [F, Prod.fst_swap, Prod.snd_swap]
    rcases lt_trichotomy (sSum c ω.1) (sSum c ω.2) with h | h | h
    · rw [abs_of_neg (by omega), if_neg (by omega), if_pos h]
      ring
    · simp [h]
    · rw [abs_of_pos (by omega), if_pos h, if_neg (by omega)]
      ring
  rw [h1, h3, h2]
  ring

/-- Summing `2(p_t-q_t)` over the cuts gives the sum of `s(u)-s(w)` over the wires. -/
theorem sum_two_pW_sub_qW {ι : Type*} [DecidableEq ι] {T : Type*} [Fintype T]
    (c : T → ι → Bool) (W : Finset (ι × ι)) :
    ∑ t, 2 * ((pW W (c t) : ℤ) - qW W (c t)) = ∑ ω ∈ W, (sSum c ω.1 - sSum c ω.2) := by
  simp only [two_pW_sub_qW, sSum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]

/-- The sum of the signs of a bit vector, in terms of its weight. -/
theorem sum_sg (Q : ℕ) (σ : Fin Q → Bool) : ∑ t, sg (σ t) = 2 * (wt σ : ℤ) - Q := by
  unfold wt
  rw [card_filter]
  push_cast
  rw [Finset.mul_sum]
  have : (Q : ℤ) = ∑ _t : Fin Q, 1 := by simp
  rw [this, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  cases σ t <;> simp [sg]

/-- The weight sum over two cubes, the discrete form of the law of `2Q` independent signs. -/
theorem sum_cube_abs (Q : ℕ) :
    ∑ σ : Fin Q → Bool, ∑ σ' : Fin Q → Bool, |(wt σ : ℤ) - wt σ'|
      = (Q : ℤ) * ((2 * Q).choose Q : ℕ) := by
  have hanti : ∀ σ' : Fin Q → Bool, wt (antipode σ') + wt σ' = Q := by
    intro σ'
    have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin Q)))
      (fun i => σ' i = false)
    simp only [card_univ, Fintype.card_fin] at h
    have e1 : wt (antipode σ') = (univ.filter (fun i => σ' i = false)).card := by
      unfold wt antipode
      congr 1
      ext i
      cases σ' i <;> simp
    have e2 : wt σ' = (univ.filter (fun i => ¬ σ' i = false)).card := by
      unfold wt
      congr 1
      ext i
      cases σ' i <;> simp
    rw [e1, e2]
    exact h
  have hsum : ∀ ρ : Fin Q ⊕ Fin Q → Bool,
      wt ρ = wt (fun i => ρ (Sum.inl i)) + wt (fun i => ρ (Sum.inr i)) := by
    intro ρ
    unfold wt
    simp only [card_filter]
    rw [Fintype.sum_sum_type]
  have hcard : Fintype.card (Fin Q ⊕ Fin Q) = 2 * Q := by
    simp [two_mul]
  have h1 := sum_wt (α := Fin Q ⊕ Fin Q) (R := ℤ) (fun k => |(Q : ℤ) - k|)
  rw [hcard] at h1
  rw [← sum_choose_abs Q, ← h1]
  rw [← (Equiv.sumArrowEquivProdArrow (Fin Q) (Fin Q) Bool).symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro σ _
  let e : (Fin Q → Bool) ≃ (Fin Q → Bool) :=
    ⟨antipode, antipode, fun a => by funext i; simp [antipode],
      fun a => by funext i; simp [antipode]⟩
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro σ' _
  have h2 := hanti σ'
  rw [hsum]
  have e1 : (fun i => (Equiv.sumArrowEquivProdArrow (Fin Q) (Fin Q) Bool).symm (σ, σ')
      (Sum.inl i)) = σ := rfl
  have e2 : (fun i => (Equiv.sumArrowEquivProdArrow (Fin Q) (Fin Q) Bool).symm (σ, σ')
      (Sum.inr i)) = σ' := rfl
  rw [e1, e2]
  have e3 : e σ' = antipode σ' := rfl
  rw [e3]
  have h3 : ((wt (antipode σ') : ℤ) + wt σ') = Q := by exact_mod_cast h2
  rw [abs_sub_comm]
  congr 1
  push_cast
  linarith

end Signs

section DigitCut
variable {H Q : ℕ}

/-- `H`-even alphabet `Fin (2H)`: the sign pattern of a word. `c_t(u)=1` iff `u_t < H`. -/
def digitCut (H : ℕ) {Q : ℕ} (t : Fin Q) (u : Fin Q → Fin (2 * H)) : Bool := decide ((u t).val < H)

/-- The sign pattern of a word. -/
def sig (H : ℕ) {Q : ℕ} (u : Fin Q → Fin (2 * H)) : Fin Q → Bool := fun t => digitCut H t u

theorem card_digit (b : Bool) :
    (univ.filter (fun g : Fin (2 * H) => decide (g.val < H) = b)).card = H := by
  have h1 : (univ.filter (fun g : Fin (2 * H) => g.val < H)).card = H := by
    have := Fin.card_filter_val_lt (n := 2 * H) (m := H)
    simpa [two_mul] using this
  cases b
  · have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * H))))
      (fun g => g.val < H)
    simp only [card_univ, Fintype.card_fin, h1] at h
    simp only [decide_eq_false_iff_not]
    omega
  · simpa using h1

theorem card_sig_fiber (σ : Fin Q → Bool) :
    (univ.filter (fun u : Fin Q → Fin (2 * H) => sig H u = σ)).card = H ^ Q := by
  have : univ.filter (fun u : Fin Q → Fin (2 * H) => sig H u = σ)
      = Fintype.piFinset (fun t => univ.filter (fun g : Fin (2 * H) => decide (g.val < H) = σ t)) := by
    ext u
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    exact funext_iff
  rw [this, Fintype.card_piFinset]
  simp [card_digit]

theorem sum_sig (φ : (Fin Q → Bool) → ℤ) :
    ∑ u : Fin Q → Fin (2 * H), φ (sig H u) = (H : ℤ) ^ Q * ∑ σ, φ σ := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := sig H) (t := univ) (fun _ _ => mem_univ _),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.sum_congr rfl (g := fun _ => φ σ)]
  · rw [Finset.sum_const, card_sig_fiber, nsmul_eq_mul]
    push_cast
    rfl
  · intro u hu
    rw [(mem_filter.mp hu).2]

theorem sSum_digit (u : Fin Q → Fin (2 * H)) :
    sSum (fun t => digitCut H t) u = 2 * (wt (sig H u) : ℤ) - Q :=
  sum_sg Q (sig H u)

/-- `∑_{u,w}|s(u)-s(w)| = H^(2Q)·2Q·C(2Q,Q)`: the expected absolute value of the difference is
that of a sum of `2Q` independent signs. -/
theorem sum_abs_digit :
    ∑ ω : (Fin Q → Fin (2 * H)) × (Fin Q → Fin (2 * H)),
        |sSum (fun t => digitCut H t) ω.1 - sSum (fun t => digitCut H t) ω.2|
      = (H : ℤ) ^ (2 * Q) * (2 * ((Q : ℤ) * ((2 * Q).choose Q : ℕ))) := by
  rw [Fintype.sum_prod_type]
  simp only [sSum_digit]
  have h1 : ∀ u : Fin Q → Fin (2 * H),
      ∑ w : Fin Q → Fin (2 * H), |2 * (wt (sig H u) : ℤ) - Q - (2 * (wt (sig H w) : ℤ) - Q)|
        = (H : ℤ) ^ Q * ∑ σ' : Fin Q → Bool, 2 * |(wt (sig H u) : ℤ) - wt σ'| := by
    intro u
    rw [← sum_sig (fun σ' => 2 * |(wt (sig H u) : ℤ) - wt σ'|)]
    apply Finset.sum_congr rfl
    intro w _
    rw [show 2 * (wt (sig H u) : ℤ) - Q - (2 * (wt (sig H w) : ℤ) - Q)
      = 2 * ((wt (sig H u) : ℤ) - wt (sig H w)) by ring, abs_mul]
    simp
  simp only [h1]
  rw [← Finset.mul_sum]
  rw [sum_sig (fun σ => ∑ σ' : Fin Q → Bool, 2 * |(wt σ : ℤ) - wt σ'|)]
  simp only [← Finset.mul_sum]
  rw [sum_cube_abs]
  ring

/-- The value of `2(p_t-q_t)` for the wire set `s(u)>s(w)`. Permuting the digits fixes the wire
set, so this does not depend on `t`. -/
theorem digit_symmetry (t t' : Fin Q) :
    ∑ ω ∈ upWires (fun t => digitCut H t), (sg (digitCut H t ω.1) - sg (digitCut H t ω.2))
      = ∑ ω ∈ upWires (fun t => digitCut H t), (sg (digitCut H t' ω.1) - sg (digitCut H t' ω.2)) := by
  let π := Equiv.swap t t'
  let e : (Fin Q → Fin (2 * H)) ≃ (Fin Q → Fin (2 * H)) :=
    ⟨fun u => u ∘ π, fun u => u ∘ π, fun u => by funext i; simp [π],
      fun u => by funext i; simp [π]⟩
  have hs : ∀ u, sSum (fun t => digitCut H t) (e u) = sSum (fun t => digitCut H t) u := by
    intro u
    unfold sSum
    exact Equiv.sum_comp π (fun i => sg (digitCut H i u))
  unfold upWires
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Fintype.sum_equiv (e.prodCongr e)
  intro ω
  simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, hs]
  have hd : ∀ u, digitCut H t' (e u) = digitCut H t u := by
    intro u
    simp [digitCut, e, π]
  rw [hd, hd]

/-- **The difference `p_t-q_t`.** With `W={s(u)>s(w)}`, `2(p_t-q_t)=H^(2Q)C(2Q,Q)`. -/
theorem two_pq_digit (hQ : 0 < Q) (t : Fin Q) :
    2 * ((pW (upWires (fun t => digitCut H t)) (digitCut H t) : ℤ)
        - qW (upWires (fun t => digitCut H t)) (digitCut H t))
      = (H : ℤ) ^ (2 * Q) * ((2 * Q).choose Q : ℕ) := by
  set W := upWires (fun t : Fin Q => digitCut H t) with hW
  have h1 := sum_two_pW_sub_qW (fun t : Fin Q => digitCut H t) W
  have h2 := two_sum_upWires (fun t : Fin Q => digitCut H t)
  rw [sum_abs_digit, ← hW] at h2
  have h3 : ∑ t' : Fin Q, 2 * ((pW W (digitCut H t') : ℤ) - qW W (digitCut H t'))
      = Q * (2 * ((pW W (digitCut H t) : ℤ) - qW W (digitCut H t))) := by
    rw [Finset.sum_congr rfl (g := fun _ => 2 * ((pW W (digitCut H t) : ℤ) - qW W (digitCut H t)))]
    · simp
    · intro t' _
      rw [two_pW_sub_qW, two_pW_sub_qW]
      exact digit_symmetry t' t
  rw [h3] at h1
  rw [← h1] at h2
  have hQ' : (2 * (Q : ℤ)) ≠ 0 := by
    have : (Q : ℤ) ≠ 0 := by exact_mod_cast hQ.ne'
    simpa using this
  apply mul_left_cancel₀ hQ'
  linear_combination h2

/-- The exponent of Proposition `cut`, as an integer: `D=H^(2Q)C(2Q,Q)/2`. -/
def cutD (H Q : ℕ) : ℕ := H ^ (2 * Q) * Nat.centralBinom Q / 2

theorem two_mul_cutD (hQ : 0 < Q) : 2 * cutD H Q = H ^ (2 * Q) * Nat.centralBinom Q := by
  unfold cutD
  apply Nat.mul_div_cancel'
  exact (Nat.two_dvd_centralBinom_of_one_le hQ).trans (Nat.dvd_mul_left _ _)

/-- **Proposition `cut`, combinatorial form.** Let `G=2H` be even. Suppose that
`T=T_1+…+T_Q`, where `T_t` is a combination of `r t` products over the `G` blocks of `P_t`:
the function `b t j g` reads only entries in rows `u` with `u_t=g`. Then `∑ r_t ≥ 2^D`. -/
theorem cut_digit {𝕜 : Type*} [Field 𝕜] (hQ : 0 < Q) (r : Fin Q → ℕ)
    (a : ∀ t, Fin (r t) → 𝕜)
    (b : ∀ t, Fin (r t) → Fin (2 * H) →
      ((Fin Q → Fin (2 * H)) × (Fin Q → Fin (2 * H)) → Bool) →
      ((Fin Q → Fin (2 * H)) × (Fin Q → Fin (2 * H)) → Bool) → 𝕜)
    (hb : ∀ t j g X X' Y Y', (∀ v : (Fin Q → Fin (2 * H)) × (Fin Q → Fin (2 * H)),
        v.1 t = g → X v = X' v) → (∀ v : (Fin Q → Fin (2 * H)) × (Fin Q → Fin (2 * H)),
        v.1 t = g → Y v = Y' v) → b t j g X Y = b t j g X' Y')
    (hT : ∀ X Y, TT 𝕜 X Y = ∑ t, ∑ j, a t j * ∏ g, b t j g X Y) :
    2 ^ cutD H Q ≤ ∑ t, r t := by
  classical
  let F : ∀ t, Fin (r t) → _ → _ → 𝕜 := fun t j X Y =>
    ∏ g ∈ univ.filter (fun g : Fin (2 * H) => decide (g.val < H) = true), b t j g X Y
  let F' : ∀ t, Fin (r t) → _ → _ → 𝕜 := fun t j X Y =>
    ∏ g ∈ univ.filter (fun g : Fin (2 * H) => ¬ decide (g.val < H) = true), b t j g X Y
  apply cut_rows (fun t : Fin Q => digitCut H t) r a F F'
  · intro t j X X' Y Y' hX hY
    apply Finset.prod_congr rfl
    intro g hg
    have hg' : decide (g.val < H) = true := (mem_filter.mp hg).2
    apply hb
    · intro v hv
      apply hX
      simp only [digitCut, hv]
      exact hg'
    · intro v hv
      apply hY
      simp only [digitCut, hv]
      exact hg'
  · intro t j X X' Y Y' hX hY
    apply Finset.prod_congr rfl
    intro g hg
    have hg' : ¬ decide (g.val < H) = true := (mem_filter.mp hg).2
    apply hb
    · intro v hv
      apply hX
      simp only [digitCut, hv]
      simpa using hg'
    · intro v hv
      apply hY
      simp only [digitCut, hv]
      simpa using hg'
  · intro X Y
    rw [hT]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    exact (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
  · intro t
    have h := two_pq_digit (H := H) hQ t
    have h2 := two_mul_cutD (H := H) hQ
    have h3 : (2 * (cutD H Q : ℤ)) = (H : ℤ) ^ (2 * Q) * ((2 * Q).choose Q : ℕ) := by
      have : Nat.centralBinom Q = (2 * Q).choose Q := Nat.centralBinom_eq_two_mul_choose Q
      rw [this] at h2
      exact_mod_cast h2
    have h4 : (pW (upWires (fun t => digitCut H t)) (digitCut H t) : ℤ)
        - qW (upWires (fun t => digitCut H t)) (digitCut H t) = cutD H Q := by
      linarith
    rw [h4]
    simp

/-- The exponent `D=(N/2)·C(2Q,Q)/4^Q`, for `N=G^(2Q)`, `G=2H`. -/
theorem cutD_eq_real (hQ : 0 < Q) :
    (cutD H Q : ℝ) = (((2 * H) ^ (2 * Q) : ℕ) : ℝ) / 2 * (Nat.centralBinom Q / 4 ^ Q) := by
  have h : (2 : ℝ) * cutD H Q = (H : ℝ) ^ (2 * Q) * Nat.centralBinom Q := by
    exact_mod_cast two_mul_cutD (H := H) hQ
  have e : (((2 * H) ^ (2 * Q) : ℕ) : ℝ) = 4 ^ Q * (H : ℝ) ^ (2 * Q) := by
    push_cast
    rw [mul_pow, pow_mul]
    norm_num
  have h4 : (4 : ℝ) ^ Q ≠ 0 := by positivity
  rw [e]
  field_simp
  linarith

/-- `D ≥ N/(4√Q)`. -/
theorem cutD_ge (hQ : 0 < Q) :
    (((2 * H) ^ (2 * Q) : ℕ) : ℝ) / (4 * Real.sqrt Q) ≤ cutD H Q := by
  rw [cutD_eq_real hQ]
  have h := central_ge Q hQ
  have hN : (0 : ℝ) ≤ (((2 * H) ^ (2 * Q) : ℕ) : ℝ) / 2 := by positivity
  calc _ = (((2 * H) ^ (2 * Q) : ℕ) : ℝ) / 2 * (1 / (2 * Real.sqrt Q)) := by
        have hs : Real.sqrt Q ≠ 0 := by
          have : (0 : ℝ) < Q := by exact_mod_cast hQ
          exact (Real.sqrt_pos.mpr this).ne'
        field_simp
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h hN

/-- **Proposition `cut`.** `∑ r_t ≥ 2^D`, with `D=(N/2)·C(2Q,Q)/4^Q` and `D ≥ N/(4√Q)`,
where `N=G^(2Q)`, `G=2H`. -/
theorem cut_prop {𝕜 : Type*} [Field 𝕜] (hQ : 0 < Q) (r : Fin Q → ℕ)
    (a : ∀ t, Fin (r t) → 𝕜)
    (b : ∀ t, Fin (r t) → Fin (2 * H) →
      ((Fin Q → Fin (2 * H)) × (Fin Q → Fin (2 * H)) → Bool) →
      ((Fin Q → Fin (2 * H)) × (Fin Q → Fin (2 * H)) → Bool) → 𝕜)
    (hb : ∀ t j g X X' Y Y', (∀ v : (Fin Q → Fin (2 * H)) × (Fin Q → Fin (2 * H)),
        v.1 t = g → X v = X' v) → (∀ v : (Fin Q → Fin (2 * H)) × (Fin Q → Fin (2 * H)),
        v.1 t = g → Y v = Y' v) → b t j g X Y = b t j g X' Y')
    (hT : ∀ X Y, TT 𝕜 X Y = ∑ t, ∑ j, a t j * ∏ g, b t j g X Y) :
    (2 : ℝ) ^ ((((2 * H) ^ (2 * Q) : ℕ) : ℝ) / 2 * (Nat.centralBinom Q / 4 ^ Q)) ≤
        ((∑ t, r t : ℕ) : ℝ) ∧
      (((2 * H) ^ (2 * Q) : ℕ) : ℝ) / (4 * Real.sqrt Q) ≤
        ((2 * H) ^ (2 * Q) : ℕ) / 2 * (Nat.centralBinom Q / 4 ^ Q) := by
  refine ⟨?_, ?_⟩
  · rw [← cutD_eq_real hQ, Real.rpow_natCast]
    exact_mod_cast cut_digit hQ r a b hb hT
  · rw [← cutD_eq_real hQ]
    exact cutD_ge hQ

end DigitCut

end TransposeBase.Exact
