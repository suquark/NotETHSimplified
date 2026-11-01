import TransposeBase.Defs

/-!
# Limits of the method -/

set_option linter.unusedSectionVars false

namespace TransposeBase
namespace Limits

open scoped BigOperators
open Finset Matrix

/-! ## Rank facts -/

section Rank

variable {k : Type*} [Field k] {m n ι : Type*} [Fintype m] [Fintype n] [DecidableEq n]

theorem rank_add_le (A B : Matrix m n k) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  have hle : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    rw [Matrix.mulVecLin_add]
    exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

theorem rank_sum_le {α : Type*} (s : Finset α) (A : α → Matrix m n k) :
    (∑ a ∈ s, A a).rank ≤ ∑ a ∈ s, (A a).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.rank_zero]
  | insert a s ha ih =>
      rw [sum_insert ha, sum_insert ha]
      exact (rank_add_le _ _).trans (Nat.add_le_add_left ih _)

end Rank

/-! ## Far rows force a large error -/

/-! ## Few rows force long reads -/

/-! ## The rank argument on a cut -/

section Cut

variable {W : Type*} [Fintype W] [DecidableEq W] {k : Type*} [Field k]

/-- `x` and `x'` agree on the set `s` of wires. -/
def AgreeBits (s : Finset W) (x x' : W → Bool) : Prop := ∀ e ∈ s, x e = x' e

/-- A function that reads `x` on `sx` and `y` on `sy`. -/
def Reads (sx sy : Finset W) (f : (W → Bool) → (W → Bool) → k) : Prop :=
  ∀ x x' y y', AgreeBits sx x x' → AgreeBits sy y y' → f x y = f x' y'

/-- **One product across the cut between `X` and `Y`.** Let `f` read `x` on `sx` and `y` on the
complement of `sy`, and let `g` read `x` on the complement of `sx` and `y` on `sy`. Then the matrix
of `f * g` has rank at most `2 ^ |sx| * 2 ^ |sy|`. -/
theorem rank_product_le (sx sy : Finset W) {f g : (W → Bool) → (W → Bool) → k}
    (hf : Reads sx syᶜ f) (hg : Reads sxᶜ sy g) :
    (Matrix.of fun x y => f x y * g x y : Matrix (W → Bool) (W → Bool) k).rank ≤
      2 ^ sx.card * 2 ^ sy.card := by
  classical
  let I := {a : sx → Bool // True} × {b : sy → Bool // True}
  let ext (s : Finset W) (a : s → Bool) : W → Bool := fun e => if h : e ∈ s then a ⟨e, h⟩ else false
  let U : Matrix (W → Bool) ((sx → Bool) × (sy → Bool)) k := fun x p =>
    if (fun e : sx => x e.1) = p.1 then g x (ext sy p.2) else 0
  let V : Matrix ((sx → Bool) × (sy → Bool)) (W → Bool) k := fun p y =>
    if (fun e : sy => y e.1) = p.2 then f (ext sx p.1) y else 0
  have hext : ∀ (s : Finset W) (x : W → Bool), AgreeBits s x (ext s fun e => x e.1) := by
    intro s x e he
    simp [ext, he]
  have hmul : (Matrix.of fun x y => f x y * g x y : Matrix (W → Bool) (W → Bool) k) = U * V := by
    ext x y
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    simp only [U, V, ite_mul, mul_ite, zero_mul, mul_zero, Matrix.of_apply]
    rw [Finset.sum_eq_single (fun e : sx => x e.1), Finset.sum_eq_single (fun e : sy => y e.1)]
    · simp only [if_true]
      have h1 : f x y = f (ext sx fun e => x e.1) y :=
        hf _ _ _ _ (hext sx x) (fun _ _ => rfl)
      have h2 : g x y = g x (ext sy fun e => y e.1) :=
        hg _ _ _ _ (fun _ _ => rfl) (hext sy y)
      rw [h1, h2]
      ring
    · intro b _ hb
      rw [if_neg (Ne.symm hb)]
    · simp
    · intro a _ ha
      refine Finset.sum_eq_zero fun b _ => ?_
      simp [Ne.symm ha]
    · simp
  rw [hmul]
  refine (Matrix.rank_mul_le_left _ _).trans ?_
  refine (Matrix.rank_le_card_width _).trans (le_of_eq ?_)
  simp

/-- **The rank argument.** Suppose the identity on `W → Bool` is a sum over the cuts `t` of `r t`
products, each with the locality of `rank_product_le` for sets `sx t`, `sy t`. If
`|sx t| + |sy t| ≤ |W| - D` for all `t`, then `∑ t, r t ≥ 2 ^ D`. -/
theorem cut_lower_bound {Q : ℕ} (sx sy : Fin Q → Finset W) {D : ℕ} (r : Fin Q → ℕ)
    (hsize : ∀ t, (sx t).card + (sy t).card + D ≤ Fintype.card W)
    (c : (t : Fin Q) → Fin (r t) → k)
    (f g : (t : Fin Q) → Fin (r t) → (W → Bool) → (W → Bool) → k)
    (hf : ∀ t i, Reads (sx t) (sy t)ᶜ (f t i)) (hg : ∀ t i, Reads (sx t)ᶜ (sy t) (g t i))
    (hsum : ∀ x y : W → Bool, ∑ t, ∑ i, c t i * (f t i x y * g t i x y) = if x = y then 1 else 0) :
    2 ^ D ≤ ∑ t, r t := by
  classical
  have hI : (1 : Matrix (W → Bool) (W → Bool) k) =
      ∑ t, ∑ i, c t i • (Matrix.of fun x y => f t i x y * g t i x y) := by
    ext x y
    simp only [Matrix.one_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    exact (hsum x y).symm
  have hrankI : (1 : Matrix (W → Bool) (W → Bool) k).rank = 2 ^ Fintype.card W := by
    rw [Matrix.rank_one]
    simp
  have hterm : ∀ t i, (c t i • (Matrix.of fun x y => f t i x y * g t i x y) :
      Matrix (W → Bool) (W → Bool) k).rank ≤ 2 ^ (Fintype.card W - D) := by
    intro t i
    have h1 := rank_product_le (sx t) (sy t) (hf t i) (hg t i)
    have h2 : c t i • (Matrix.of fun x y => f t i x y * g t i x y) =
        (Matrix.of fun x y => f t i x y * g t i x y) * (c t i • (1 : Matrix _ _ k)) := by
      simp
    rw [h2]
    refine (Matrix.rank_mul_le_left _ _).trans (h1.trans ?_)
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by have := hsize t; omega)
  have hle : 2 ^ Fintype.card W ≤ (∑ t, r t) * 2 ^ (Fintype.card W - D) := by
    rw [← hrankI, hI]
    refine (rank_sum_le _ _).trans ?_
    rw [sum_mul]
    refine sum_le_sum fun t _ => (rank_sum_le _ _).trans ?_
    calc _ ≤ ∑ _i : Fin (r t), 2 ^ (Fintype.card W - D) := sum_le_sum fun i _ => hterm t i
      _ = _ := by simp
  have hDW : D ≤ Fintype.card W := by
    rcases Nat.eq_zero_or_pos Q with h0 | h0
    · subst h0
      simp at hle
    · have := hsize ⟨0, h0⟩
      omega
  have hsplit : 2 ^ Fintype.card W = 2 ^ D * 2 ^ (Fintype.card W - D) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit] at hle
  exact Nat.le_of_mul_le_mul_right hle (by positivity)

end Cut

/-! ## The signs -/

/-! ## Half arcs: the rank argument is limited -/

/-! ## The rank argument for block sums -/

section Digit

variable {Q : ℕ} {A : Type*} [Fintype A] [DecidableEq A] {k : Type*} [Field k]

/-- The bit matrix `X` of an assignment of the wires in `W`: the bit of `ω` at the cell `tr ω`. -/
def wireX (W : Finset (Cell Q A)) (x : {ω // ω ∈ W} → Bool) : Cell Q A → Bool :=
  fun ω => if h : tr ω ∈ W then x ⟨tr ω, h⟩ else false

/-- The bit matrix `Y` of an assignment of the wires in `W`: the bit of `ω` at the cell `ω`. -/
def wireY (W : Finset (Cell Q A)) (y : {ω // ω ∈ W} → Bool) : Cell Q A → Bool :=
  fun ω => if h : ω ∈ W then y ⟨ω, h⟩ else false

/-- `Y = Xᵀ` for the matrices of two assignments exactly when the assignments agree. -/
theorem wire_transpose_iff (W : Finset (Cell Q A)) (x y : {ω // ω ∈ W} → Bool) :
    (∀ ω, wireY W y ω = wireX W x (tr ω)) ↔ x = y := by
  have htt : ∀ ω : Cell Q A, tr (tr ω) = ω := fun ω => by simp [tr]
  constructor
  · intro h
    funext e
    have h1 := h e.1
    have hmem : tr (tr e.1) ∈ W := by rw [htt]; exact e.2
    simp only [wireY, wireX, e.2, dif_pos, hmem] at h1
    have h3 : (⟨tr (tr e.1), hmem⟩ : {ω // ω ∈ W}) = e := Subtype.ext (htt _)
    rw [h3] at h1
    exact h1.symm
  · rintro rfl ω
    by_cases hω : ω ∈ W
    · have hmem : tr (tr ω) ∈ W := by rw [htt]; exact hω
      simp only [wireY, wireX, dif_pos hω, dif_pos hmem]
      congr 2
    · have hmem : ¬ tr (tr ω) ∈ W := by rw [htt]; exact hω
      simp only [wireY, wireX, dif_neg hω, dif_neg hmem]

/-- **The rank argument for digit partitions.** Let `k` be a field, and suppose `∑ t, T t` is the indicator of
`Y = Xᵀ` on bit matrices, with `T t` a
linear combination of `r t` products over the blocks of `P_t`. Let `c t` merge the blocks of `P_t` into
two parts, and let `W` be a set of cells. Write `sx t` for the wires whose `X` bit lies in the part
`true`, and `sy t` for the wires whose `Y` bit lies in the part `false`. If
`|sx t| + |sy t| + D ≤ |W|` for all `t`, then `∑ t, r t ≥ 2 ^ D`.

In the notation of the note, `|sx t| + |sy t| = 2 * q_t + e_t` when the parts are labelled so that
`q_t ≤ p_t`, so the hypothesis says `p_t - q_t ≥ D`. -/
theorem digit_lower_bound (c : Fin Q → A → Bool) (W : Finset (Cell Q A)) (r : Fin Q → ℕ) {D : ℕ}
    (T : Fin Q → (Cell Q A → k) → (Cell Q A → k) → k) (hT : ∀ t, IsBlockSum t (r t) (T t))
    (hsum : IsTransposeIndicator fun X Y : Cell Q A → k => ∑ t, T t X Y)
    (hsize : ∀ t, (W.filter fun ω => c t (ω.2 t) = true).card +
      (W.filter fun ω => c t (ω.1 t) = false).card + D ≤ W.card) :
    2 ^ D ≤ ∑ t, r t := by
  classical
  choose cf p hp hfp using hT
  choose Φ hΦ hpΦ using hp
  let E := {ω // ω ∈ W}
  let sx : Fin Q → Finset E := fun t => univ.filter fun e => c t (e.1.2 t) = true
  let sy : Fin Q → Finset E := fun t => univ.filter fun e => c t (e.1.1 t) = false
  have hcard : ∀ (P : Cell Q A → Prop) [DecidablePred P],
      (univ.filter fun e : E => P e.1).card = (W.filter P).card := by
    intro P _
    refine card_bij (fun e _ => e.1) ?_ ?_ ?_
    · intro e he
      exact mem_filter.mpr ⟨e.2, (mem_filter.mp he).2⟩
    · intro e _ e' _ h
      exact Subtype.ext h
    · intro ω hω
      exact ⟨⟨ω, (mem_filter.mp hω).1⟩, mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hω).2⟩, rfl⟩
  have hsize' : ∀ t, (sx t).card + (sy t).card + D ≤ Fintype.card E := by
    intro t
    have h1 := hcard (fun ω => c t (ω.2 t) = true)
    have h2 := hcard (fun ω => c t (ω.1 t) = false)
    have h3 : Fintype.card E = W.card := Fintype.card_coe W
    rw [h3]
    simp only [sx, sy]
    rw [h1, h2]
    exact hsize t
  let X' : (E → Bool) → Cell Q A → k := fun x ω => bit (wireX W x ω)
  let Y' : (E → Bool) → Cell Q A → k := fun y ω => bit (wireY W y ω)
  have hX : ∀ t g (x x' : E → Bool), (∀ e : E, e.1.2 t = g → x e = x' e) →
      AgreeOn t g (X' x) (X' x') := by
    intro t g x x' h ω hω
    simp only [X', wireX]
    by_cases hm : tr ω ∈ W
    · rw [dif_pos hm, dif_pos hm, h ⟨tr ω, hm⟩ hω]
    · rw [dif_neg hm, dif_neg hm]
  have hY : ∀ t g (y y' : E → Bool), (∀ e : E, e.1.1 t = g → y e = y' e) →
      AgreeOn t g (Y' y) (Y' y') := by
    intro t g y y' h ω hω
    simp only [Y', wireY]
    by_cases hm : ω ∈ W
    · rw [dif_pos hm, dif_pos hm, h ⟨ω, hm⟩ hω]
    · rw [dif_neg hm, dif_neg hm]
  let f : (t : Fin Q) → Fin (r t) → (E → Bool) → (E → Bool) → k := fun t i x y =>
    ∏ g ∈ univ.filter (fun g => c t g = true), Φ t i g (X' x) (Y' y)
  let g' : (t : Fin Q) → Fin (r t) → (E → Bool) → (E → Bool) → k := fun t i x y =>
    ∏ g ∈ univ.filter (fun g => ¬ c t g = true), Φ t i g (X' x) (Y' y)
  refine cut_lower_bound (k := k) sx sy r hsize' cf f g' ?_ ?_ ?_
  · intro t i x x' y y' hx hy
    refine prod_congr rfl fun g hg => ?_
    have hg' : c t g = true := (mem_filter.mp hg).2
    refine hΦ t i g _ _ _ _ (hX t g x x' fun e he => hx e ?_) (hY t g y y' fun e he => hy e ?_)
    · exact mem_filter.mpr ⟨mem_univ _, by rw [he]; exact hg'⟩
    · rw [mem_compl]
      intro hmem
      have := (mem_filter.mp hmem).2
      rw [he, hg'] at this
      cases this
  · intro t i x x' y y' hx hy
    refine prod_congr rfl fun g hg => ?_
    have hg' : ¬ c t g = true := (mem_filter.mp hg).2
    refine hΦ t i g _ _ _ _ (hX t g x x' fun e he => hx e ?_) (hY t g y y' fun e he => hy e ?_)
    · rw [mem_compl]
      intro hmem
      have := (mem_filter.mp hmem).2
      rw [he] at this
      exact hg' this
    · refine mem_filter.mpr ⟨mem_univ _, ?_⟩
      rw [he]
      simpa using hg'
  · intro x y
    have hind := hsum (wireX W x) (wireY W y)
    simp only [wire_transpose_iff] at hind
    rw [← hind]
    refine sum_congr rfl fun t _ => ?_
    rw [hfp]
    refine sum_congr rfl fun i _ => ?_
    rw [hpΦ]
    congr 1
    simp only [f, g']
    exact prod_filter_mul_prod_filter_not _ _ _

end Digit

end Limits
end TransposeBase
