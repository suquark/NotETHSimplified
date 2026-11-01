import SatBase.SparseSearch
import SatBase.BranchingEstimate

/-! One potential argument for quantities that add across the actual branch.
The measured quantity can be a leaf count, an evaluation count, or work with
a fixed allowance. Only its leaf cap and branch inequality are required. -/
namespace SatBase

theorem sparsePotential_exp_bound {n L : ℕ} (hL : 2≤L)
    (value : SparseState n L → ℝ) (C : ℝ) (hC : 0≤C)
    (hleaf : ∀ s, chooseSparseRule s.formula L=none → value s≤C)
    (hbranch : ∀ s r hr, value s≤value (s.left hL r hr)+value (s.right hL r hr))
    (s : SparseState n L) :
    value s≤C*Real.exp ((20*Real.log L+10)*n/L) := by
  have hq : 1≤L^2 := by nlinarith
  have hc := (branchingRate_pos (L^2) hq).le
  have hrec : ∀ D : ℕ, ∀ t : SparseState n L, t.remaining=D →
      value t≤C*Real.exp (branchingRate (L^2)*D) := by
    intro D
    induction D using Nat.strong_induction_on with
    | h D ih =>
      intro t ht
      cases hr : chooseSparseRule t.formula L with
      | none =>
        have he : 1≤Real.exp (branchingRate (L^2)*D) := by
          have hp : 0≤branchingRate (L^2)*(D:ℝ) := mul_nonneg hc (Nat.cast_nonneg _)
          linarith [Real.add_one_le_exp (branchingRate (L^2)*D)]
        exact (hleaf t hr).trans (le_mul_of_one_le_right hC he)
      | some r =>
        have hd := t.remaining_decreases hL r hr
        have hl := ih (t.left hL r hr).remaining (by omega) (t.left hL r hr) rfl
        have hright := ih (t.right hL r hr).remaining (by omega) (t.right hL r hr) rfl
        have hg := t.remaining_gains hL r hr
        calc
          _ ≤ value (t.left hL r hr)+value (t.right hL r hr) := hbranch t r hr
          _ ≤ C*Real.exp (branchingRate (L^2)*(t.left hL r hr).remaining)+
              C*Real.exp (branchingRate (L^2)*(t.right hL r hr).remaining) := add_le_add hl hright
          _ = C*(Real.exp (branchingRate (L^2)*(t.left hL r hr).remaining)+
              Real.exp (branchingRate (L^2)*(t.right hL r hr).remaining)) := by ring
          _ ≤ C*Real.exp (branchingRate (L^2)*t.remaining) :=
            mul_le_mul_of_nonneg_left (branching_exp_bound (L^2) _ _ _ hq hg.1 hg.2) hC
          _ = _ := by rw [ht]
  have hparam : branchingRate (L^2)*(10*n*L:ℕ)=(20*Real.log (L:ℝ)+10)*n/L := by
    unfold branchingRate
    push_cast
    rw [Real.log_pow]
    have hLp : (L:ℝ)≠0 := by exact_mod_cast (by omega : L≠0)
    field_simp
    ring
  calc
    _ ≤ C*Real.exp (branchingRate (L^2)*s.remaining) := hrec _ s rfl
    _ ≤ C*Real.exp (branchingRate (L^2)*(10*n*L:ℕ)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le (10*n*L) (packingPotential s.formula L)) hc)) hC
    _ = _ := by rw [hparam]

end SatBase
