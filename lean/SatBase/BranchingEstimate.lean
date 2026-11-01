import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! One asymmetric branch preserves an exponential budget: the left
remaining potential falls by one and the right by q. -/
namespace SatBase

noncomputable def branchingRate (q : ℕ) : ℝ := (Real.log q+1)/q

theorem branchingRate_pos (q : ℕ) (hq : 1≤q) : 0<branchingRate q := by
  have hq1 : (1:ℝ)≤q := by exact_mod_cast hq
  have hlog := Real.log_nonneg hq1
  unfold branchingRate
  positivity

/-- The two edge weights have total at most one. -/
theorem branching_weights (q : ℕ) (hq : 1≤q) :
    Real.exp (-branchingRate q)+Real.exp (-branchingRate q*q)≤1 := by
  have hq1 : (1:ℝ)≤q := by exact_mod_cast hq
  have hqp : (0:ℝ)<q := by linarith
  have hlog := Real.log_nonneg hq1
  have hlin : 1+(q:ℝ)⁻¹≤Real.exp (branchingRate q) := by
    have h := Real.add_one_le_exp (branchingRate q)
    have hi : (q:ℝ)⁻¹≤branchingRate q := by
      unfold branchingRate
      rw [inv_eq_one_div]
      exact div_le_div_of_nonneg_right (by linarith) hqp.le
    linarith
  have hfirst : Real.exp (-branchingRate q)≤(q:ℝ)/(q+1) := by
    rw [Real.exp_neg]
    have hp : 0<1+(q:ℝ)⁻¹ := by positivity
    have hh := inv_anti₀ hp hlin
    calc
      _ ≤ (1+(q:ℝ)⁻¹)⁻¹ := hh
      _ = _ := by field_simp
  have hsecond : Real.exp (-branchingRate q*q)≤1/(2*(q:ℝ)) := by
    have he : Real.exp (branchingRate q*q)=Real.exp 1*q := by
      unfold branchingRate
      rw [div_mul_cancel₀ _ hqp.ne']
      rw [Real.exp_add,Real.exp_log hqp,mul_comm]
    rw [show -branchingRate q*q=-(branchingRate q*q) by ring,Real.exp_neg,he]
    have he2 : (2:ℝ)≤Real.exp 1 := by
      linarith [Real.add_one_le_exp 1]
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_right he2 hqp.le)
  have hsum : (q:ℝ)/(q+1)+1/(2*q)≤1 := by
    rw [div_add_div _ _ (by positivity) (by positivity)]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  linarith

/-- One branching step preserves the exponential budget. -/
theorem branching_exp_bound (q D Dl Dr : ℕ) (hq : 1≤q)
    (hl : Dl+1≤D) (hr : Dr+q≤D) :
    Real.exp (branchingRate q*Dl)+Real.exp (branchingRate q*Dr)≤
      Real.exp (branchingRate q*D) := by
  have hc := (branchingRate_pos q hq).le
  have hl' : (Dl:ℝ)+1≤D := by exact_mod_cast hl
  have hr' : (Dr:ℝ)+q≤D := by exact_mod_cast hr
  have hleft : branchingRate q*Dl≤branchingRate q*D-branchingRate q := by
    nlinarith
  have hright : branchingRate q*Dr≤branchingRate q*D-branchingRate q*q := by
    nlinarith
  calc
    _ ≤ Real.exp (branchingRate q*D-branchingRate q)+
        Real.exp (branchingRate q*D-branchingRate q*q) :=
      add_le_add (Real.exp_le_exp.mpr hleft) (Real.exp_le_exp.mpr hright)
    _ = Real.exp (branchingRate q*D)*
        (Real.exp (-branchingRate q)+Real.exp (-branchingRate q*q)) := by
      simp only [sub_eq_add_neg,neg_mul,Real.exp_add,mul_add]
    _ ≤ _ := by
      simpa using mul_le_mul_of_nonneg_left (branching_weights q hq)
        (Real.exp_pos (branchingRate q*D)).le

end SatBase
