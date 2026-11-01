import OnePigeonhole.Pseudo.FinalHelpers
import OnePigeonhole.Pseudo.Leaf

/-!
# The cost of the core program, as a real bound

`nS ^ 3 * 2 ^ (M / m) ≤ (6 * m) ^ 9 * exp (9 * (log m + 3) * M / m)`, with `nS` the loop bound of the masks (`exp_part`). This is the cost of
Section 5 of `papers/one-pigeonhole/proof.tex`, with the masks in place of the triples. All other factors of the cost of the core are polynomials
(`core_real`).
-/

namespace OnePigeonhole.Pseudo.Final

open Finset TransposeBase.Pseudo OnePigeonhole.Pseudo.Leaf

/-- The loop bound of the masks. -/
theorem nS_le (S : Setup) :
    ((S.nS : ℕ) : ℝ) ≤ (6 * (S.m : ℝ)) ^ 3 * Real.exp (3 * Real.log (6 * S.m) * S.M / S.m) := by
  have hL0 : (0 : ℝ) < S.m := by exact_mod_cast S.m_pos
  have h6 : (0 : ℝ) < 6 * S.m := by positivity
  have h6' : (1 : ℝ) ≤ 6 * S.m := by
    have : (1 : ℝ) ≤ S.m := by exact_mod_cast S.m_pos
    linarith
  have hb : ((2 : ℝ) ^ Nat.clog 2 (3 * S.m)) ≤ 6 * S.m := by exact_mod_cast two_pow_clog_le S.m_two
  have hdiv : ((S.M / S.m : ℕ) : ℝ) ≤ (S.M : ℝ) / S.m := Nat.cast_div_le
  have hlog : 0 ≤ Real.log (6 * (S.m : ℝ)) := Real.log_nonneg h6'
  have e : ((S.nS : ℕ) : ℝ) = ((2 : ℝ) ^ Nat.clog 2 (3 * S.m)) ^ (3 * (S.r + 1)) := by
    simp only [Setup.nS, clOf]
    push_cast
    rw [← pow_mul]
    congr 1
    ring
  rw [e]
  calc ((2 : ℝ) ^ Nat.clog 2 (3 * S.m)) ^ (3 * (S.r + 1)) ≤ (6 * (S.m : ℝ)) ^ (3 * (S.r + 1)) :=
        pow_le_pow_left₀ (by positivity) hb _
    _ = (6 * (S.m : ℝ)) ^ 3 * (6 * (S.m : ℝ)) ^ (3 * S.r) := by
        rw [← pow_add]
        congr 1
        ring
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc (6 * (S.m : ℝ)) ^ (3 * S.r)
            = Real.exp (Real.log (6 * (S.m : ℝ)) * ((3 * S.r : ℕ) : ℝ)) := by
              rw [mul_comm (Real.log _), Real.exp_nat_mul, Real.exp_log h6]
          _ ≤ _ := by
              refine Real.exp_le_exp.mpr ?_
              have e2 : 3 * Real.log (6 * (S.m : ℝ)) * (S.M : ℝ) / S.m =
                  Real.log (6 * (S.m : ℝ)) * (3 * ((S.M : ℝ) / S.m)) := by ring
              rw [e2]
              refine mul_le_mul_of_nonneg_left ?_ hlog
              push_cast
              linarith

theorem two_pow_Mm_le (S : Setup) :
    ((2 : ℝ) ^ (S.M / S.m)) ≤ Real.exp (2 * S.M / S.m) := by
  have hdiv : ((S.M / S.m : ℕ) : ℝ) ≤ (S.M : ℝ) / S.m := Nat.cast_div_le
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hm0 : (0 : ℝ) ≤ (S.M : ℝ) / S.m := by positivity
  calc (2 : ℝ) ^ (S.M / S.m)
      = Real.exp (Real.log 2 * ((S.M / S.m : ℕ) : ℝ)) := by
        rw [mul_comm (Real.log _), Real.exp_nat_mul, Real.exp_log (by norm_num)]
    _ ≤ _ := by
        refine Real.exp_le_exp.mpr ?_
        have h0 : (0 : ℝ) ≤ ((S.M / S.m : ℕ) : ℝ) := by positivity
        calc Real.log 2 * ((S.M / S.m : ℕ) : ℝ) ≤ 1 * ((S.M / S.m : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_right hlog2 h0
          _ ≤ 2 * ((S.M : ℝ) / S.m) := by linarith
          _ = _ := by ring

/-- **The exponential factors.** -/
theorem exp_part (S : Setup) :
    ((S.nS : ℕ) : ℝ) ^ 3 * (2 : ℝ) ^ (S.M / S.m) ≤
      (6 * (S.m : ℝ)) ^ 9 * Real.exp (9 * (Real.log S.m + 3) * S.M / S.m) := by
  have hL0 : (0 : ℝ) < S.m := by exact_mod_cast S.m_pos
  have hN0 : (0 : ℝ) ≤ S.M := by positivity
  have h2 := nS_le S
  have h3 := two_pow_Mm_le S
  have hlog6 : Real.log (6 * (S.m : ℝ)) ≤ Real.log S.m + 2 := by
    rw [Real.log_mul (by norm_num) hL0.ne']
    have : Real.log 6 ≤ 2 := by
      have h : Real.log 6 ≤ Real.log (Real.exp 2) := by
        refine Real.log_le_log (by norm_num) ?_
        have := Real.add_one_le_exp (1 : ℝ)
        have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        have h27 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        rw [e2]
        nlinarith
      rwa [Real.log_exp] at h
    linarith
  have h6 : (0 : ℝ) < 6 * S.m := by positivity
  have hcube : ((S.nS : ℕ) : ℝ) ^ 3 ≤
      (6 * (S.m : ℝ)) ^ 9 * Real.exp (9 * Real.log (6 * S.m) * S.M / S.m) := by
    calc ((S.nS : ℕ) : ℝ) ^ 3
        ≤ ((6 * (S.m : ℝ)) ^ 3 * Real.exp (3 * Real.log (6 * S.m) * S.M / S.m)) ^ 3 :=
          pow_le_pow_left₀ (by positivity) h2 _
      _ = _ := by
          rw [mul_pow, ← Real.exp_nat_mul, ← pow_mul]
          congr 2
          push_cast
          ring
  have hsum : 9 * Real.log (6 * S.m) * (S.M : ℝ) / S.m + 2 * S.M / S.m ≤ 9 * (Real.log S.m + 3) * S.M / S.m := by
    have h0 : 0 ≤ (S.M : ℝ) / S.m := by positivity
    have e : 9 * (Real.log S.m + 3) * (S.M : ℝ) / S.m - (9 * Real.log (6 * S.m) * S.M / S.m + 2 * S.M / S.m)
        = (9 * (Real.log S.m + 2 - Real.log (6 * S.m)) + 7) * ((S.M : ℝ) / S.m) := by
      ring
    have h4 : 0 ≤ (9 * (Real.log S.m + 2 - Real.log (6 * S.m)) + 7) * ((S.M : ℝ) / S.m) :=
      mul_nonneg (by linarith) h0
    linarith
  calc ((S.nS : ℕ) : ℝ) ^ 3 * (2 : ℝ) ^ (S.M / S.m)
      ≤ ((6 * (S.m : ℝ)) ^ 9 * Real.exp (9 * Real.log (6 * S.m) * S.M / S.m)) * Real.exp (2 * S.M / S.m) := by
        gcongr
    _ = (6 * (S.m : ℝ)) ^ 9 * Real.exp (9 * Real.log (6 * S.m) * S.M / S.m + 2 * S.M / S.m) := by
        rw [Real.exp_add]
        ring
    _ ≤ _ := by
        gcongr

/-- **The cost of the core program, for a bound `Y ≥ M + 1, T, v + 1` and `Unode ≤ 34000 * Y ^ 6`.** -/
theorem core_real {m Kc dc : ℕ}
    (hKd : ∀ S : Setup, S.m = m → ops S.W (coreE S.m S.lt S.nodeE) S.core ≤
      S.Q * S.Nq ^ S.Q * S.nS ^ 3 *
        (Kc * S.T ^ dc +
          S.L * 2 ^ (S.M / S.m) * (Kc * S.T ^ dc + 2 * (S.Unode * (S.v + 1)))))
    (S : Setup) (hSm : S.m = m) {Y : ℕ} (hY : 1 ≤ Y) (hN : S.M + 1 ≤ Y) (hT : S.T ≤ Y) (hv : S.v + 1 ≤ Y)
    (hU : S.Unode ≤ 34000 * Y ^ 6) :
    (ops S.W (coreE S.m S.lt S.nodeE) S.core : ℝ) ≤
      (6 * (S.m : ℝ)) ^ 9 * Real.exp (9 * (Real.log S.m + 3) * S.M / S.m) *
        (S.Q * (Kc + S.L * (Kc + 68000))) * (Y : ℝ) ^ (S.Q + dc + 7) := by
  have hYr : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hcast : (ops S.W (coreE S.m S.lt S.nodeE) S.core : ℝ) ≤
      (S.Q : ℝ) * ((S.Nq : ℝ) ^ S.Q) * (((S.nS : ℕ) : ℝ) ^ 3) *
        (((Kc : ℝ) * (S.T : ℝ) ^ dc) +
          (S.L : ℝ) * (2 : ℝ) ^ (S.M / S.m) * ((Kc : ℝ) * (S.T : ℝ) ^ dc + 2 * ((S.Unode : ℝ) * ((S.v + 1 : ℕ) : ℝ)))) := by
    exact_mod_cast hKd S hSm
  have h2 := core_arith (q := (S.Q : ℝ)) (x2 := ((S.nS : ℕ) : ℝ) ^ 3)
    (x3 := (2 : ℝ) ^ (S.M / S.m)) (a := (S.Nq : ℝ) ^ S.Q)
    (b := (S.T : ℝ) ^ dc) (u := (S.Unode : ℝ)) (v := ((S.v + 1 : ℕ) : ℝ)) (k := (Kc : ℝ)) (l := (S.L : ℝ))
    (P := (Y : ℝ) ^ S.Q) (D := (Y : ℝ) ^ dc) (y := (Y : ℝ)) (by positivity) (by positivity)
    (one_le_pow₀ (by norm_num)) (by positivity)
    (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hN) _) (by positivity)
    (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hT) _) (by positivity)
    (by exact_mod_cast hU) (by positivity) (by exact_mod_cast hv) hYr (one_le_pow₀ hYr) (one_le_pow₀ hYr)
    (by positivity) (by positivity)
  have hE := exp_part S
  have ePow : (Y : ℝ) ^ (S.Q + dc + 7) = (Y : ℝ) ^ S.Q * (Y : ℝ) ^ dc * (Y : ℝ) ^ 7 := by
    rw [pow_add, pow_add]
  rw [ePow]
  refine hcast.trans (h2.trans ?_)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE (by positivity)) (by positivity)

end OnePigeonhole.Pseudo.Final
