import DominantStrings.Pseudo.RectSpec

/-!
# One step as a program

From a program for the weights of a level with `K' * K'` words, `wtNext` is a program for the weights of the next level.
From a program for its word functions, `wordNext` is a program for the word functions of the next level. The direction and the bits of
the choices come from the code in the frame.

Each helper of `Prog.lean` has its own lemma. It proves the value and the cost together, for a variable direction.
The costs are multiples of the monomials `mon K' C n = (K' + 1) ^ n * (C + 1)`, so the arithmetic of costs is linear.
-/

namespace DominantStrings.Pseudo

open Finset TransposeBase.Pseudo TransposeBase.Pseudo.Leaf

/-- The size conditions of one step. -/
structure StepBig (W : ℕ) (f : Frm) (K' base : ℕ) (w : ℕ → ℕ → ℕ) : Prop where
  rect : RectBig W f.sc f.bk
  hW : (K' + 1) ^ 4 + base + 8 * f.sc + 8 < W
  hsym : ∀ x y, w x y = w y x
  htot : ∑ x ∈ range (K' * K'), ∑ y ∈ range (K' * K'), w x y ≤ f.sc

/-- The bound on the operations of `wtNext`. -/
def nextWtCost (K' C : ℕ) : ℕ := 4000 * (K' + 1) ^ 4 * (C + 1)

/-- The bound on the operations of `wordNext`. `Eb` bounds the number of ends on the words of one `u`. -/
def nextWordCost (K' Cw Cword Eb sc : ℕ) : ℕ :=
  2 ^ Eb * (20000 * (K' + 1) ^ 8 * (Cw + 1) + (K' + 1) ^ 3 * (3 * rectCost sc + 100) + (K' + 1) * (Cword + 1))

namespace StepSpec

/-! ### Branches: only the branch that runs is counted -/

section Rules

variable {W : ℕ} {env : List ℕ} {a b c d : Expr} {x y r : ℕ} {ca cb cc cd : ℕ} {z : ℤ}

theorem run_ite_pos (ha : Run W a env x ca) (hb : Run W b env y cb) (h : x ≤ y)
    (hc : Run W c env r cc) : Run W (.ite a b c d) env r (1 + ca + cb + cc) := by
  refine ⟨by simp only [eval, ha.1, hb.1, if_pos h, hc.1], ?_⟩
  have := ha.2; have := hb.2; have := hc.2
  simp only [ops, ha.1, hb.1, if_pos h]; omega

theorem run_ite_neg (ha : Run W a env x ca) (hb : Run W b env y cb) (h : ¬ x ≤ y)
    (hd : Run W d env r cd) : Run W (.ite a b c d) env r (1 + ca + cb + cd) := by
  refine ⟨by simp only [eval, ha.1, hb.1, if_neg h, hd.1], ?_⟩
  have := ha.2; have := hb.2; have := hd.2
  simp only [ops, ha.1, hb.1, if_neg h]; omega

theorem runZ_ite_pos (ha : Run W a env x ca) (hb : Run W b env y cb) (h : x ≤ y)
    (hc : RunZ W c env z cc) : RunZ W (.ite a b c d) env z (1 + ca + cb + cc) := by
  have := ha.2; have := hb.2; have := hc.2
  refine ⟨?_, ?_⟩
  · have he : eval W (.ite a b c d) env = eval W c env := by simp only [eval, ha.1, hb.1, if_pos h]
    simp only [evalZ, he]; exact hc.1
  · simp only [ops, ha.1, hb.1, if_pos h]; omega

theorem runZ_ite_neg (ha : Run W a env x ca) (hb : Run W b env y cb) (h : ¬ x ≤ y)
    (hd : RunZ W d env z cd) : RunZ W (.ite a b c d) env z (1 + ca + cb + cd) := by
  have := ha.2; have := hb.2; have := hd.2
  refine ⟨?_, ?_⟩
  · have he : eval W (.ite a b c d) env = eval W d env := by simp only [eval, ha.1, hb.1, if_neg h]
    simp only [evalZ, he]; exact hd.1
  · simp only [ops, ha.1, hb.1, if_neg h]; omega

theorem run_eqX_pos (ha : Run W a env x ca) (hb : Run W b env y cb) (h : x = y)
    (hc : Run W c env r cc) : Run W (eqX a b c d) env r (2 + 2 * (ca + cb) + cc) :=
  Run.mono (run_ite_pos ha hb h.le (run_ite_pos hb ha h.ge hc)) (by omega)

theorem run_eqX_neg (ha : Run W a env x ca) (hb : Run W b env y cb) (h : x ≠ y)
    (hd : Run W d env r cd) : Run W (eqX a b c d) env r (2 + 2 * (ca + cb) + cd) := by
  by_cases hxy : x ≤ y
  · exact Run.mono (run_ite_pos ha hb hxy (run_ite_neg hb ha (by omega) hd)) (by omega)
  · exact Run.mono (run_ite_neg ha hb hxy hd) (by omega)

theorem runZ_eqX_pos (ha : Run W a env x ca) (hb : Run W b env y cb) (h : x = y)
    (hc : RunZ W c env z cc) : RunZ W (eqX a b c d) env z (2 + 2 * (ca + cb) + cc) :=
  RunZ.mono (runZ_ite_pos ha hb h.le (runZ_ite_pos hb ha h.ge hc)) (by omega)

theorem runZ_eqX_neg (ha : Run W a env x ca) (hb : Run W b env y cb) (h : x ≠ y)
    (hd : RunZ W d env z cd) : RunZ W (eqX a b c d) env z (2 + 2 * (ca + cb) + cd) := by
  by_cases hxy : x ≤ y
  · exact RunZ.mono (runZ_ite_pos ha hb hxy (runZ_ite_neg hb ha (by omega) hd)) (by omega)
  · exact RunZ.mono (runZ_ite_neg ha hb hxy hd) (by omega)

/-- A test of equality, in the ring of words. -/
theorem runZ_eqTest (ha : Run W a env x ca) (hb : Run W b env y cb) :
    RunZ W (eqX a b (.lit 1) (.lit 0)) env (if x = y then 1 else 0) (3 + 2 * (ca + cb)) := by
  by_cases h : x = y
  · rw [if_pos h]; exact RunZ.mono (runZ_eqX_pos ha hb h RunZ.lit1) (by omega)
  · rw [if_neg h]; exact RunZ.mono (runZ_eqX_neg ha hb h RunZ.lit0) (by omega)

theorem run_minE {W : ℕ} {env : List ℕ} {ia ib a b : ℕ} (ha : env.getD ia 0 = a) (hb : env.getD ib 0 = b) :
    Run W (.ite (.var ia) (.var ib) (.var ia) (.var ib)) env (min a b) 4 := by
  by_cases h : a ≤ b
  · exact Run.mono (Run.eq (run_ite_pos (Run.var ha) (Run.var hb) h (Run.var ha)) (min_eq_left h).symm) (by omega)
  · exact Run.mono (Run.eq (run_ite_neg (Run.var ha) (Run.var hb) h (Run.var hb))
      (min_eq_right (by omega)).symm) (by omega)

theorem run_maxE {W : ℕ} {env : List ℕ} {ia ib a b : ℕ} (ha : env.getD ia 0 = a) (hb : env.getD ib 0 = b) :
    Run W (.ite (.var ia) (.var ib) (.var ib) (.var ia)) env (max a b) 4 := by
  by_cases h : a ≤ b
  · exact Run.mono (Run.eq (run_ite_pos (Run.var ha) (Run.var hb) h (Run.var hb)) (max_eq_right h).symm) (by omega)
  · exact Run.mono (Run.eq (run_ite_neg (Run.var ha) (Run.var hb) h (Run.var ha))
      (max_eq_left (by omega)).symm) (by omega)

end Rules

/-! ### The monomials of the costs -/

/-- A monomial of the costs. -/
def mon (K' C n : ℕ) : ℕ := (K' + 1) ^ n * (C + 1)

theorem mon_pos (K' C n : ℕ) : 1 ≤ mon K' C n := Nat.succ_le_of_lt (by unfold mon; positivity)

theorem mon_succ (K' C n : ℕ) : (K' + 1) * mon K' C n = mon K' C (n + 1) := by unfold mon; ring

theorem mon_two (K' C n : ℕ) : (K' + 1) * (K' + 1) * mon K' C n = mon K' C (n + 2) := by unfold mon; ring

theorem mon_le_succ (K' C n : ℕ) : mon K' C n ≤ mon K' C (n + 1) := by
  rw [← mon_succ]
  exact Nat.le_mul_of_pos_left _ (by omega)

/-- The chain of the monomials, for `omega`. -/
theorem mon_chain (K' C : ℕ) : C + 1 = mon K' C 0 ∧ 1 ≤ mon K' C 0 ∧ mon K' C 0 ≤ mon K' C 1 ∧
    mon K' C 1 ≤ mon K' C 2 ∧ mon K' C 2 ≤ mon K' C 3 ∧ mon K' C 3 ≤ mon K' C 4 ∧ mon K' C 4 ≤ mon K' C 5 ∧
    mon K' C 5 ≤ mon K' C 6 ∧ mon K' C 6 ≤ mon K' C 7 ∧ mon K' C 7 ≤ mon K' C 8 :=
  ⟨by simp [mon], mon_pos .., mon_le_succ .., mon_le_succ .., mon_le_succ .., mon_le_succ .., mon_le_succ ..,
    mon_le_succ .., mon_le_succ .., mon_le_succ ..⟩

theorem loop_le {P M R c cn B : ℕ} (hP : 1 ≤ P) (hM : 1 ≤ M) (hB : B ≤ c * M + R) :
    1 + cn + P * (B + 1) ≤ (c + cn + 2) * (P * M) + P * R := by
  have h1 : 1 ≤ P * M := Nat.mul_pos hP hM
  have h2 : P * (B + 1) ≤ P * (c * M + R + M) := Nat.mul_le_mul_left _ (by omega)
  have h3 : P * (c * M + R + M) = c * (P * M) + P * R + P * M := by ring
  have h4 : (c + cn + 2) * (P * M) = c * (P * M) + cn * (P * M) + 2 * (P * M) := by ring
  have h5 : cn * 1 ≤ cn * (P * M) := Nat.mul_le_mul_left _ h1
  omega

/-- A loop below `K' + 1`. -/
theorem loop_mon1 {K' C n c cn B : ℕ} (hB : B ≤ c * mon K' C n) :
    1 + cn + (K' + 1) * (B + 1) ≤ (c + cn + 2) * mon K' C (n + 1) := by
  have := loop_le (P := K' + 1) (R := 0) (cn := cn) (by omega) (mon_pos K' C n) (by omega : B ≤ c * mon K' C n + 0)
  rwa [mon_succ, Nat.mul_zero, Nat.add_zero] at this

/-- A loop below `(K' + 1) * (K' + 1)`. -/
theorem loop_mon2 {K' C n c cn B : ℕ} (hB : B ≤ c * mon K' C n) :
    1 + cn + (K' + 1) * (K' + 1) * (B + 1) ≤ (c + cn + 2) * mon K' C (n + 2) := by
  have := loop_le (P := (K' + 1) * (K' + 1)) (R := 0) (cn := cn) (Nat.mul_pos (by omega) (by omega))
    (mon_pos K' C n) (by omega : B ≤ c * mon K' C n + 0)
  rwa [mon_two, Nat.mul_zero, Nat.add_zero] at this

/-! ### The context of the helpers -/

section Helpers

variable {W : ℕ} {f : Frm} {K' base C : ℕ} {wt : ℕ → ℕ → ℕ → Expr} {w : ℕ → ℕ → ℕ}

/-- The hypotheses of one step. -/
structure StepCtx (W : ℕ) (f : Frm) (K' base C : ℕ) (wt : ℕ → ℕ → ℕ → Expr) (w : ℕ → ℕ → ℕ) : Prop where
  big : StepBig W f K' base w
  hK : 0 < K'
  hwt : WtSpec W f (K' * K') wt w C

/-- The level of the step, for a direction. -/
abbrev lvl (K' base : ℕ) (f : Frm) (w : ℕ → ℕ → ℕ) (dir : Bool) : Lev :=
  ⟨K', w, f.c / 2 ^ base % 2 ^ K' ^ 4, dir, f.sc⟩

local notation "L" => lvl K' base f w

namespace StepCtx

variable (H : StepCtx W f K' base C wt w)
include H

theorem K4 : K' ^ 4 + base + 8 * f.sc + 8 < W := by
  have h1 : K' ^ 4 ≤ (K' + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have := H.big.hW
  omega

theorem ltW {n : ℕ} (h : n ≤ K' ^ 4 + base + 8 * f.sc + 7) : n < W := by
  have := H.K4
  omega

theorem lt2 {n : ℕ} (h : n ≤ K' ^ 4 + base + 8 * f.sc + 8) : n < 2 ^ W := by
  have := H.K4
  exact lt_trans (by omega : n < W) Nat.lt_two_pow_self

theorem KK_le : K' * K' ≤ K' ^ 4 := by
  have h : 1 ≤ K' := H.hK
  calc K' * K' = K' ^ 2 := by ring
    _ ≤ K' ^ 4 := Nat.pow_le_pow_right h (by norm_num)

theorem K_le : K' ≤ K' ^ 4 := by
  have h : 1 ≤ K' := H.hK
  calc K' = K' ^ 1 := by ring
    _ ≤ K' ^ 4 := Nat.pow_le_pow_right h (by norm_num)

theorem run_wt {env : List ℕ} {g ix iy x y : ℕ} (hf : f.At env g) (hx : env.getD ix 0 = x)
    (hy : env.getD iy 0 = y) (hxK : x < K' * K') (hyK : y < K' * K') : Run W (wt g ix iy) env (w x y) C :=
  H.hwt hf hx hy hxK hyK

/-! #### Sizes of the weights -/

theorem w_le {x y : ℕ} (hx : x < K' * K') (hy : y < K' * K') : w x y ≤ f.sc :=
  (DominantStrings.le_total hx hy).trans H.big.htot

theorem ends_le {x : ℕ} (hx : x < K' * K') : ∑ y ∈ range (K' * K'), w x y ≤ f.sc :=
  (single_le_sum (f := fun x => ∑ y ∈ range (K' * K'), w x y) (fun _ _ => Nat.zero_le _) (mem_range.mpr hx)).trans
    H.big.htot

theorem off_le {x y : ℕ} (hx : x < K' * K') (hy : y ≤ K' * K') : ∑ t ∈ range y, w x t ≤ f.sc :=
  (sum_le_sum_of_subset (range_subset_range.mpr hy)).trans (H.ends_le hx)

end StepCtx

theorem wd_lt {dir : Bool} {u v : ℕ} (hu : u < K') (hv : v < K') : (L dir).wd u v < K' * K' := by
  cases dir
  · exact digit_lt hv hu
  · exact digit_lt hu hv

/-! #### The direction and the coordinates -/

theorem run_wdE (H : StepCtx W f K' base C wt w) {env : List ℕ} {id iu iv u v : ℕ} {dir : Bool}
    (hd : env.getD id 0 = dir.toNat) (hu : env.getD iu 0 = u) (hv : env.getD iv 0 = v)
    (huK : u < K') (hvK : v < K') : Run W (wdE K' id iu iv) env ((L dir).wd u v) 8 := by
  have hl := H.KK_le
  have hk := H.K_le
  have h1 := digit_lt huK hvK
  have h2 := digit_lt hvK huK
  have r1 : Run W (.add (.mul (.var iu) (.lit K')) (.var iv)) env (u * K' + v) 5 :=
    Run.mono (Run.add (Run.mul (Run.var hu) (Run.lit (H.lt2 (by omega))) (H.lt2 (by omega))) (Run.var hv)
      (H.lt2 (by omega))) (by omega)
  have r2 : Run W (.add (.mul (.var iv) (.lit K')) (.var iu)) env (v * K' + u) 5 :=
    Run.mono (Run.add (Run.mul (Run.var hv) (Run.lit (H.lt2 (by omega))) (H.lt2 (by omega))) (Run.var hu)
      (H.lt2 (by omega))) (by omega)
  have l0 : Run W (.lit 0) env 0 1 := Run.lit (H.lt2 (by omega))
  cases dir with
  | false => exact Run.mono (run_ite_pos (Run.var hd) l0 (le_refl _) r2) (by omega)
  | true => exact Run.mono (run_ite_neg (Run.var hd) l0 (by simp) r1) (by omega)

theorem run_pairMinE {W : ℕ} (hW : 2 ≤ W) {env : List ℕ} {ia ib a b : ℕ} (ha : env.getD ia 0 = a)
    (hb : env.getD ib 0 = b) (hlt : a < 2 ^ W) : Run W (pairMinE ia ib) env (pairMin a b) 16 :=
  Run.mono (run_minE ha hb) (by omega)

theorem pm_of_ne {dir : Bool} {u u' v v' : ℕ} (h1 : u ≠ u') (h2 : v ≠ v') :
    (L dir).pm u u' v v' = pairMin (w ((L dir).wd u v) ((L dir).wd u' v')) (w ((L dir).wd u v') ((L dir).wd u' v)) := by
  simp [Lev.pm, h1, h2]

theorem pm_le_w {dir : Bool} {u u' v v' : ℕ} : (L dir).pm u u' v v' ≤ w ((L dir).wd u v) ((L dir).wd u' v') := by
  by_cases h : u = u' ∨ v = v'
  · simp [Lev.pm, h]
  · simp only [Lev.pm, if_neg h]
    exact pairMin_le_left _ _

theorem run_pmE (H : StepCtx W f K' base C wt w) {env : List ℕ} {g id iu iu' iv iv' u u' v v' : ℕ} {dir : Bool}
    (hf : f.At env g) (hd : env.getD id 0 = dir.toNat) (hu : env.getD iu 0 = u) (hu' : env.getD iu' 0 = u')
    (hv : env.getD iv 0 = v) (hv' : env.getD iv' 0 = v')
    (huK : u < K') (huK' : u' < K') (hvK : v < K') (hvK' : v' < K') :
    Run W (pmE K' wt g id iu iu' iv iv') env ((L dir).pm u u' v v') (66 + 2 * C) := by
  have hl0 : Run W (.lit 0) env 0 1 := Run.lit (H.lt2 (by omega))
  by_cases h1 : u = u'
  · exact Run.mono (Run.eq (run_eqX_pos (Run.var hu) (Run.var hu') h1 hl0) (by simp [Lev.pm, h1])) (by omega)
  by_cases h2 : v = v'
  · exact Run.mono (Run.eq (run_eqX_neg (Run.var hu) (Run.var hu') h1
      (run_eqX_pos (Run.var hv) (Run.var hv') h2 hl0)) (by simp [Lev.pm, h2])) (by omega)
  rw [pm_of_ne h1 h2]
  have x1 := wd_lt (K' := K') (base := base) (f := f) (w := w) (dir := dir) huK hvK
  have x2 := wd_lt (K' := K') (base := base) (f := f) (w := w) (dir := dir) huK' hvK'
  have x3 := wd_lt (K' := K') (base := base) (f := f) (w := w) (dir := dir) huK hvK'
  have x4 := wd_lt (K' := K') (base := base) (f := f) (w := w) (dir := dir) huK' hvK
  have hsc := H.w_le x1 x2
  refine Run.mono (run_eqX_neg (Run.var hu) (Run.var hu') h1 (run_eqX_neg (Run.var hv) (Run.var hv') h2
    (Run.letE (run_wdE H hd hu hv huK hvK) (Run.letE (run_wdE H hd hu' hv' huK' hvK')
    (Run.letE (run_wdE H hd hu hv' huK hvK') (Run.letE (run_wdE H hd hu' hv huK' hvK)
    (Run.letE (H.run_wt ((((hf.up _).up _).up _).up _) rfl rfl x1 x2)
    (Run.letE (H.run_wt ((((((hf.up _).up _).up _).up _).up _)) rfl rfl x3 x4)
      (run_pairMinE (by have := H.K4; omega) rfl rfl (H.lt2 (by omega))))))))))) (by omega)

/-! #### The bit of a rectangle -/

theorem digit4_lt {K' a b c e : ℕ} (ha : a < K') (hb : b < K') (hc : c < K') (he : e < K') :
    ((a * K' + b) * K' + c) * K' + e < K' ^ 4 := by
  have step : ∀ {x n y : ℕ}, x < n → y < K' → x * K' + y < n * K' := by
    intro x n y hx hy
    calc x * K' + y < x * K' + K' := by omega
      _ = (x + 1) * K' := by ring
      _ ≤ n * K' := Nat.mul_le_mul_right _ hx
  have h1 := step ha hb
  have h2 := step h1 hc
  have h3 := step h2 he
  calc _ < K' * K' * K' * K' := h3
    _ = K' ^ 4 := by ring

theorem run_d4 (H : StepCtx W f K' base C wt w) {env : List ℕ} {ia ib ic ie a b c e : ℕ}
    (ha : env.getD ia 0 = a) (hb : env.getD ib 0 = b) (hc : env.getD ic 0 = c) (he : env.getD ie 0 = e)
    (haK : a < K') (hbK : b < K') (hcK : c < K') (heK : e < K') :
    Run W (.add (.mul (.add (.mul (.add (.mul (.var ia) (.lit K')) (.var ib)) (.lit K')) (.var ic)) (.lit K')) (.var ie))
      env (((a * K' + b) * K' + c) * K' + e) 13 := by
  have h := digit4_lt haK hbK hcK heK
  have hk := H.K_le
  have h1 : (a * K' + b) * K' + c ≤ ((a * K' + b) * K' + c) * K' := Nat.le_mul_of_pos_right _ H.hK
  have h2 : a * K' + b ≤ (a * K' + b) * K' := Nat.le_mul_of_pos_right _ H.hK
  exact Run.mono (Run.add (Run.mul (Run.add (Run.mul (Run.add (Run.mul (Run.var ha) (Run.lit (H.lt2 (by omega)))
    (H.lt2 (by omega))) (Run.var hb) (H.lt2 (by omega))) (Run.lit (H.lt2 (by omega))) (H.lt2 (by omega)))
    (Run.var hc) (H.lt2 (by omega))) (Run.lit (H.lt2 (by omega))) (H.lt2 (by omega))) (Run.var he)
    (H.lt2 (by omega))) (by omega)

theorem idx_lt {dir : Bool} {u u' v v' : ℕ} (huK : u < K') (huK' : u' < K') (hvK : v < K') (hvK' : v' < K') :
    (L dir).idx u u' v v' < K' ^ 4 := by
  cases dir
  · exact digit4_lt hvK hvK' huK huK'
  · exact digit4_lt huK huK' hvK hvK'

theorem run_idxE (H : StepCtx W f K' base C wt w) {env : List ℕ} {id iu iu' iv iv' u u' v v' : ℕ} {dir : Bool}
    (hd : env.getD id 0 = dir.toNat) (hu : env.getD iu 0 = u) (hu' : env.getD iu' 0 = u')
    (hv : env.getD iv 0 = v) (hv' : env.getD iv' 0 = v')
    (huK : u < K') (huK' : u' < K') (hvK : v < K') (hvK' : v' < K') :
    Run W (idxE K' id iu iu' iv iv') env ((L dir).idx u u' v v') 16 := by
  have l0 : Run W (.lit 0) env 0 1 := Run.lit (H.lt2 (by omega))
  cases dir with
  | false => exact Run.mono (run_ite_pos (Run.var hd) l0 (le_refl _) (run_d4 H hv hv' hu hu' hvK hvK' huK huK')) (by omega)
  | true => exact Run.mono (run_ite_neg (Run.var hd) l0 (by simp) (run_d4 H hu hu' hv hv' huK huK' hvK hvK')) (by omega)

theorem pol_eq {dir : Bool} {u u' v v' : ℕ} (huK : u < K') (huK' : u' < K') (hvK : v < K') (hvK' : v' < K') :
    (L dir).pol u u' v v' = !(f.c.testBit (base + (L dir).idx u u' v v')) := by
  have hlt := idx_lt (base := base) (f := f) (w := w) (dir := dir) huK huK' hvK hvK'
  simp only [Lev.pol]
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm]
  simp [hlt]

theorem run_polE (H : StepCtx W f K' base C wt w) {env : List ℕ} {g id iu iu' iv iv' u u' v v' : ℕ} {dir : Bool}
    (hf : f.At env g) (hd : env.getD id 0 = dir.toNat) (hu : env.getD iu 0 = u) (hu' : env.getD iu' 0 = u')
    (hv : env.getD iv 0 = v) (hv' : env.getD iv' 0 = v')
    (huK : u < K') (huK' : u' < K') (hvK : v < K') (hvK' : v' < K') :
    Run W (polE K' base g id iu iu' iv iv') env ((L dir).pol u u' v v').toNat 26 := by
  have hlt := idx_lt (base := base) (f := f) (w := w) (dir := dir) huK huK' hvK hvK'
  have hW2 : 2 ≤ W := by have := H.K4; omega
  have hbit : Run W (bitX g (.add (.lit base) (idxE K' id iu iu' iv iv'))) env
      (f.c.testBit (base + (L dir).idx u u' v v')).toNat 23 :=
    Run.mono (Run.bitX hf.c (Run.add (Run.lit (H.lt2 (by omega))) (run_idxE H hd hu hu' hv hv' huK huK' hvK hvK')
      (H.lt2 (by omega))) (H.ltW (by omega)) hW2) (by omega)
  have l0 : Run W (.lit 0) env 0 1 := Run.lit (H.lt2 (by omega))
  have l1 : Run W (.lit 1) env 1 1 := Run.lit (H.lt2 (by omega))
  rw [pol_eq huK huK' hvK hvK']
  cases hb : f.c.testBit (base + (L dir).idx u u' v v') with
  | false =>
    rw [hb] at hbit
    exact Run.mono (run_ite_pos hbit l0 (le_refl _) l1) (by omega)
  | true =>
    rw [hb] at hbit
    exact Run.mono (run_ite_neg hbit l0 (by simp) l0) (by omega)

theorem run_dLenE {W : ℕ} {env : List ℕ} {ic im : ℕ} {cheap : Bool} {m : ℕ} (hc : env.getD ic 0 = cheap.toNat)
    (hm : env.getD im 0 = m) (hlt : 4 * m + 8 < 2 ^ W) : Run W (dLenE ic im) env (dLen cheap m) 20 := by
  have l0 : Run W (.lit 0) env 0 1 := Run.lit (by omega)
  have l2 : Run W (.lit 2) env 2 1 := Run.lit (by omega)
  have l4 : Run W (.lit 4) env 4 1 := Run.lit (by omega)
  have l5 : Run W (.lit 5) env 5 1 := Run.lit (by omega)
  have l8 : Run W (.lit 8) env 8 1 := Run.lit (by omega)
  cases cheap with
  | false =>
    have hr : Run W (.mul (.lit 2) (.var im)) env (2 * m) 3 :=
      Run.mono (Run.mul l2 (Run.var hm) (by omega)) (by omega)
    exact Run.mono (Run.eq (run_ite_pos (Run.var hc) l0 (le_refl _) hr) (by simp [dLen])) (by omega)
  | true =>
    have l1 : Run W (.lit 1) env 1 1 := Run.lit (by omega)
    have hr : m ≠ 0 → Run W (.add (.sub (.var im) (.lit 1))
        (.div (.add (.mul (.lit 8) (.div (.var im) (.lit 2))) (.lit 4)) (.lit 5))) env
        (m - 1 + (8 * (m / 2) + 4) / 5) 13 := fun h0 =>
      Run.mono (Run.add (Run.sub (Run.var hm) l1 (by omega) (by omega))
        (Run.div (Run.add (Run.mul l8 (Run.div (Run.var hm) l2) (by omega)) l4 (by omega)) l5) (by omega)) (by omega)
    by_cases h0 : m = 0
    · subst h0
      exact Run.mono (Run.eq (run_ite_neg (Run.var hc) l0 (by simp) (run_ite_pos (Run.var hm) l0 (le_refl _) l0))
        (by simp [dLen])) (by omega)
    · exact Run.mono (Run.eq (run_ite_neg (Run.var hc) l0 (by simp)
        (run_ite_neg (Run.var hm) l0 (by omega) (hr h0))) (by simp [dLen, h0])) (by omega)

theorem dLen_le_two (b : Bool) (m : ℕ) : dLen b m ≤ 2 * m := by
  simp only [dLen]
  split_ifs <;> omega

theorem run_beq {W : ℕ} (hW : 2 ≤ W) {env : List ℕ} {ia ib : ℕ} {p q : Bool} (ha : env.getD ia 0 = p.toNat)
    (hb : env.getD ib 0 = q.toNat) : Run W (eqX (.var ia) (.var ib) (.lit 1) (.lit 0)) env (p == q).toNat 7 := by
  have h1 : (1 : ℕ) < 2 ^ W := Nat.one_lt_two_pow (by omega)
  by_cases h : p = q
  · subst h
    have e : (p == p).toNat = 1 := by simp
    rw [e]
    exact Run.mono (run_eqX_pos (Run.var ha) (Run.var hb) rfl (Run.lit h1)) (by omega)
  · have e : (p == q).toNat = 0 := by cases p <;> cases q <;> simp_all
    rw [e]
    have hne : p.toNat ≠ q.toNat := by cases p <;> cases q <;> simp_all
    exact Run.mono (run_eqX_neg (Run.var ha) (Run.var hb) hne (Run.lit (by omega))) (by omega)

theorem pm_le_sc (H : StepCtx W f K' base C wt w) {dir : Bool} {u u' v v' : ℕ} (huK : u < K') (huK' : u' < K')
    (hvK : v < K') (hvK' : v' < K') : (L dir).pm u u' v v' ≤ f.sc :=
  pm_le_w.trans (H.w_le (wd_lt huK hvK) (wd_lt huK' hvK'))

theorem dd_le {dir : Bool} {u u' v v' : ℕ} : (L dir).dd u u' v v' ≤ 2 * (L dir).pm u u' v v' := by
  simp only [Lev.dd]
  split_ifs
  · exact dLen_le_two _ _
  · exact Nat.zero_le _

theorem run_ddE (H : StepCtx W f K' base C wt w) {env : List ℕ} {g id iu iu' iv iv' u u' v v' : ℕ} {dir : Bool}
    (hf : f.At env g) (hd : env.getD id 0 = dir.toNat) (hu : env.getD iu 0 = u) (hu' : env.getD iu' 0 = u')
    (hv : env.getD iv 0 = v) (hv' : env.getD iv' 0 = v')
    (huK : u < K') (huK' : u' < K') (hvK : v < K') (hvK' : v' < K') :
    Run W (ddE K' base wt g id iu iu' iv iv') env ((L dir).dd u u' v v') (125 + 2 * C) := by
  have l0 : Run W (.lit 0) env 0 1 := Run.lit (H.lt2 (by omega))
  by_cases hvv : v' ≤ v
  · have e : (L dir).dd u u' v v' = 0 := by simp [Lev.dd, not_lt.mpr hvv]
    rw [e]
    exact Run.mono (run_ite_pos (Run.var hv') (Run.var hv) hvv l0) (by omega)
  · have hlt : v < v' := by omega
    have e : (L dir).dd u u' v v' = dLen ((L dir).pol u u' v v' == dir) ((L dir).pm u u' v v') := by
      simp [Lev.dd, hlt]
    rw [e]
    have hsc := pm_le_sc H (dir := dir) huK huK' hvK hvK'
    exact Run.mono (run_ite_neg (Run.var hv') (Run.var hv) hvv
      (Run.letE (run_polE H hf hd hu hu' hv hv' huK huK' hvK hvK')
      (Run.letE (run_pmE H (hf.up _) hd hu hu' hv hv' huK huK' hvK hvK')
      (Run.letE (run_beq (by have := H.K4; omega) rfl hd)
        (run_dLenE rfl rfl (H.lt2 (by omega))))))) (by omega)

theorem run_carryE (H : StepCtx W f K' base C wt w) {env : List ℕ} {g id iu iu' iv iv' u u' v v' : ℕ} {dir : Bool}
    (hf : f.At env g) (hd : env.getD id 0 = dir.toNat) (hu : env.getD iu 0 = u) (hu' : env.getD iu' 0 = u')
    (hv : env.getD iv 0 = v) (hv' : env.getD iv' 0 = v')
    (huK : u < K') (huK' : u' < K') (hvK : v < K') (hvK' : v' < K') :
    Run W (carryE K' wt g id iu iu' iv iv') env ((L dir).carry u u' v v') (85 + 3 * C) := by
  have x1 := wd_lt (base := base) (f := f) (w := w) (dir := dir) huK hvK
  have x2 := wd_lt (base := base) (f := f) (w := w) (dir := dir) huK' hvK'
  have hsc := H.w_le x1 x2
  have hle : (L dir).pm u u' v v' ≤ w ((L dir).wd u v) ((L dir).wd u' v') := pm_le_w
  have hlt : w ((L dir).wd u v) ((L dir).wd u' v') < 2 ^ W := H.lt2 (by omega)
  have hf2 := (hf.up ((L dir).wd u v)).up ((L dir).wd u' v')
  exact Run.mono (Run.letE (run_wdE H hd hu hv huK hvK) (Run.letE (run_wdE H hd hu' hv' huK' hvK')
    (Run.sub (H.run_wt hf2 rfl rfl x1 x2) (run_pmE H hf2 hd hu hu' hv hv' huK huK' hvK hvK') hlt hle))) (by omega)

theorem seg_le (H : StepCtx W f K' base C wt w) {dir : Bool} {u u' v v' : ℕ} (huK : u < K') (huK' : u' < K')
    (hvK : v < K') (hvK' : v' < K') : (L dir).seg u u' v v' ≤ 3 * f.sc := by
  have h1 := pm_le_sc H (dir := dir) huK huK' hvK hvK'
  have h2 := dd_le (K' := K') (base := base) (f := f) (w := w) (dir := dir) (u := u) (u' := u') (v := v) (v' := v')
  have h3 := H.w_le (wd_lt (base := base) (f := f) (w := w) (dir := dir) huK hvK)
    (wd_lt (base := base) (f := f) (w := w) (dir := dir) huK' hvK')
  simp only [Lev.seg, Lev.carry] at h2 ⊢
  omega

theorem run_segE (H : StepCtx W f K' base C wt w) {env : List ℕ} {g id iu iu' iv iv' u u' v v' : ℕ} {dir : Bool}
    (hf : f.At env g) (hd : env.getD id 0 = dir.toNat) (hu : env.getD iu 0 = u) (hu' : env.getD iu' 0 = u')
    (hv : env.getD iv 0 = v) (hv' : env.getD iv' 0 = v')
    (huK : u < K') (huK' : u' < K') (hvK : v < K') (hvK' : v' < K') :
    Run W (segE K' base wt g id iu iu' iv iv') env ((L dir).seg u u' v v') (211 + 5 * C) := by
  have h := seg_le H (dir := dir) huK huK' hvK hvK'
  exact Run.mono (Run.add (run_carryE H hf hd hu hu' hv hv' huK huK' hvK hvK')
    (run_ddE H hf hd hu hu' hv hv' huK huK' hvK hvK') (H.lt2 (by unfold Lev.seg at h; omega))) (by omega)

theorem run_segSE (H : StepCtx W f K' base C wt w) {env : List ℕ} {g id iu iu' is u u' s : ℕ} {dir : Bool}
    (hf : f.At env g) (hd : env.getD id 0 = dir.toNat) (hu : env.getD iu 0 = u) (hu' : env.getD iu' 0 = u')
    (hs : env.getD is 0 = s) (huK : u < K') (huK' : u' < K') (hsK : s < K' * K') :
    Run W (segSE K' base wt g id iu iu' is) env ((L dir).segS u u' s) (219 + 5 * C) := by
  have hk := H.K_le
  have l1 : Run W (.lit K') env K' 1 := Run.lit (H.lt2 (by omega))
  have r1 : Run W (.div (.var is) (.lit K')) env (s / K') 3 := Run.mono (Run.div (Run.var hs) l1) (by omega)
  have r2 : Run W (.mod (.var (is + 1)) (.lit K')) (s / K' :: env) (s % K') 3 :=
    Run.mono (Run.mod (Run.var hs) (Run.lit (H.lt2 (by omega)))) (by omega)
  exact Run.mono (Run.letE r1 (Run.letE r2 (run_segE H ((hf.up _).up _) hd hu hu' rfl rfl huK huK'
    (digit_div_lt hsK) (digit_mod_lt hsK)))) (by omega)

/-! #### The new weights -/

theorem newW_total (H : StepCtx W f K' base C wt w) {dir : Bool} :
    ∑ u ∈ range K', ∑ u' ∈ range K', (L dir).newW u u' ≤ f.sc :=
  (newW_total_le (L dir) H.hK H.big.hsym).trans H.big.htot

theorem newW_le_sc (H : StepCtx W f K' base C wt w) {dir : Bool} {u u' : ℕ} (hu : u < K') (hu' : u' < K') :
    (L dir).newW u u' ≤ f.sc :=
  (DominantStrings.le_total hu hu').trans (newW_total H)

theorem newW_off_le (H : StepCtx W f K' base C wt w) {dir : Bool} {u u' : ℕ} (hu : u < K') (hu' : u' ≤ K') :
    ∑ t ∈ range u', (L dir).newW u t ≤ f.sc :=
  (sum_le_sum_of_subset (range_subset_range.mpr hu')).trans
    ((single_le_sum (f := fun u => ∑ u' ∈ range K', (L dir).newW u u') (fun _ _ => Nat.zero_le _)
      (mem_range.mpr hu)).trans (newW_total H))

theorem KK_le_PP (K' : ℕ) : K' * K' ≤ (K' + 1) * (K' + 1) := Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)

theorem run_newWE (H : StepCtx W f K' base C wt w) {env : List ℕ} {g id iu iu' u u' : ℕ} {dir : Bool}
    (hf : f.At env g) (hd : env.getD id 0 = dir.toNat) (hu : env.getD iu 0 = u) (hu' : env.getD iu' 0 = u')
    (huK : u < K') (huK' : u' < K') :
    Run W (newWE K' base wt g id iu iu') env ((L dir).newW u u') (243 * mon K' C 2) := by
  have hc := mon_chain K' C
  by_cases h : u = u'
  · have e : (L dir).newW u u' = 0 := by simp [Lev.newW, h]
    rw [e]
    exact Run.mono (run_eqX_pos (Run.var hu) (Run.var hu') h (Run.lit (H.lt2 (by omega)))) (by omega)
  · have e : (L dir).newW u u' = ∑ s ∈ range (K' * K'), (L dir).segS (min u u') (max u u') s := by
      simp [Lev.newW, h]
    have hle := newW_le_sc H (dir := dir) huK huK'
    rw [e] at hle ⊢
    have hmin : min u u' < K' := lt_of_le_of_lt (min_le_left _ _) huK
    have hmax : max u u' < K' := max_lt huK huK'
    have hl := H.KK_le
    have hsum : Run W (.sum (.lit (K' * K')) (segSE K' base wt (g + 3) (id + 3) 2 1 0))
        (max u u' :: min u u' :: env) (∑ s ∈ range (K' * K'), (L dir).segS (min u u') (max u u') s)
        (1 + 1 + (K' + 1) * (K' + 1) * (219 + 5 * C + 1)) :=
      Run.sum (Run.lit (H.lt2 (by omega))) (KK_le_PP K')
        (fun s hs => run_segSE H (((hf.up _).up _).up s) hd rfl rfl rfl hmin hmax hs) (H.lt2 (by omega))
    have hb : 1 + 1 + (K' + 1) * (K' + 1) * (219 + 5 * C + 1) ≤ (224 + 1 + 2) * mon K' C 2 :=
      loop_mon2 (K' := K') (C := C) (n := 0) (c := 224) (cn := 1) (B := 219 + 5 * C) (by omega)
    exact Run.mono (run_eqX_neg (Run.var hu) (Run.var hu') h (Run.letE (run_minE hu hu') (Run.letE (run_maxE hu hu') hsum)))
      (by omega)

theorem psi_le (H : StepCtx W f K' base C wt w) {dir : Bool} : psi K' (L dir).newW ≤ f.sc * f.sc := by
  unfold psi
  calc ∑ x ∈ range K', ∑ y ∈ range K', (L dir).newW x y ^ 2
      ≤ ∑ x ∈ range K', ∑ y ∈ range K', f.sc * (L dir).newW x y :=
        sum_le_sum fun x hx => sum_le_sum fun y hy => by
          rw [sq]
          exact Nat.mul_le_mul_right _ (newW_le_sc H (mem_range.mp hx) (mem_range.mp hy))
    _ = f.sc * ∑ x ∈ range K', ∑ y ∈ range K', (L dir).newW x y := by simp only [mul_sum]
    _ ≤ f.sc * f.sc := Nat.mul_le_mul_left _ (newW_total H)

theorem sc_sq_lt (H : StepCtx W f K' base C wt w) : f.sc * f.sc < 2 ^ W := by
  have h1 : f.sc < 2 ^ f.sc := Nat.lt_two_pow_self
  calc f.sc * f.sc ≤ 2 ^ f.sc * 2 ^ f.sc := Nat.mul_le_mul h1.le h1.le
    _ = 2 ^ (f.sc + f.sc) := by rw [pow_add]
    _ < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by have := H.K4; omega)

theorem run_psiE (H : StepCtx W f K' base C wt w) {env : List ℕ} {g id : ℕ} {dir : Bool}
    (hf : f.At env g) (hd : env.getD id 0 = dir.toNat) :
    Run W (psiE K' base wt g id) env (psi K' (L dir).newW) (253 * mon K' C 4) := by
  have hc := mon_chain K' C
  have hk := H.K_le
  have hpsi := psi_le H (dir := dir)
  have hsq := sc_sq_lt H
  have hbody : ∀ x < K', ∀ y < K', Run W (.letE (newWE K' base wt (g + 2) (id + 2) 1 0) (.mul (.var 0) (.var 0)))
      (y :: x :: env) ((L dir).newW x y ^ 2) (247 * mon K' C 2) := by
    intro x hx y hy
    have hn : Run W (newWE K' base wt (g + 2) (id + 2) 1 0) (y :: x :: env) ((L dir).newW x y) (243 * mon K' C 2) :=
      run_newWE H ((hf.up x).up y) hd rfl rfl hx hy
    have hle := newW_le_sc H (dir := dir) hx hy
    have hlt : (L dir).newW x y * (L dir).newW x y < 2 ^ W :=
      lt_of_le_of_lt (Nat.mul_le_mul hle hle) hsq
    have hmul : Run W (.mul (.var 0) (.var 0)) ((L dir).newW x y :: y :: x :: env) ((L dir).newW x y ^ 2) 3 :=
      Run.mono (Run.eq (Run.mul (Run.var rfl) (Run.var rfl) hlt) (sq _).symm) (by omega)
    exact Run.mono (Run.letE hn hmul) (by omega)
  have hinner : ∀ x < K', Run W (.sum (.lit K') (.letE (newWE K' base wt (g + 2) (id + 2) 1 0) (.mul (.var 0) (.var 0))))
      (x :: env) (∑ y ∈ range K', (L dir).newW x y ^ 2) (250 * mon K' C 3) := by
    intro x hx
    have hle : ∑ y ∈ range K', (L dir).newW x y ^ 2 ≤ f.sc * f.sc :=
      (single_le_sum (f := fun x => ∑ y ∈ range K', (L dir).newW x y ^ 2) (fun _ _ => Nat.zero_le _)
        (mem_range.mpr hx)).trans hpsi
    have hb : 1 + 1 + (K' + 1) * (247 * mon K' C 2 + 1) ≤ (247 + 1 + 2) * mon K' C 3 :=
      loop_mon1 (K' := K') (C := C) (n := 2) (c := 247) (cn := 1) (B := 247 * mon K' C 2) le_rfl
    exact Run.mono (Run.sum (T := K' + 1) (Run.lit (H.lt2 (by omega))) (Nat.le_succ _) (hbody x hx)
      (lt_of_le_of_lt hle hsq)) (by omega)
  have hb : 1 + 1 + (K' + 1) * (250 * mon K' C 3 + 1) ≤ (250 + 1 + 2) * mon K' C 4 :=
    loop_mon1 (K' := K') (C := C) (n := 3) (c := 250) (cn := 1) (B := 250 * mon K' C 3) le_rfl
  exact Run.mono (Run.sum (T := K' + 1) (Run.lit (H.lt2 (by omega))) (Nat.le_succ _) hinner
    (lt_of_le_of_lt hpsi hsq)) (by omega)

theorem run_dirE (H : StepCtx W f K' base C wt w) {env : List ℕ} {g : ℕ} (hf : f.At env g) :
    Run W (dirE K' base wt g) env (dirOf K' w f.sc (f.c / 2 ^ base % 2 ^ K' ^ 4)).toNat (512 * mon K' C 4) := by
  have hc := mon_chain K' C
  have h1 : Run W (.letE (.lit 1) (psiE K' base wt (g + 1) 0)) env (psi K' (L true).newW) (2 + 253 * mon K' C 4) :=
    Run.mono (Run.letE (Run.lit (H.lt2 (by omega))) (run_psiE H (hf.up 1) rfl)) (by omega)
  have h0 : Run W (.letE (.lit 0) (psiE K' base wt (g + 1) 0)) env (psi K' (L false).newW) (2 + 253 * mon K' C 4) :=
    Run.mono (Run.letE (Run.lit (H.lt2 (by omega))) (run_psiE H (hf.up 0) rfl)) (by omega)
  have l1 : Run W (.lit 1) env 1 1 := Run.lit (H.lt2 (by omega))
  have l0 : Run W (.lit 0) env 0 1 := Run.lit (H.lt2 (by omega))
  by_cases h : psi K' (L true).newW ≤ psi K' (L false).newW
  · have e : (dirOf K' w f.sc (f.c / 2 ^ base % 2 ^ K' ^ 4)).toNat = 1 := by
      have : dirOf K' w f.sc (f.c / 2 ^ base % 2 ^ K' ^ 4) = true := decide_eq_true h
      rw [this]; rfl
    rw [e]
    exact Run.mono (run_ite_pos h1 h0 h l1) (by omega)
  · have e : (dirOf K' w f.sc (f.c / 2 ^ base % 2 ^ K' ^ 4)).toNat = 0 := by
      have : dirOf K' w f.sc (f.c / 2 ^ base % 2 ^ K' ^ 4) = false := decide_eq_false h
      rw [this]; rfl
    rw [e]
    exact Run.mono (run_ite_neg h1 h0 h l0) (by omega)

/-! #### Reading the numbers of the words of `u` -/

/-- The number of the word `wd u v`, read from the number `Z` of the words of `u`. -/
def readZ (l : Lev) (u Z v : ℕ) : ℕ :=
  viewL l.K' (fun v => ∑ y ∈ range (l.K' * l.K'), l.w (l.wd u v) y) Z v

/-- The numbers `B v` of the words of `u`, read from the number `Z`. -/
def readB (l : Lev) (u Z v : ℕ) : ℕ → ℕ := viewL (l.K' * l.K') (l.w (l.wd u v)) (readZ l u Z v)

theorem run_endsE (H : StepCtx W f K' base C wt w) {env : List ℕ} {g ix x : ℕ} (hf : f.At env g)
    (hx : env.getD ix 0 = x) (hxK : x < K' * K') :
    Run W (endsE wt (K' * K') g ix) env (∑ y ∈ range (K' * K'), w x y) (4 * mon K' C 2) := by
  have hl := H.KK_le
  have hle := H.ends_le hxK
  have hc := mon_chain K' C
  have hb : 1 + 1 + (K' + 1) * (K' + 1) * (C + 1) ≤ (1 + 1 + 2) * mon K' C 2 :=
    loop_mon2 (K' := K') (C := C) (n := 0) (c := 1) (cn := 1) (B := C) (by omega)
  have hs : Run W (.sum (.lit (K' * K')) (wt (g + 1) (ix + 1) 0)) env (∑ y ∈ range (K' * K'), w x y)
      (1 + 1 + (K' + 1) * (K' + 1) * (C + 1)) :=
    Run.sum (Run.lit (H.lt2 (by omega))) (KK_le_PP K') (fun y hy => H.run_wt (hf.up y) hx rfl hxK hy) (H.lt2 (by omega))
  exact Run.mono hs (by omega)

theorem run_offE (H : StepCtx W f K' base C wt w) {env : List ℕ} {g ix iy x y : ℕ} (hf : f.At env g)
    (hx : env.getD ix 0 = x) (hy : env.getD iy 0 = y) (hxK : x < K' * K') (hyK : y ≤ K' * K') :
    Run W (offE wt g ix iy) env (∑ t ∈ range y, w x t) (4 * mon K' C 2) := by
  have hle := H.off_le hxK hyK
  have hc := mon_chain K' C
  have hb : 1 + 1 + (K' + 1) * (K' + 1) * (C + 1) ≤ (1 + 1 + 2) * mon K' C 2 :=
    loop_mon2 (K' := K') (C := C) (n := 0) (c := 1) (cn := 1) (B := C) (by omega)
  have hs : Run W (.sum (.var iy) (wt (g + 1) (ix + 1) 0)) env (∑ t ∈ range y, w x t)
      (1 + 1 + (K' + 1) * (K' + 1) * (C + 1)) :=
    Run.sum (Run.var hy) (hyK.trans (KK_le_PP K')) (fun t ht => H.run_wt (hf.up t) hx rfl hxK (by omega)) (H.lt2 (by omega))
  exact Run.mono hs (by omega)

theorem row_total_le (H : StepCtx W f K' base C wt w) {dir : Bool} {u : ℕ} (hu : u < K') :
    ∑ v ∈ range K', ∑ y ∈ range (K' * K'), w ((L dir).wd u v) y ≤ f.sc := by
  have h := Pot.sum_wd (L dir) (fun x => ∑ y ∈ range (K' * K'), w x y)
  calc ∑ v ∈ range K', ∑ y ∈ range (K' * K'), w ((L dir).wd u v) y
      ≤ ∑ u ∈ range K', ∑ v ∈ range K', ∑ y ∈ range (K' * K'), w ((L dir).wd u v) y :=
        single_le_sum (f := fun u => ∑ v ∈ range K', ∑ y ∈ range (K' * K'), w ((L dir).wd u v) y)
          (fun _ _ => Nat.zero_le _) (mem_range.mpr hu)
    _ = ∑ x ∈ range (K' * K'), ∑ y ∈ range (K' * K'), w x y := h
    _ ≤ f.sc := H.big.htot

theorem rowOff_le (H : StepCtx W f K' base C wt w) {dir : Bool} {u v : ℕ} (hu : u < K') (hv : v ≤ K') :
    ∑ t ∈ range v, ∑ y ∈ range (K' * K'), w ((L dir).wd u t) y ≤ f.sc :=
  (sum_le_sum_of_subset (range_subset_range.mpr hv)).trans (row_total_le H hu)

theorem run_rowOffE (H : StepCtx W f K' base C wt w) {env : List ℕ} {g id iu iv u v : ℕ} {dir : Bool}
    (hf : f.At env g) (hd : env.getD id 0 = dir.toNat) (hu : env.getD iu 0 = u) (hv : env.getD iv 0 = v)
    (huK : u < K') (hvK : v ≤ K') :
    Run W (rowOffE K' wt g id iu iv) env (∑ t ∈ range v, ∑ y ∈ range (K' * K'), w ((L dir).wd u t) y)
      (16 * mon K' C 3) := by
  have hc := mon_chain K' C
  have hle := rowOff_le H (dir := dir) huK hvK
  have hbody : ∀ t < v, Run W (.letE (wdE K' (id + 1) (iu + 1) 0) (endsE wt (K' * K') (g + 2) 0)) (t :: env)
      (∑ y ∈ range (K' * K'), w ((L dir).wd u t) y) (13 * mon K' C 2) := by
    intro t ht
    have htK : t < K' := by omega
    exact Run.mono (Run.letE (run_wdE H hd hu rfl huK htK)
      (run_endsE H ((hf.up t).up _) rfl (wd_lt huK htK))) (by omega)
  have hb : 1 + 1 + (K' + 1) * (13 * mon K' C 2 + 1) ≤ (13 + 1 + 2) * mon K' C 3 :=
    loop_mon1 (K' := K') (C := C) (n := 2) (c := 13) (cn := 1) (B := 13 * mon K' C 2) le_rfl
  have hs : Run W (.sum (.var iv) (.letE (wdE K' (id + 1) (iu + 1) 0) (endsE wt (K' * K') (g + 2) 0))) env
      (∑ t ∈ range v, ∑ y ∈ range (K' * K'), w ((L dir).wd u t) y) (1 + 1 + (K' + 1) * (13 * mon K' C 2 + 1)) :=
    Run.sum (Run.var hv) (by omega) hbody (H.lt2 (by omega))
  exact Run.mono hs (by omega)

theorem run_zvE (H : StepCtx W f K' base C wt w) {env : List ℕ} {g id iu iZ iv u Z v : ℕ} {dir : Bool}
    (hf : f.At env g) (hd : env.getD id 0 = dir.toNat) (hu : env.getD iu 0 = u) (hZ : env.getD iZ 0 = Z)
    (hv : env.getD iv 0 = v) (huK : u < K') (hvK : v < K') :
    Run W (zvE K' wt g id iu iZ iv) env (readZ (L dir) u Z v) (34 * mon K' C 3) := by
  have hc := mon_chain K' C
  have x := wd_lt (base := base) (f := f) (w := w) (dir := dir) huK hvK
  have hf1 := hf.up ((L dir).wd u v)
  have r1 : Run W (rowOffE K' wt (g + 1) (id + 1) (iu + 1) (iv + 1)) ((L dir).wd u v :: env) _ _ :=
    run_rowOffE H hf1 hd hu hv huK hvK.le
  have r2 : Run W (endsE wt (K' * K') (g + 1) 0) ((L dir).wd u v :: env) _ _ := run_endsE H hf1 rfl x
  have h1 := rowOff_le H (dir := dir) huK hvK.le
  have h2 := H.ends_le x
  have e : readZ (L dir) u Z v = Z / 2 ^ (∑ t ∈ range v, ∑ y ∈ range (K' * K'), w ((L dir).wd u t) y) %
      2 ^ (∑ y ∈ range (K' * K'), w ((L dir).wd u v) y) := if_pos hvK
  rw [e]
  exact Run.mono (Run.letE (run_wdE H hd hu hv huK hvK) (Run.mod (Run.div (Run.var hZ) (Run.pow2 r1 (H.ltW (by omega))))
    (Run.pow2 r2 (H.ltW (by omega))))) (by omega)

theorem run_bvE (H : StepCtx W f K' base C wt w) {env : List ℕ} {g id iu iZ iv iy u Z v y : ℕ} {dir : Bool}
    (hf : f.At env g) (hd : env.getD id 0 = dir.toNat) (hu : env.getD iu 0 = u) (hZ : env.getD iZ 0 = Z)
    (hv : env.getD iv 0 = v) (hy : env.getD iy 0 = y) (huK : u < K') (hvK : v < K') (hyK : y < K' * K') :
    Run W (bvE K' wt g id iu iZ iv iy) env (readB (L dir) u Z v y) (55 * mon K' C 3) := by
  have hc := mon_chain K' C
  have x := wd_lt (base := base) (f := f) (w := w) (dir := dir) huK hvK
  have hf1 := hf.up ((L dir).wd u v)
  have zv : Run W (zvE K' wt (g + 1) (id + 1) (iu + 1) (iZ + 1) (iv + 1)) ((L dir).wd u v :: env) _ _ :=
    run_zvE H hf1 hd hu hZ hv huK hvK
  have hf2 := hf1.up (readZ (L dir) u Z v)
  have roff : Run W (offE wt (g + 2) 1 (iy + 2)) (readZ (L dir) u Z v :: (L dir).wd u v :: env) _ _ :=
    run_offE H hf2 (x := (L dir).wd u v) (y := y) rfl hy x hyK.le
  have rwt : Run W (wt (g + 2) 1 (iy + 2)) (readZ (L dir) u Z v :: (L dir).wd u v :: env) _ _ :=
    H.run_wt hf2 (x := (L dir).wd u v) (y := y) rfl hy x hyK
  have e : readB (L dir) u Z v y = readZ (L dir) u Z v / 2 ^ (∑ t ∈ range y, w ((L dir).wd u v) t) %
      2 ^ w ((L dir).wd u v) y := if_pos hyK
  rw [e]
  have h1 := H.off_le x hyK.le
  have h2 := H.w_le x hyK
  exact Run.mono (Run.letE (run_wdE H hd hu hv huK hvK) (Run.letE zv (Run.mod (Run.div (Run.var rfl)
    (Run.pow2 roff (H.ltW (by omega)))) (Run.pow2 rwt (H.ltW (by omega)))))) (by omega)

theorem run_bpE (H : StepCtx W f K' base C wt w) {env : List ℕ} {g id iu iZ iu' u Z u' : ℕ} {dir : Bool}
    (hf : f.At env g) (hd : env.getD id 0 = dir.toNat) (hu : env.getD iu 0 = u) (hZ : env.getD iZ 0 = Z)
    (hu' : env.getD iu' 0 = u') (huK : u < K') (huK' : u' < K') :
    Run W (bpE K' base wt g id iu iZ iu') env (viewL K' ((L dir).newW u) Z u') (494 * mon K' C 3) := by
  have hc := mon_chain K' C
  have h1 := newW_off_le H (dir := dir) huK huK'.le
  have h2 := newW_le_sc H (dir := dir) huK huK'
  have hb : 1 + 1 + (K' + 1) * (243 * mon K' C 2 + 1) ≤ (243 + 1 + 2) * mon K' C 3 :=
    loop_mon1 (K' := K') (C := C) (n := 2) (c := 243) (cn := 1) (B := 243 * mon K' C 2) le_rfl
  have hs : Run W (.sum (.var iu') (newWE K' base wt (g + 1) (id + 1) (iu + 1) 0)) env
      (∑ t ∈ range u', (L dir).newW u t) (1 + 1 + (K' + 1) * (243 * mon K' C 2 + 1)) :=
    Run.sum (Run.var hu') (by omega) (fun t ht => run_newWE H (hf.up t) hd hu rfl huK (by omega)) (H.lt2 (by omega))
  have e : viewL K' ((L dir).newW u) Z u' =
      Z / 2 ^ (∑ t ∈ range u', (L dir).newW u t) % 2 ^ (L dir).newW u u' := if_pos huK'
  rw [e]
  exact Run.mono (Run.mod (Run.div (Run.var hZ) (Run.pow2 hs (H.ltW (by omega))))
    (Run.pow2 (run_newWE H hf hd hu hu' huK huK') (H.ltW (by omega)))) (by omega)

theorem newW_eq_segs {dir : Bool} {u1 u2 : ℕ} (h : u1 < u2) :
    (L dir).newW u1 u2 = ∑ s ∈ range (K' * K'), (L dir).segS u1 u2 s := by
  simp [Lev.newW, h.ne, min_eq_left h.le, max_eq_right h.le]

theorem run_segPartE (H : StepCtx W f K' base C wt w) {env : List ℕ} {g id iu1 iu2 ib is u1 u2 b s : ℕ} {dir : Bool}
    (hf : f.At env g) (hd : env.getD id 0 = dir.toNat) (hu1 : env.getD iu1 0 = u1) (hu2 : env.getD iu2 0 = u2)
    (hb : env.getD ib 0 = b) (hs : env.getD is 0 = s) (hu1K : u1 < K') (hu2K : u2 < K') (hlt : u1 < u2)
    (hsK : s < K' * K') :
    Run W (segPartE K' base wt g id iu1 iu2 ib is) env (viewL (K' * K') ((L dir).segS u1 u2) b s) (456 * mon K' C 2) := by
  have hc := mon_chain K' C
  have htot : ∑ t ∈ range (K' * K'), (L dir).segS u1 u2 t ≤ f.sc := by
    rw [← newW_eq_segs hlt]
    exact newW_le_sc H hu1K hu2K
  have h1 : ∑ t ∈ range s, (L dir).segS u1 u2 t ≤ f.sc :=
    (sum_le_sum_of_subset (range_subset_range.mpr hsK.le)).trans htot
  have h2 : (L dir).segS u1 u2 s ≤ f.sc :=
    (single_le_sum (f := fun t => (L dir).segS u1 u2 t) (fun _ _ => Nat.zero_le _) (mem_range.mpr hsK)).trans htot
  have hbd : 1 + 1 + (K' + 1) * (K' + 1) * (219 + 5 * C + 1) ≤ (224 + 1 + 2) * mon K' C 2 :=
    loop_mon2 (K' := K') (C := C) (n := 0) (c := 224) (cn := 1) (B := 219 + 5 * C) (by omega)
  have hsum : Run W (.sum (.var is) (segSE K' base wt (g + 1) (id + 1) (iu1 + 1) (iu2 + 1) 0)) env
      (∑ t ∈ range s, (L dir).segS u1 u2 t) (1 + 1 + (K' + 1) * (K' + 1) * (219 + 5 * C + 1)) :=
    Run.sum (Run.var hs) (hsK.le.trans (KK_le_PP K'))
      (fun t ht => run_segSE H (hf.up t) hd hu1 hu2 rfl hu1K hu2K (by omega)) (H.lt2 (by omega))
  have e : viewL (K' * K') ((L dir).segS u1 u2) b s =
      b / 2 ^ (∑ t ∈ range s, (L dir).segS u1 u2 t) % 2 ^ (L dir).segS u1 u2 s := if_pos hsK
  rw [e]
  exact Run.mono (Run.mod (Run.div (Run.var hb) (Run.pow2 hsum (H.ltW (by omega))))
    (Run.pow2 (run_segSE H hf hd hu1 hu2 hs hu1K hu2K hsK) (H.ltW (by omega)))) (by omega)

/-! #### The factor of a segment -/

theorem carry_le_sc (H : StepCtx W f K' base C wt w) {dir : Bool} {u u' v v' : ℕ} (huK : u < K') (huK' : u' < K')
    (hvK : v < K') (hvK' : v' < K') : (L dir).carry u u' v v' ≤ f.sc := by
  have h := H.w_le (wd_lt (base := base) (f := f) (w := w) (dir := dir) huK hvK)
    (wd_lt (base := base) (f := f) (w := w) (dir := dir) huK' hvK')
  exact (Nat.sub_le _ _).trans h

/-- The index of a segment has at most `2 * sc` bits. -/
theorem xi_lt (H : StepCtx W f K' base C wt w) {dir : Bool} {u u' v v' b : ℕ} (huK : u < K') (huK' : u' < K')
    (hvK : v < K') (hvK' : v' < K') (hb : b < 2 ^ (L dir).seg u u' v v') :
    b / 2 ^ (L dir).carry u u' v v' < 2 ^ (2 * f.sc) := by
  have h1 : (L dir).dd u u' v v' ≤ 2 * f.sc :=
    dd_le.trans (by have := pm_le_sc H (dir := dir) huK huK' hvK hvK'; omega)
  have h2 : b < 2 ^ (L dir).carry u u' v v' * 2 ^ (L dir).dd u u' v v' := by
    rw [← pow_add]
    exact hb
  exact lt_of_lt_of_le (Nat.div_lt_of_lt_mul h2) (Nat.pow_le_pow_right (by norm_num) h1)

/-- The lets that the two branches of `segTE` have in common. -/
theorem runZ_segLets (H : StepCtx W f K' base C wt w) {env : List ℕ} {g id iu iu1 iu2 iu' iv iv' iZ u u1 u2 u' v v' Z : ℕ}
    {dir : Bool} {body : Expr} {z : ℤ} {cb : ℕ}
    (hf : f.At env g) (hd : env.getD id 0 = dir.toNat) (hu : env.getD iu 0 = u) (hu1 : env.getD iu1 0 = u1)
    (hu2 : env.getD iu2 0 = u2) (hu' : env.getD iu' 0 = u') (hv : env.getD iv 0 = v) (hv' : env.getD iv' 0 = v')
    (hZ : env.getD iZ 0 = Z) (huK : u < K') (hu1K : u1 < K') (hu2K : u2 < K') (huK' : u' < K') (hvK : v < K')
    (hvK' : v' < K')
    (hbody : RunZ W body (readB (L dir) u Z v' ((L dir).wd u' v) :: (L dir).wd u' v ::
      readB (L dir) u Z v ((L dir).wd u' v') :: (L dir).wd u' v' :: (L dir).carry u1 u2 v v' :: (L dir).pm u1 u2 v v' :: env)
      z cb) :
    RunZ W (.letE (pmE K' wt g id iu1 iu2 iv iv') <|
      .letE (carryE K' wt (g + 1) (id + 1) (iu1 + 1) (iu2 + 1) (iv + 1) (iv' + 1)) <|
      .letE (wdE K' (id + 2) (iu' + 2) (iv' + 2)) <|
      .letE (bvE K' wt (g + 3) (id + 3) (iu + 3) (iZ + 3) (iv + 3) 0) <|
      .letE (wdE K' (id + 4) (iu' + 4) (iv + 4)) <|
      .letE (bvE K' wt (g + 5) (id + 5) (iu + 5) (iZ + 5) (iv' + 5) 0) <|
        body) env z (288 * mon K' C 3 + cb) := by
  have hc := mon_chain K' C
  have hf1 := hf.up ((L dir).pm u1 u2 v v')
  have hf2 := hf1.up ((L dir).carry u1 u2 v v')
  have hf3 := hf2.up ((L dir).wd u' v')
  have hf4 := hf3.up (readB (L dir) u Z v ((L dir).wd u' v'))
  have hf5 := hf4.up ((L dir).wd u' v)
  have y1 := wd_lt (base := base) (f := f) (w := w) (dir := dir) huK' hvK'
  have y2 := wd_lt (base := base) (f := f) (w := w) (dir := dir) huK' hvK
  exact RunZ.mono (RunZ.letE (run_pmE H hf hd hu1 hu2 hv hv' hu1K hu2K hvK hvK') <|
    RunZ.letE (run_carryE H hf1 hd hu1 hu2 hv hv' hu1K hu2K hvK hvK') <|
    RunZ.letE (run_wdE H hd hu' hv' huK' hvK') <|
    RunZ.letE (run_bvE H hf3 (y := (L dir).wd u' v') hd hu hZ hv rfl huK hvK y1) <|
    RunZ.letE (run_wdE H hd hu' hv huK' hvK) <|
    RunZ.letE (run_bvE H hf5 (y := (L dir).wd u' v) hd hu hZ hv' rfl huK hvK' y2) hbody) (by omega)

/-- The marks of a bundle of wires, as a program. -/
theorem runZ_mkWE {env : List ℕ} {iw it ih d t h T : ℕ} (hW : 2 ≤ W) (hd : env.getD iw 0 = d)
    (ht : env.getD it 0 = t) (hh : env.getD ih 0 = h) (hdW : d < W) (hdT : d ≤ T) :
    RunZ W (mkWE iw it ih) env (mkW d t h) (2 + T * 14) := by
  have hbody : ∀ j < d, RunZ W (.sub (bitX (ih + 1) (.var 0)) (bitX (it + 1) (.var 0))) (j :: env)
      (b2z (h.testBit j) - b2z (t.testBit j)) 13 := by
    intro j hj
    have h1 := Run.bitX (W := W) (env := j :: env) (ki := ih + 1) (x := h) hh (Run.var (i := 0) (x := j) rfl) (by omega) hW
    have h2 := Run.bitX (W := W) (env := j :: env) (ki := it + 1) (x := t) ht (Run.var (i := 0) (x := j) rfl) (by omega) hW
    exact (RunZ.sub h1.toZ h2.toZ).eq (by rw [Rect.b2z_toNat, Rect.b2z_toNat])
  exact RunZ.mono (RunZ.prod (Run.var hd) hdT hbody) (by omega)

/-- The sign of the tail ends of a bundle, as a program. -/
theorem runZ_sgnPE {env : List ℕ} {id it d t T : ℕ} (hW : 2 ≤ W) (hd : env.getD id 0 = d)
    (ht : env.getD it 0 = t) (hdW : d < W) (hdT : d ≤ T) :
    RunZ W (sgnPE id it) env (sgnP d t) (2 + T * 14) := by
  have hbody : ∀ j < d, RunZ W (.ite (bitX (it + 1) (.var 0)) (.lit 0) (.lit 1) (.sub (.lit 0) (.lit 1)))
      (j :: env) (if t.testBit j then -1 else 1) 13 := by
    intro j hj
    have h1 := Run.bitX (W := W) (env := j :: env) (ki := it + 1) (x := t) ht (Run.var (i := 0) (x := j) rfl) (by omega) hW
    have h0 : Run W (.lit 0) (j :: env) 0 1 := Run.lit (by positivity)
    refine RunZ.mono (RunZ.ite h1 h0 (fun hb => RunZ.lit1.eq ?_) (fun hb => (RunZ.sub RunZ.lit0 RunZ.lit1).eq ?_))
      (by omega)
    · have : t.testBit j = false := by cases e : t.testBit j <;> simp_all
      simp [this]
    · have : t.testBit j = true := by cases e : t.testBit j <;> simp_all
      simp [this]
  exact RunZ.mono (RunZ.prod (Run.var hd) hdT hbody) (by omega)

/-- The width of the index of a segment, as in `Lev.dd`. -/
theorem dd_eq {dir : Bool} {u1 u2 v v' : ℕ} (hlt : v < v') :
    (L dir).dd u1 u2 v v' = dLen ((L dir).pol u1 u2 v v' == dir) ((L dir).pm u1 u2 v v') := by
  simp only [Lev.dd, if_pos hlt]

/-- The lets of the index at the tail side of a segment. -/
theorem runZ_idxTail (H : StepCtx W f K' base C wt w) {env : List ℕ} {g id iu1 iu2 iv iv' ib u1 u2 v v' b : ℕ}
    {dir : Bool} {b2 y2 b1 y1 cr m : ℕ} {rectX : Expr} {z : ℤ} {cx : ℕ}
    (hf : f.At env g) (hd : env.getD id 0 = dir.toNat) (hu1 : env.getD iu1 0 = u1) (hu2 : env.getD iu2 0 = u2)
    (hv : env.getD iv 0 = v) (hv' : env.getD iv' 0 = v') (hb : env.getD ib 0 = b)
    (hu1K : u1 < K') (hu2K : u2 < K') (hvK : v < K') (hvK' : v' < K') (hcr : cr < W)
    (hmpm : m = (L dir).pm u1 u2 v v')
    (hz : v < v' → RunZ W rectX (b2 % 2 ^ m :: b1 % 2 ^ m :: (L dir).dd u1 u2 v v' :: b / 2 ^ cr ::
      ((L dir).pol u1 u2 v v').toNat :: b2 :: y2 :: b1 :: y1 :: cr :: m :: env) z cx) :
    RunZ W (.ite (.var (iv' + 6)) (.var (iv + 6)) (.lit 1) <|
        .letE (polE K' base (g + 6) (id + 6) (iu1 + 6) (iu2 + 6) (iv + 6) (iv' + 6)) <|
        .letE (.div (.var (ib + 7)) (.pow2 (.var 5))) <|
        .letE (.letE (eqX (.var 1) (.var (id + 8)) (.lit 1) (.lit 0)) (dLenE 0 8)) <|
        .letE (.mod (.var 5) (.pow2 (.var 8))) <|
        .letE (.mod (.var 4) (.pow2 (.var 9))) <|
          rectX) (b2 :: y2 :: b1 :: y1 :: cr :: m :: env) (if v < v' then z else 1) (80 + cx) := by
  by_cases hvv : v' ≤ v
  · rw [if_neg (by omega)]
    exact RunZ.mono (runZ_ite_pos (Run.var hv') (Run.var hv) hvv RunZ.lit1) (by omega)
  · have hlt : v < v' := by omega
    rw [if_pos hlt]
    have hWb := H.big.hW
    have hmsc := pm_le_sc H (dir := dir) hu1K hu2K hvK hvK'
    have hmW : m < W := by rw [hmpm]; exact H.ltW (by omega)
    have hf6 := (((((((hf.up m).up cr).up y1).up b1).up y2).up b2))
    set pl := ((L dir).pol u1 u2 v v').toNat with hpl
    have r0 : Run W (polE K' base (g + 6) (id + 6) (iu1 + 6) (iu2 + 6) (iv + 6) (iv' + 6))
        (b2 :: y2 :: b1 :: y1 :: cr :: m :: env) pl 26 :=
      run_polE H hf6 hd hu1 hu2 hv hv' hu1K hu2K hvK hvK'
    have r1 : Run W (.div (.var (ib + 7)) (.pow2 (.var 5))) (pl :: b2 :: y2 :: b1 :: y1 :: cr :: m :: env)
        (b / 2 ^ cr) 4 := Run.mono (Run.div (Run.var hb) (Run.pow2 (Run.var rfl) hcr)) (by omega)
    have r2 : Run W (.letE (eqX (.var 1) (.var (id + 8)) (.lit 1) (.lit 0)) (dLenE 0 8))
        (b / 2 ^ cr :: pl :: b2 :: y2 :: b1 :: y1 :: cr :: m :: env) ((L dir).dd u1 u2 v v') 31 := by
      rw [dd_eq hlt, ← hmpm]
      exact Run.mono (Run.letE (Rect.run_cheap (pol := (L dir).pol u1 u2 v v') (dir := dir) (by omega) rfl hd)
        (run_dLenE rfl rfl (H.lt2 (by omega)))) (by omega)
    have r3 : Run W (.mod (.var 5) (.pow2 (.var 8)))
        ((L dir).dd u1 u2 v v' :: b / 2 ^ cr :: pl :: b2 :: y2 :: b1 :: y1 :: cr :: m :: env)
        (b1 % 2 ^ m) 4 := Run.mono (Run.mod (Run.var rfl) (Run.pow2 (Run.var rfl) hmW)) (by omega)
    have r4 : Run W (.mod (.var 4) (.pow2 (.var 9)))
        (b1 % 2 ^ m :: (L dir).dd u1 u2 v v' :: b / 2 ^ cr :: pl :: b2 :: y2 :: b1 :: y1 :: cr :: m :: env)
        (b2 % 2 ^ m) 4 := Run.mono (Run.mod (Run.var rfl) (Run.pow2 (Run.var rfl) hmW)) (by omega)
    exact RunZ.mono (runZ_ite_neg (Run.var hv') (Run.var hv) hvv (RunZ.letE r0 (RunZ.letE r1 (RunZ.letE r2
      (RunZ.letE r3 (RunZ.letE r4 (hz hlt))))))) (by omega)

/-- The lets of the index at the head side of a segment: the head side reads the complement. -/
theorem runZ_idxHead (H : StepCtx W f K' base C wt w) {env : List ℕ} {g id iu1 iu2 iv iv' ib u1 u2 v v' b : ℕ}
    {dir : Bool} {b2 y2 b1 y1 cr m : ℕ} {rectX : Expr} {z : ℤ} {cx : ℕ}
    (hf : f.At env g) (hd : env.getD id 0 = dir.toNat) (hu1 : env.getD iu1 0 = u1) (hu2 : env.getD iu2 0 = u2)
    (hv : env.getD iv 0 = v) (hv' : env.getD iv' 0 = v') (hb : env.getD ib 0 = b)
    (hu1K : u1 < K') (hu2K : u2 < K') (hvK : v < K') (hvK' : v' < K') (hcr : cr < W)
    (hmpm : m = (L dir).pm u1 u2 v v') (hy : b / 2 ^ cr < 2 ^ (L dir).dd u1 u2 v v')
    (hz : v < v' → RunZ W rectX (b2 % 2 ^ m :: b1 % 2 ^ m ::
      compN ((L dir).dd u1 u2 v v') (b / 2 ^ cr) :: (L dir).dd u1 u2 v v' :: b / 2 ^ cr ::
      ((L dir).pol u1 u2 v v').toNat :: b2 :: y2 :: b1 :: y1 :: cr :: m :: env) z cx) :
    RunZ W (.ite (.var (iv' + 6)) (.var (iv + 6)) (.lit 1) <|
        .letE (polE K' base (g + 6) (id + 6) (iu1 + 6) (iu2 + 6) (iv + 6) (iv' + 6)) <|
        .letE (.div (.var (ib + 7)) (.pow2 (.var 5))) <|
        .letE (.letE (eqX (.var 1) (.var (id + 8)) (.lit 1) (.lit 0)) (dLenE 0 8)) <|
        .letE (.sub (.sub (.pow2 (.var 0)) (.lit 1)) (.var 1)) <|
        .letE (.mod (.var 6) (.pow2 (.var 9))) <|
        .letE (.mod (.var 5) (.pow2 (.var 10))) <|
          rectX) (b2 :: y2 :: b1 :: y1 :: cr :: m :: env) (if v < v' then z else 1) (90 + cx) := by
  by_cases hvv : v' ≤ v
  · rw [if_neg (by omega)]
    exact RunZ.mono (runZ_ite_pos (Run.var hv') (Run.var hv) hvv RunZ.lit1) (by omega)
  · have hlt : v < v' := by omega
    rw [if_pos hlt]
    have hWb := H.big.hW
    have hmsc := pm_le_sc H (dir := dir) hu1K hu2K hvK hvK'
    have hmW : m < W := by rw [hmpm]; exact H.ltW (by omega)
    have hddle : (L dir).dd u1 u2 v v' ≤ 2 * f.sc := dd_le.trans (by omega)
    have hddW : (L dir).dd u1 u2 v v' < W := H.ltW (by omega)
    have hf6 := (((((((hf.up m).up cr).up y1).up b1).up y2).up b2))
    set pl := ((L dir).pol u1 u2 v v').toNat with hpl
    set dd := (L dir).dd u1 u2 v v' with hdd
    have r0 : Run W (polE K' base (g + 6) (id + 6) (iu1 + 6) (iu2 + 6) (iv + 6) (iv' + 6))
        (b2 :: y2 :: b1 :: y1 :: cr :: m :: env) pl 26 :=
      run_polE H hf6 hd hu1 hu2 hv hv' hu1K hu2K hvK hvK'
    have r1 : Run W (.div (.var (ib + 7)) (.pow2 (.var 5))) (pl :: b2 :: y2 :: b1 :: y1 :: cr :: m :: env)
        (b / 2 ^ cr) 4 := Run.mono (Run.div (Run.var hb) (Run.pow2 (Run.var rfl) hcr)) (by omega)
    have r2 : Run W (.letE (eqX (.var 1) (.var (id + 8)) (.lit 1) (.lit 0)) (dLenE 0 8))
        (b / 2 ^ cr :: pl :: b2 :: y2 :: b1 :: y1 :: cr :: m :: env) dd 31 := by
      rw [hdd, dd_eq hlt, ← hmpm]
      exact Run.mono (Run.letE (Rect.run_cheap (pol := (L dir).pol u1 u2 v v') (dir := dir) (by omega) rfl hd)
        (run_dLenE rfl rfl (H.lt2 (by omega)))) (by omega)
    have hp1 : 1 ≤ 2 ^ dd := Nat.one_le_two_pow
    have hpW : 2 ^ dd < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) hddW
    have r5 : Run W (.sub (.sub (.pow2 (.var 0)) (.lit 1)) (.var 1))
        (dd :: b / 2 ^ cr :: pl :: b2 :: y2 :: b1 :: y1 :: cr :: m :: env) (compN dd (b / 2 ^ cr)) 7 :=
      Run.mono (Run.sub (Run.sub (Run.pow2 (Run.var rfl) hddW) (Run.lit (by omega)) hpW hp1) (Run.var rfl)
        (by omega) (by omega)) (by omega)
    have r3 : Run W (.mod (.var 6) (.pow2 (.var 9)))
        (compN dd (b / 2 ^ cr) :: dd :: b / 2 ^ cr :: pl :: b2 :: y2 :: b1 :: y1 :: cr :: m :: env)
        (b1 % 2 ^ m) 4 := Run.mono (Run.mod (Run.var rfl) (Run.pow2 (Run.var rfl) hmW)) (by omega)
    have r4 : Run W (.mod (.var 5) (.pow2 (.var 10)))
        (b1 % 2 ^ m :: compN dd (b / 2 ^ cr) :: dd :: b / 2 ^ cr :: pl :: b2 :: y2 :: b1 :: y1 :: cr :: m :: env)
        (b2 % 2 ^ m) 4 := Run.mono (Run.mod (Run.var rfl) (Run.pow2 (Run.var rfl) hmW)) (by omega)
    exact RunZ.mono (runZ_ite_neg (Run.var hv') (Run.var hv) hvv (RunZ.letE r0 (RunZ.letE r1 (RunZ.letE r2
      (RunZ.letE r5 (RunZ.letE r3 (RunZ.letE r4 (hz hlt)))))))) (by omega)

theorem runZ_segTE (H : StepCtx W f K' base C wt w) {env : List ℕ} {g id iu iu' iv iv' ib iZ u u' v v' b Z : ℕ}
    {dir : Bool} (hf : f.At env g) (hd : env.getD id 0 = dir.toNat) (hu : env.getD iu 0 = u) (hu' : env.getD iu' 0 = u')
    (hv : env.getD iv 0 = v) (hv' : env.getD iv' 0 = v') (hb : env.getD ib 0 = b) (hZ : env.getD iZ 0 = Z)
    (huK : u < K') (huK' : u' < K') (hvK : v < K') (hvK' : v' < K')
    (hbk : b < 2 ^ (L dir).seg (min u u') (max u u') v v') :
    RunZ W (segTE K' base wt g id iu iu' iv iv' ib iZ) env ((L dir).segT u u' v v' b (readB (L dir) u Z))
      (450 * mon K' C 3 + 2 * rectCost f.sc) := by
  have hc := mon_chain K' C
  have hWb := H.big.hW
  have hR : 2 * f.sc * 14 + 2 ≤ rectCost f.sc := by unfold rectCost; nlinarith
  by_cases hle : u' ≤ u
  · rw [min_eq_right hle, max_eq_left hle] at hbk
    have e : (L dir).segT u u' v v' b (readB (L dir) u Z) =
        (if b % 2 ^ (L dir).carry u' u v v' = readB (L dir) u Z v' ((L dir).wd u' v) / 2 ^ (L dir).pm u' u v v'
          then 1 else 0) *
        (if v < v' then
          rectB dir ((L dir).pol u' u v v') ((L dir).pm u' u v v')
            (compN ((L dir).dd u' u v v') (b / 2 ^ (L dir).carry u' u v v'))
            (readB (L dir) u Z v ((L dir).wd u' v') % 2 ^ (L dir).pm u' u v v')
            (readB (L dir) u Z v' ((L dir).wd u' v) % 2 ^ (L dir).pm u' u v v')
        else 1) := if_neg (by omega)
    rw [e]
    have hm := pm_le_sc H (dir := dir) huK' huK hvK hvK'
    have hcr := carry_le_sc H (dir := dir) huK' huK hvK hvK'
    have hmW : (L dir).pm u' u v v' < W := H.ltW (by omega)
    have hcW : (L dir).carry u' u v v' < W := H.ltW (by omega)
    have hy : b / 2 ^ (L dir).carry u' u v v' < 2 ^ (L dir).dd u' u v v' := by
      have h2 : b < 2 ^ (L dir).carry u' u v v' * 2 ^ (L dir).dd u' u v v' := by
        rw [← pow_add]
        exact hbk
      exact Nat.div_lt_of_lt_mul h2
    have hddle : (L dir).dd u' u v v' ≤ 2 * f.sc := dd_le.trans (by omega)
    have hξ : compN ((L dir).dd u' u v v') (b / 2 ^ (L dir).carry u' u v v') < 2 ^ (2 * f.sc) :=
      lt_of_lt_of_le (compN_lt _ _) (Nat.pow_le_pow_right (by norm_num) hddle)
    have hbody := RunZ.mul
      (runZ_eqTest (W := W) (env := readB (L dir) u Z v' ((L dir).wd u' v) :: (L dir).wd u' v ::
        readB (L dir) u Z v ((L dir).wd u' v') :: (L dir).wd u' v' :: (L dir).carry u' u v v' :: (L dir).pm u' u v v' :: env)
        (a := .mod (.var (ib + 6)) (.pow2 (.var 4))) (b := .div (.var 0) (.pow2 (.var 5)))
        (x := b % 2 ^ (L dir).carry u' u v v')
        (y := readB (L dir) u Z v' ((L dir).wd u' v) / 2 ^ (L dir).pm u' u v v')
        (Run.mod (Run.var hb) (Run.pow2 (Run.var rfl) hcW)) (Run.div (Run.var rfl) (Run.pow2 (Run.var rfl) hmW)))
      (runZ_idxHead H (ib := ib) (b := b) (iu1 := iu') (iu2 := iu) (rectX := rectBE (id + 12) 5 11 2 1 0)
        hf hd hu' hu hv hv' hb huK' huK hvK hvK' hcW rfl hy
        (fun _ => runZ_rectBE H.big.rect hd rfl rfl rfl rfl rfl hm hξ))
    exact RunZ.mono (runZ_ite_pos (Run.var hu') (Run.var hu) hle
      (runZ_segLets H hf hd hu hu' hu hu' hv hv' hZ huK huK' huK huK' hvK hvK' hbody)) (by omega)
  · have hlt : u < u' := by omega
    rw [min_eq_left hlt.le, max_eq_right hlt.le] at hbk
    have e : (L dir).segT u u' v v' b (readB (L dir) u Z) =
        (if b % 2 ^ (L dir).carry u u' v v' = readB (L dir) u Z v ((L dir).wd u' v') / 2 ^ (L dir).pm u u' v v'
          then 1 else 0) *
        (if (L dir).wd u' v' < (L dir).wd u v then (-1) ^ (L dir).carry u u' v v' else 1) *
        (if v < v' then
          sgnP ((L dir).dd u u' v v') (b / 2 ^ (L dir).carry u u' v v') *
          rectA dir ((L dir).pol u u' v v') f.sc ((L dir).pm u u' v v') (b / 2 ^ (L dir).carry u u' v v')
            (readB (L dir) u Z v ((L dir).wd u' v') % 2 ^ (L dir).pm u u' v v')
            (readB (L dir) u Z v' ((L dir).wd u' v) % 2 ^ (L dir).pm u u' v v')
        else 1) := if_pos hlt
    rw [e]
    have hm := pm_le_sc H (dir := dir) huK huK' hvK hvK'
    have hcr := carry_le_sc H (dir := dir) huK huK' hvK hvK'
    have hξ := xi_lt H (dir := dir) huK huK' hvK hvK' hbk
    have hmW : (L dir).pm u u' v v' < W := H.ltW (by omega)
    have hcW : (L dir).carry u u' v v' < W := H.ltW (by omega)
    have hddle : (L dir).dd u u' v v' ≤ 2 * f.sc := dd_le.trans (by omega)
    have hddW : (L dir).dd u u' v v' < W := H.ltW (by omega)
    set E6 := readB (L dir) u Z v' ((L dir).wd u' v) :: (L dir).wd u' v ::
        readB (L dir) u Z v ((L dir).wd u' v') :: (L dir).wd u' v' :: (L dir).carry u u' v v' :: (L dir).pm u u' v v' :: env
      with hE6
    have hf10 : ∀ {e0 e1 e2 e3 e4 : ℕ}, f.At (e0 :: e1 :: e2 :: e3 :: e4 :: E6) (g + 11) := fun {e0 e1 e2 e3 e4} =>
      (((((((((((hf.up _).up _).up _).up _).up _).up _).up e4).up e3).up e2).up e1).up e0)
    have hrev : RunZ W (.ite (wdE K' (id + 6) (iu + 6) (iv + 6)) (.var 3) (.lit 1) (signE 4)) E6
        (if (L dir).wd u' v' < (L dir).wd u v then (-1) ^ (L dir).carry u u' v v' else 1) 30 := by
      have hw := run_wdE H (env := E6) (id := id + 6) (iu := iu + 6) (iv := iv + 6) hd hu hv huK hvK
      have hs := Rect.runZ_signE (W := W) (env := E6) (ir := 4) (r := (L dir).carry u u' v v')
        (by have := H.big.hW; omega) rfl
      refine RunZ.mono (RunZ.ite hw (Run.var (i := 3) (x := (L dir).wd u' v') rfl) (fun h1 => RunZ.lit1.eq ?_)
        (fun h1 => hs.eq ?_)) (by omega)
      · rw [if_neg (by omega)]
      · rw [if_pos (by omega)]
    have hbody := RunZ.mul (RunZ.mul
      (runZ_eqTest (W := W) (env := E6)
        (a := .mod (.var (ib + 6)) (.pow2 (.var 4))) (b := .div (.var 2) (.pow2 (.var 5)))
        (x := b % 2 ^ (L dir).carry u u' v v')
        (y := readB (L dir) u Z v ((L dir).wd u' v') / 2 ^ (L dir).pm u u' v v')
        (Run.mod (Run.var hb) (Run.pow2 (Run.var rfl) hcW)) (Run.div (Run.var rfl) (Run.pow2 (Run.var rfl) hmW)))
      hrev)
      (runZ_idxTail H (ib := ib) (b := b) (iu1 := iu) (iu2 := iu')
        (rectX := .mul (sgnPE 2 3) (rectAE (id + 11) 4 (g + 11 + 2) 10 3 1 0 (g + 11 + 1)))
        hf hd hu hu' hv hv' hb huK huK' hvK hvK' hcW rfl
        (fun _ => RunZ.mul (runZ_sgnPE (T := 2 * f.sc) (by omega) rfl rfl hddW hddle)
          (runZ_rectAE H.big.rect hd rfl hf10.sc rfl rfl rfl rfl hf10.bk hm hξ)))
    exact RunZ.mono (runZ_ite_neg (Run.var hu') (Run.var hu) hle
      (runZ_segLets H hf hd hu hu hu' hu' hv hv' hZ huK huK huK' huK' hvK hvK' hbody)) (by omega)

/-! #### The factor of a word of the next level -/

/-- The marks of the wires inside the node `u` between `wd u v` and `wd u v'`, in the first product of `transE`. -/
theorem runZ_transMark (H : StepCtx W f K' base C wt w) {env : List ℕ} {g id iu iZ u Z v v' : ℕ} {dir : Bool}
    (hf : f.At env g) (hd : env.getD id 0 = dir.toNat) (hu : env.getD iu 0 = u) (hZ : env.getD iZ 0 = Z)
    (huK : u < K') (hvK : v < K') (hvK' : v' < K') :
    RunZ W (.ite (.var 0) (.var 1) (.lit 1) <|
        .letE (wdE K' (id + 2) (iu + 2) 0) <|
        .letE (wdE K' (id + 3) (iu + 3) 2) <|
        .letE (bvE K' wt (g + 4) (id + 4) (iu + 4) (iZ + 4) 3 1) <|
        .letE (bvE K' wt (g + 5) (id + 5) (iu + 5) (iZ + 5) 3 1) <|
        .letE (wt (g + 6) 2 3) <|
          mkWE 0 2 1) (v' :: v :: env)
      (if v < v' then mkW (w ((L dir).wd u v) ((L dir).wd u v')) (readB (L dir) u Z v ((L dir).wd u v'))
        (readB (L dir) u Z v' ((L dir).wd u v)) else 1)
      (140 * mon K' C 3 + rectCost f.sc) := by
  have hc := mon_chain K' C
  have hR : f.sc * 14 + 2 ≤ rectCost f.sc := by unfold rectCost; nlinarith
  have v0 : Run W (.var 0) (v' :: v :: env) v' 1 := Run.var rfl
  have v1 : Run W (.var 1) (v' :: v :: env) v 1 := Run.var rfl
  by_cases hvv : v' ≤ v
  · rw [if_neg (by omega)]
    exact RunZ.mono (runZ_ite_pos v0 v1 hvv RunZ.lit1) (by omega)
  · have hlt : v < v' := by omega
    rw [if_pos hlt]
    have x1 := wd_lt (base := base) (f := f) (w := w) (dir := dir) huK hvK'
    have x2 := wd_lt (base := base) (f := f) (w := w) (dir := dir) huK hvK
    have hf2 := (hf.up v).up v'
    have hf3 := hf2.up ((L dir).wd u v')
    have hf4 := hf3.up ((L dir).wd u v)
    have hf5 := hf4.up (readB (L dir) u Z v ((L dir).wd u v'))
    have hf6 := hf5.up (readB (L dir) u Z v' ((L dir).wd u v))
    have hwle := H.w_le x2 x1
    have hwW : w ((L dir).wd u v) ((L dir).wd u v') < W := H.ltW (by omega)
    have rw6 : Run W (wt (g + 6) 2 3) (readB (L dir) u Z v' ((L dir).wd u v) :: readB (L dir) u Z v ((L dir).wd u v') ::
        (L dir).wd u v :: (L dir).wd u v' :: v' :: v :: env) (w ((L dir).wd u v) ((L dir).wd u v')) C :=
      H.run_wt hf6 rfl rfl x2 x1
    exact RunZ.mono (runZ_ite_neg v0 v1 hvv (RunZ.letE (run_wdE H hd hu rfl huK hvK') (RunZ.letE (run_wdE H hd hu rfl huK hvK)
      (RunZ.letE (run_bvE H hf4 (v := v) (y := (L dir).wd u v') hd hu hZ rfl rfl huK hvK x1)
      (RunZ.letE (run_bvE H hf5 (v := v') (y := (L dir).wd u v) hd hu hZ rfl rfl huK hvK' x2)
      (RunZ.letE rw6 (runZ_mkWE (T := f.sc) (by have := H.big.hW; omega) rfl rfl rfl hwW hwle))))))) (by omega)

/-- One segment `s` in the second product of `transE`. -/
theorem runZ_transSeg (H : StepCtx W f K' base C wt w) {env : List ℕ} {g id iu iZ u u' Z b s : ℕ} {dir : Bool}
    (hf : f.At env g) (hd : env.getD id 0 = dir.toNat) (hu : env.getD iu 0 = u) (hZ : env.getD iZ 0 = Z)
    (huK : u < K') (huK' : u' < K') (hne : u ≠ u') (hsK : s < K' * K') :
    RunZ W (.letE (segPartE K' base wt (g + 5) (id + 5) 2 1 3 0) <|
        .letE (.div (.var 1) (.lit K')) <|
        .letE (.mod (.var 2) (.lit K')) <|
          segTE K' base wt (g + 8) (id + 8) (iu + 8) 7 1 0 2 (iZ + 8))
      (s :: max u u' :: min u u' :: b :: u' :: env)
      ((L dir).segT u u' (s / K') (s % K') (viewL (K' * K') ((L dir).segS (min u u') (max u u')) b s) (readB (L dir) u Z))
      (915 * mon K' C 3 + 2 * rectCost f.sc) := by
  have hc := mon_chain K' C
  have hk := H.K_le
  have hmin : min u u' < K' := lt_of_le_of_lt (min_le_left _ _) huK
  have hmax : max u u' < K' := max_lt huK huK'
  have hlt : min u u' < max u u' := by omega
  have hf5 := (((((hf.up u').up b).up (min u u')).up (max u u')).up s)
  have rp : Run W (segPartE K' base wt (g + 5) (id + 5) 2 1 3 0) (s :: max u u' :: min u u' :: b :: u' :: env)
      (viewL (K' * K') ((L dir).segS (min u u') (max u u')) b s) (456 * mon K' C 2) :=
    run_segPartE H hf5 hd rfl rfl rfl rfl hmin hmax hlt hsK
  generalize hx : viewL (K' * K') ((L dir).segS (min u u') (max u u')) b s = x at rp ⊢
  have hxlt : x < 2 ^ (L dir).seg (min u u') (max u u') (s / K') (s % K') := by
    rw [← hx]
    unfold viewL
    rw [if_pos hsK]
    exact Nat.mod_lt _ (by positivity)
  have r1 : Run W (.div (.var 1) (.lit K')) (x :: s :: max u u' :: min u u' :: b :: u' :: env) (s / K') 3 :=
    Run.mono (Run.div (Run.var rfl) (Run.lit (H.lt2 (by omega)))) (by omega)
  have r2 : Run W (.mod (.var 2) (.lit K')) (s / K' :: x :: s :: max u u' :: min u u' :: b :: u' :: env) (s % K') 3 :=
    Run.mono (Run.mod (Run.var rfl) (Run.lit (H.lt2 (by omega)))) (by omega)
  have hf8 := ((hf5.up x).up (s / K')).up (s % K')
  have rt : RunZ W (segTE K' base wt (g + 8) (id + 8) (iu + 8) 7 1 0 2 (iZ + 8))
      (s % K' :: s / K' :: x :: s :: max u u' :: min u u' :: b :: u' :: env)
      ((L dir).segT u u' (s / K') (s % K') x (readB (L dir) u Z)) (450 * mon K' C 3 + 2 * rectCost f.sc) :=
    runZ_segTE H hf8 hd hu rfl rfl rfl rfl hZ huK huK' (digit_div_lt hsK) (digit_mod_lt hsK) hxlt
  exact RunZ.mono (RunZ.letE rp (RunZ.letE r1 (RunZ.letE r2 rt))) (by omega)

/-- One word `u'` in the second product of `transE`. -/
theorem runZ_transWord (H : StepCtx W f K' base C wt w) {env : List ℕ} {g id iu iZ iZ' u u' Z Z' : ℕ} {dir : Bool}
    (hf : f.At env g) (hd : env.getD id 0 = dir.toNat) (hu : env.getD iu 0 = u) (hZ : env.getD iZ 0 = Z)
    (hZ' : env.getD iZ' 0 = Z') (huK : u < K') (huK' : u' < K') :
    RunZ W (eqX (.var 0) (.var (iu + 1)) (.lit 1) <|
        .letE (bpE K' base wt (g + 1) (id + 1) (iu + 1) (iZ' + 1) 0) <|
        .letE (.ite (.var (iu + 2)) (.var 1) (.var (iu + 2)) (.var 1)) <|
        .letE (.ite (.var (iu + 3)) (.var 2) (.var 2) (.var (iu + 3))) <|
        .prod (.lit (K' * K')) <|
          .letE (segPartE K' base wt (g + 5) (id + 5) 2 1 3 0) <|
          .letE (.div (.var 1) (.lit K')) <|
          .letE (.mod (.var 2) (.lit K')) <|
            segTE K' base wt (g + 8) (id + 8) (iu + 8) 7 1 0 2 (iZ + 8)) (u' :: env)
      (if u' = u then 1 else ∏ s ∈ range (K' * K'),
        (L dir).segT u u' (s / K') (s % K')
          (viewL (K' * K') ((L dir).segS (min u u') (max u u')) (viewL K' ((L dir).newW u) Z' u') s) (readB (L dir) u Z))
      (1429 * mon K' C 5 + (K' + 1) * (K' + 1) * (2 * rectCost f.sc)) := by
  have hc := mon_chain K' C
  have hl := H.KK_le
  have v0 : Run W (.var 0) (u' :: env) u' 1 := Run.var rfl
  have vu : Run W (.var (iu + 1)) (u' :: env) u 1 := Run.var hu
  by_cases h : u' = u
  · rw [if_pos h]
    exact RunZ.mono (runZ_eqX_pos v0 vu h RunZ.lit1) (by omega)
  · rw [if_neg h]
    have hne : u ≠ u' := Ne.symm h
    have rb : Run W (bpE K' base wt (g + 1) (id + 1) (iu + 1) (iZ' + 1) 0) (u' :: env)
        (viewL K' ((L dir).newW u) Z' u') (494 * mon K' C 3) := run_bpE H (hf.up u') hd hu hZ' rfl huK huK'
    generalize viewL K' ((L dir).newW u) Z' u' = b at rb ⊢
    have r1 : Run W (.ite (.var (iu + 2)) (.var 1) (.var (iu + 2)) (.var 1)) (b :: u' :: env) (min u u') 4 :=
      run_minE hu rfl
    have r2 : Run W (.ite (.var (iu + 3)) (.var 2) (.var 2) (.var (iu + 3))) (min u u' :: b :: u' :: env) (max u u') 4 :=
      run_maxE hu rfl
    have hloop := RunZ.prod (T := (K' + 1) * (K' + 1)) (Run.lit (env := max u u' :: min u u' :: b :: u' :: env)
      (H.lt2 (by omega) : K' * K' < 2 ^ W)) (KK_le_PP K')
      (fun s hs => runZ_transSeg H (b := b) (s := s) hf hd hu hZ huK huK' hne hs)
    have hbd : 1 + 1 + (K' + 1) * (K' + 1) * (915 * mon K' C 3 + 2 * rectCost f.sc + 1) ≤
        918 * mon K' C 5 + (K' + 1) * (K' + 1) * (2 * rectCost f.sc) := by
      have := loop_le (P := (K' + 1) * (K' + 1)) (M := mon K' C 3) (R := 2 * rectCost f.sc) (c := 915) (cn := 1)
        (B := 915 * mon K' C 3 + 2 * rectCost f.sc) (Nat.mul_pos (by omega) (by omega)) (mon_pos ..) le_rfl
      rwa [mon_two] at this
    exact RunZ.mono (runZ_eqX_neg v0 vu h (RunZ.letE rb (RunZ.letE r1 (RunZ.letE r2 hloop)))) (by omega)

theorem runZ_transE (H : StepCtx W f K' base C wt w) {env : List ℕ} {g id iu iZ iZ' u Z Z' : ℕ} {dir : Bool}
    (hf : f.At env g) (hd : env.getD id 0 = dir.toNat) (hu : env.getD iu 0 = u) (hZ : env.getD iZ 0 = Z)
    (hZ' : env.getD iZ' 0 = Z') (huK : u < K') :
    RunZ W (transE K' base wt g id iu iZ iZ') env
      ((L dir).trans u (readB (L dir) u Z) (viewL K' ((L dir).newW u) Z'))
      (1600 * mon K' C 6 + 3 * ((K' + 1) * ((K' + 1) * (K' + 1) * rectCost f.sc))) := by
  have hc := mon_chain K' C
  have hk := H.K_le
  have hK2 : K' < 2 ^ W := H.lt2 (by omega)
  have b1 : 1 + 1 + (K' + 1) * (140 * mon K' C 3 + rectCost f.sc + 1) ≤
      143 * mon K' C 4 + (K' + 1) * rectCost f.sc := by
    have := loop_le (P := K' + 1) (M := mon K' C 3) (R := rectCost f.sc) (c := 140) (cn := 1)
      (B := 140 * mon K' C 3 + rectCost f.sc) (by omega) (mon_pos ..) le_rfl
    rwa [mon_succ] at this
  have b2 : 1 + 1 + (K' + 1) * (143 * mon K' C 4 + (K' + 1) * rectCost f.sc + 1) ≤
      146 * mon K' C 5 + (K' + 1) * ((K' + 1) * rectCost f.sc) := by
    have := loop_le (P := K' + 1) (M := mon K' C 4) (R := (K' + 1) * rectCost f.sc) (c := 143) (cn := 1)
      (B := 143 * mon K' C 4 + (K' + 1) * rectCost f.sc) (by omega) (mon_pos ..) le_rfl
    rwa [mon_succ] at this
  have b3 : 1 + 1 + (K' + 1) * (1429 * mon K' C 5 + (K' + 1) * (K' + 1) * (2 * rectCost f.sc) + 1) ≤
      1432 * mon K' C 6 + (K' + 1) * ((K' + 1) * (K' + 1) * (2 * rectCost f.sc)) := by
    have := loop_le (P := K' + 1) (M := mon K' C 5) (R := (K' + 1) * (K' + 1) * (2 * rectCost f.sc)) (c := 1429)
      (cn := 1) (B := 1429 * mon K' C 5 + (K' + 1) * (K' + 1) * (2 * rectCost f.sc)) (by omega) (mon_pos ..) le_rfl
    rwa [mon_succ] at this
  have hRR : (K' + 1) * ((K' + 1) * rectCost f.sc) ≤ (K' + 1) * ((K' + 1) * (K' + 1) * rectCost f.sc) := by
    have : (K' + 1) * rectCost f.sc ≤ (K' + 1) * (K' + 1) * rectCost f.sc := by
      rw [mul_assoc]
      exact Nat.le_mul_of_pos_left _ (by omega)
    exact Nat.mul_le_mul_left _ this
  have hR2 : (K' + 1) * ((K' + 1) * (K' + 1) * (2 * rectCost f.sc)) =
      2 * ((K' + 1) * ((K' + 1) * (K' + 1) * rectCost f.sc)) := by ring
  exact RunZ.mono (RunZ.mul
    (RunZ.mono (RunZ.prod (T := K' + 1) (Run.lit hK2) (Nat.le_succ _) (fun v hv =>
      RunZ.mono (RunZ.prod (T := K' + 1) (Run.lit hK2) (Nat.le_succ _) (fun v' hv' =>
        runZ_transMark H hf hd hu hZ huK hv hv')) b1)) b2)
    (RunZ.prod (T := K' + 1) (Run.lit hK2) (Nat.le_succ _) (fun u' hu' =>
      runZ_transWord H hf hd hu hZ hZ' huK hu'))) (by omega)

theorem readZ_lt {dir : Bool} {u Z v : ℕ} (hv : v < K') :
    readZ (L dir) u Z v < 2 ^ ∑ y ∈ range (K' * K'), w ((L dir).wd u v) y := by
  unfold readZ viewL
  rw [if_pos hv]
  exact Nat.mod_lt _ (by positivity)

/-- The product of the old word functions in `wordNext`. -/
theorem runZ_wordProd (H : StepCtx W f K' base C wt w) {word : ℕ → ℕ → ℕ → Expr} {F : ℕ → (ℕ → ℕ) → ℤ} {Cword : ℕ}
    (hword : WordSpec W f (K' * K') word w F Cword) {env : List ℕ} {g iu u Z : ℕ} {dir : Bool} (hf : f.At env g)
    (hu : env.getD iu 0 = u) (huK : u < K') :
    RunZ W (.prod (.lit K') <|
        .letE (wdE K' 2 (iu + 3) 0) <|
        .letE (zvE K' wt (g + 4) 3 (iu + 4) 2 1) <|
          word (g + 5) 1 0) (Z :: dir.toNat :: env)
      (∏ v ∈ range K', F ((L dir).wd u v) (readB (L dir) u Z v)) (47 * mon K' C 4 + (K' + 1) * Cword) := by
  have hc := mon_chain K' C
  have hk := H.K_le
  have hbody : ∀ v < K', RunZ W (.letE (wdE K' 2 (iu + 3) 0) <| .letE (zvE K' wt (g + 4) 3 (iu + 4) 2 1) <| word (g + 5) 1 0)
      (v :: Z :: dir.toNat :: env) (F ((L dir).wd u v) (readB (L dir) u Z v)) (44 * mon K' C 3 + Cword) := by
    intro v hv
    have x := wd_lt (base := base) (f := f) (w := w) (dir := dir) huK hv
    have hf3 := ((hf.up dir.toNat).up Z).up v
    have hf4 := hf3.up ((L dir).wd u v)
    have hf5 := hf4.up (readZ (L dir) u Z v)
    have r1 : Run W (zvE K' wt (g + 4) 3 (iu + 4) 2 1) ((L dir).wd u v :: v :: Z :: dir.toNat :: env)
        (readZ (L dir) u Z v) (34 * mon K' C 3) := run_zvE H hf4 rfl hu rfl rfl huK hv
    have r2 : RunZ W (word (g + 5) 1 0) (readZ (L dir) u Z v :: (L dir).wd u v :: v :: Z :: dir.toNat :: env)
        (F ((L dir).wd u v) (readB (L dir) u Z v)) Cword :=
      hword hf5 rfl rfl x (readZ_lt hv)
    exact RunZ.mono (RunZ.letE (run_wdE H rfl hu rfl huK hv) (RunZ.letE r1 r2)) (by omega)
  have hbd : 1 + 1 + (K' + 1) * (44 * mon K' C 3 + Cword + 1) ≤ 47 * mon K' C 4 + (K' + 1) * Cword := by
    have := loop_le (P := K' + 1) (M := mon K' C 3) (R := Cword) (c := 44) (cn := 1)
      (B := 44 * mon K' C 3 + Cword) (by omega) (mon_pos ..) le_rfl
    rwa [mon_succ] at this
  exact RunZ.mono (RunZ.prod (T := K' + 1) (Run.lit (H.lt2 (by omega))) (Nat.le_succ _) hbody) hbd

/-- The arithmetic of the cost of `wordNext`: everything before the loop goes into the body. -/
theorem word_cost_le {T A B X : ℕ} (hT : 1 ≤ T) (h : A + B + 1 ≤ X) : A + T * (B + 1) ≤ T * X := by
  have h1 : A * 1 ≤ A * T := Nat.mul_le_mul_left _ hT
  calc A + T * (B + 1) ≤ A * T + T * (B + 1) := by omega
    _ = T * (A + B + 1) := by ring
    _ ≤ T * X := Nat.mul_le_mul_left _ h

theorem runZ_wordNext (H : StepCtx W f K' base C wt w) {word : ℕ → ℕ → ℕ → Expr} {F : ℕ → (ℕ → ℕ) → ℤ} {Cword Eb : ℕ}
    (hword : WordSpec W f (K' * K') word w F Cword) {d : Bool}
    (hdir : d = dirOf K' w f.sc (f.c / 2 ^ base % 2 ^ K' ^ 4))
    (hE : ∀ u < K', ∑ v ∈ range K', ∑ y ∈ range (K' * K'), w ((L d).wd u v) y ≤ Eb)
    {env : List ℕ} {g iu iZ' u Z' : ℕ} (hf : f.At env g) (hu : env.getD iu 0 = u) (hZ' : env.getD iZ' 0 = Z')
    (huK : u < K') :
    RunZ W (wordNext K' base wt word g iu iZ') env ((L d).stepF F u (viewL K' ((L d).newW u) Z'))
      (nextWordCost K' C Cword Eb f.sc) := by
  have hc := mon_chain K' C
  have hk := H.K_le
  have hd0 : Run W (dirE K' base wt g) env d.toNat (512 * mon K' C 4) := by
    rw [hdir]
    exact run_dirE H hf
  have hf1 := hf.up d.toNat
  have hrow := row_total_le H (dir := d) huK
  -- the bound of the loop
  have hhdr : Run W (.sum (.lit K') (.letE (wdE K' 1 (iu + 2) 0) (endsE wt (K' * K') (g + 3) 0))) (d.toNat :: env)
      (∑ v ∈ range K', ∑ y ∈ range (K' * K'), w ((L d).wd u v) y) (1 + 1 + (K' + 1) * (13 * mon K' C 2 + 1)) :=
    Run.sum (Run.lit (H.lt2 (by omega))) (Nat.le_succ _) (fun v hv => Run.mono (Run.letE (run_wdE H rfl hu rfl huK hv)
      (run_endsE H ((hf1.up v).up _) rfl (wd_lt huK hv))) (by omega)) (H.lt2 (by omega))
  have hb0 : 1 + 1 + (K' + 1) * (13 * mon K' C 2 + 1) ≤ (13 + 1 + 2) * mon K' C 3 :=
    loop_mon1 (K' := K') (C := C) (n := 2) (c := 13) (cn := 1) (B := 13 * mon K' C 2) le_rfl
  have hn : Run W (.pow2 (.sum (.lit K') (.letE (wdE K' 1 (iu + 2) 0) (endsE wt (K' * K') (g + 3) 0)))) (d.toNat :: env)
      (2 ^ ∑ v ∈ range K', ∑ y ∈ range (K' * K'), w ((L d).wd u v) y) (1 + (1 + 1 + (K' + 1) * (13 * mon K' C 2 + 1))) :=
    Run.pow2 hhdr (H.ltW (by omega))
  have hkT : 2 ^ (∑ v ∈ range K', ∑ y ∈ range (K' * K'), w ((L d).wd u v) y) ≤ 2 ^ Eb :=
    Nat.pow_le_pow_right (by norm_num) (hE u huK)
  -- the body of the loop
  have hbody : ∀ Z < 2 ^ ∑ v ∈ range K', ∑ y ∈ range (K' * K'), w ((L d).wd u v) y,
      RunZ W (.mul (transE K' base wt (g + 2) 1 (iu + 2) 0 (iZ' + 2)) <|
        .prod (.lit K') <|
          .letE (wdE K' 2 (iu + 3) 0) <|
          .letE (zvE K' wt (g + 4) 3 (iu + 4) 2 1) <|
            word (g + 5) 1 0) (Z :: d.toNat :: env)
        ((L d).trans u (readB (L d) u Z) (viewL K' ((L d).newW u) Z') *
          ∏ v ∈ range K', F ((L d).wd u v) (readB (L d) u Z v))
        (1700 * mon K' C 6 + 3 * ((K' + 1) * ((K' + 1) * (K' + 1) * rectCost f.sc)) + (K' + 1) * Cword) := by
    intro Z _
    exact RunZ.mono (RunZ.mul (runZ_transE H (hf1.up Z) rfl hu rfl hZ' huK) (runZ_wordProd H hword hf hu huK)) (by omega)
  -- the value
  have hval : ∑ Z ∈ range (2 ^ ∑ v ∈ range K', ∑ y ∈ range (K' * K'), w ((L d).wd u v) y),
      ((L d).trans u (readB (L d) u Z) (viewL K' ((L d).newW u) Z') *
        ∏ v ∈ range K', F ((L d).wd u v) (readB (L d) u Z v)) =
      (L d).stepF F u (viewL K' ((L d).newW u) Z') :=
    sum_viewL_two K' (K' * K') (fun v y => w ((L d).wd u v) y)
      (fun B => (L d).trans u B (viewL K' ((L d).newW u) Z') * ∏ v ∈ range K', F ((L d).wd u v) (B v))
  rw [← hval]
  -- the cost
  have hT : 1 ≤ 2 ^ Eb := Nat.one_le_two_pow
  have hX : nextWordCost K' C Cword Eb f.sc = 2 ^ Eb * (20000 * mon K' C 8 +
      (3 * ((K' + 1) * ((K' + 1) * (K' + 1) * rectCost f.sc)) + (K' + 1) ^ 3 * 100) + ((K' + 1) * Cword + (K' + 1))) := by
    unfold nextWordCost mon
    ring
  rw [hX]
  refine RunZ.mono (RunZ.letE hd0 (RunZ.sum (T := 2 ^ Eb) hn hkT hbody)) ?_
  have := word_cost_le (T := 2 ^ Eb)
    (A := 1 + 512 * mon K' C 4 + (1 + (1 + (1 + 1 + (K' + 1) * (13 * mon K' C 2 + 1)))))
    (B := 1700 * mon K' C 6 + 3 * ((K' + 1) * ((K' + 1) * (K' + 1) * rectCost f.sc)) + (K' + 1) * Cword)
    (X := 20000 * mon K' C 8 + (3 * ((K' + 1) * ((K' + 1) * (K' + 1) * rectCost f.sc)) + (K' + 1) ^ 3 * 100) +
      ((K' + 1) * Cword + (K' + 1))) hT (by omega)
  omega

end Helpers

end StepSpec

open StepSpec in
/-- **The weights of the next level.** -/
theorem wtNext_spec {W : ℕ} {f : Frm} {K' base C : ℕ} {wt : ℕ → ℕ → ℕ → Expr} {w : ℕ → ℕ → ℕ}
    (hB : StepBig W f K' base w) (hK : 0 < K') (hwt : WtSpec W f (K' * K') wt w C) :
    WtSpec W f K' (wtNext K' base wt) (stepLev K' base f.sc f.c w).newW (nextWtCost K' C) := by
  have H : StepCtx W f K' base C wt w := ⟨hB, hK, hwt⟩
  intro g ix iy x y env hf hx hy hxK hyK
  have hc := mon_chain K' C
  have e : nextWtCost K' C = 4000 * mon K' C 4 := by unfold nextWtCost mon; ring
  exact Run.mono (Run.letE (run_dirE H hf) (run_newWE H (hf.up _) rfl hx hy hxK hyK)) (by omega)

open StepSpec in
/-- **The word functions of the next level.** -/
theorem wordNext_spec {W : ℕ} {f : Frm} {K' base Cw Cword Eb : ℕ} {wt word : ℕ → ℕ → ℕ → Expr}
    {w : ℕ → ℕ → ℕ} {F : ℕ → (ℕ → ℕ) → ℤ}
    (hB : StepBig W f K' base w) (hK : 0 < K') (hwt : WtSpec W f (K' * K') wt w Cw)
    (hword : WordSpec W f (K' * K') word w F Cword)
    (hE : ∀ u < K', ∑ v ∈ range K', ∑ y ∈ range (K' * K'), w ((stepLev K' base f.sc f.c w).wd u v) y ≤ Eb) :
    WordSpec W f K' (wordNext K' base wt word) (stepLev K' base f.sc f.c w).newW
      ((stepLev K' base f.sc f.c w).stepF F) (nextWordCost K' Cw Cword Eb f.sc) := by
  have H : StepCtx W f K' base Cw wt w := ⟨hB, hK, hwt⟩
  intro g iu iZ' u Z' env hf hu hZ' huK _
  exact runZ_wordNext H hword rfl hE hf hu hZ' huK

end DominantStrings.Pseudo
