import TransposeBase.Pseudo.TreePath

/-!
# The traversal of the branching tree as a program

No formula is stored. The state of the loop is the path word `p` (see `TreeWalk`). The formula at a node is
recomputed from the root by a `fold` along the bits of `p` (`pathE`).

**Layout of the environment.** `treeE L fuelE leafE` runs on `encF n F :: n :: rest`. It binds the root word,
so that `fuelE` runs on `root :: encF n F :: n :: rest`. At a node with word `p`:

* the loop body and the successor run on `p :: root :: encF n F :: n :: rest`;
* `leafE` runs on `encF n t.formula :: p :: root :: encF n F :: n :: rest`, where `t` is the state at `p`.

So variable `0` of `leafE` is the word of the leaf formula, variable `1` is the path, variable `2` is the root
word `encF n (normalizeClauses F)`, variable `3` is `encF n F`, and variable `4` is `n`.
-/

namespace TransposeBase.Pseudo.CnfTree

open SatBase Finset TransposeBase.Sat

variable {W n L : ℕ} {env : List ℕ}

/-- The size conditions. -/
structure TreeCtx (W n L : ℕ) : Prop where
  ctx : Ctx W n
  depth : 10 * n * L + 3 ≤ W
  sq : L * L < 2 ^ W

/-- The number `10 * n * L + 1` of bits of a path word. -/
def depthE (L nv : ℕ) : Expr := .add (.mul (.mul (.lit 10) (.var nv)) (.lit L)) (.lit 1)

/-- The word of the state at the path word in the variable `p`, from the root word in the variable `root`.
The bits of the path are read from the top. -/
def pathE (L p root nv : ℕ) : Expr :=
  .fold (depthE L nv) (.var root)
    (.letE (.sub (depthE L (nv + 2)) (.add (.var 1) (.lit 1)))
      (.ite (.div (.var (p + 3)) (.pow2 (.add (.var 0) (.lit 1)))) (.lit 0)
        (.var 1)
        (.letE (bitE (p + 3) 0) (stepE L 2 0 (nv + 4)))))

/-- One step of stripping a trailing zero. -/
def stripE : Expr := .ite (.mod (.var 0) (.lit 2)) (.lit 0) (.div (.var 0) (.lit 2)) (.var 0)

/-- The successor of a leaf: the odd part of `p + 1`, and the sentinel `0` if that is `1`. -/
def leafNextE (L p nv : ℕ) : Expr :=
  .letE (.fold (.add (depthE L nv) (.lit 1)) (.add (.var p) (.lit 1)) stripE)
    (.ite (.var 0) (.lit 1) (.lit 0) (.var 0))

/-- The successor in preorder, on `p :: root :: encF n F :: n :: rest`. -/
def succE (L : ℕ) : Expr :=
  .ite (.var 0) (.lit 0) (.lit 0)
    (.letE (pathE L 0 1 3)
      (.ite (RE 4) (ruleE L 0 4) (leafNextE L 1 4) (.mul (.lit 2) (.var 1))))

/-- The loop body, on `p :: root :: encF n F :: n :: rest`: at a leaf, the indicator that `leafE` is not zero. -/
def bodyE (L : ℕ) (leafE : Expr) : Expr :=
  .ite (.var 0) (.lit 0) (.lit 0)
    (.letE (pathE L 0 1 3)
      (.ite (RE 4) (ruleE L 0 4) (.ite leafE (.lit 0) (.lit 0) (.lit 1)) (.lit 0)))

/-- The whole traversal, on `encF n F :: n :: rest`. -/
def treeE (L : ℕ) (fuelE leafE : Expr) : Expr :=
  .letE (normE 0 1) (.sumIter fuelE (.lit 1) (succE L) (bodyE L leafE))

/-- The cost of `pathE` is `pathC L * (n + 1) ^ 8`. -/
def pathC (L : ℕ) : ℕ := 9 + (10 * L + 1) * 350101

section

variable (hT : TreeCtx W n L) (hL : 2 ≤ L)
include hT hL

theorem run_depthE {nv : ℕ} (hn : env.getD nv 0 = n) :
    Run W (depthE L nv) env (10 * n * L + 1) 7 := by
  have hC := hT.ctx
  have hd := hT.depth
  have hl : L < 2 ^ W := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by omega)) hT.sq
  have h10 : (10 : ℕ) < 2 ^ W := by
    calc 10 < 2 ^ 8 := by norm_num
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hC.eight_le
  have hle : 10 * n ≤ 10 * n * L := Nat.le_mul_of_pos_right _ (by omega)
  have a := run_mul (run_lit h10) (run_var hn) (hC.lt_pow (by omega))
  have b := run_mul a (run_lit hl) (hC.lt_pow (by omega))
  have c := run_add b (run_one hC.one_le) (hC.lt_pow (by omega))
  exact c.mono (by omega)

theorem run_pathE {nv p root pv : ℕ} (s0 : SparseState n L) (hn : env.getD nv 0 = n)
    (hp : env.getD p 0 = pv) (hroot : env.getD root 0 = encF n s0.formula)
    (hpv : pv < 2 ^ (10 * n * L + 1)) :
    Run W (pathE L p root nv) env (encF n (stateW hL s0 pv).formula) (pathC L * (n + 1) ^ 8) := by
  have hC := hT.ctx
  have hd := hT.depth
  have ww := hC.one_le
  have m1 : 1 ≤ (n + 1) ^ 7 := Nat.one_le_pow _ _ (by omega)
  set D := 10 * n * L + 1 with hD
  have hDW : D < W := by omega
  let g : ℕ → ℕ := fun i => encF n (stateW hL s0 (pv / 2 ^ (D - i))).formula
  have hg0 : g 0 = encF n s0.formula := by
    simp only [g, Nat.sub_zero]
    rw [Nat.div_eq_of_lt hpv, stateW_le_one hL s0 (by omega)]
  have := run_fold (g := g) (B := 350100 * (n + 1) ^ 7) (run_depthE hT hL hn)
    ((run_var hroot).val hg0.symm)
    (fun i hi => by
      -- the current position
      have hnv2 := gd (g i) (gd i hn)
      have hp2 := gd (g i) (gd i hp)
      obtain ⟨j, hj⟩ : ∃ j, D = i + 1 + j := ⟨D - (i + 1), by omega⟩
      have hji : D - (i + 1) = j := by omega
      have hi1 : D - i = j + 1 := by omega
      have hi2 : (g i :: i :: env).getD 1 0 = i := by simp
      have hsub : Run W (.sub (depthE L (nv + 2)) (.add (.var 1) (.lit 1))) (g i :: i :: env) j 11 := by
        have a := run_depthE (env := g i :: i :: env) hT hL hnv2
        have b := run_add (run_var hi2) (run_one ww) (hC.lt_pow (by omega))
        have := run_sub a b (by omega) (hC.lt_pow (by omega))
        rw [← hD, hji] at this
        exact this.mono (by omega)
      have hj0 : (j :: g i :: i :: env).getD 0 0 = j := gd0 j
      have hp3 := gd j hp2
      have hst : (j :: g i :: i :: env).getD 1 0 = g i := by simp
      have hpw := run_pow2 (run_add (run_var hj0) (run_one ww) (hC.lt_pow (by omega)))
        (show j + 1 < W by omega)
      have hdiv := run_div (run_var hp3) hpw
      obtain ⟨x, hx⟩ : ∃ x, pv / 2 ^ (j + 1) = x := ⟨_, rfl⟩
      obtain ⟨y, hy⟩ : ∃ y, pv / 2 ^ j = y := ⟨_, rfl⟩
      rw [hx] at hdiv
      have hxy : y / 2 = x := by
        rw [← hx, ← hy, pow_succ, Nat.div_div_eq_div_mul]
      have hgi : g i = encF n (stateW hL s0 x).formula := by
        simp only [g, hi1, hx]
      have hgs : g (i + 1) = encF n (stateW hL s0 y).formula := by
        simp only [g, hji, hy]
      have inner : Run W (.ite (.div (.var (p + 3)) (.pow2 (.add (.var 0) (.lit 1)))) (.lit 0)
          (.var 1) (.letE (bitE (p + 3) 0) (stepE L 2 0 (nv + 4))))
          (j :: g i :: i :: env) (g (i + 1)) (350000 * (n + 1) ^ 7 + 25) := by
        refine (run_ite (Bc := 350000 * (n + 1) ^ 7 + 8) hdiv (run_zero ww) ?_ ?_).mono (by omega)
        · intro hle
          have hx0 : x = 0 := by omega
          have hy1 : y ≤ 1 := by omega
          have : g (i + 1) = g i := by
            rw [hgs, hgi, stateW_le_one hL s0 hy1, stateW_le_one hL s0 (by omega : x ≤ 1)]
          rw [this]
          exact (run_var hst).mono (by omega)
        · intro hne
          have hx1 : 1 ≤ x := by omega
          have hy2 : 2 ≤ y := by omega
          have hbit : Run W (bitE (p + 3) 0) (j :: g i :: i :: env) (y % 2) 6 := by
            refine ⟨?_, (ops_bitE W _ _ _).le⟩
            rw [eval_bitE W _ _ _ hC.two_le (by rw [hj0]; omega), hp3, hj0,
              Nat.testBit_eq_decide_div_mod_eq]
            rw [hy]
            rcases Nat.mod_two_eq_zero_or_one y with h | h <;> simp [h]
          have hbit0 : ((y % 2) :: j :: g i :: i :: env).getD 0 0 = y % 2 := gd0 _
          have hnv4 := gd (y % 2) (gd j hnv2)
          have hf4 : ((y % 2) :: j :: g i :: i :: env).getD 2 0 =
              encF n (stateW hL s0 x).formula := by
            simp [hgi]
          have hs := run_stepE (L := L) (f := 2) (b := 0) hC hnv4 hL hT.sq (stateW hL s0 x) hf4 hbit0
          have hyb : (decide (y % 2 ≠ 0)) = decide (y % 2 = 1) := by
            rcases Nat.mod_two_eq_zero_or_one y with h | h <;> simp [h]
          rw [hyb, ← hxy, ← stateW_step hL s0 hy2, ← hgs] at hs
          exact (run_let hbit hs).mono (by omega)
      exact (run_let hsub inner).mono (by omega))
  have hval : g D = encF n (stateW hL s0 pv).formula := by
    simp [g]
  rw [hval] at this
  refine this.mono ?_
  have hDle : D ≤ (10 * L + 1) * (n + 1) ^ 1 := by
    rw [pow_one, hD]
    have : 10 * n * L ≤ 10 * L * (n + 1) := by nlinarith
    nlinarith
  have h := loop_le' (K := 1 + 7 + 1) (B := 350100 * (n + 1) ^ 7) (e := 1) (a := 10 * L + 1) (c := 350100)
    (d := 7) (C := pathC L) (m := n + 1) (N := D) (p := 1) (by omega) hDle le_rfl
    (by simp only [pathC]; omega)
  exact h

theorem oddPart_pos {q : ℕ} (hq : 0 < q) : 0 < oddPart q := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rw [oddPart, dif_neg (by omega)]
    split
    · exact ih (q / 2) (by omega) (by omega)
    · exact hq

theorem run_leafNextE {nv p pv : ℕ} (hn : env.getD nv 0 = n) (hp : env.getD p 0 = pv)
    (hp0 : 0 < pv) (hpv : pv + 1 ≤ 2 ^ (10 * n * L + 1)) :
    Run W (leafNextE L p nv) env (leafNext pv) (18 + (10 * L + 2) * 9 * (n + 1)) := by
  have hC := hT.ctx
  have hd := hT.depth
  have ww := hC.one_le
  have hsmall : pv + 1 < 2 ^ W :=
    lt_of_le_of_lt hpv (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have h2 : (2 : ℕ) < 2 ^ W := hC.lt_pow (by have := hC.eight_le; omega)
  let g : ℕ → ℕ := fun i => stripStep^[i] (pv + 1)
  have hf := run_fold (g := g) (B := 8)
    (run_add (run_depthE hT hL hn) (run_one ww) (hC.lt_pow (by omega)))
    (run_add (run_var hp) (run_one ww) hsmall)
    (fun i _ => by
      have h0 : (g i :: i :: env).getD 0 0 = g i := gd0 _
      have hv := run_var (W := W) h0
      have hg : g (i + 1) = stripStep (g i) := by
        simp only [g]
        rw [Function.iterate_succ_apply']
      rw [hg]
      have := run_ite (c := .div (.var 0) (.lit 2)) (d := .var 0) (v := stripStep (g i)) (Bc := 3)
        (run_mod hv (run_lit h2)) (run_zero ww)
        (fun h => by
          rw [stripStep, if_pos h]
          exact run_div hv (run_lit h2))
        (fun h => by
          rw [stripStep, if_neg h]
          exact hv.mono (by omega))
      exact this.mono (by omega))
  have hval : g (10 * n * L + 1 + 1) = oddPart (pv + 1) :=
    strip_iterate (by omega) (by
      rw [pow_succ]
      omega)
  rw [hval] at hf
  have hpos := oddPart_pos (q := pv + 1) (by omega)
  have h0 : (oddPart (pv + 1) :: env).getD 0 0 = oddPart (pv + 1) := gd0 _
  have hl := run_ite (c := .lit 0) (d := .var 0) (v := leafNext pv) (Bc := 1)
    (run_var h0) (run_one ww)
    (fun h => by
      rw [leafNext, if_pos (by omega)]
      exact run_zero ww)
    (fun h => by
      rw [leafNext, if_neg (by omega)]
      exact run_var h0)
  refine (run_let hf hl).mono ?_
  have : (10 * n * L + 1 + 1) ≤ (10 * L + 2) * (n + 1) := by nlinarith
  have h9 := Nat.mul_le_mul_right 9 this
  have e : (10 * L + 2) * (n + 1) * 9 = (10 * L + 2) * 9 * (n + 1) := by ring
  omega

end

theorem cost_shape (n a c : ℕ) : a * (n + 1) ^ 8 + 102000 * (n + 1) ^ 6 + c + 40 ≤
    (a + 110000) * (n + 1) ^ 8 + c := by
  have h6 : (n + 1) ^ 6 ≤ (n + 1) ^ 8 := pow_le_pow_m n (by norm_num)
  have h1 : 1 ≤ (n + 1) ^ 8 := Nat.one_le_pow _ _ (by omega)
  have e : (a + 110000) * (n + 1) ^ 8 = a * (n + 1) ^ 8 + 110000 * (n + 1) ^ 8 := by ring
  omega

section Node

variable {rest : List ℕ} {Fw : ℕ} (hT : TreeCtx W n L) (hL : 2 ≤ L) (s0 : SparseState n L)
include hT

/-- The cost of the successor is `succC L * (n + 1) ^ 8`. -/
def succC (L : ℕ) : ℕ := pathC L + 110000 + (10 * L + 2) * 9

/-- The environment of the loop at the word `p`. -/
noncomputable def nodeEnv (s0 : SparseState n L) (Fw : ℕ) (rest : List ℕ) (p : ℕ) : List ℕ :=
  p :: encF n s0.formula :: Fw :: n :: rest

/-- The environment of `leafE` at the word `p`. -/
noncomputable def leafEnv (hL : 2 ≤ L) (s0 : SparseState n L) (Fw : ℕ) (rest : List ℕ) (p : ℕ) : List ℕ :=
  encF n (stateW hL s0 p).formula :: nodeEnv s0 Fw rest p

theorem run_succE {pv : ℕ} (hgood : pv = 0 ∨ (0 < pv ∧ pv + 1 ≤ 2 ^ (10 * n * L + 1))) :
    Run W (succE L) (nodeEnv s0 Fw rest pv) (succWord (IntAt hL s0) pv) (succC L * (n + 1) ^ 8) := by
  have hC := hT.ctx
  have hd := hT.depth
  have ww := hC.one_le
  have m8 : 1 ≤ (n + 1) ^ 8 := Nat.one_le_pow _ _ (by omega)
  have hp0' : (nodeEnv s0 Fw rest pv).getD 0 0 = pv := rfl
  have hroot : (nodeEnv s0 Fw rest pv).getD 1 0 = encF n s0.formula := rfl
  have hn3 : (nodeEnv s0 Fw rest pv).getD 3 0 = n := rfl
  have hcost : succC L * (n + 1) ^ 8 = (pathC L + 110000) * (n + 1) ^ 8 + (10 * L + 2) * 9 * (n + 1) ^ 8 := by
    unfold succC; ring
  have hA : (10 * L + 2) * 9 * (n + 1) ≤ (10 * L + 2) * 9 * (n + 1) ^ 8 :=
    Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) _)
  have hsh := cost_shape n (pathC L) ((10 * L + 2) * 9 * (n + 1) ^ 8)
  have hA' : 0 ≤ pathC L * (n + 1) ^ 8 := Nat.zero_le _
  have hge : 10 ≤ (pathC L + 110000) * (n + 1) ^ 8 := by nlinarith
  rw [hcost]
  rcases hgood with rfl | ⟨hp0, hpb⟩
  · have := run_ite (c := .lit 0) (d := .letE (pathE L 0 1 3)
        (.ite (RE 4) (ruleE L 0 4) (leafNextE L 1 4) (.mul (.lit 2) (.var 1))))
        (v := succWord (IntAt hL s0) 0) (Bc := 1) (run_var hp0') (run_zero ww)
        (fun _ => by
          rw [succWord_zero]
          exact run_zero ww)
        (fun h => absurd (le_refl 0) h)
    exact this.mono (by omega)
  · have hne : pv ≠ 0 := by omega
    have hpa := run_pathE hT hL s0 hn3 hp0' hroot (show pv < _ by omega)
    set st := (stateW hL s0 pv) with hst
    set e2 := encF n st.formula :: nodeEnv s0 Fw rest pv with he2
    have hn4 : e2.getD 4 0 = n := rfl
    have hf : e2.getD 0 0 = encF n st.formula := rfl
    have hp1 : e2.getD 1 0 = pv := rfl
    have hr := run_ruleE (L := L) hC hn4 st.width hT.sq (by omega) hf
    have hR := run_RE hC hn4
    have hle := run_leafNextE hT hL hn4 hp1 hp0 hpb
    have h2p : 2 * pv < 2 ^ W := by
      have : 2 ^ (10 * n * L + 1 + 1) ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [pow_succ] at this
      omega
    have h2 : (2 : ℕ) < 2 ^ W := hC.lt_pow (by have := hC.eight_le; omega)
    have hmul := run_mul (run_lit (env := e2) h2) (run_var hp1) h2p
    have hin : Run W (.ite (RE 4) (ruleE L 0 4) (leafNextE L 1 4) (.mul (.lit 2) (.var 1))) e2
        (succWord (IntAt hL s0) pv) (1 + 13 + 102000 * (n + 1) ^ 6 + (18 + (10 * L + 2) * 9 * (n + 1))) := by
      refine run_ite hR hr ?_ ?_
      · intro h
        have hnone := rule_leaf_iff.mp h
        have hi : ¬ IntAt hL s0 pv := by simp only [IntAt, ne_eq, not_not]; exact hnone
        have : succWord (IntAt hL s0) pv = leafNext pv := by simp [succWord, hne, hi]
        rw [this]
        exact hle
      · intro h
        have hi : IntAt hL s0 pv := by
          simp only [IntAt, ne_eq]
          exact fun hn => h (rule_leaf_iff.mpr hn)
        have : succWord (IntAt hL s0) pv = 2 * pv := by simp [succWord, hne, hi]
        rw [this]
        exact hmul.mono (by nlinarith)
    have := run_let hpa hin
    have := run_ite (c := .lit 0) (v := succWord (IntAt hL s0) pv) (run_var hp0') (run_zero ww)
      (fun h => absurd h (by omega)) (fun _ => this)
    refine this.mono ?_
    omega

/-- The cost of the loop body, except `leafE`, is `bodyC L * (n + 1) ^ 8`. -/
def bodyC (L : ℕ) : ℕ := pathC L + 110000

theorem run_bodyE {leafE : Expr} {U pv : ℕ}
    (hgood : pv = 0 ∨ (0 < pv ∧ pv + 1 ≤ 2 ^ (10 * n * L + 1)))
    (hU : pv ≠ 0 → ¬ IntAt hL s0 pv → ops W leafE (leafEnv hL s0 Fw rest pv) ≤ U) :
    Test W (bodyE L leafE) (nodeEnv s0 Fw rest pv)
      (pv ≠ 0 ∧ ¬ IntAt hL s0 pv ∧ eval W leafE (leafEnv hL s0 Fw rest pv) ≠ 0)
      (U + bodyC L * (n + 1) ^ 8) := by
  have hC := hT.ctx
  have ww := hC.one_le
  have m8 : 1 ≤ (n + 1) ^ 8 := Nat.one_le_pow _ _ (by omega)
  have hp0' : (nodeEnv s0 Fw rest pv).getD 0 0 = pv := rfl
  have hroot : (nodeEnv s0 Fw rest pv).getD 1 0 = encF n s0.formula := rfl
  have hn3 : (nodeEnv s0 Fw rest pv).getD 3 0 = n := rfl
  have hsh := cost_shape n (pathC L) U
  have hge : 10 ≤ (pathC L + 110000) * (n + 1) ^ 8 := by nlinarith
  simp only [bodyC]
  rcases hgood with rfl | ⟨hp0, hpb⟩
  · have := run_ite (c := .lit 0) (d := .letE (pathE L 0 1 3)
        (.ite (RE 4) (ruleE L 0 4) (.ite leafE (.lit 0) (.lit 0) (.lit 1)) (.lit 0)))
        (v := ind ((0 : ℕ) ≠ 0 ∧ ¬ IntAt hL s0 0 ∧ eval W leafE (leafEnv hL s0 Fw rest 0) ≠ 0)) (Bc := 1)
        (run_var hp0') (run_zero ww)
        (fun _ => by
          rw [ind_neg (by simp)]
          exact run_zero ww)
        (fun h => absurd (le_refl 0) h)
    exact this.mono (by omega)
  · have hne : pv ≠ 0 := by omega
    have hpa := run_pathE hT hL s0 hn3 hp0' hroot (show pv < _ by omega)
    have hn4 : (leafEnv hL s0 Fw rest pv).getD 4 0 = n := rfl
    have hf : (leafEnv hL s0 Fw rest pv).getD 0 0 = encF n (stateW hL s0 pv).formula := rfl
    have hr := run_ruleE (L := L) hC hn4 (stateW hL s0 pv).width hT.sq (by omega) hf
    have hR := run_RE hC hn4
    have hin : Run W (.ite (RE 4) (ruleE L 0 4) (.ite leafE (.lit 0) (.lit 0) (.lit 1)) (.lit 0))
        (leafEnv hL s0 Fw rest pv)
        (ind (pv ≠ 0 ∧ ¬ IntAt hL s0 pv ∧ eval W leafE (leafEnv hL s0 Fw rest pv) ≠ 0))
        (1 + 13 + 102000 * (n + 1) ^ 6 + (U + 3)) := by
      refine run_ite hR hr ?_ ?_
      · intro h
        have hnone := rule_leaf_iff.mp h
        have hi : ¬ IntAt hL s0 pv := by simp only [IntAt, ne_eq, not_not]; exact hnone
        have hb := hU hne hi
        by_cases hv : eval W leafE (leafEnv hL s0 Fw rest pv) ≠ 0
        · rw [ind_pos ⟨hne, hi, hv⟩]
          have := run_ite (c := .lit 0) (d := .lit 1) (a := leafE) (v := 1) (Bc := 1)
            (⟨rfl, hb⟩ : Run W leafE _ _ U) (run_zero ww)
            (fun h => absurd (by omega) hv)
            (fun _ => run_one ww)
          exact this.mono (by omega)
        · rw [ind_neg (fun h => hv h.2.2)]
          have := run_ite (c := .lit 0) (d := .lit 1) (a := leafE) (v := 0) (Bc := 1)
            (⟨rfl, hb⟩ : Run W leafE _ _ U) (run_zero ww)
            (fun _ => run_zero ww)
            (fun h => absurd (by omega) h)
          exact this.mono (by omega)
      · intro h
        have hi : IntAt hL s0 pv := by
          simp only [IntAt, ne_eq]
          exact fun hn => h (rule_leaf_iff.mpr hn)
        rw [ind_neg (fun h => h.2.1 hi)]
        exact (run_zero ww).mono (by omega)
    have := run_let hpa hin
    have := run_ite (c := .lit 0)
      (v := ind (pv ≠ 0 ∧ ¬ IntAt hL s0 pv ∧ eval W leafE (leafEnv hL s0 Fw rest pv) ≠ 0))
      (run_var hp0') (run_zero ww)
      (fun h => absurd h (by omega)) (fun _ => this)
    refine this.mono ?_
    omega

end Node

/-! ### The loop -/

theorem eval_sumIter_nat (W : ℕ) (n s f b : Expr) (env : List ℕ) :
    eval W (.sumIter n s f b) env =
      (∑ k ∈ range (eval W n env), eval W b (iterate W f (eval W s env) env k :: env)) % 2 ^ W := by
  simp only [eval]
  generalize eval W n env = m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, sum_range_succ]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [foldl_iter_fst, ih, Nat.mod_add_mod]

/-- The `k`-th word of the walk from the root. -/
noncomputable def walkA (hL : 2 ≤ L) (s0 : SparseState n L) (k : ℕ) : ℕ :=
  (succWord (IntAt hL s0))^[k] 1

/-- The word of the walk is a positive leaf with nonzero leaf value. -/
def PosLeaf (W : ℕ) (hL : 2 ≤ L) (s0 : SparseState n L) (Fw : ℕ) (rest : List ℕ) (leafE : Expr)
    (p : ℕ) : Prop :=
  p ≠ 0 ∧ ¬ IntAt hL s0 p ∧ eval W leafE (leafEnv hL s0 Fw rest p) ≠ 0

theorem agrees_root (hL : 2 ≤ L) (s0 : SparseState n L) :
    Agrees (IntAt hL s0) (sparseTree hL s0) 1 :=
  agrees_sparseTree hL s0 s0 1 (by omega) (stateW_le_one hL s0 le_rfl)

theorem walk_good (hL : 2 ≤ L) (s0 : SparseState n L) (k : ℕ) :
    walkA hL s0 k = 0 ∨ (0 < walkA hL s0 k ∧ walkA hL s0 k + 1 ≤ 2 ^ (10 * n * L + 1)) := by
  rcases walk_mem (IntAt hL s0) (sparseTree hL s0) (agrees_root hL s0) k with h | h
  · exact Or.inl h
  · exact Or.inr ⟨pos_of_mem_pre (by omega) h, word_bound hL s0 h⟩

theorem walk_leaf_reach (hL : 2 ≤ L) (s0 : SparseState n L) (k : ℕ) (h0 : walkA hL s0 k ≠ 0)
    (hi : ¬ IntAt hL s0 (walkA hL s0 k)) : Reach hL s0 (stateW hL s0 (walkA hL s0 k)) := by
  rcases walk_mem (IntAt hL s0) (sparseTree hL s0) (agrees_root hL s0) k with h | h
  · exact absurd h h0
  · exact reach_of_mem hL s0 s0 1 (by omega) (stateW_le_one hL s0 le_rfl) _ h hi

/-- The cost bound of the whole traversal is `fuel * (U + treeP L n) + treeP L n`, besides the cost of `fuelE`. -/
noncomputable def treeP (L n : ℕ) : ℕ := (succC L + bodyC L + 100000) * (n + 1) ^ 8

section Top

variable {rest : List ℕ} (hT : TreeCtx W n L) (hL : 2 ≤ L)

include hT in
/-- The loop from the root word. Its value is the number of positive leaves among the first `fuel` words
of the walk, and by `walk_getElem` each node is one word of the walk. -/
theorem loop_spec (s0 : SparseState n L) (Fw : ℕ) {fuelE leafE : Expr} {fuel U : ℕ}
    (hfuel : eval W fuelE (encF n s0.formula :: Fw :: n :: rest) = fuel) (hf2 : fuel < 2 ^ W)
    (hU : ∀ t, Reach hL s0 t → ∀ p, ops W leafE (encF n t.formula :: p :: encF n s0.formula :: Fw :: n :: rest) ≤ U) :
    eval W (.sumIter fuelE (.lit 1) (succE L) (bodyE L leafE))
        (encF n s0.formula :: Fw :: n :: rest) =
      ∑ k ∈ range fuel, ind (PosLeaf W hL s0 Fw rest leafE (walkA hL s0 k)) ∧
    ops W (.sumIter fuelE (.lit 1) (succE L) (bodyE L leafE)) (encF n s0.formula :: Fw :: n :: rest) ≤
      ops W fuelE (encF n s0.formula :: Fw :: n :: rest) + 2 +
        fuel * (U + (succC L + bodyC L) * (n + 1) ^ 8 + 1) := by
  have ww := hT.ctx.one_le
  set env1 := encF n s0.formula :: Fw :: n :: rest with henv
  have hs1 : eval W (.lit 1) env1 = 1 := (run_one ww).1
  have hit : ∀ k, iterate W (succE L) (eval W (.lit 1) env1) env1 k = walkA hL s0 k := by
    intro k
    induction k with
    | zero => exact hs1
    | succ k ih =>
      simp only [iterate]
      rw [ih]
      have := (run_succE (rest := rest) (Fw := Fw) hT hL s0 (walk_good hL s0 k)).1
      simp only [walkA] at this ⊢
      rw [Function.iterate_succ_apply']
      exact this
  have hbody : ∀ k, Test W (bodyE L leafE) (walkA hL s0 k :: env1)
      (PosLeaf W hL s0 Fw rest leafE (walkA hL s0 k)) (U + bodyC L * (n + 1) ^ 8) := by
    intro k
    exact run_bodyE (rest := rest) (Fw := Fw) hT hL s0 (walk_good hL s0 k)
      (fun h0 hi => hU _ (walk_leaf_reach hL s0 k h0 hi) _)
  have hsum : ∑ k ∈ range fuel, ind (PosLeaf W hL s0 Fw rest leafE (walkA hL s0 k)) ≤ fuel := by
    calc _ ≤ ∑ k ∈ range fuel, 1 := sum_le_sum (fun k _ => ind_le_one _)
      _ = fuel := by simp
  constructor
  · rw [eval_sumIter_nat, hfuel]
    have hcong : ∑ k ∈ range fuel, eval W (bodyE L leafE)
        (iterate W (succE L) (eval W (.lit 1) env1) env1 k :: env1) =
        ∑ k ∈ range fuel, ind (PosLeaf W hL s0 Fw rest leafE (walkA hL s0 k)) :=
      sum_congr rfl (fun k _ => by
        rw [hit k]
        exact (hbody k).1)
    rw [hcong]
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt hsum hf2)
  · have := ops_sumIter_le W fuelE (.lit 1) (succE L) (bodyE L leafE) env1
      (B := U + (succC L + bodyC L) * (n + 1) ^ 8) (by
        intro k _
        rw [hit k]
        have h1 := (hbody k).2
        have h2 : ops W (succE L) (walkA hL s0 k :: env1) ≤ succC L * (n + 1) ^ 8 :=
          (run_succE (rest := rest) (Fw := Fw) hT hL s0 (walk_good hL s0 k)).2
        have e : (succC L + bodyC L) * (n + 1) ^ 8 = succC L * (n + 1) ^ 8 + bodyC L * (n + 1) ^ 8 := by
          ring
        change ops W (bodyE L leafE) (walkA hL s0 k :: env1) + ops W (succE L) (walkA hL s0 k :: env1) ≤ _
        omega)
    rw [hfuel] at this
    have h3 : ops W (.lit 1) env1 = 1 := rfl
    omega

include hT in
/-- **The traversal.** The value of `treeE` is the number of positive leaves met by the walk, it is not zero
exactly when some leaf of `sparseTree` has a nonzero leaf value, and the cost has the stated shape. -/
theorem treeE_spec (F : ClauseSet (SignedLiteral n)) (hw : ∀ C ∈ F, C.card ≤ 3) {fuelE leafE : Expr}
    {fuel U : ℕ}
    (hfuel : eval W fuelE
      (encF n (initialSparseState F hw L hL).formula :: encF n F :: n :: rest) = fuel)
    (hf1 : 2 * (sparseTree hL (initialSparseState F hw L hL)).numLeaves ≤ fuel) (hf2 : fuel < 2 ^ W)
    (hU : ∀ t, Reach hL (initialSparseState F hw L hL) t → ∀ p,
      ops W leafE (encF n t.formula :: p :: encF n (initialSparseState F hw L hL).formula ::
        encF n F :: n :: rest) ≤ U) :
    (eval W (treeE L fuelE leafE) (encF n F :: n :: rest) ≠ 0 ↔
      ∃ p ∈ pre (sparseTree hL (initialSparseState F hw L hL)) 1,
        ¬ IntAt hL (initialSparseState F hw L hL) p ∧
        eval W leafE (leafEnv hL (initialSparseState F hw L hL) (encF n F) rest p) ≠ 0) ∧
    ops W (treeE L fuelE leafE) (encF n F :: n :: rest) ≤
      ops W fuelE (encF n (initialSparseState F hw L hL).formula :: encF n F :: n :: rest) +
        fuel * (U + treeP L n) + treeP L n := by
  set s0 := initialSparseState F hw L hL with hs0
  have hC := hT.ctx
  have hnorm := run_normE (F := F) (f := 0) (nv := 1) (env := encF n F :: n :: rest) hC rfl hw rfl
  have hroot : encF n (normalizeClauses F) = encF n s0.formula := rfl
  rw [hroot] at hnorm
  obtain ⟨hval, hops⟩ := loop_spec (rest := rest) hT hL s0 (encF n F) hfuel hf2 hU
  have hA := agrees_root hL s0
  constructor
  · have e : eval W (treeE L fuelE leafE) (encF n F :: n :: rest) =
        ∑ k ∈ range fuel, ind (PosLeaf W hL s0 (encF n F) rest leafE (walkA hL s0 k)) := by
      simp only [treeE, eval]
      rw [hnorm.1]
      exact hval
    rw [e, Ne, sum_eq_zero_iff]
    constructor
    · intro h
      push Not at h
      obtain ⟨k, _, hk⟩ := h
      have hk' := ind_ne_zero.mp hk
      rcases walk_mem (IntAt hL s0) (sparseTree hL s0) hA k with h0 | hm
      · exact absurd h0 hk'.1
      · exact ⟨_, hm, hk'.2.1, hk'.2.2⟩
    · rintro ⟨p, hp, hi, hv⟩ hall
      obtain ⟨k, hk, he⟩ := walk_visits (IntAt hL s0) (sparseTree hL s0) hA hp
      have hlen := length_pre_le (sparseTree hL s0) 1
      have hk2 : k ∈ range fuel := mem_range.mpr (by omega)
      have := hall k hk2
      apply ind_ne_zero.mpr _ this
      refine ⟨?_, ?_, ?_⟩
      · change (succWord (IntAt hL s0))^[k] 1 ≠ 0
        rw [he]
        exact (pos_of_mem_pre (by omega) hp).ne'
      · change ¬ IntAt hL s0 ((succWord (IntAt hL s0))^[k] 1)
        rw [he]
        exact hi
      · change eval W leafE (leafEnv hL s0 (encF n F) rest ((succWord (IntAt hL s0))^[k] 1)) ≠ 0
        rw [he]
        exact hv
  · have e : ops W (treeE L fuelE leafE) (encF n F :: n :: rest) =
        1 + ops W (normE 0 1) (encF n F :: n :: rest) +
          ops W (.sumIter fuelE (.lit 1) (succE L) (bodyE L leafE))
            (encF n s0.formula :: encF n F :: n :: rest) := by
      simp only [treeE, ops]
      rw [hnorm.1]
    rw [e]
    have h1 := hnorm.2
    have h7 : (n + 1) ^ 7 ≤ (n + 1) ^ 8 := pow_le_pow_m n (by norm_num)
    have m8 : 1 ≤ (n + 1) ^ 8 := Nat.one_le_pow _ _ (by omega)
    have ep : treeP L n = (succC L + bodyC L) * (n + 1) ^ 8 + 100000 * (n + 1) ^ 8 := by
      unfold treeP
      ring
    have hmul : fuel * (U + (succC L + bodyC L) * (n + 1) ^ 8 + 1) ≤ fuel * (U + treeP L n) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

include hT in
/-- **The final theorem.** With a leaf program that decides each reached leaf, `treeE` decides `F`. The fuel
is a computed value, at least twice the number of leaves of the tree. Here `L ≥ 2`, `F` has clause width at most
three, and the word size satisfies `TreeCtx`. -/
theorem treeE_correct (F : ClauseSet (SignedLiteral n)) (hw : ∀ C ∈ F, C.card ≤ 3) {fuelE leafE : Expr}
    {fuel U : ℕ}
    (hfuel : eval W fuelE
      (encF n (initialSparseState F hw L hL).formula :: encF n F :: n :: rest) = fuel)
    (hf1 : 2 * (sparseTree hL (initialSparseState F hw L hL)).numLeaves ≤ fuel) (hf2 : fuel < 2 ^ W)
    (H : ∀ t, Reach hL (initialSparseState F hw L hL) t → ∀ p,
      let env := encF n t.formula :: p :: encF n (initialSparseState F hw L hL).formula ::
        encF n F :: n :: rest
      (eval W leafE env ≠ 0 ↔ ∃ x, holdsFormula (literalHolds x) t.formula) ∧ ops W leafE env ≤ U) :
    (eval W (treeE L fuelE leafE) (encF n F :: n :: rest) ≠ 0 ↔
      ∃ x, holdsFormula (literalHolds x) F) ∧
    ops W (treeE L fuelE leafE) (encF n F :: n :: rest) ≤
      ops W fuelE (encF n (initialSparseState F hw L hL).formula :: encF n F :: n :: rest) +
        fuel * (U + treeP L n) + treeP L n := by
  set s0 := initialSparseState F hw L hL with hs0
  obtain ⟨h1, h2⟩ := treeE_spec (rest := rest) hT hL F hw hfuel hf1 hf2
    (fun t ht p => (H t ht p).2)
  refine ⟨?_, h2⟩
  rw [h1]
  have hA := agrees_root hL s0
  have hsat : (∃ x, holdsFormula (literalHolds x) F) ↔ ∃ x, holdsFormula (literalHolds x) s0.formula := by
    simp only [hs0, initialSparseState, normalizeClauses_equivalent]
  rw [hsat, sat_iff_leaf hL s0]
  constructor
  · rintro ⟨p, hp, hi, hv⟩
    have hr := reach_of_mem hL s0 s0 1 (by omega) (stateW_le_one hL s0 le_rfl) p hp hi
    exact ⟨_, hr, (H _ hr p).1.mp hv⟩
  · rintro ⟨t, ht, hx⟩
    obtain ⟨p, hp, hst, hi⟩ := mem_of_reach hL s0 ht 1 (by omega) (stateW_le_one hL s0 le_rfl)
    refine ⟨p, hp, hi, ?_⟩
    subst hst
    exact (H _ ht p).1.mpr hx

end Top

end TransposeBase.Pseudo.CnfTree
