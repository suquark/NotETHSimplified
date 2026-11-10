import DominantStrings.Pseudo.Final

/-!
# Formulas with few occurrences of each variable

`Final.pseudo_bounded`: for every bound `D` on the occurrences of a variable and every `ε > 0` there are one program `P`
and constants `C`, `b`, `c` such that, for every 3-CNF `F` on `n` variables in which every variable occurs in at most `D`
clauses, every word size `W ≥ c * (n + 1) ^ 3` and every environment that continues below `encF n F :: n`, the value of
`P` is not zero exactly when `F` is satisfiable, and `P` costs at most `C * (n + 1) ^ b * 2 ^ (ε * n)` word operations.

The program `boundedE` has no branching tree. Up to `K ^ 2` variables it tries all assignments. Above, it runs one chain
on `F` itself: this is `leafE`, with the formula of the leaf equal to `F`.
-/

namespace DominantStrings.Pseudo.Final

open Finset SatBase TransposeBase TransposeBase.Sat TransposeBase.General TransposeBase.Pseudo
  TransposeBase.Pseudo.Final TransposeBase.Pseudo.Leaf TransposeBase.Pseudo.CnfTree

/-- The program for formulas with few occurrences: exhaustive search up to `n₀` variables, and one chain above. The three
`letE` put the environment into the form `encF n F :: p :: root :: enc :: n :: rest` that `leafE` reads. -/
def boundedE (n₀ H : ℕ) : Expr :=
  .ite (.var 1) (.lit n₀) bruteE (.letE (.lit 0) (.letE (.lit 0) (.letE (.var 2) (leafE 2 H))))

theorem eval_boundedE {W n₀ H n w : ℕ} {rest : List ℕ} (h : n₀ < 2 ^ W) :
    eval W (boundedE n₀ H) (w :: n :: rest) =
      if n ≤ n₀ then eval W bruteE (w :: n :: rest)
      else eval W (leafE 2 H) (w :: 0 :: 0 :: w :: n :: rest) := by
  have h1 : eval W (.lit n₀) (w :: n :: rest) = n₀ := eval_lit_small W h
  have h0 : ∀ e : List ℕ, eval W (.lit 0) e = 0 := fun e => eval_lit_small W (by positivity)
  show (if eval W (.var 1) (w :: n :: rest) ≤ eval W (.lit n₀) (w :: n :: rest) then _ else _) = _
  rw [h1]
  simp only [eval, h0]
  rfl

theorem ops_boundedE {W n₀ H n w : ℕ} {rest : List ℕ} (h : n₀ < 2 ^ W) :
    ops W (boundedE n₀ H) (w :: n :: rest) =
      3 + if n ≤ n₀ then ops W bruteE (w :: n :: rest)
        else 6 + ops W (leafE 2 H) (w :: 0 :: 0 :: w :: n :: rest) := by
  have h1 : eval W (.lit n₀) (w :: n :: rest) = n₀ := eval_lit_small W h
  have hv : eval W (.var 1) (w :: n :: rest) = n := rfl
  have h0 : ∀ e : List ℕ, eval W (.lit 0) e = 0 := fun e => eval_lit_small W (by positivity)
  show 1 + 1 + 1 + (if eval W (.var 1) (w :: n :: rest) ≤ eval W (.lit n₀) (w :: n :: rest) then _ else _) = _
  rw [h1, hv]
  by_cases hn : n ≤ n₀
  · rw [if_pos hn, if_pos hn]
  · rw [if_neg hn, if_neg hn]
    have e : ops W (.letE (.lit 0) (.letE (.lit 0) (.letE (.var 2) (leafE 2 H)))) (w :: n :: rest) =
        6 + ops W (leafE 2 H) (w :: 0 :: 0 :: w :: n :: rest) := by
      simp only [ops, eval, Nat.zero_mod]
      rw [show (0 :: 0 :: w :: n :: rest).getD 2 0 = w from rfl]
      omega
    rw [e]

set_option maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
/-- **The pseudocode theorem for formulas with few occurrences.** For every bound `D` and every `ε > 0` there are one
program `P` and constants `C`, `b`, `c`. For every formula `F` on `n` variables with clauses of at most three literals in
which every variable occurs in at most `D` clauses, every word size `W ≥ c * (n + 1) ^ 3`, and every environment that
continues below `encF n F :: n`, the value of `P` is not zero exactly when `F` is satisfiable, and the number of word
operations is at most `C * (n + 1) ^ b * 2 ^ (ε * n)`. -/
theorem pseudo_bounded (D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (P : Expr) (C : ℝ) (b c : ℕ), 8 ≤ c ∧ ∀ (n : ℕ) (F : ClauseSet (SignedLiteral n)) (hw : ∀ C ∈ F, C.card ≤ 3),
      (∀ v, variableOccurrences F v ≤ D) → ∀ (W : ℕ) (rest : List ℕ), c * (n + 1) ^ 3 ≤ W →
      let env := encF n F :: n :: rest
      (eval W P env ≠ 0 ↔ ∃ x, holdsFormula (literalHolds x) F) ∧
      (ops W P env : ℝ) ≤ C * ((n : ℝ) + 1) ^ b * 2 ^ (ε * n) := by
  classical
  -- the parameters
  obtain ⟨d, hd⟩ : ∃ d, d = D + 3 := ⟨_, rfl⟩
  have hd3 : 3 ≤ d := by omega
  obtain ⟨H, htrate⟩ := exists_rate (1 + d) hε
  have hrate : ∀ n : ℕ, (((∑ i ∈ range H, EbD 2 H (leafP d n) i) + Ef H (leafP d n) : ℕ) : ℝ) ≤ ε * n := fun n =>
    (exponent_le (1 + d) H n).trans (mul_le_mul_of_nonneg_right htrate (Nat.cast_nonneg _))
  obtain ⟨A, hA⟩ := core_spec 2 H
  -- the program and the constants
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = Ktow 2 H ^ 2 := ⟨_, rfl⟩
  obtain ⟨a1, ha1⟩ : ∃ a1, a1 = 48 + (2 * d + Ktow 2 H + 12) ^ 2 := ⟨_, rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ a2, a2 = (Ktow 2 H + 1) ^ 4 + chainBits 2 H + 16 * (1 + d) + 9 := ⟨_, rfl⟩
  obtain ⟨a3, ha3⟩ : ∃ a3, a3 = (2 * (1 + d) + 2) ^ 3 + 1 := ⟨_, rfl⟩
  obtain ⟨a4, ha4⟩ : ∃ a4, a4 = 2 * (1 + d) * nRectTot 2 H + 1 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = 8 + (n₀ + 1) + a1 + a2 + a3 + a4 := ⟨_, rfl⟩
  obtain ⟨C1, hC1⟩ : ∃ C1 : ℕ, C1 = (range (n₀ + 1)).sup bruteB := ⟨_, rfl⟩
  obtain ⟨C3, hC3⟩ : ∃ C3 : ℝ, C3 = 9 + (leafC (Ktow 2 H) d A : ℝ) := ⟨_, rfl⟩
  have hC30 : 0 ≤ C3 := by
    rw [hC3]
    positivity
  have hC10 : (0 : ℝ) ≤ C1 := Nat.cast_nonneg _
  refine ⟨boundedE n₀ H, (C1 : ℝ) + 3 + C3, 9, c, by omega, ?_⟩
  intro n F hw hdeg W rest hcWn
  have hsup : n ≤ n₀ → bruteB n ≤ C1 := fun hn => by
    rw [hC1]
    exact Finset.le_sup (f := bruteB) (mem_range.mpr (Nat.lt_succ_of_le hn))
  have hA3 : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hcW : ∀ x, x ≤ c → x * (n + 1) ^ 3 ≤ W := fun x hx => (Nat.mul_le_mul_right _ hx).trans hcWn
  have hcleW : c ≤ W := (Nat.le_mul_of_pos_right _ hA3).trans hcWn
  have hCtx0 : (2 * n + 2) ^ 3 ≤ W := by
    have e : (2 * n + 2) ^ 3 = 8 * (n + 1) ^ 3 := by ring
    rw [e]
    exact hcW 8 (by omega)
  have hW1 := hcW a1 (by omega)
  have hW2 := hcW a2 (by omega)
  have hW3 := hcW a3 (by omega)
  have hW4 := hcW a4 (by omega)
  rw [ha1] at hW1
  rw [ha2] at hW2
  rw [ha3] at hW3
  rw [ha4] at hW4
  dsimp only
  have hWpow : W < 2 ^ W := Nat.lt_two_pow_self
  have hCtx : Ctx W n := ⟨hCtx0⟩
  have hn₀lt : n₀ < 2 ^ W := by omega
  have hA1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := by positivity
    linarith
  have hE : (1 : ℝ) ≤ (2 : ℝ) ^ (ε * n) := Real.one_le_rpow (by norm_num) (by positivity)
  by_cases hn : n ≤ n₀
  · -- few variables: exhaustive search
    refine ⟨?_, ?_⟩
    · rw [eval_boundedE hn₀lt, if_pos hn, bruteE_eval hCtx hw rest, ind_ne_zero]
    · rw [ops_boundedE hn₀lt, if_pos hn]
      refine const_le_bound (C' := (C1 : ℝ) + 3) ?_ (by positivity) (by linarith) hA1 hE
      have : 3 + ops W bruteE (encF n F :: n :: rest) ≤ C1 + 3 := by
        have := hsup hn
        have := bruteE_ops (W := W) (n := n) hCtx (encF n F) rest
        omega
      exact_mod_cast this
  · -- many variables: one chain on `F`
    have hth : Ktow 2 H ^ 2 ≤ n := by omega
    have hdeg' : ∀ v, variableOccurrences F v ≤ d := fun v => (hdeg v).trans (by omega)
    obtain ⟨h1, h2⟩ := leaf_main hA le_rfl (G := F) hw hd3 hdeg' hth hW1 hW2 hW3 hW4 0 0 (encF n F) rest
    refine ⟨?_, ?_⟩
    · rw [eval_boundedE hn₀lt, if_neg hn]
      exact h1
    · rw [ops_boundedE hn₀lt, if_neg hn]
      have hexp : (2 : ℝ) ^ ((∑ i ∈ range H, EbD 2 H (leafP d n) i) + Ef H (leafP d n)) ≤ (2 : ℝ) ^ (ε * n) := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (hrate n)
      have h3 : ((3 + (6 + ops W (leafE 2 H) (encF n F :: 0 :: 0 :: encF n F :: n :: rest)) : ℕ) : ℝ) ≤
          9 + (leafC (Ktow 2 H) d A : ℝ) * ((n : ℝ) + 1) ^ 9 *
            (2 : ℝ) ^ ((∑ i ∈ range H, EbD 2 H (leafP d n) i) + Ef H (leafP d n)) := by
        have : 3 + (6 + ops W (leafE 2 H) (encF n F :: 0 :: 0 :: encF n F :: n :: rest)) ≤
            9 + leafC (Ktow 2 H) d A * (n + 1) ^ 9 *
              2 ^ ((∑ i ∈ range H, EbD 2 H (leafP d n) i) + Ef H (leafP d n)) := by omega
        exact_mod_cast this
      refine h3.trans ?_
      have hL0 : (0 : ℝ) ≤ (leafC (Ktow 2 H) d A : ℝ) := Nat.cast_nonneg _
      have hP1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 9 := one_le_pow₀ hA1
      have hX : (leafC (Ktow 2 H) d A : ℝ) * ((n : ℝ) + 1) ^ 9 *
          (2 : ℝ) ^ ((∑ i ∈ range H, EbD 2 H (leafP d n) i) + Ef H (leafP d n)) ≤
          (leafC (Ktow 2 H) d A : ℝ) * ((n : ℝ) + 1) ^ 9 * (2 : ℝ) ^ (ε * n) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      have hPE : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 9 * (2 : ℝ) ^ (ε * n) := one_le_mul_of_one_le_of_one_le hP1 hE
      have e : ((C1 : ℝ) + 3 + C3) * ((n : ℝ) + 1) ^ 9 * (2 : ℝ) ^ (ε * n) =
          ((C1 : ℝ) + 3 + 9) * (((n : ℝ) + 1) ^ 9 * (2 : ℝ) ^ (ε * n)) +
            (leafC (Ktow 2 H) d A : ℝ) * ((n : ℝ) + 1) ^ 9 * (2 : ℝ) ^ (ε * n) := by
        rw [hC3]
        ring
      rw [e]
      generalize ((n : ℝ) + 1) ^ 9 * (2 : ℝ) ^ (ε * n) = PE at hPE ⊢
      have h9 : (9 : ℝ) ≤ ((C1 : ℝ) + 3 + 9) * PE := by nlinarith
      linarith

end DominantStrings.Pseudo.Final
