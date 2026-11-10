import TransposeBase.Statements
import TransposeBase.Machine.FinalRun
import DominantStrings.Pseudo.Final
import FormalizationKit.ResourceTransfer

/-!
# The end-to-end theorem on the primitive machine

`machine_main`: for every `ε > 0` there is one primitive multitape machine that decides 3-SAT on the fixed encoding
`encodeCNF F` in at most `C * (ℓ + 1) ^ d * 2 ^ (ε * n)` steps, where `ℓ` is the length of the encoding and `n` is the
number of variables. On every prefix of the same run the visited space is at most `C' * (ℓ + 1) ^ d'`.

The word size is `W = wOf c ℓ = c * (ℓ + 1) ^ 4 + ℓ`. It is computed from the input length, and `pseudo_wide` allows every
word size above `c₀ * (n + 1) ^ 3`, because `n ≤ ℓ`.
-/

set_option linter.unusedSectionVars false

namespace DominantStrings.Machine

open TransposeBase.Machine
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open TransposeBase.Pseudo SatBase
open TransposeBase.Pseudo.CnfTree (Run run_let run_ite run_zero run_one)
open TransposeBase.Machine.Parse (toCNF)

/-! ### The value of the whole program -/

theorem main_value (P : Expr) {n : ℕ} (G : SAT.CNF (Fin n)) (hw : SAT.WidthAtMost 3 G) {W : ℕ}
    (hW : 3 * Parse.Qof (Encoding.encodeCNF G).length + (Encoding.encodeCNF G).length + 3 ≤ W)
    (hC2 : (2 * (Encoding.encodeCNF G).length + 2) ^ 3 ≤ W) :
    let x := BinaryArithmetic.toNat (Encoding.encodeCNF G)
    let N := (Encoding.encodeCNF G).length
    let E := CnfTree.encF n (toCNF G) :: n :: x :: N :: []
    eval W (mainE P) [x, N] = (if eval W P E = 0 then 0 else 1) ∧
      ops W (mainE P) [x, N] ≤ 60 + 213 * N + ops W P E := by
  intro x N E
  obtain ⟨a1, a2⟩ := Parse.parse_main G hw hW hC2
  have w : 1 ≤ W := by omega
  have hP : Run W P E (eval W P E) (ops W P E) := ⟨rfl, le_rfl⟩
  have t : Run W (.ite P (.lit 0) (.lit 0) (.lit 1)) E (if eval W P E = 0 then 0 else 1) (1 + ops W P E + 1 + 1) :=
    run_ite hP (run_zero w)
      (fun h => by
        rw [if_pos (by omega)]
        exact run_zero w)
      (fun h => by
        rw [if_neg (by omega)]
        exact run_one w)
  have r := run_let a1 (run_let a2 t)
  refine ⟨r.1, r.2.trans ?_⟩
  omega

/-! ### Sizes -/

theorem padOf_eq (c ℓ : ℕ) : padOf c ℓ = c * (ℓ + 1) ^ 4 := by
  simp only [padOf]
  ring

theorem w_facts {c₀ ℓ n : ℕ} (hn : n ≤ ℓ) :
    3 * Parse.Qof ℓ + ℓ + 3 ≤ wOf (c₀ + 100) ℓ ∧ (2 * ℓ + 2) ^ 3 ≤ wOf (c₀ + 100) ℓ ∧
      c₀ * (n + 1) ^ 3 ≤ wOf (c₀ + 100) ℓ ∧
      wOf (c₀ + 100) ℓ + 1 ≤ (c₀ + 101) * (ℓ + 1) ^ 4 := by
  have hA1 : 1 ≤ (ℓ + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hAl : ℓ + 1 ≤ (ℓ + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  have h3 : (ℓ + 1) ^ 3 ≤ (ℓ + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hn3 : (n + 1) ^ 3 ≤ (ℓ + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hQ : Parse.Qof ℓ ≤ 16 * (ℓ + 1) ^ 4 + 1 := by
    have h1 : 2 * ℓ + 1 ≤ 2 * (ℓ + 1) := by omega
    have h2 := Nat.mul_le_mul (Nat.mul_le_mul h1 h1) (Nat.mul_le_mul h1 h1)
    have e : 2 * (ℓ + 1) * (2 * (ℓ + 1)) * (2 * (ℓ + 1) * (2 * (ℓ + 1))) = 16 * (ℓ + 1) ^ 4 := by ring
    simp only [Parse.Qof]
    omega
  have h8 : (2 * ℓ + 2) ^ 3 = 8 * (ℓ + 1) ^ 3 := by ring
  have hw : wOf (c₀ + 100) ℓ = (c₀ + 100) * (ℓ + 1) ^ 4 + ℓ := by
    rw [wOf, padOf_eq]
  have e1 : (c₀ + 100) * (ℓ + 1) ^ 4 = c₀ * (ℓ + 1) ^ 4 + 100 * (ℓ + 1) ^ 4 := by ring
  have e2 : (c₀ + 101) * (ℓ + 1) ^ 4 = c₀ * (ℓ + 1) ^ 4 + 101 * (ℓ + 1) ^ 4 := by ring
  have hc0 : c₀ * (n + 1) ^ 3 ≤ c₀ * (ℓ + 1) ^ 4 := Nat.mul_le_mul_left _ (hn3.trans h3)
  rw [hw]
  refine ⟨by omega, by omega, by omega, by omega⟩

/-! ### The bound in real numbers -/

theorem time_real {A E K C0 O y2 L : ℝ} {b : ℕ} (hA : 1 ≤ A) (hE : 1 ≤ E) (hK : 0 ≤ K) (hC0 : 0 ≤ C0) (hy0 : 0 ≤ y2)
    (hy : y2 ≤ K * A ^ 8) (hL : L ≤ A) (hO : O ≤ C0 * A ^ b * E) :
    7 * (1000 * y2 + ((60 + 213 * L + O) * (7000 * y2) + 5)) ≤
      7 * (1000 * K + 7000 * K * (273 + C0) + 5) * A ^ (b + 9) * E := by
  have hAb : 1 ≤ A ^ b := one_le_pow₀ hA
  have hA8 : 1 ≤ A ^ 8 := one_le_pow₀ hA
  have hA0 : 0 < A := by linarith
  set R := A * (A ^ b * E) with hR
  have hbE : 1 ≤ A ^ b * E := by nlinarith
  have hR1 : A ≤ R := le_mul_of_one_le_right hA0.le hbE
  have hRb : A ^ b * E ≤ R := le_mul_of_one_le_left (by positivity) hA
  have hR0 : 1 ≤ R := hA.trans hR1
  have h1 : 60 + 213 * L + O ≤ (273 + C0) * R := by
    have : O ≤ C0 * R := by
      calc O ≤ C0 * A ^ b * E := hO
        _ = C0 * (A ^ b * E) := by ring
        _ ≤ C0 * R := mul_le_mul_of_nonneg_left hRb hC0
    nlinarith
  have h2 : (60 + 213 * L + O) * (7000 * y2) ≤ (273 + C0) * R * (7000 * (K * A ^ 8)) :=
    mul_le_mul h1 (by linarith) (by positivity) (by positivity)
  have hPR : 1 ≤ A ^ 8 * R := by nlinarith
  have h3 : y2 ≤ K * (A ^ 8 * R) := by
    refine hy.trans ?_
    have : K * A ^ 8 * 1 ≤ K * A ^ 8 * R := mul_le_mul_of_nonneg_left hR0 (by positivity)
    nlinarith
  have e : 7 * (1000 * K + 7000 * K * (273 + C0) + 5) * A ^ (b + 9) * E =
      7 * (1000 * K + 7000 * K * (273 + C0) + 5) * (A ^ 8 * R) := by
    rw [hR]
    ring
  rw [e]
  have e2 : (273 + C0) * R * (7000 * (K * A ^ 8)) = 7000 * K * (273 + C0) * (A ^ 8 * R) := by ring
  nlinarith

/-! ### The statement about one run -/

theorem decides_of_runs {machine : PrimitiveMachine} {width d C' d' : ℕ} {C ε : ℝ}
    (h : RunsWithin machine width C d ε C' d') : DecidesWithBound machine width C d ε := by
  intro n G hG
  obtain ⟨answer, time, e, ht, hs, ha, hb, -⟩ := h n G hG
  exact ⟨answer, time, ⟨e.config, ⟨time, le_rfl, locatedTrace_erase ht⟩, hs⟩, ha, hb⟩

/-- The machine, its time and its space. -/
theorem machine_runs (ε : ℝ) (hε : 0 < ε) :
    ∃ (machine : PrimitiveMachine) (C : ℝ) (d C' d' : ℕ), 0 < C ∧ 0 < d ∧ RunsWithin machine 3 C d ε C' d' := by
  obtain ⟨P, C0, b, c₀, -, hP⟩ := DominantStrings.Pseudo.Final.pseudo_wide ε hε
  set c := c₀ + 100 with hc
  set program := StructuredCalls.compiled (mainC c P) (F _ 12) (F _ 0) with hprogram
  set K : ℝ := (((c₀ + 101) ^ 2 : ℕ) : ℝ) with hK
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  refine ⟨GuardedCompiler.primitive program, 7 * (1000 * K + 7000 * K * (273 + |C0|) + 5), b + 9,
    slots (mainE P) 2 * (7100 * (c₀ + 101) ^ 2 + 16), 8, by positivity, by omega, ?_⟩
  intro n G hG
  set I := Encoding.encodeCNF G with hI
  set N := I.length with hN
  have hnN : n ≤ N := Encoding.numVariables_le_formulaBitLength G
  obtain ⟨f1, f2, f3, f4⟩ := w_facts (c₀ := c₀) (n := n) hnN
  set W := wOf c N with hW
  have hmain := main_value P G hG f1 f2
  obtain ⟨hval, hops⟩ := hmain
  set x := BinaryArithmetic.toNat I with hx
  set E := CnfTree.encF n (toCNF G) :: n :: x :: N :: [] with hE
  obtain ⟨hsat, hbound⟩ := hP n (toCNF G) (Parse.toCNF_wide hG) W [x, N] f3
  have hrun := main_run c (by omega) P I
  obtain ⟨time, htime, d, ht, hs, -, hsp⟩ :=
    FormalizationKit.ResourceTransfer.primitive_of_source program I _ _ _ N le_rfl hrun
  have hsat' : eval W P E ≠ 0 ↔ ∃ x, holdsFormula (literalHolds x) (toCNF G) := hsat
  have hbound' : (ops W P E : ℝ) ≤ C0 * ((n : ℝ) + 1) ^ b * 2 ^ (ε * n) := hbound
  have hval' : eval W (mainE P) [x, N] = if eval W P E = 0 then 0 else 1 := hval
  have hops' : ops W (mainE P) [x, N] ≤ 60 + 213 * N + ops W P E := hops
  have htime' : time ≤ 7 * (1000 * (W + 1) ^ 2 + (ops W (mainE P) [x, N] * (7000 * (W + 1) ^ 2) + 5)) := htime
  refine ⟨_, time, d, ht, hs, ?_, ?_, ?_⟩
  · -- correctness
    show decide (eval W (mainE P) [x, N] % 2 = 1) = true ↔ _
    rw [decide_eq_true_iff, Parse.sat_iff, ← hsat', hval']
    by_cases h0 : eval W P E = 0 <;> simp [h0]
  · -- time
    have hA : (1 : ℝ) ≤ (N : ℝ) + 1 := by
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      linarith
    have hE1 : (1 : ℝ) ≤ (2 : ℝ) ^ (ε * n) := Real.one_le_rpow (by norm_num) (by positivity)
    have hnat : time ≤ 7 * (1000 * (W + 1) ^ 2 + ((60 + 213 * N + ops W P E) * (7000 * (W + 1) ^ 2) + 5)) := by
      refine htime'.trans (Nat.mul_le_mul_left _ ?_)
      have := Nat.mul_le_mul_right (7000 * (W + 1) ^ 2) hops'
      omega
    have hcast : (time : ℝ) ≤ 7 * (1000 * ((W : ℝ) + 1) ^ 2 +
        ((60 + 213 * (N : ℝ) + (ops W P E : ℝ)) * (7000 * ((W : ℝ) + 1) ^ 2) + 5)) := by
      exact_mod_cast hnat
    have hy : ((W : ℝ) + 1) ^ 2 ≤ K * ((N : ℝ) + 1) ^ 8 := by
      have h1 : (W + 1) ^ 2 ≤ (c₀ + 101) ^ 2 * (N + 1) ^ 8 := by
        calc (W + 1) ^ 2 ≤ ((c₀ + 101) * (N + 1) ^ 4) ^ 2 := Nat.pow_le_pow_left f4 2
          _ = _ := by ring
      rw [hK]
      exact_mod_cast h1
    have hO : (ops W P E : ℝ) ≤ |C0| * ((N : ℝ) + 1) ^ b * (2 : ℝ) ^ (ε * n) := by
      refine hbound'.trans ?_
      have hnA : (n : ℝ) + 1 ≤ (N : ℝ) + 1 := by
        have : (n : ℝ) ≤ N := by exact_mod_cast hnN
        linarith
      have h3 : ((n : ℝ) + 1) ^ b ≤ ((N : ℝ) + 1) ^ b := pow_le_pow_left₀ (by positivity) hnA _
      have hrp : (0 : ℝ) ≤ (2 : ℝ) ^ (ε * n) := by positivity
      refine mul_le_mul_of_nonneg_right ?_ hrp
      calc C0 * ((n : ℝ) + 1) ^ b ≤ |C0| * ((n : ℝ) + 1) ^ b :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
    have := time_real (b := b) (L := (N : ℝ)) hA hE1 hK0 (abs_nonneg C0) (by positivity) hy
      (by linarith) hO
    refine hcast.trans (this.trans (le_of_eq ?_))
    simp only [runtimeBound]
    rfl
  · -- space
    intro k y hk hty
    refine (hsp k y hk hty).trans ?_
    have h1 : (W + 1) ^ 2 ≤ (c₀ + 101) ^ 2 * (N + 1) ^ 8 := by
      calc (W + 1) ^ 2 ≤ ((c₀ + 101) * (N + 1) ^ 4) ^ 2 := Nat.pow_le_pow_left f4 2
        _ = _ := by ring
    have h2 : N + 1 ≤ (N + 1) ^ 8 := Nat.le_self_pow (by norm_num) _
    have h3 : B W + N + 15 ≤ (7100 * (c₀ + 101) ^ 2 + 16) * (N + 1) ^ 8 := by
      have e : (7100 * (c₀ + 101) ^ 2 + 16) * (N + 1) ^ 8 =
          7100 * ((c₀ + 101) ^ 2 * (N + 1) ^ 8) + 16 * (N + 1) ^ 8 := by ring
      simp only [B]
      omega
    have h4 := Nat.mul_le_mul_left (slots (mainE P) 2) h3
    rw [mul_assoc]
    exact h4

/-- **The end-to-end theorem.** For every `ε > 0` there is one primitive machine that decides 3-SAT on the fixed
encoding, in time `C * (ℓ + 1) ^ d * 2 ^ (ε * n)`, with visited space `C' * (ℓ + 1) ^ d'` on every prefix of the same
run. Here `ℓ = formulaBitLength F` and `n` is the number of variables. -/
theorem machine_main (ε : ℝ) (hε : 0 < ε) :
    ∃ (machine : PrimitiveMachine) (C : ℝ) (d C' d' : ℕ), 0 < C ∧ 0 < d ∧
      DecidesWithBound machine 3 C d ε ∧ RunsWithin machine 3 C d ε C' d' := by
  obtain ⟨machine, C, d, C', d', hC, hd, h⟩ := machine_runs ε hε
  exact ⟨machine, C, d, C', d', hC, hd, decides_of_runs h, h⟩

/-- For every exponent, 3-SAT on the fixed encoding is feasible on a primitive machine. -/
theorem eth_false : ∀ ε > 0, ExponentFeasible 3 ε := by
  intro ε hε
  obtain ⟨machine, C, d, -, -, hC, hd, h, -⟩ := machine_main ε hε
  exact ⟨machine, C, d, hC, hd, h⟩

/-- The hypothesis fails. -/
theorem not_ETH : ¬ ETH := by
  rintro ⟨δ, hδ, h⟩
  exact h (eth_false δ hδ)

end DominantStrings.Machine
