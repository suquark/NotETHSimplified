import TransposeBase.Statements
import OnePigeonhole.Machine.Helpers
import OnePigeonhole.Pseudo.Final

/-!
# The end-to-end theorem on the primitive machine

`machine_main`: for every `ε > 0` there is one primitive multitape machine that decides 3-SAT on the fixed encoding `encodeCNF F` in at most
`C * (ℓ + 1) ^ d * 2 ^ (ε * n)` steps, where `ℓ` is the length of the encoding and `n` is the number of variables. On every prefix of the same run the
visited space is at most `C' * (ℓ + 1) ^ d'`.

The word size is `W = wOf c ℓ = c * (ℓ + 1) ^ 4 + ℓ`. It is computed from the input length, and `pseudo_wide` allows every word size above
`c₀ * (n + 1) ^ 3`, because `n ≤ ℓ`. The compiler of `TransposeBase.Machine` runs any `Expr`, so this file needs only the program of `pseudo_wide`.
-/

set_option linter.unusedSectionVars false

namespace OnePigeonhole.Machine

open TransposeBase.Machine
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open TransposeBase.Pseudo SatBase
open TransposeBase.Machine.Parse (toCNF)

/-! ### The statement about one run -/

theorem decides_of_runs {machine : PrimitiveMachine} {width d C' d' : ℕ} {C ε : ℝ}
    (h : RunsWithin machine width C d ε C' d') : DecidesWithBound machine width C d ε := by
  intro n G hG
  obtain ⟨answer, time, e, ht, hs, ha, hb, -⟩ := h n G hG
  exact ⟨answer, time, ⟨e.config, ⟨time, le_rfl, locatedTrace_erase ht⟩, hs⟩, ha, hb⟩

/-- The machine, its time and its space. -/
theorem machine_runs (ε : ℝ) (hε : 0 < ε) :
    ∃ (machine : PrimitiveMachine) (C : ℝ) (d C' d' : ℕ), 0 < C ∧ 0 < d ∧ RunsWithin machine 3 C d ε C' d' := by
  obtain ⟨P, C0, b, c₀, -, hP⟩ := OnePigeonhole.Pseudo.Final.pseudo_wide ε hε
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

/-- **The end-to-end theorem.** For every `ε > 0` there is one primitive machine that decides 3-SAT on the fixed encoding, in time
`C * (ℓ + 1) ^ d * 2 ^ (ε * n)`, with visited space `C' * (ℓ + 1) ^ d'` on every prefix of the same run. Here `ℓ = formulaBitLength F` and `n` is the number of
variables. -/
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

end OnePigeonhole.Machine
