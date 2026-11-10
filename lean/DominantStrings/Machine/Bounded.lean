import DominantStrings.Machine.FinalMain
import DominantStrings.Pseudo.Bounded
import DominantStrings.Statements

/-!
# The machine for formulas with few occurrences

`machine_bounded`: for every bound `D` and every `ε > 0` there is one primitive multitape machine that decides 3-SAT on the
fixed encoding `encodeCNF G`, for every input `G` in which every variable occurs in at most `D` clauses, in at most
`C * (ℓ + 1) ^ d * 2 ^ (ε * n)` steps. On every prefix of the same run the visited space is at most `C' * (ℓ + 1) ^ d'`.

The proof is `machine_runs` with `pseudo_bounded` in place of `pseudo_wide`. The translation `toCNF` does not add
occurrences (`occ_toCNF`).
-/

set_option linter.unusedSectionVars false

namespace DominantStrings.Machine

open TransposeBase.Machine
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open TransposeBase.Pseudo SatBase
open TransposeBase.Pseudo.CnfTree (Run run_let run_ite run_zero run_one)
open TransposeBase.Machine.Parse (toCNF toClause toSigned)
open Finset

/-- The translation of formulas keeps the occurrences of a variable or lowers them. -/
theorem occ_toCNF {n : ℕ} (G : SAT.CNF (Fin n)) (v : Fin n) : variableOccurrences (toCNF G) v ≤ occurrences G v := by
  classical
  have key : ∀ b : Bool, literalOccurrences (toCNF G) (v, b) ≤
      (G.filter (fun C => (⟨v, b⟩ : SAT.Literal (Fin n)) ∈ C)).card := by
    intro b
    unfold literalOccurrences toCNF
    have hsub : (G.image toClause).filter (fun C => (v, b) ∈ C) ⊆
        (G.filter (fun C => (⟨v, b⟩ : SAT.Literal (Fin n)) ∈ C)).image toClause := by
      intro C hC
      obtain ⟨hmem, hp⟩ := mem_filter.mp hC
      obtain ⟨D, hD, rfl⟩ := mem_image.mp hmem
      refine mem_image_of_mem _ (mem_filter.mpr ⟨hD, ?_⟩)
      obtain ⟨l, hl, he⟩ := mem_image.mp hp
      have : l = ⟨v, b⟩ := by
        cases l
        simp only [toSigned, Prod.mk.injEq] at he
        rw [he.1, he.2]
      rw [← this]
      exact hl
    exact (card_le_card hsub).trans card_image_le
  unfold variableOccurrences occurrences
  have h1 := key false
  have h2 := key true
  omega

/-- **The machine for formulas with few occurrences**, its time and its space. -/
theorem machine_bounded (D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (machine : PrimitiveMachine) (C : ℝ) (d C' d' : ℕ), 0 < C ∧ 0 < d ∧
      RunsWithinBounded machine 3 D C d ε C' d' := by
  obtain ⟨P, C0, b, c₀, -, hP⟩ := DominantStrings.Pseudo.Final.pseudo_bounded D ε hε
  set c := c₀ + 100 with hc
  set program := StructuredCalls.compiled (mainC c P) (F _ 12) (F _ 0) with hprogram
  set K : ℝ := (((c₀ + 101) ^ 2 : ℕ) : ℝ) with hK
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  refine ⟨GuardedCompiler.primitive program, 7 * (1000 * K + 7000 * K * (273 + |C0|) + 5), b + 9,
    slots (mainE P) 2 * (7100 * (c₀ + 101) ^ 2 + 16), 8, by positivity, by omega, ?_⟩
  intro n G hG hD
  set I := Encoding.encodeCNF G with hI
  set N := I.length with hN
  have hnN : n ≤ N := Encoding.numVariables_le_formulaBitLength G
  obtain ⟨f1, f2, f3, f4⟩ := w_facts (c₀ := c₀) (n := n) hnN
  set W := wOf c N with hW
  have hmain := main_value P G hG f1 f2
  obtain ⟨hval, hops⟩ := hmain
  set x := BinaryArithmetic.toNat I with hx
  set E := CnfTree.encF n (toCNF G) :: n :: x :: N :: [] with hE
  obtain ⟨hsat, hbound⟩ := hP n (toCNF G) (Parse.toCNF_wide hG) (fun v => (occ_toCNF G v).trans (hD v)) W [x, N] f3
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

end DominantStrings.Machine
