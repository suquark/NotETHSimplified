import OnePigeonhole.Pseudo.FinalHelpers
import FormalizationKit.ResourceTransfer
import TransposeBase.Machine.FinalRun

/-! Arithmetic used to pass from the word program to the machine. -/

section

set_option linter.unusedSectionVars false

namespace OnePigeonhole.Machine

open TransposeBase.Machine
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open TransposeBase.Pseudo SatBase
open TransposeBase.Pseudo.CnfTree (Run run_let run_ite run_zero run_one)
open TransposeBase.Machine.Parse (toCNF)

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

end OnePigeonhole.Machine

end
