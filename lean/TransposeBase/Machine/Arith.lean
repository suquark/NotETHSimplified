import FormalizationKit.MachineArithmetic
import FormalizationKit.MachineSignedComparison
import FormalizationKit.MachineWordNegation
import TransposeBase.Machine.Ev

/-!
# Word routines on fixed work stacks

The stacks `0` to `7` are work stacks of the routines, `8` is the scratch stack of `copyC`, stack `9` holds
the modulus `2 ^ W`, and stack `10` holds the ruler: `W` zero bits, which is also the word of `0`. The operands
of a routine are on the stacks `0` and `1`, and its result is on the stack `0`.

The routines are complete calls of the library programs, with the program's stacks at fixed numbers.
This file: addition, multiplication, subtraction and comparison.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace TransposeBase.Machine

open OAI.Algorithms.SubexponentialSAT
open BitProgram StructuredCalls ModularRingPrograms ModularDivisionPrograms
open FormalizationKit

variable {S : ℕ} [NeZero S]

/-- The memory between routines: empty work stacks, the modulus and the ruler. -/
structure Clean (W : ℕ) (m : Mem) : Prop where
  w0 : m 0 = []
  w1 : m 1 = []
  w2 : m 2 = []
  w3 : m 3 = []
  w4 : m 4 = []
  w5 : m 5 = []
  w6 : m 6 = []
  w7 : m 7 = []
  w8 : m 8 = []
  modulus : m 9 = wordOf (W + 1) (2 ^ W)
  ruler : m 10 = List.replicate W false

/-- The modulus word has the value `2 ^ W`. -/
theorem toNat_modulus (W : ℕ) : BinaryArithmetic.toNat (wordOf (W + 1) (2 ^ W)) = 2 ^ W :=
  toNat_wordOf (by rw [pow_succ]; have : 0 < 2 ^ W := by positivity
                   omega)

/-- Stack numbers of an identity placement. -/
def idPorts (s : ℕ) : Fin s → ℕ := fun j => j.val

theorem idPorts_injective (s : ℕ) : Function.Injective (idPorts s) := fun _ _ h => Fin.ext h

/-- Equality of explicit memories. -/
macro "mem_eq" : tactic =>
  `(tactic| (funext i; simp only [Function.update_apply]; split_ifs <;> simp_all))

/-! ### Addition and multiplication -/

/-- A modular routine: place a copy of the modulus, call the program, remove the copy. -/
def modCore (S : ℕ) [NeZero S] {l : ℕ} (P : Program 8 8 l) : Cmd 10 S :=
  .seq (copyC S 9 5) (.seq (liftC S (by norm_num) P (idPorts 8)) (clearC S 5))

theorem ev_modCore {W v l : ℕ} (P : Program 8 8 l) (hS : 11 ≤ S) {m : Mem} (hc : Clean W m)
    {xs ys : List Bool}
    (hP : ∀ regs, ∃ finalRegs output,
      RunsIn P (6000 * (W + 1) ^ 2)
        ⟨some P.entry, regs, extendSeven (scalarInput xs ys (wordOf (W + 1) (2 ^ W))) []⟩
        ⟨none, finalRegs, extendSeven (resting output (wordOf (W + 1) (2 ^ W)) []) []⟩ ∧
      output.length = W ∧ BinaryArithmetic.toNat output = v) :
    Ev (modCore S P) (Function.update (Function.update m 0 xs) 1 ys) (Function.update m 0 (wordOf W v))
      (6000 * (W + 1) ^ 2 + 9 * (W + 1) + 8) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hmod, hrul⟩ := hc
  set M₀ := Function.update (Function.update m 0 xs) 1 ys with hM₀
  set mw := wordOf (W + 1) (2 ^ W) with hmw
  have e₁ : Ev (copyC S 9 5) M₀ (Function.update M₀ 5 mw) (7 * (W + 1) + 5) :=
    ev_copy' (by omega) (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
      (by simp [hM₀, Function.update_apply, h8]) (by simp [hM₀, Function.update_apply, hmod, hmw])
      (by simp [hM₀, Function.update_apply, h5]) (by simp [hmw])
  have e₂ : Ev (liftC S (by norm_num) P (idPorts 8)) (Function.update M₀ 5 mw)
      (Function.update (Function.update m 0 (wordOf W v)) 5 mw) (6000 * (W + 1) ^ 2) := by
    refine (ev_lift (Q := fun _ => True) (by norm_num) P (idPorts 8) (idPorts_injective 8)
      (fun j => by have := j.2; simp only [idPorts]; omega) ?_ fun regs => ?_).weaken
    · intro i hi
      have hi8 : 8 ≤ i := by
        by_contra hlt
        exact hi ⟨i, by omega⟩ rfl
      have n0 : i ≠ 0 := by omega
      have n1 : i ≠ 1 := by omega
      have n5 : i ≠ 5 := by omega
      simp [hM₀, Function.update_apply, n0, n1, n5]
    · obtain ⟨rf, out, ⟨n, hn, ht⟩, hl, hv⟩ := hP regs
      have hout : out = wordOf W v := eq_wordOf hl hv
      subst hout
      refine ⟨rf, n, hn, ?_, trivial⟩
      have hs : (fun j : Fin 8 => Function.update M₀ 5 mw (idPorts 8 j)) =
          extendSeven (scalarInput xs ys mw) [] := by
        funext j
        fin_cases j <;> simp [idPorts, hM₀, extendSeven, scalarInput, seven, Function.update_apply, *]
      have hf : (fun j : Fin 8 => Function.update (Function.update m 0 (wordOf W v)) 5 mw (idPorts 8 j)) =
          extendSeven (resting (wordOf W v) mw []) [] := by
        funext j
        fin_cases j <;> simp [idPorts, extendSeven, resting, seven, Function.update_apply, *]
      rw [hs, hf]
      exact ht
  have e₃ : Ev (clearC S 5) (Function.update (Function.update m 0 (wordOf W v)) 5 mw)
      (Function.update (Function.update (Function.update m 0 (wordOf W v)) 5 mw) 5 []) (2 * (W + 1) + 3) :=
    ev_clear' (by omega) _ (by simp [hmw])
  have e := EvQ.seq e₁ (EvQ.seq e₂ e₃)
  refine (ev_eq e ?_).mono (by omega)
  mem_eq

/-- The hypotheses of the library routines for the modulus `2 ^ W`. -/
theorem modulus_facts (W : ℕ) :
    (wordOf (W + 1) (2 ^ W)).length ≤ W + 1 ∧ 0 < BinaryArithmetic.toNat (wordOf (W + 1) (2 ^ W)) ∧
      BinaryArithmetic.toNat (wordOf (W + 1) (2 ^ W)) ≤ 2 ^ W := by
  rw [toNat_modulus]
  exact ⟨by simp, by positivity, le_rfl⟩

/-- Addition modulo `2 ^ W`. -/
abbrev addCore (S : ℕ) [NeZero S] : Cmd 10 S := modCore S wordAddProgram

/-- Multiplication modulo `2 ^ W`. -/
abbrev mulCore (S : ℕ) [NeZero S] : Cmd 10 S := modCore S wordMulProgram

theorem ev_add {W a b : ℕ} (hS : 11 ≤ S) {m : Mem} (hc : Clean W m) (ha : a < 2 ^ W) (hb : b < 2 ^ W) :
    Ev (addCore S) (Function.update (Function.update m 0 (wordOf W a)) 1 (wordOf W b))
      (Function.update m 0 (wordOf W ((a + b) % 2 ^ W))) (6000 * (W + 1) ^ 2 + 9 * (W + 1) + 8) := by
  refine ev_modCore _ hS hc fun regs => ?_
  obtain ⟨hl, hp, hcap⟩ := modulus_facts W
  obtain ⟨rf, out, h, hlen, hv⟩ := wordAdd_value regs (wordOf W a) (wordOf W b) _ W (by simp) (by simp) hl hp hcap
  refine ⟨rf, out, h, hlen, ?_⟩
  rw [hv, toNat_wordOf ha, toNat_wordOf hb, toNat_modulus]

theorem ev_mul {W a b : ℕ} (hS : 11 ≤ S) {m : Mem} (hc : Clean W m) (ha : a < 2 ^ W) (hb : b < 2 ^ W) :
    Ev (mulCore S) (Function.update (Function.update m 0 (wordOf W a)) 1 (wordOf W b))
      (Function.update m 0 (wordOf W ((a * b) % 2 ^ W))) (6000 * (W + 1) ^ 2 + 9 * (W + 1) + 8) := by
  refine ev_modCore _ hS hc fun regs => ?_
  obtain ⟨hl, hp, hcap⟩ := modulus_facts W
  obtain ⟨rf, out, h, hlen, hv⟩ := wordMul_value regs (wordOf W a) (wordOf W b) _ W (by simp) (by simp) hl hp hcap
  refine ⟨rf, out, h, hlen, ?_⟩
  rw [hv, toNat_wordOf ha, toNat_wordOf hb, toNat_modulus]

/-! ### Subtraction -/

open MachineWordNegation in
/-- Replace the word on the stack `1` by its negation modulo `2 ^ W`. -/
def negC (S : ℕ) [NeZero S] : Cmd 10 S :=
  .seq (.base (.atom (.set 0 false))) (liftC S (by norm_num) negateProgram ![1, 2, 3])

open MachineWordNegation in
theorem negate_value {W b : ℕ} (hb : b < 2 ^ W) :
    (wordNegate false (wordOf W b)).1 = wordOf W ((2 ^ W - b) % 2 ^ W) := by
  have hv := wordNegate_value (wordOf W b)
  rw [toNat_wordOf hb, length_wordOf] at hv
  have hlen : (wordNegate false (wordOf W b)).1.length = W := by rw [wordNegate_length]; simp
  have hlt := toNat_lt (wordNegate false (wordOf W b)).1
  rw [hlen] at hlt
  apply eq_wordOf hlen
  generalize BinaryArithmetic.toNat (wordNegate false (wordOf W b)).1 = x at *
  have hpos : 0 < 2 ^ W := by positivity
  cases hbit : (wordNegate false (wordOf W b)).2
  · rw [hbit] at hv
    simp only [BinaryArithmetic.bitVal_false, Nat.mul_zero] at hv
    have hb0 : b = 0 := by omega
    have hx0 : x = 0 := by omega
    subst hb0 hx0
    simp
  · rw [hbit] at hv
    simp only [BinaryArithmetic.bitVal_true, Nat.mul_one] at hv
    have hbpos : 0 < b := by omega
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

open MachineWordNegation in
theorem ev_neg {W b : ℕ} (hS : 11 ≤ S) {M : Mem} (hb : b < 2 ^ W) (hM1 : M 1 = wordOf W b)
    (h2 : M 2 = []) (h3 : M 3 = []) :
    Ev (negC S) M (Function.update M 1 (wordOf W ((2 ^ W - b) % 2 ^ W))) (8 * W + 7) := by
  intro regs
  set M' := Function.update M 1 (wordOf W ((2 ^ W - b) % 2 ^ W)) with hM'
  have e₁ := Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 10) false) (⟨regs, view S M⟩ : State 10 S))
  have hreg : (StructuredProgram.Atom.set (0 : Fin 10) false).eval (⟨regs, view S M⟩ : State 10 S) =
      ⟨Function.update regs 0 false, view S M⟩ := rfl
  rw [hreg] at e₁
  obtain ⟨n, rf, e₂, hn, _⟩ := ev_lift_at (S := S) (r := 8) (by norm_num) negateProgram ![1, 2, 3]
    (m := M) (m' := M') (t := 8 * W + 6) (Q := fun _ => True) (by decide)
    (fun j => by fin_cases j <;> simp <;> omega)
    (fun i hi => by
      have n1 : i ≠ 1 := fun e => hi 0 (by simp [e])
      simp [hM', Function.update_apply, n1])
    (Function.update regs 0 false) (by
      obtain ⟨rf, ht⟩ := negate_trace (Function.update regs 0 false ∘ Fin.castLE (by norm_num))
        (wordOf W b)
      have hz : (Function.update regs 0 false ∘ Fin.castLE (by norm_num : 8 ≤ 10)) (0 : Fin 8) = false := by
        simp only [Function.comp]
        exact Function.update_self ..
      rw [hz, negate_value hb, length_wordOf] at ht
      refine ⟨rf, _, le_rfl, ?_, trivial⟩
      have hs : (fun j : Fin 3 => M ((![1, 2, 3] : Fin 3 → ℕ) j)) =
          BinaryPrograms.Add.stackState (wordOf W b) [] [] := by
        funext j
        fin_cases j <;> simp [BinaryPrograms.Add.stackState, *]
      have hf : (fun j : Fin 3 => M' ((![1, 2, 3] : Fin 3 → ℕ) j)) =
          BinaryPrograms.Add.stackState (wordOf W ((2 ^ W - b) % 2 ^ W)) [] [] := by
        funext j
        fin_cases j <;> simp [BinaryPrograms.Add.stackState, hM', Function.update_apply, *]
      rw [hs, hf]
      exact ht)
  exact ⟨_, rf, e₁.seq e₂, by omega, trivial⟩

/-- Subtraction: negate the second operand, then add. -/
def subCore (S : ℕ) [NeZero S] : Cmd 10 S := .seq (negC S) (addCore S)

theorem ev_sub {W a b : ℕ} (hS : 11 ≤ S) {m : Mem} (hc : Clean W m) (ha : a < 2 ^ W) (hb : b < 2 ^ W) :
    Ev (subCore S) (Function.update (Function.update m 0 (wordOf W a)) 1 (wordOf W b))
      (Function.update m 0 (wordOf W ((a + (2 ^ W - b % 2 ^ W)) % 2 ^ W)))
      (6000 * (W + 1) ^ 2 + 18 * (W + 1) + 8) := by
  have hneg := ev_neg (S := S) (W := W) (b := b) hS
    (M := Function.update (Function.update m 0 (wordOf W a)) 1 (wordOf W b)) hb
    (by simp) (by simp [Function.update_apply, hc.w2]) (by simp [Function.update_apply, hc.w3])
  rw [Function.update_idem] at hneg
  have hlt : (2 ^ W - b) % 2 ^ W < 2 ^ W := Nat.mod_lt _ (by positivity)
  have hadd := ev_add (S := S) hS hc ha hlt
  have hval : (a + (2 ^ W - b) % 2 ^ W) % 2 ^ W = (a + (2 ^ W - b % 2 ^ W)) % 2 ^ W := by
    rw [Nat.mod_eq_of_lt hb]
    rcases Nat.eq_zero_or_pos b with rfl | hpos
    · simp
    · rw [Nat.mod_eq_of_lt (by omega : 2 ^ W - b < 2 ^ W)]
  rw [hval] at hadd
  exact (EvQ.seq hneg hadd).mono (by omega)

/-! ### Comparison -/

open MachineSignedComparison in
/-- Compare the words on the stacks `0` and `1` and leave `a < b` in the register `0`. All work stacks are
empty afterwards. -/
def ltCore (S : ℕ) [NeZero S] : Cmd 10 S :=
  .seq (pushB S 3 false) (.seq (pushB S 4 false)
    (.seq (liftC S (le_refl 10) comparisonProgram (idPorts 5)) (popC S 0)))

open MachineSignedComparison in
theorem ev_lt {W a b : ℕ} (hS : 11 ≤ S) {m : Mem} (hc : Clean W m) (ha : a < 2 ^ W) (hb : b < 2 ^ W) :
    EvQ (ltCore S) (Function.update (Function.update m 0 (wordOf W a)) 1 (wordOf W b)) m
      (32 * W + 53) fun rf => rf 0 = decide (a < b) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hmod, hrul⟩ := hc
  set M₀ := Function.update (Function.update m 0 (wordOf W a)) 1 (wordOf W b) with hM₀
  have e₁ := ev_pushB (S := S) (s := 3) (by omega) false M₀
  have e₂ := ev_pushB (S := S) (s := 4) (by omega) false (Function.update M₀ 3 (false :: M₀ 3))
  set M₂ := Function.update (Function.update M₀ 3 (false :: M₀ 3)) 4
    (false :: Function.update M₀ 3 (false :: M₀ 3) 4) with hM₂
  set ans := decide (a < b) with hans
  have e₃ : Ev (liftC S (le_refl 10) comparisonProgram (idPorts 5)) M₂ (Function.update m 0 [ans])
      (32 * W + 48) := by
    refine (ev_lift (Q := fun _ => True) (le_refl 10) comparisonProgram (idPorts 5) (idPorts_injective 5)
      (fun j => by have := j.2; simp only [idPorts]; omega) ?_ fun regs => ?_).weaken
    · intro i hi
      have hi5 : 5 ≤ i := by
        by_contra hlt
        exact hi ⟨i, by omega⟩ rfl
      have n0 : i ≠ 0 := by omega
      have n1 : i ≠ 1 := by omega
      have n3 : i ≠ 3 := by omega
      have n4 : i ≠ 4 := by omega
      simp [hM₂, hM₀, Function.update_apply, n0, n1, n3, n4]
    · obtain ⟨rf, ht, _, _⟩ := word_comparison_resources regs (wordOf W a) (wordOf W b) false false (by simp)
      rw [length_wordOf] at ht
      refine ⟨rf, _, le_rfl, ?_, trivial⟩
      have hs : (fun j : Fin 5 => M₂ (idPorts 5 j)) =
          comparisonStacks (wordOf W a) (wordOf W b) [] [false] [false] := by
        funext j
        fin_cases j <;> simp [idPorts, hM₂, hM₀, comparisonStacks, Function.update_apply, *]
      have hf : (fun j : Fin 5 => Function.update m 0 [ans] (idPorts 5 j)) =
          comparisonStacks [ans] [] [] [] [] := by
        funext j
        fin_cases j <;> simp [idPorts, comparisonStacks, Function.update_apply, *]
      rw [hs, hf]
      have hv : decide (MachineSignedDivision.signedValue false (BinaryArithmetic.toNat (wordOf W a)) <
          MachineSignedDivision.signedValue false (BinaryArithmetic.toNat (wordOf W b))) = ans := by
        rw [toNat_wordOf ha, toNat_wordOf hb, hans]
        simp [MachineSignedDivision.signedValue]
      rw [hv] at ht
      exact ht
  have e₄ := ev_pop (S := S) (s := 0) (by omega) (Function.update m 0 [ans])
  have hlast : Function.update (Function.update m 0 [ans]) 0 (Function.update m 0 [ans] 0).tail = m := by
    mem_eq
  rw [hlast] at e₄
  have e₄' : EvQ (popC S 0) (Function.update m 0 [ans]) m 1 fun rf => rf 0 = ans :=
    e₄.mapQ fun r hr => by simpa using hr.1
  exact (EvQ.seq e₁ (EvQ.seq e₂ (EvQ.seq e₃ e₄'))).mono (by omega)

end TransposeBase.Machine
