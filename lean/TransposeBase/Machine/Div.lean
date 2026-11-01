import TransposeBase.Machine.Arith

/-!
# Division and remainder

A zero test on the divisor selects the branch. A positive divisor goes to the library's binary long division.
The quotient has length `W`. The remainder has length `2 * W`, and the ruler cuts it back to `W` bits.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace TransposeBase.Machine

open OAI.Algorithms.SubexponentialSAT
open BitProgram StructuredCalls CounterPrograms CounterForPrograms
open ModularQuotientPrograms ModularQuotientArithmetic ModularRingPrograms
open FormalizationKit

variable {S : ℕ} [NeZero S]

/-! ### Counter programs on two stacks -/

/-- Test the stack `s` for zero; the stack `scr` is its scratch stack. The answer is in the register `2`. -/
def zeroC (S : ℕ) [NeZero S] (s scr : ℕ) : Cmd 10 S := liftC S (by norm_num) zeroProgram ![s, scr]

/-- Increment (`c = true`) or decrement (`c = false`) the stack `s`. -/
def rippleC (S : ℕ) [NeZero S] (c : Bool) (s scr : ℕ) : Cmd 10 S :=
  liftC S (by norm_num) (rippleProgram c) ![s, scr]

private theorem local_regs (r : Fin 3 → Bool) : counterRegs (r 0) (r 1) (r 2) = r := by
  funext i
  fin_cases i <;> rfl

private theorem two_injective {s scr : ℕ} (hne : s ≠ scr) : Function.Injective (![s, scr] : Fin 2 → ℕ) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [Ne.symm hne]

private theorem two_lt {s scr : ℕ} (hs : s < S) (hscr : scr < S) (j : Fin 2) :
    (![s, scr] : Fin 2 → ℕ) j < S := by
  fin_cases j <;> simpa

private theorem two_stacks {m : Mem} {s scr : ℕ} {xs : List Bool} (hx : m s = xs) (hy : m scr = []) :
    (fun j : Fin 2 => m ((![s, scr] : Fin 2 → ℕ) j)) = counterStacks xs [] := by
  funext j
  fin_cases j <;> simp [counterStacks, hx, hy]

theorem ev_zero {s scr L : ℕ} (hs : s < S) (hscr : scr < S) (hne : s ≠ scr) {m : Mem} (hm : m scr = [])
    (hL : (m s).length ≤ L) :
    EvQ (zeroC S s scr) m m (8 * L + 6) fun rf => rf 2 = isZero (m s) := by
  refine (ev_lift (Q := fun r => r 2 = isZero (m s)) (by norm_num) zeroProgram ![s, scr] (two_injective hne)
    (two_lt hs hscr) (fun _ _ => rfl) fun r => ?_).mapQ fun rf h => h
  have ht := zero_local_trace (r 0) (r 1) (r 2) (m s)
  refine ⟨counterRegs false false (isZero (m s)), 8 * (m s).length + 6, by omega, ?_, rfl⟩
  rw [two_stacks rfl hm]
  simpa [localData, local_regs, StructuredProgram.State.withPC] using ht

theorem ev_ripple {c : Bool} {s scr L : ℕ} (hs : s < S) (hscr : scr < S) (hne : s ≠ scr) {m : Mem}
    (hm : m scr = []) (hL : (m s).length ≤ L) :
    Ev (rippleC S c s scr) m (Function.update m s (ripple c (m s))) (8 * L + 8) := by
  refine (ev_lift (Q := fun _ => True) (by norm_num) (rippleProgram c) ![s, scr] (two_injective hne)
    (two_lt hs hscr) (fun i hi => ?_) fun r => ?_).weaken
  · have n : i ≠ s := fun e => hi 0 (by simp [e])
    simp [Function.update_apply, n]
  · have ht := ripple_local_trace c (r 0) (r 1) (r 2) (m s)
    refine ⟨counterRegs false false (r 2), rippleCost c (m s) + 1, ?_, ?_, trivial⟩
    · have := rippleCost_le c (m s)
      omega
    · rw [two_stacks rfl hm, two_stacks (xs := ripple c (m s)) (by simp)
        (by simpa [Function.update_apply, hne.symm] using hm)]
      simpa [localData, local_regs, StructuredProgram.State.withPC] using ht

theorem isZero_wordOf {W b : ℕ} (hb : b < 2 ^ W) : isZero (wordOf W b) = decide (b = 0) := by
  apply Bool.eq_iff_iff.mpr
  rw [isZero_eq_true_iff, value_eq_toNat, toNat_wordOf hb]
  simp

/-! ### Long division -/

/-- The places of the long division's stacks: the dividend is on the stack `0`, the divisor on the
stack `1`, and afterwards the remainder is on the stack `6` and the quotient on the stack `7`. -/
def qPorts : Fin 8 → ℕ := ![6, 2, 3, 4, 5, 1, 0, 7]

theorem qPorts_injective : Function.Injective qPorts := by decide

def quotC (S : ℕ) [NeZero S] : Cmd 10 S := liftC S (by norm_num) quotientProgram qPorts

/-- The remainder word of the long division. -/
def remOf (W a b : ℕ) : List Bool := (divide (wordOf W b) (wordOf W a)).2

theorem remOf_length (W a b : ℕ) : (remOf W a b).length = W + W := by
  rw [remOf, divide_remainder_length]
  simp

theorem remOf_value {W a b : ℕ} (ha : a < 2 ^ W) (hb : b < 2 ^ W) (hpos : 0 < b) :
    BinaryArithmetic.toNat (remOf W a b) = a % b := by
  have h := divide_remainder_correct (wordOf W b) (wordOf W a) (by rwa [toNat_wordOf hb])
  rwa [toNat_wordOf hb, toNat_wordOf ha] at h

theorem quot_word {W a b : ℕ} (ha : a < 2 ^ W) (hb : b < 2 ^ W) (hpos : 0 < b) :
    (divide (wordOf W b) (wordOf W a)).1 = wordOf W (a / b) := by
  apply eq_wordOf
  · simp [divide_quotient_length]
  · have h := divide_quotient_correct (wordOf W b) (wordOf W a) (by rwa [toNat_wordOf hb])
    rwa [toNat_wordOf hb, toNat_wordOf ha] at h

theorem ev_quot {W a b : ℕ} (hS : 11 ≤ S) {m : Mem} (hc : Clean W m) (ha : a < 2 ^ W) (hb : b < 2 ^ W)
    (hpos : 0 < b) :
    Ev (quotC S) (Function.update (Function.update m 0 (wordOf W a)) 1 (wordOf W b))
      (Function.update (Function.update (Function.update m 1 (wordOf W b)) 6 (remOf W a b)) 7
        (wordOf W (a / b))) (400 * (W + 1) ^ 2) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hmod, hrul⟩ := hc
  refine (ev_lift (Q := fun _ => True) (by norm_num) quotientProgram qPorts qPorts_injective
    (fun j => by fin_cases j <;> simp [qPorts] <;> omega) (fun i hi => ?_) fun r => ?_).weaken
  · have n0 : i ≠ 0 := fun e => hi 6 (by simp [e, qPorts])
    have n1 : i ≠ 1 := fun e => hi 5 (by simp [e, qPorts])
    have n6 : i ≠ 6 := fun e => hi 0 (by simp [e, qPorts])
    have n7 : i ≠ 7 := fun e => hi 7 (by simp [e, qPorts])
    simp [Function.update_apply, n0, n1, n6, n7]
  · obtain ⟨rf, n, hn, ht⟩ := quotient_correct r (wordOf W b) (wordOf W a)
    refine ⟨rf, n, ?_, ?_, trivial⟩
    · refine hn.trans ?_
      simp only [length_wordOf]
      have h2w := Nat.pow_le_pow_left (by omega : W + W + 1 ≤ 2 * (W + 1)) 2
      nlinarith
    · have hs : (fun j : Fin 8 => Function.update (Function.update m 0 (wordOf W a)) 1 (wordOf W b) (qPorts j)) =
          quotientStacks [] (wordOf W b) (wordOf W a) [] := by
        funext j
        fin_cases j <;> simp [qPorts, Function.update_apply, *]
      have hf : (fun j : Fin 8 => Function.update (Function.update (Function.update m 1 (wordOf W b)) 6
          (remOf W a b)) 7 (wordOf W (a / b)) (qPorts j)) =
          quotientStacks (divide (wordOf W b) (wordOf W a)).2 (wordOf W b) []
            (divide (wordOf W b) (wordOf W a)).1 := by
        rw [quot_word ha hb hpos]
        funext j
        fin_cases j <;> simp [qPorts, remOf, Function.update_apply, *]
      rw [hs, hf]
      exact ht

/-- `a / b`, with `a / 0 = 0`: the word of zero is a copy of the ruler. -/
def divCore (S : ℕ) [NeZero S] : Cmd 10 S :=
  .seq (zeroC S 1 2) (.ite 2
    (.seq (clearC S 1) (.seq (clearC S 0) (copyC S 10 0)))
    (.seq (quotC S) (.seq (clearC S 6) (.seq (clearC S 1) (mvC S 7 0)))))

theorem ev_div {W a b : ℕ} (hS : 11 ≤ S) {m : Mem} (hc : Clean W m) (ha : a < 2 ^ W) (hb : b < 2 ^ W) :
    Ev (divCore S) (Function.update (Function.update m 0 (wordOf W a)) 1 (wordOf W b))
      (Function.update m 0 (wordOf W (a / b))) (400 * (W + 1) ^ 2 + 40 * (W + 1) + 30) := by
  have hc' := hc
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hmod, hrul⟩ := hc
  set M := Function.update (Function.update m 0 (wordOf W a)) 1 (wordOf W b) with hM
  have ez := ev_zero (S := S) (s := 1) (scr := 2) (L := W + 1) (by omega) (by omega) (by norm_num)
    (m := M) (by simp [hM, Function.update_apply, *]) (by simp [hM, Function.update_apply, *])
  have hM1 : M 1 = wordOf W b := by simp [hM]
  rw [hM1, isZero_wordOf hb] at ez
  refine (EvQ.ite (t₂ := 400 * (W + 1) ^ 2 + 30 * (W + 1) + 20) ez (fun hv => ?_) (fun hv => ?_)).mono
    (by omega)
  · have hb0 : b = 0 := by simpa using hv
    subst hb0
    have e₁ : Ev (clearC S 1) M (Function.update M 1 []) (2 * (W + 1) + 3) :=
      ev_clear' (by omega) _ (by simp [hM])
    have e₂ : Ev (clearC S 0) (Function.update M 1 []) (Function.update (Function.update M 1 []) 0 [])
        (2 * (W + 1) + 3) := ev_clear' (by omega) _ (by simp [hM, Function.update_apply])
    have e₃ : Ev (copyC S 10 0) (Function.update (Function.update M 1 []) 0 [])
        (Function.update (Function.update (Function.update M 1 []) 0 []) 0 (List.replicate W false))
        (7 * (W + 1) + 5) :=
      ev_copy' (by omega) (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
        (by simp [hM, Function.update_apply, *]) (by simp [hM, Function.update_apply, *]) (by simp) (by simp)
    have e := EvQ.seq e₁ (EvQ.seq e₂ e₃)
    refine (ev_eq e ?_).mono (by nlinarith)
    simp only [Nat.div_zero, wordOf_zero, hM]
    mem_eq
  · have hpos : 0 < b := by
      have : b ≠ 0 := by simpa using hv
      omega
    have e₁ := ev_quot (S := S) hS hc' ha hb hpos
    rw [← hM] at e₁
    set M₁ := Function.update (Function.update (Function.update m 1 (wordOf W b)) 6 (remOf W a b)) 7
      (wordOf W (a / b))
    have e₂ : Ev (clearC S 6) M₁ (Function.update M₁ 6 []) (2 * (W + W) + 3) :=
      ev_clear' (by omega) _ (by simp [M₁, Function.update_apply, remOf_length])
    have e₃ : Ev (clearC S 1) (Function.update M₁ 6 []) (Function.update (Function.update M₁ 6 []) 1 [])
        (2 * W + 3) := ev_clear' (by omega) _ (by simp [M₁, Function.update_apply])
    have e₄ : Ev (mvC S 7 0) (Function.update (Function.update M₁ 6 []) 1 [])
        (Function.update (Function.update (Function.update (Function.update M₁ 6 []) 1 []) 0
          (wordOf W (a / b))) 7 []) (9 * W + 8) :=
      ev_mv (by omega) (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
        (by simp [M₁, Function.update_apply, *]) (by simp [M₁, Function.update_apply, *])
        (by simp [M₁, Function.update_apply, *]) (by simp)
    have e := EvQ.seq e₁ (EvQ.seq e₂ (EvQ.seq e₃ e₄))
    refine (ev_eq e ?_).mono (by nlinarith)
    simp only [M₁]
    mem_eq

/-- Normalize the stack `0` to the width of the shape on the stack `7`. -/
def normC (S : ℕ) [NeZero S] : Cmd 10 S := liftC S (by norm_num) normalizeProgram (idPorts 8)

/-- `a % b`, with `a % 0 = a`. -/
def remCore (S : ℕ) [NeZero S] : Cmd 10 S :=
  .seq (zeroC S 1 2) (.ite 2 (clearC S 1)
    (.seq (quotC S) (.seq (clearC S 7) (.seq (clearC S 1) (.seq (mvC S 6 0)
      (.seq (copyC S 10 7) (normC S)))))))

theorem ev_norm {W x : ℕ} (hS : 11 ≤ S) {m : Mem} (hc : Clean W m) {xs : List Bool}
    (hx : BinaryArithmetic.toNat xs = x) (hlt : x < 2 ^ W) (hlen : xs.length ≤ W + W) :
    Ev (normC S) (Function.update (Function.update m 0 xs) 7 (List.replicate W false))
      (Function.update m 0 (wordOf W x)) (11 * W + 9) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hmod, hrul⟩ := hc
  refine (ev_lift (Q := fun _ => True) (by norm_num) normalizeProgram (idPorts 8) (idPorts_injective 8)
    (fun j => by have := j.2; simp only [idPorts]; omega) (fun i hi => ?_) fun r => ?_).weaken
  · have hi8 : 8 ≤ i := by
      by_contra hl
      exact hi ⟨i, by omega⟩ rfl
    have n0 : i ≠ 0 := by omega
    have n7 : i ≠ 7 := by omega
    simp [Function.update_apply, n0, n7]
  · obtain ⟨rf, n, hn, ht⟩ := normalize_correct r xs (List.replicate W false) []
    have hpad : ModularArithmetic.padTo (List.replicate W false) xs = wordOf W x := by
      apply eq_wordOf
      · simpa using ModularArithmetic.padTo_length (List.replicate W false) xs
      · rw [padTo_value_of_lt _ _ (by simpa [hx] using hlt), hx]
    rw [hpad] at ht
    refine ⟨rf, n, ?_, ?_, trivial⟩
    · simp only [List.length_replicate] at hn
      omega
    · have hs : (fun j : Fin 8 => Function.update (Function.update m 0 xs) 7 (List.replicate W false)
          (idPorts 8 j)) = normalizationState xs (List.replicate W false) [] [] := by
        funext j
        fin_cases j <;> simp [idPorts, normalizationState, Function.update_apply, *]
      have hf : (fun j : Fin 8 => Function.update m 0 (wordOf W x) (idPorts 8 j)) =
          normalizationState (wordOf W x) [] [] [] := by
        funext j
        fin_cases j <;> simp [idPorts, normalizationState, Function.update_apply, *]
      rw [hs, hf]
      exact ht

theorem ev_rem {W a b : ℕ} (hS : 11 ≤ S) {m : Mem} (hc : Clean W m) (ha : a < 2 ^ W) (hb : b < 2 ^ W) :
    Ev (remCore S) (Function.update (Function.update m 0 (wordOf W a)) 1 (wordOf W b))
      (Function.update m 0 (wordOf W (a % b))) (400 * (W + 1) ^ 2 + 80 * (W + 1) + 50) := by
  have hc' := hc
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hmod, hrul⟩ := hc
  set M := Function.update (Function.update m 0 (wordOf W a)) 1 (wordOf W b) with hM
  have ez := ev_zero (S := S) (s := 1) (scr := 2) (L := W + 1) (by omega) (by omega) (by norm_num)
    (m := M) (by simp [hM, Function.update_apply, *]) (by simp [hM, Function.update_apply, *])
  have hM1 : M 1 = wordOf W b := by simp [hM]
  rw [hM1, isZero_wordOf hb] at ez
  refine (EvQ.ite (t₂ := 400 * (W + 1) ^ 2 + 70 * (W + 1) + 40) ez (fun hv => ?_) (fun hv => ?_)).mono
    (by omega)
  · have hb0 : b = 0 := by simpa using hv
    subst hb0
    have e₁ : Ev (clearC S 1) M (Function.update M 1 []) (2 * (W + 1) + 3) :=
      ev_clear' (by omega) _ (by simp [hM])
    refine (ev_eq e₁ ?_).mono (by nlinarith)
    simp only [Nat.mod_zero, hM]
    mem_eq
  · have hpos : 0 < b := by
      have : b ≠ 0 := by simpa using hv
      omega
    have e₁ := ev_quot (S := S) hS hc' ha hb hpos
    rw [← hM] at e₁
    set M₁ := Function.update (Function.update (Function.update m 1 (wordOf W b)) 6 (remOf W a b)) 7
      (wordOf W (a / b))
    have e₂ : Ev (clearC S 7) M₁ (Function.update M₁ 7 []) (2 * W + 3) :=
      ev_clear' (by omega) _ (by simp [M₁, Function.update_apply])
    have e₃ : Ev (clearC S 1) (Function.update M₁ 7 []) (Function.update (Function.update M₁ 7 []) 1 [])
        (2 * W + 3) := ev_clear' (by omega) _ (by simp [M₁, Function.update_apply])
    have e₄ : Ev (mvC S 6 0) (Function.update (Function.update M₁ 7 []) 1 [])
        (Function.update (Function.update (Function.update (Function.update M₁ 7 []) 1 []) 0
          (remOf W a b)) 6 []) (9 * (W + W) + 8) :=
      ev_mv (by omega) (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
        (by simp [M₁, Function.update_apply, *]) (by simp [M₁, Function.update_apply, *])
        (by simp [M₁, Function.update_apply, *]) (by simp [remOf_length])
    set M₂ := Function.update (Function.update (Function.update (Function.update M₁ 7 []) 1 []) 0
      (remOf W a b)) 6 []
    have e₅ : Ev (copyC S 10 7) M₂ (Function.update M₂ 7 (List.replicate W false)) (7 * W + 5) :=
      ev_copy' (by omega) (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
        (by simp [M₂, M₁, Function.update_apply, *]) (by simp [M₂, M₁, Function.update_apply, *])
        (by simp [M₂, M₁, Function.update_apply, *]) (by simp)
    have hlt : a % b < 2 ^ W := (Nat.mod_le _ _).trans_lt ha
    have e₆ := ev_norm (S := S) hS hc' (xs := remOf W a b) (remOf_value ha hb hpos) hlt
      (by rw [remOf_length])
    have hmem : Function.update M₂ 7 (List.replicate W false) =
        Function.update (Function.update m 0 (remOf W a b)) 7 (List.replicate W false) := by
      simp only [M₂, M₁]
      mem_eq
    rw [hmem] at e₅
    have e := EvQ.seq e₁ (EvQ.seq e₂ (EvQ.seq e₃ (EvQ.seq e₄ (EvQ.seq e₅ e₆))))
    exact e.mono (by nlinarith)

end TransposeBase.Machine
