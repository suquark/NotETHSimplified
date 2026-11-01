import TransposeBase.Machine.Div

/-!
# Literals, powers of two and the loop counter

A literal is in the program text, and it can be much longer than `W`. Each of its bits first pops one bit of a
copy of the ruler, and an empty ruler ends the routine, so the running time does not depend on the literal.
A power of two walks along the ruler and counts its exponent down.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace TransposeBase.Machine

open OAI.Algorithms.SubexponentialSAT
open BitProgram StructuredCalls CounterPrograms
open ModularArithmetic (padTo padTo_length)
open FormalizationKit

variable {S : ℕ} [NeZero S]

/-! ### Literals -/

/-- Write the bits on the stack `3` while the ruler copy on the stack `2` lasts; then pad with zeros. -/
def litC (S : ℕ) [NeZero S] : List Bool → Cmd 10 S
  | [] => xferC S 2 3
  | b :: bs => .seq (popC S 2) (.ite 1 (.seq (pushB S 3 b) (litC S bs)) (.base .skip))

theorem padTo_nil_zeros (k : ℕ) : padTo (List.replicate k false) [] = List.replicate k false := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, padTo, ih]

theorem ev_litC (hS : 11 ≤ S) (bits : List Bool) (k : ℕ) (acc : List Bool) (m : Mem)
    (h2 : m 2 = List.replicate k false) (h3 : m 3 = acc) :
    Ev (litC S bits) m
      (Function.update (Function.update m 2 []) 3 ((padTo (List.replicate k false) bits).reverse ++ acc))
      (7 * k + 5) := by
  induction bits generalizing k acc m with
  | nil =>
    have e := ev_xfer (S := S) (src := 2) (dst := 3) (by omega) (by omega) (by norm_num) m
    rw [h2, h3, ← padTo_nil_zeros k] at e
    refine e.mono ?_
    simp only [List.length_replicate, padTo_nil_zeros]
    omega
  | cons b bs ih =>
    cases k with
    | zero =>
      have ep := ev_pop (S := S) (s := 2) (by omega) m
      rw [h2] at ep
      have ep' : EvQ (popC S 2) m (Function.update m 2 []) 1 fun r => r 1 = false :=
        ep.mapQ fun r hr => by simpa using hr.2
      refine (ev_eq (EvQ.ite (t₂ := 3) ep' (fun hv => by simp at hv) fun _ =>
        (ev_skip _).mono (by omega)) ?_).mono (by omega)
      simp only [List.replicate_zero, padTo, List.reverse_nil, List.nil_append, ← h3]
      funext i
      by_cases hi : i = 3
      · subst hi; simp
      · simp [Function.update_apply, hi]
    | succ k =>
      have ep := ev_pop (S := S) (s := 2) (by omega) m
      rw [h2] at ep
      have ep' : EvQ (popC S 2) m (Function.update m 2 (List.replicate k false)) 1 fun r => r 1 = true :=
        ep.mapQ fun r hr => by simpa [List.replicate_succ] using hr.2
      set M := Function.update m 2 (List.replicate k false) with hM
      have e₁ := ev_pushB (S := S) (s := 3) (by omega) b M
      have h3M : M 3 = acc := by simp [hM, h3]
      rw [h3M] at e₁
      have e₂ := ih k (b :: acc) (Function.update M 3 (b :: acc)) (by simp [hM]) (by simp)
      refine (ev_eq (EvQ.ite (t₂ := 7 * k + 7) ep' (fun _ => (EvQ.seq e₁ e₂).mono (by omega)) (fun hv => by simp at hv)) ?_).mono
        (by omega)
      simp only [List.replicate_succ, padTo, List.reverse_cons, List.append_assoc, List.cons_append,
        List.nil_append, hM]
      funext i
      by_cases hi : i = 3
      · subst hi; simp
      · by_cases hi2 : i = 2
        · subst hi2; simp
        · simp [Function.update_apply, hi, hi2]

/-- Write the word of `n % 2 ^ W` on the stack `0`. -/
def litCore (S : ℕ) [NeZero S] (n : ℕ) : Cmd 10 S :=
  .seq (copyC S 10 2) (.seq (litC S n.bits) (xferC S 3 0))

theorem padded_bits (W n : ℕ) : padTo (List.replicate W false) n.bits = wordOf W (n % 2 ^ W) := by
  apply eq_wordOf
  · simpa using padTo_length (List.replicate W false) n.bits
  · rw [toNat_padTo, MachineArithmetic.bits_value, List.length_replicate]

theorem ev_lit {W : ℕ} (hS : 11 ≤ S) {m : Mem} (hc : Clean W m) (n : ℕ) :
    Ev (litCore S n) m (Function.update m 0 (wordOf W (n % 2 ^ W))) (20 * (W + 1) + 20) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hmod, hrul⟩ := hc
  have e₁ : Ev (copyC S 10 2) m (Function.update m 2 (List.replicate W false)) (7 * W + 5) :=
    ev_copy' (by omega) (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num) h8 hrul h2 (by simp)
  have e₂ := ev_litC (S := S) hS n.bits W [] (Function.update m 2 (List.replicate W false)) (by simp)
    (by simp [Function.update_apply, h3])
  rw [padded_bits, List.append_nil] at e₂
  set M := Function.update (Function.update (Function.update m 2 (List.replicate W false)) 2 [])
    3 (wordOf W (n % 2 ^ W)).reverse with hM
  have e₃ := ev_xfer (S := S) (src := 3) (dst := 0) (by omega) (by omega) (by norm_num) M
  have hM3 : M 3 = (wordOf W (n % 2 ^ W)).reverse := by simp [hM]
  have hM0 : M 0 = [] := by simp [hM, Function.update_apply, h0]
  rw [hM3, hM0, List.reverse_reverse, List.append_nil] at e₃
  have e := EvQ.seq e₁ (EvQ.seq e₂ e₃)
  refine (ev_eq e ?_).mono (by simp only [List.length_reverse, length_wordOf]; omega)
  simp only [hM]
  mem_eq

/-! ### The loop counter -/

theorem ripple_length_ge (c : Bool) (bs : List Bool) : bs.length ≤ (ripple c bs).length := by
  induction bs with
  | nil => simp [ripple]
  | cons b bs ih =>
    simp only [ripple, List.length_cons]
    split_ifs <;> simp
    omega

theorem ripple_true_word {W k : ℕ} (h : k + 1 < 2 ^ W) : ripple true (wordOf W k) = wordOf W (k + 1) := by
  have hk : k < 2 ^ W := by omega
  apply eq_wordOf
  · apply le_antisymm
    · apply increment_length_le_of_lt _ _ (by simp)
      rwa [value_eq_toNat, toNat_wordOf hk]
    · simpa using ripple_length_ge true (wordOf W k)
  · rw [← value_eq_toNat, value_increment, value_eq_toNat, toNat_wordOf hk]

theorem ripple_false_word {W k : ℕ} (hk : k < 2 ^ W) (hpos : 0 < k) :
    ripple false (wordOf W k) = wordOf W (k - 1) := by
  have hv : 0 < value (wordOf W k) := by rwa [value_eq_toNat, toNat_wordOf hk]
  apply eq_wordOf
  · rw [decrement_length hv]
    simp
  · have h1 := value_decrement hv
    have h2 : value (wordOf W k) = k := by rw [value_eq_toNat, toNat_wordOf hk]
    rw [← value_eq_toNat]
    omega

/-- Add one to the word on the stack `i`. The stack `1` is the scratch stack. -/
def incC (S : ℕ) [NeZero S] (i : ℕ) : Cmd 10 S := rippleC S true i 1

theorem ev_inc {W k i : ℕ} (hi : i < S) (hS : 11 ≤ S) (hne : i ≠ 1) {m : Mem} (hm1 : m 1 = [])
    (hmi : m i = wordOf W k) (hk : k + 1 < 2 ^ W) :
    Ev (incC S i) m (Function.update m i (wordOf W (k + 1))) (8 * W + 8) := by
  have e := ev_ripple (S := S) (c := true) (s := i) (scr := 1) (L := W) hi (by omega) hne hm1 (by simp [hmi])
  rwa [hmi, ripple_true_word hk] at e

/-! ### Powers of two -/

/-- The register `0` becomes: the stack `0` is not zero, and the stack `2` is not empty. -/
def powGuard (S : ℕ) [NeZero S] : Cmd 10 S :=
  .seq (zeroC S 0 1) (.seq (.base (.atom (.peek (F S 2) 3 4)))
    (.seq (.base (.atom (.bnot 2 2))) (.base (.atom (.band 0 2 4)))))

theorem ev_powGuard {L : ℕ} (hS : 11 ≤ S) {m : Mem} (h1 : m 1 = []) (hL : (m 0).length ≤ L) :
    EvQ (powGuard S) m m (8 * L + 9) fun r => r 0 = ((!isZero (m 0)) && (m 2).head?.isSome) := by
  intro regs
  obtain ⟨n, r₁, e₁, hn, hq⟩ := ev_zero (S := S) (s := 0) (scr := 1) (L := L) (by omega) (by omega)
    (by norm_num) h1 hL regs
  have e₂ := Eval.base (StructuredProgram.Eval.atom (.peek (F S 2) (3 : Fin 10) 4) (⟨r₁, view S m⟩ : State 10 S))
  have e₃ := Eval.base (StructuredProgram.Eval.atom (.bnot (s := S) (2 : Fin 10) 2)
    (StructuredProgram.Atom.eval (.peek (F S 2) (3 : Fin 10) 4) (⟨r₁, view S m⟩ : State 10 S)))
  have e₄ := Eval.base (StructuredProgram.Eval.atom (.band (s := S) (0 : Fin 10) 2 4)
    (StructuredProgram.Atom.eval (.bnot (s := S) (2 : Fin 10) 2)
    (StructuredProgram.Atom.eval (.peek (F S 2) (3 : Fin 10) 4) (⟨r₁, view S m⟩ : State 10 S))))
  have e := e₁.seq (e₂.seq (e₃.seq e₄))
  refine ⟨_, _, e, by omega, ?_⟩
  simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, execInstr,
    StructuredProgram.State.ofCfg, readRegs, Function.update_apply, view_F m (show 2 < S by omega), hq]

/-- One step of the walk along the ruler: one more zero bit, and the exponent decreases. -/
def powBody (S : ℕ) [NeZero S] : Cmd 10 S :=
  .seq (popC S 2) (.seq (pushB S 3 false) (.seq (rippleC S false 0 1) (powGuard S)))

/-- The memory after `k` steps of the walk. -/
def powMem (W a : ℕ) (m : Mem) (k : ℕ) : Mem :=
  Function.update (Function.update (Function.update m 0 (wordOf W (a - k))) 2
    (List.replicate (W - k) false)) 3 (List.replicate k false)

/-- The loop is the initial guard and a `while` on the register `0`. -/
theorem ev_for {test : Fin 10} {g body : Cmd 10 S} (M : ℕ → Mem) (N τ t : ℕ)
    (hg : EvQ g (M 0) (M 0) t fun r => r test = decide (0 < N))
    (h : ∀ k < N, EvQ body (M k) (M (k + 1)) τ fun r => r test = decide (k + 1 < N)) :
    Ev (.seq g (.while test body)) (M 0) (M N) (t + (N * (τ + 1) + 1)) := fun regs => by
  obtain ⟨n₁, r₁, e₁, b₁, hr⟩ := hg regs
  obtain ⟨n₂, r₂, e₂, b₂⟩ := ev_while M N τ h 0 (Nat.zero_le _) r₁ hr
  exact ⟨n₁ + n₂, r₂, e₁.seq e₂, by simp only [Nat.sub_zero] at b₂; omega, trivial⟩

theorem ev_powWalk {W a : ℕ} (hS : 11 ≤ S) {m : Mem} (hc : Clean W m) (ha : a < 2 ^ W) :
    Ev (.seq (powGuard S) (.while 0 (powBody S))) (powMem W a m 0) (powMem W a m (min a W))
      (40 * (W + 1) ^ 2) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hmod, hrul⟩ := hc
  have hmem1 : ∀ k, powMem W a m k 1 = [] := fun k => by simp [powMem, Function.update_apply, h1]
  have hmem0 : ∀ k, powMem W a m k 0 = wordOf W (a - k) := fun k => by simp [powMem, Function.update_apply]
  have hmem2 : ∀ k, powMem W a m k 2 = List.replicate (W - k) false := fun k => by
    simp [powMem, Function.update_apply]
  have hmem3 : ∀ k, powMem W a m k 3 = List.replicate k false := fun k => by simp [powMem]
  have hsub : ∀ k, a - k < 2 ^ W := fun k => by omega
  have hguard : ∀ k, EvQ (powGuard S) (powMem W a m k) (powMem W a m k) (8 * W + 9)
      fun r => r 0 = decide (k < min a W) := fun k => by
    refine (ev_powGuard (L := W) hS (hmem1 k) (by simp [hmem0])).mapQ fun r hr => ?_
    rw [hr, hmem0, hmem2, isZero_wordOf (hsub k)]
    apply Bool.eq_iff_iff.mpr
    cases hd : W - k with
    | zero =>
      simp
      omega
    | succ d =>
      simp [List.replicate_succ]
      omega
  have hbody : ∀ k < min a W, EvQ (powBody S) (powMem W a m k) (powMem W a m (k + 1)) (16 * W + 20)
      fun r => r 0 = decide (k + 1 < min a W) := fun k hk => by
    have hkW : k < W := lt_of_lt_of_le hk (min_le_right _ _)
    have hka : k < a := lt_of_lt_of_le hk (min_le_left _ _)
    have hd : W - k = (W - (k + 1)) + 1 := by omega
    have e₁ := ev_pop (S := S) (s := 2) (by omega) (powMem W a m k)
    rw [hmem2, hd] at e₁
    have e₁' := e₁.weaken
    simp only [List.replicate_succ, List.tail_cons] at e₁'
    set M₁ := Function.update (powMem W a m k) 2 (List.replicate (W - (k + 1)) false) with hM₁
    have e₂ := ev_pushB (S := S) (s := 3) (by omega) false M₁
    set M₂ := Function.update M₁ 3 (false :: M₁ 3) with hM₂
    have e₃ := ev_ripple (S := S) (c := false) (s := 0) (scr := 1) (L := W) (m := M₂) (by omega) (by omega)
      (by norm_num) (by simp [hM₂, hM₁, Function.update_apply, hmem1])
      (by simp [hM₂, hM₁, Function.update_apply, hmem0])
    have hM₂0 : M₂ 0 = wordOf W (a - k) := by simp [hM₂, hM₁, Function.update_apply, hmem0]
    rw [hM₂0, ripple_false_word (hsub k) (by omega)] at e₃
    have hmem : Function.update M₂ 0 (wordOf W (a - k - 1)) = powMem W a m (k + 1) := by
      have h3M : M₁ 3 = List.replicate k false := by simp [hM₁, hmem3]
      simp only [hM₂, hM₁, h3M] at *
      funext i
      by_cases i0 : i = 0
      · subst i0
        simp [powMem, Nat.sub_add_eq]
      · by_cases i2 : i = 2
        · subst i2
          simp [powMem, Function.update_apply]
        · by_cases i3 : i = 3
          · subst i3
            simp [powMem, List.replicate_succ]
          · simp [powMem, Function.update_apply, i0, i2, i3]
    rw [hmem] at e₃
    exact (EvQ.seq e₁' (EvQ.seq e₂ (EvQ.seq e₃ (hguard (k + 1))))).mono (by omega)
  have hf := ev_for (powMem W a m) (min a W) (16 * W + 20) (8 * W + 9) (hguard 0) hbody
  refine hf.mono ?_
  have hmin : min a W ≤ W := min_le_right _ _
  have hmul := Nat.mul_le_mul_right (16 * W + 20 + 1) hmin
  nlinarith

/-- `2 ^ a` if `a < W`, and `0` otherwise. The exponent is on the stack `0`, and the result too. -/
def powCore (S : ℕ) [NeZero S] : Cmd 10 S :=
  .seq (copyC S 10 2) (.seq (.seq (powGuard S) (.while 0 (powBody S)))
    (.seq (.seq (popC S 2) (.ite 1 (pushB S 3 true) (.base .skip)))
      (.seq (xferC S 2 3) (.seq (clearC S 0) (xferC S 3 0)))))

theorem ev_pow {W a : ℕ} (hS : 11 ≤ S) {m : Mem} (hc : Clean W m) (ha : a < 2 ^ W) :
    Ev (powCore S) (Function.update m 0 (wordOf W a))
      (Function.update m 0 (wordOf W (if a < W then 2 ^ a else 0))) (41 * (W + 1) ^ 2 + 60 * (W + 1) + 60) := by
  have hc' := hc
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hmod, hrul⟩ := hc
  have e₁ : Ev (copyC S 10 2) (Function.update m 0 (wordOf W a)) (powMem W a m 0) (7 * W + 5) := by
    have := ev_copy' (S := S) (src := 10) (dst := 2) (L := W) (m := Function.update m 0 (wordOf W a))
      (x := List.replicate W false)
      (by omega) (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
      (by simp [Function.update_apply, h8]) (by simp [Function.update_apply, hrul])
      (by simp [Function.update_apply, h2]) (by simp)
    refine ev_eq this ?_
    simp only [powMem, Nat.sub_zero, List.replicate_zero]
    mem_eq
  have e₂ := ev_powWalk (S := S) hS hc' ha
  set N := min a W with hN
  have hlen0 : (powMem W a m N 0).length ≤ W := by simp [powMem, Function.update_apply]
  by_cases haW : a < W
  · have hNa : N = a := min_eq_left haW.le
    rw [if_pos haW]
    set M := powMem W a m N with hM
    have hM2 : M 2 = false :: List.replicate (W - a - 1) false := by
      obtain ⟨d, hd⟩ : ∃ d, W - a = d + 1 := ⟨W - a - 1, by omega⟩
      have hd' : W - a - 1 = d := by omega
      have hval : M 2 = List.replicate (W - a) false := by
        simp [hM, powMem, hNa, Function.update_apply]
      rw [hd', hval, hd, List.replicate_succ]
    have hM3 : M 3 = List.replicate a false := by simp [hM, powMem, hNa]
    have ep := ev_pop (S := S) (s := 2) (by omega) M
    rw [hM2] at ep
    have ep' : EvQ (popC S 2) M (Function.update M 2 (List.replicate (W - a - 1) false)) 1
        fun r => r 1 = true := ep.mapQ fun r hr => by simpa using hr.2
    set M₁ := Function.update M 2 (List.replicate (W - a - 1) false) with hM₁
    have ep₂ := ev_pushB (S := S) (s := 3) (by omega) true M₁
    have e₃ := EvQ.ite (t₂ := 2) (n := .base .skip) ep' (fun _ => ep₂) (fun hv => by simp at hv)
    set M₂ := Function.update M₁ 3 (true :: M₁ 3) with hM₂
    have e₄ := ev_xfer (S := S) (src := 2) (dst := 3) (by omega) (by omega) (by norm_num) M₂
    set M₃ := Function.update (Function.update M₂ 2 []) 3 ((M₂ 2).reverse ++ M₂ 3) with hM₃
    have e₅ := ev_clear (S := S) (i := 0) (by omega) M₃
    have e₆ := ev_xfer (S := S) (src := 3) (dst := 0) (by omega) (by omega) (by norm_num)
      (Function.update M₃ 0 [])
    have e := EvQ.seq e₁ (EvQ.seq e₂ (EvQ.seq e₃ (EvQ.seq e₄ (EvQ.seq e₅ e₆))))
    have hM₂2 : M₂ 2 = List.replicate (W - a - 1) false := by simp [hM₂, hM₁]
    have hM₂3 : M₂ 3 = true :: List.replicate a false := by simp [hM₂, hM₁, Function.update_apply, hM3]
    have hM₃3 : M₃ 3 = List.replicate (W - a - 1) false ++ true :: List.replicate a false := by
      simp [hM₃, hM₂2, hM₂3]
    have hM₃0 : M₃ 0 = M 0 := by simp [hM₃, hM₂, hM₁, Function.update_apply]
    refine (ev_eq e ?_).mono ?_
    · rw [← wordOf_two_pow haW]
      simp only [Function.update_self, Function.update_apply, hM₃3]
      funext i
      by_cases i0 : i = 0
      · subst i0
        simp [List.reverse_append]
      · by_cases i3 : i = 3
        · subst i3
          simp [h3]
        · by_cases i2 : i = 2
          · subst i2
            simp [hM₃, h2]
          · simp [hM₃, hM₂, hM₁, hM, powMem, Function.update_apply, i0, i2, i3]
    · simp only [hM₂2, hM₃0, Function.update_self, hM₃3, Function.update_apply]
      have hM0 : (M 0).length ≤ W := hlen0
      simp
      omega
  · have hNW : N = W := min_eq_right (by omega)
    rw [if_neg haW, wordOf_zero]
    set M := powMem W a m N with hM
    have hM2 : M 2 = [] := by simp [hM, powMem, hNW, Function.update_apply]
    have hM3 : M 3 = List.replicate W false := by simp [hM, powMem, hNW]
    have ep := ev_pop (S := S) (s := 2) (by omega) M
    rw [hM2] at ep
    have ep' : EvQ (popC S 2) M (Function.update M 2 []) 1 fun r => r 1 = false :=
      ep.mapQ fun r hr => by simpa using hr.2
    have hself : Function.update M 2 [] = M := by rw [← hM2]; simp
    rw [hself] at ep'
    have e₃ := EvQ.ite (t₂ := 2) (y := pushB S 3 true) ep' (fun hv => by simp at hv)
      (fun _ => (ev_skip (S := S) M).mono (by omega))
    have e₄ := ev_xfer (S := S) (src := 2) (dst := 3) (by omega) (by omega) (by norm_num) M
    rw [hM2, hM3] at e₄
    simp only [List.reverse_nil, List.nil_append] at e₄
    set M₃ := Function.update (Function.update M 2 []) 3 (List.replicate W false) with hM₃
    have e₅ := ev_clear (S := S) (i := 0) (by omega) M₃
    have e₆ := ev_xfer (S := S) (src := 3) (dst := 0) (by omega) (by omega) (by norm_num)
      (Function.update M₃ 0 [])
    have e := EvQ.seq e₁ (EvQ.seq e₂ (EvQ.seq e₃ (EvQ.seq e₄ (EvQ.seq e₅ e₆))))
    refine (ev_eq e ?_).mono ?_
    · simp only [Function.update_self, Function.update_apply]
      funext i
      by_cases i0 : i = 0
      · subst i0
        simp [hM₃, Function.update_apply]
      · by_cases i3 : i = 3
        · subst i3
          simp [h3]
        · by_cases i2 : i = 2
          · subst i2
            simp [hM₃, hM, Function.update_apply, h2]
          · simp [hM₃, hM, powMem, Function.update_apply, i0, i2, i3]
    · have hM₃0 : (M₃ 0).length ≤ W := by
        simpa [hM₃, Function.update_apply] using hlen0
      have hM₃3 : (M₃ 3).length = W := by simp [hM₃]
      simp only [List.length_nil, Function.update_apply, List.length_replicate]
      simp
      omega

end TransposeBase.Machine
