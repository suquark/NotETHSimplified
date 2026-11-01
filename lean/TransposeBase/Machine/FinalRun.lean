import TransposeBase.Machine.ParsePrefix
import TransposeBase.Machine.ParseRun

/-!
# One program: prefix, compiled word program, answer

`mainC c P` is one command on `slots (mainE P) 2` stacks. The prefix prepares the words, the compiled `mainE P` writes
its value to the stack `13`, and the suffix pops the lowest bit of that word and pushes it on the stack `0`.
`main_run` is the complete execution of the compiled program from `initial`, with one bound on all of its prefixes.
-/

set_option linter.unusedSectionVars false

namespace TransposeBase.Machine

open OAI.Algorithms.SubexponentialSAT
open BitProgram StructuredCalls
open TransposeBase.Pseudo
open SqrtLogSpace.StructuredSpace

/-- Parse, run `P` on `encF n F :: n :: x :: ℓ :: []`, and normalize the value to `0` or `1`. -/
def mainE (P : Expr) : Expr :=
  .letE Parse.nE (.letE Parse.encE (.ite P (.lit 0) (.lit 0) (.lit 1)))

variable {S : ℕ} [NeZero S]

/-- Move the lowest bit of the value to the output stack. -/
def suffixC (S : ℕ) [NeZero S] : Cmd 10 S :=
  .seq (popC S 13) (.ite 0 (pushB S 0 true) (pushB S 0 false))

theorem ev_suffix (hS : 14 ≤ S) {m : Mem} {b : Bool} {rest : List Bool} (h13 : m 13 = b :: rest) (h0 : m 0 = []) :
    Ev (suffixC S) m (Function.update (Function.update m 13 rest) 0 [b]) 4 := by
  have ep := ev_pop (S := S) (s := 13) (by omega) m
  rw [h13] at ep
  have ep' : EvQ (popC S 13) m (Function.update m 13 rest) 1 fun r => r 0 = b :=
    ep.mapQ fun r hr => by simpa using hr.1
  have hne : Function.update m 13 rest 0 = [] := by simp [h0]
  have e := EvQ.ite (y := pushB S 0 true) (n := pushB S 0 false) (t₂ := 2)
    (m₂ := Function.update (Function.update m 13 rest) 0 [b]) ep'
    (fun hb => by
      have := ev_pushB (S := S) (s := 0) (by omega) true (Function.update m 13 rest)
      rw [hne] at this
      rw [hb]
      exact this)
    (fun hb => by
      have := ev_pushB (S := S) (s := 0) (by omega) false (Function.update m 13 rest)
      rw [hne] at this
      rw [hb]
      exact this)
  exact e.mono (by omega)

/-- The whole command. -/
def mainC (c : ℕ) (P : Expr) : Cmd 10 (slots (mainE P) 2) :=
  .seq (prefixC _ c) (.seq (compile (mainE P) 2) (suffixC _))

theorem slots_main_ge (P : Expr) : 14 ≤ slots (mainE P) 2 := by
  have := stack_pos (mainE P)
  simp only [slots]
  omega

/-- The stack bound covers the whole prefix. -/
theorem pre_bound (W : ℕ) : W + 1000 * (W + 1) ^ 2 ≤ B W := by
  have := square_ge W
  simp only [B]
  omega

/-- `compile_correct` for an environment of two words. -/
theorem compile_correct_two (e : Expr) (W x y : ℕ) (state : State 10 (slots e 2))
    (hlt : ∀ z ∈ [x, y], z < 2 ^ W) (hp : Prepared W [x, y] state.stacks) :
    ∃ n final, RunN (B W) (compile e 2) n state final ∧
      final.stacks = Function.update state.stacks (F (slots e 2) 13) (wordOf W (eval W e [x, y])) ∧
      n ≤ ops W e [x, y] * (7000 * (W + 1) ^ 2) := by
  obtain ⟨n, final, he, hs, hn, hb⟩ := compile_correct e W [x, y] state hlt hp
  exact ⟨n, final, ⟨he, hb⟩, hs, hn⟩

/-- A run of a command is a complete run of its compiled program. -/
theorem source_of_run {c : Cmd 10 S} {n Bd : ℕ} {a b : State 10 S} {ip op : Fin S} {I : List Bool} {ans : Bool}
    (hrun : RunN Bd c n a b) (hreg : a.regs = fun _ => false)
    (hst : a.stacks = fun i => if i = ip then I else []) (hout : b.stacks op = [ans]) :
    ∃ final, Trace (compiled c ip op) (n + 1) (initial (compiled c ip op) I) final ∧ final.pc = none ∧
      final.stacks (compiled c ip op).outputStack = [ans] ∧
      ∀ k x, k ≤ n + 1 → Trace (compiled c ip op) k (initial (compiled c ip op) I) x →
        ∀ j, (x.stacks j).length ≤ Bd := by
  have hinit : initial (compiled c ip op) I = a.withPC (some (compiled c ip op).entry) := by
    obtain ⟨r, st⟩ := a
    simp only at hreg hst
    subst hreg hst
    rfl
  rw [hinit]
  exact ⟨b.withPC none, compiled_halt_trace hrun.eval _ _, rfl, hout,
    compiled_halt_stack_bound hrun.eval _ _ (hrun.pref _ _)⟩

/-- The complete execution. Here `W = wOf c I.length`, and `v` is the value of `mainE P`. -/
theorem main_run (c : ℕ) (hc : 1 ≤ c) (P : Expr) (I : List Bool) :
    let W := wOf c I.length
    let env := [BinaryArithmetic.toNat I, I.length]
    let p := compiled (mainC c P) (F _ 12) (F _ 0)
    ∃ steps ≤ 1000 * (W + 1) ^ 2 + (ops W (mainE P) env * (7000 * (W + 1) ^ 2) + 5), ∃ final,
      Trace p steps (initial p I) final ∧ final.pc = none ∧
      final.stacks p.outputStack = [decide (eval W (mainE P) env % 2 = 1)] ∧
      ∀ n x, n ≤ steps → Trace p n (initial p I) x → ∀ j, (x.stacks j).length ≤ B W := by
  intro W env p
  have hS := slots_main_ge P
  have hWge : 1 ≤ W := by
    have := wOf_facts (c := c) (ℓ := I.length) hc
    have h4 : I.length + 1 ≤ wOf c I.length + 1 := this.1
    have h5 : 1 ≤ padOf c I.length := Nat.mul_pos hc (by positivity)
    simp only [W, wOf]
    omega
  have hIW : I.length ≤ W := by simp [W, wOf]
  have henv : ∀ x ∈ env, x < 2 ^ W := by
    intro x hx
    simp only [env, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact toNat_input_lt c I
    · exact lt_of_le_of_lt hIW Nat.lt_two_pow_self
  have hg := GoQ.of_ev (B := B W) (L := W) (ev_prefix (S := slots (mainE P) 2) hS c hc I)
    (fun i => by
      by_cases hi : i = 12
      · subst hi; simpa using hIW
      · simp [Function.update_apply, hi]) (pre_bound W)
  obtain ⟨n₁, r₁, h₁, hn₁, -⟩ := hg (fun _ => false)
  have hp := prepared_M5 (S := slots (mainE P) 2) hS c I
  obtain ⟨n₂, final, h₂', hs, hn₂⟩ := compile_correct_two (mainE P) W _ _ ⟨r₁, view (slots (mainE P) 2) (M5 c I)⟩ henv hp
  set v := eval W (mainE P) env with hv
  have hvlt : v < 2 ^ W := eval_lt_word W _ _ henv
  have hs' : final.stacks = view (slots (mainE P) 2) (Function.update (M5 c I) 13 (wordOf W v)) := by
    rw [view_update (by omega)]
    exact hs
  obtain ⟨rg, st⟩ := final
  simp only at hs'
  subst hs'
  have h₂ : RunN (B W) (compile (mainE P) 2) n₂ ⟨r₁, view (slots (mainE P) 2) (M5 c I)⟩
      ⟨rg, view (slots (mainE P) 2) (Function.update (M5 c I) 13 (wordOf W v))⟩ := h₂'
  obtain ⟨W', hW'⟩ : ∃ W', W = W' + 1 := ⟨W - 1, by omega⟩
  have hhead : wordOf W v = decide (v % 2 = 1) :: wordOf (W - 1) (v / 2) := by
    rw [hW']
    rfl
  have hsmall : ∀ i, (Function.update (M5 c I) 13 (wordOf W v) i).length ≤ W + 1 := by
    intro i
    by_cases h13 : i = 13
    · subst h13; simp
    by_cases h12 : i = 12
    · subst h12; simp [Function.update_apply, W, wOf]; omega
    by_cases h11 : i = 11
    · subst h11; simp [Function.update_apply, W]
    by_cases h10 : i = 10
    · subst h10; simp [Function.update_apply]; omega
    by_cases h9 : i = 9
    · subst h9; simp [Function.update_apply, W]
    · simp [Function.update_apply, h9, h10, h11, h12, h13]
  have hg₃ := GoQ.of_ev (B := B W) (L := W + 1)
    (ev_suffix (S := slots (mainE P) 2) (m := Function.update (M5 c I) 13 (wordOf W v)) hS
      (by simpa using hhead) (by simp [Function.update_apply])) hsmall (by
      have := square_ge W
      simp only [B]
      omega)
  obtain ⟨n₃, r₃, h₃, hn₃, -⟩ := hg₃ rg
  have hrun := h₁.seq (h₂.seq h₃)
  have hrun' : RunN (B W) (mainC c P) (n₁ + (n₂ + n₃)) _ _ := hrun
  have hst : view (slots (mainE P) 2) (Function.update E0 12 I) = fun i => if i = F (slots (mainE P) 2) 12 then I else [] := by
    funext i
    have hval : (F (slots (mainE P) 2) 12).val = 12 := F_val (by omega)
    by_cases hi : i = F (slots (mainE P) 2) 12
    · subst hi
      simp [view, hval]
    · have hne : i.val ≠ 12 := fun e => hi (Fin.ext (by rw [hval]; exact e))
      simp [hi, view, hne]
  have hout : view (slots (mainE P) 2) (Function.update (Function.update
      (Function.update (M5 c I) 13 (wordOf W v)) 13 (wordOf (W - 1) (v / 2))) 0 [decide (v % 2 = 1)]) (F (slots (mainE P) 2) 0) =
      [decide (v % 2 = 1)] := by
    rw [view_F _ (by omega)]
    simp
  obtain ⟨final, h1, h2, h3, h4⟩ := source_of_run (ip := F (slots (mainE P) 2) 12) (op := F (slots (mainE P) 2) 0) (I := I)
    (ans := decide (v % 2 = 1)) hrun' rfl hst hout
  have hn₁' : n₁ ≤ 1000 * (W + 1) ^ 2 := hn₁
  have hn₂' : n₂ ≤ ops W (mainE P) env * (7000 * (W + 1) ^ 2) := hn₂
  exact ⟨_, by omega, final, h1, h2, h3, h4⟩

end TransposeBase.Machine
