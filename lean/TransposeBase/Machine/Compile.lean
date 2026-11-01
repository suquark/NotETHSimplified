import TransposeBase.Machine.Iter

/-!
# The compiler from `Expr` to Boolean-stack programs -/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace TransposeBase.Machine

open OAI.Algorithms.SubexponentialSAT
open BitProgram StructuredCalls
open TransposeBase.Pseudo
open SqrtLogSpace.StructuredSpace

/-- The compiler, for a fixed number of stacks. `map` gives the slot of each variable, and `t` is the first
free slot, which also receives the value. -/
def compileAux (S : ℕ) [NeZero S] : Expr → List ℕ → ℕ → Cmd 10 S
  | .var j => varC S j
  | .lit n => litE S n
  | .add a b => binE S (addCore S) (compileAux S a) (compileAux S b)
  | .sub a b => binE S (subCore S) (compileAux S a) (compileAux S b)
  | .mul a b => binE S (mulCore S) (compileAux S a) (compileAux S b)
  | .div a b => binE S (divCore S) (compileAux S a) (compileAux S b)
  | .mod a b => binE S (remCore S) (compileAux S a) (compileAux S b)
  | .pow2 a => unE S (powCore S) (compileAux S a)
  | .ite a b c d => iteE S (compileAux S a) (compileAux S b) (compileAux S c) (compileAux S d)
  | .letE a b => letC S (compileAux S a) (compileAux S b)
  | .fold n s b => foldE S (compileAux S n) (compileAux S s) (compileAux S b)
  | .sum n b => sumE S (compileAux S n) (compileAux S b)
  | .prod n b => prodE S (compileAux S n) (compileAux S b)
  | .sumIter n s f b => iterE S (compileAux S n) (compileAux S s) (compileAux S b) (compileAux S f)

/-- The induction on the expression: each constructor is one lemma. -/
theorem correct_compile (W : ℕ) {S : ℕ} [NeZero S] (hS : 11 ≤ S) (e : Expr) :
    Correct W e (compileAux S e) := by
  have hsq := square_ge W
  have hT : 6000 * (W + 1) ^ 2 + 18 * (W + 1) + 8 + 3 * (9 * W + 8) ≤ T W := by simp only [T]; omega
  have hD : 400 * (W + 1) ^ 2 + 80 * (W + 1) + 50 + 3 * (9 * W + 8) ≤ T W := by simp only [T]; omega
  induction e with
  | var j => exact correct_var j
  | lit n => exact correct_lit n
  | add a b iha ihb =>
    exact correct_bin (fun x y => (x + y) % 2 ^ W) (fun _ _ _ hc hx hy => ev_add hS hc hx hy) (fun _ => rfl)
      (fun _ => rfl) rfl (by omega) iha ihb
  | sub a b iha ihb =>
    exact correct_bin (fun x y => (x + (2 ^ W - y % 2 ^ W)) % 2 ^ W) (fun _ _ _ hc hx hy => ev_sub hS hc hx hy)
      (fun _ => rfl) (fun _ => rfl) rfl hT iha ihb
  | mul a b iha ihb =>
    exact correct_bin (fun x y => (x * y) % 2 ^ W) (fun _ _ _ hc hx hy => ev_mul hS hc hx hy) (fun _ => rfl)
      (fun _ => rfl) rfl (by omega) iha ihb
  | div a b iha ihb =>
    exact correct_bin (fun x y => x / y) (fun _ _ _ hc hx hy => ev_div hS hc hx hy) (fun _ => rfl)
      (fun _ => rfl) rfl (by omega) iha ihb
  | mod a b iha ihb =>
    exact correct_bin (fun x y => x % y) (fun _ _ _ hc hx hy => ev_rem hS hc hx hy) (fun _ => rfl)
      (fun _ => rfl) rfl hD iha ihb
  | pow2 a iha => exact correct_pow2 hS iha
  | ite a b c d iha ihb ihc ihd => exact correct_ite iha ihb ihc ihd
  | letE a b iha ihb => exact correct_let iha ihb
  | fold n s b ihn ihs ihb => exact correct_fold ihn ihs ihb
  | sum n b ihn ihb => exact correct_sum hS ihn ihb
  | prod n b ihn ihb => exact correct_prod hS ihn ihb
  | sumIter n s f b ihn ihs ihf ihb => exact correct_sumIter hS ihn ihs ihf ihb

/-- The number of stacks: the environment, the live words of `stack e`, and eleven fixed stacks. -/
def slots (e : Expr) (d : ℕ) : ℕ := d + stack e + 11

instance (e : Expr) (d : ℕ) : NeZero (slots e d) := ⟨by simp [slots]⟩

/-- The compiled program of `e` with `d` environment slots. -/
def compile (e : Expr) (d : ℕ) : Cmd 10 (slots e d) :=
  compileAux (slots e d) e (List.range d).reverse d

/-- The state that the caller prepares: `S` is the number of stacks. -/
structure Prepared (W : ℕ) (env : List ℕ) {S : ℕ} [NeZero S] (st : Fin S → List Bool) : Prop where
  /-- Work stacks and the scratch stack are empty. -/
  work : ∀ i, i < 9 → st (F S i) = []
  /-- The read-only modulus: `W + 1` bits, value `2 ^ W`. -/
  modulus : st (F S 9) = wordOf (W + 1) (2 ^ W)
  /-- The read-only ruler: `W` bits. -/
  ruler : st (F S 10) = List.replicate W false
  /-- The variable `j` is in the slot `env.length - 1 - j`, as a `W`-bit little-endian word. -/
  vars : ∀ j (h : j < env.length), st (F S (11 + (env.length - 1 - j))) = wordOf W env[j]
  /-- All higher slots are empty. -/
  empty : ∀ i, env.length ≤ i → 11 + i < S → st (F S (11 + i)) = []

/-- A memory that restricts to the given stacks. -/
private def memOf {S : ℕ} (st : Fin S → List Bool) : Mem := fun i => if h : i < S then st ⟨i, h⟩ else []

private theorem view_memOf {S : ℕ} (st : Fin S → List Bool) : view S (memOf st) = st := by
  funext i
  simp [view, memOf]

private theorem memOf_F {S : ℕ} [NeZero S] (st : Fin S → List Bool) {i : ℕ} (h : i < S) :
    memOf st i = st (F S i) := by
  have hF : F S i = ⟨i, h⟩ := Fin.ext (F_val h)
  simp [memOf, h, hF]

private theorem forall₂_range (W : ℕ) (m : Mem) (t : ℕ) (env : List ℕ) (ht : env.length ≤ t)
    (hlt : ∀ x ∈ env, x < 2 ^ W)
    (hv : ∀ j (h : j < env.length), m (11 + (env.length - 1 - j)) = wordOf W env[j]) :
    List.Forall₂ (fun s x => s < t ∧ m (11 + s) = wordOf W x ∧ x < 2 ^ W)
      (List.range env.length).reverse env := by
  induction env with
  | nil => exact .nil
  | cons x rest ih =>
    simp only [List.length_cons, List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append]
    refine .cons ⟨by simp at ht; omega, ?_, hlt x (by simp)⟩ (ih (by simp at ht; omega)
      (fun y hy => hlt y (by simp [hy])) fun j h => ?_)
    · have := hv 0 (by simp)
      simpa using this
    · have := hv (j + 1) (by simpa using h)
      have hidx : (x :: rest).length - 1 - (j + 1) = rest.length - 1 - j := by simp; omega
      rw [hidx] at this
      simpa using this

private theorem good_of_prepared {W : ℕ} {env : List ℕ} {S : ℕ} [NeZero S] {st : Fin S → List Bool}
    (h : Prepared W env st) (hS : env.length + 11 < S + 1) (hS' : 11 ≤ S) (hlt : ∀ x ∈ env, x < 2 ^ W) :
    Good W (List.range env.length).reverse env env.length (memOf st) := by
  have hwork : ∀ i, i < 9 → memOf st i = [] := fun i hi => by
    rw [memOf_F st (by omega)]
    exact h.work i hi
  have hmod : memOf st 9 = wordOf (W + 1) (2 ^ W) := by
    rw [memOf_F st (by omega)]
    exact h.modulus
  have hrul : memOf st 10 = List.replicate W false := by
    rw [memOf_F st (by omega)]
    exact h.ruler
  have hemp : ∀ i, env.length ≤ i → memOf st (11 + i) = [] := fun i hi => by
    by_cases hlt : 11 + i < S
    · rw [memOf_F st hlt]
      exact h.empty i hi hlt
    · simp [memOf, hlt]
  have hvar : ∀ j (hj : j < env.length), memOf st (11 + (env.length - 1 - j)) = wordOf W env[j] := fun j hj => by
    rw [memOf_F st (by omega)]
    exact h.vars j hj
  refine ⟨⟨hwork 0 (by norm_num), hwork 1 (by norm_num), hwork 2 (by norm_num), hwork 3 (by norm_num),
    hwork 4 (by norm_num), hwork 5 (by norm_num), hwork 6 (by norm_num), hwork 7 (by norm_num),
    hwork 8 (by norm_num), hmod, hrul⟩, forall₂_range W _ _ env le_rfl hlt hvar, hemp, fun i => ?_⟩
  by_cases hi9 : i < 9
  · simp [hwork i hi9]
  by_cases hi : i = 9
  · subst hi
    simp [hmod]
  by_cases hi10 : i = 10
  · subst hi10
    simp [hrul]
  obtain ⟨k, rfl⟩ : ∃ k, i = 11 + k := ⟨i - 11, by omega⟩
  by_cases hk : env.length ≤ k
  · simp [hemp k hk]
  · have hj : env.length - 1 - k < env.length := by omega
    have := hvar (env.length - 1 - k) hj
    have hidx : env.length - 1 - (env.length - 1 - k) = k := by omega
    rw [hidx] at this
    simp [this]

/-- **The generic compiler theorem.** From a prepared state, `compile e env.length` writes the word of
`eval W e env` to the slot `env.length` and changes no other stack. The final registers are arbitrary. The
number of instructions is at most `ops W e env * 7000 * (W + 1) ^ 2`, and on every prefix every stack has at most
`7100 * (W + 1) ^ 2` bits. -/
theorem compile_correct (e : Expr) (W : ℕ) (env : List ℕ) (state : State 10 (slots e env.length))
    (hlt : ∀ x ∈ env, x < 2 ^ W) (hp : Prepared W env state.stacks) :
    ∃ n final, Eval (compile e env.length) n state final ∧
      final.stacks = Function.update state.stacks (F (slots e env.length) (11 + env.length))
        (wordOf W (eval W e env)) ∧
      n ≤ ops W e env * (7000 * (W + 1) ^ 2) ∧
      ∀ (ip op : Fin (slots e env.length)) (k : ℕ) (x : Cfg 10 (slots e env.length) _), k ≤ n →
        Trace (compiled (compile e env.length) ip op) k
          (state.withPC (some (compiled (compile e env.length) ip op).entry)) x →
        ∀ i, (x.stacks i).length ≤ 7100 * (W + 1) ^ 2 := by
  have hsp := stack_pos e
  have hS : 11 ≤ slots e env.length := by simp only [slots]; omega
  have hg := good_of_prepared hp (by simp only [slots]; omega) hS hlt
  have hC := correct_compile W hS e
  have hgo := hC _ _ _ _ hg (by simp only [slots]; omega)
  obtain ⟨n, rf, hrun, hn, _⟩ := hgo state.regs
  have hstart : (⟨state.regs, view (slots e env.length) (memOf state.stacks)⟩ :
      State 10 (slots e env.length)) = state := by
    rw [view_memOf]
  have hfinal : view (slots e env.length) (Function.update (memOf state.stacks) (11 + env.length)
      (wordOf W (eval W e env))) = Function.update state.stacks (F (slots e env.length) (11 + env.length))
        (wordOf W (eval W e env)) := by
    rw [view_update (by simp only [slots]; omega), view_memOf]
  rw [hstart, hfinal] at hrun
  exact ⟨n, _, hrun.eval, rfl, hn, hrun.pref⟩

end TransposeBase.Machine
