import TransposeBase.Pseudo.WordBound
import TransposeBase.Machine.Run

/-!
# Word slots and the compilation judgement

The slot `i` is the stack `11 + i`. `Good W map env t m` says what the compiled code of an expression may assume:
the variable `j` is in the slot `map[j]`, and the slots from `t` on are empty. `Correct W e C` says that `C map t`
writes the value of `e` to the slot `t` and leaves the rest of the memory as it was.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace TransposeBase.Machine

open OAI.Algorithms.SubexponentialSAT
open StructuredCalls
open TransposeBase.Pseudo

variable {S : ℕ} [NeZero S]

/-- The instruction budget of one word operation. -/
def T (W : ℕ) : ℕ := 7000 * (W + 1) ^ 2

/-- The bound on every stack, on every prefix. -/
def B (W : ℕ) : ℕ := 7100 * (W + 1) ^ 2

theorem square_ge (W : ℕ) : W + 1 ≤ (W + 1) ^ 2 := by nlinarith

/-- Equality of explicit memories, with arithmetic on the stack numbers. -/
macro "mem_eq'" : tactic =>
  `(tactic| (funext i; simp only [Function.update_apply]; split_ifs <;> first | rfl | (exfalso; omega) | simp_all))

/-- All stacks of an explicit memory are short. -/
macro "small_tac" h:term : tactic =>
  `(tactic| (intro i; simp only [Function.update_apply]; split_ifs <;> first | exact $h i | simp))

theorem Clean.high {W i : ℕ} {m : Mem} (h : Clean W m) (hi : 11 ≤ i) (x : List Bool) :
    Clean W (Function.update m i x) := by
  have n : ∀ j, j < 11 → j ≠ i := fun j hj e => by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Function.update_of_ne (n 0 (by norm_num))]; exact h.w0
  · rw [Function.update_of_ne (n 1 (by norm_num))]; exact h.w1
  · rw [Function.update_of_ne (n 2 (by norm_num))]; exact h.w2
  · rw [Function.update_of_ne (n 3 (by norm_num))]; exact h.w3
  · rw [Function.update_of_ne (n 4 (by norm_num))]; exact h.w4
  · rw [Function.update_of_ne (n 5 (by norm_num))]; exact h.w5
  · rw [Function.update_of_ne (n 6 (by norm_num))]; exact h.w6
  · rw [Function.update_of_ne (n 7 (by norm_num))]; exact h.w7
  · rw [Function.update_of_ne (n 8 (by norm_num))]; exact h.w8
  · rw [Function.update_of_ne (n 9 (by norm_num))]; exact h.modulus
  · rw [Function.update_of_ne (n 10 (by norm_num))]; exact h.ruler

/-- The memory that the compiled code of an expression may assume. -/
structure Good (W : ℕ) (map env : List ℕ) (t : ℕ) (m : Mem) : Prop where
  clean : Clean W m
  vars : List.Forall₂ (fun s x => s < t ∧ m (11 + s) = wordOf W x ∧ x < 2 ^ W) map env
  empty : ∀ i, t ≤ i → m (11 + i) = []
  small : ∀ i, (m i).length ≤ W + 1

theorem Good.env_lt {W t : ℕ} {map env : List ℕ} {m : Mem} (h : Good W map env t m) :
    ∀ x ∈ env, x < 2 ^ W := by
  have key : ∀ {map env : List ℕ},
      List.Forall₂ (fun s x => s < t ∧ m (11 + s) = wordOf W x ∧ x < 2 ^ W) map env → ∀ x ∈ env, x < 2 ^ W := by
    intro map env hf
    induction hf with
    | nil => simp
    | cons h₁ _ ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h₁.2.2
      · exact ih x hx
  exact key h.vars

/-- A word in the slot `t`, and the first free slot moves up. -/
theorem Good.step {W t x : ℕ} {map env : List ℕ} {m : Mem} (h : Good W map env t m) :
    Good W map env (t + 1) (Function.update m (11 + t) (wordOf W x)) := by
  refine ⟨h.clean.high (by omega) _, h.vars.imp fun s y hr => ?_, fun i hi => ?_, ?_⟩
  · refine ⟨by omega, ?_, hr.2.2⟩
    rw [Function.update_of_ne (by omega)]
    exact hr.2.1
  · rw [Function.update_of_ne (by omega)]
    exact h.empty i (by omega)
  · have := h.small
    small_tac this

/-- One more variable, in a slot below `t`. -/
theorem Good.cons {W t s x : ℕ} {map env : List ℕ} {m : Mem} (h : Good W map env t m) (hs : s < t)
    (hm : m (11 + s) = wordOf W x) (hx : x < 2 ^ W) : Good W (s :: map) (x :: env) t m :=
  ⟨h.clean, .cons ⟨hs, hm, hx⟩ h.vars, h.empty, h.small⟩

theorem stack_pos (e : Expr) : 1 ≤ stack e := by
  induction e <;> simp only [stack] <;> omega

/-- The compilation judgement of an expression. -/
def Correct (W : ℕ) (e : Expr) (C : List ℕ → ℕ → Cmd 10 S) : Prop :=
  ∀ map env t m, Good W map env t m → 11 + t + stack e ≤ S →
    Go (B W) (C map t) m (Function.update m (11 + t) (wordOf W (eval W e env))) (ops W e env * T W)

theorem go_eq {B t : ℕ} {c : Cmd 10 S} {m m' m'' : Mem} {Q : Regs → Prop} (h : GoQ B c m m' t Q)
    (e : m' = m'') : GoQ B c m m'' t Q := e ▸ h

/-- Routines count as one word operation: the local estimate is uniform in `W`. -/
theorem go_routine {W t : ℕ} {c : Cmd 10 S} {m m' : Mem} {Q : Regs → Prop} (h : EvQ c m m' t Q)
    (hs : ∀ i, (m i).length ≤ W + 1) (ht : t ≤ T W) : GoQ (B W) c m m' t Q :=
  GoQ.of_ev h hs (by have := square_ge W; simp only [T, B] at *; omega)

/-! ### Operations on slots through the work stacks -/

/-- Apply a binary routine to the slots `x` and `y`: the result goes to `x`, and `y` becomes empty. -/
def binC (S : ℕ) [NeZero S] (core : Cmd 10 S) (x y : ℕ) : Cmd 10 S :=
  .seq (mvC S x 0) (.seq (mvC S y 1) (.seq core (mvC S 0 x)))

theorem ev_bin {W x y tc : ℕ} {wa wb wr : List Bool} {core : Cmd 10 S} {m : Mem} (hS : 11 ≤ S) (hx : x < S)
    (hy : y < S) (hx11 : 11 ≤ x) (hy11 : 11 ≤ y) (hne : x ≠ y) (hc : Clean W m) (hmx : m x = wa) (hmy : m y = wb)
    (hla : wa.length = W) (hlb : wb.length = W) (hlr : wr.length = W)
    (hcore : Ev core
      (Function.update (Function.update (Function.update (Function.update m x []) y []) 0 wa) 1 wb)
      (Function.update (Function.update (Function.update m x []) y []) 0 wr) tc) :
    Ev (binC S core x y) m (Function.update (Function.update m x wr) y []) (tc + 3 * (9 * W + 8)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hmod, hrul⟩ := hc
  have e₁ := ev_mv (S := S) (src := x) (dst := 0) (L := W) (m := m) (x := wa) hx (by omega) (by omega) (by omega)
    (by omega) (by norm_num) h8 hmx h0 (by omega)
  set M₁ := Function.update (Function.update m 0 wa) x [] with hM₁
  have e₂ := ev_mv (S := S) (src := y) (dst := 1) (L := W) (m := M₁) (x := wb) hy (by omega) (by omega) (by omega)
    (by omega) (by norm_num)
    (by rw [hM₁, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact h8)
    (by rw [hM₁, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hmy)
    (by rw [hM₁, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact h1)
    (by omega)
  have hmem₂ : Function.update (Function.update M₁ 1 wb) y [] =
      Function.update (Function.update (Function.update (Function.update m x []) y []) 0 wa) 1 wb := by
    simp only [hM₁]
    mem_eq'
  rw [hmem₂] at e₂
  set M₃ := Function.update (Function.update (Function.update m x []) y []) 0 wr with hM₃
  have e₄ := ev_mv (S := S) (src := 0) (dst := x) (L := W) (m := M₃) (x := wr) (by omega) hx (by omega) (by omega)
    (by norm_num) (by omega)
    (by rw [hM₃]; simp only [Function.update_apply]; split_ifs <;> first | (exfalso; omega) | exact h8)
    (by simp [hM₃]) (by rw [hM₃]; simp only [Function.update_apply]; split_ifs <;> first | (exfalso; omega) | rfl)
    (by omega)
  have hmem₄ : Function.update (Function.update M₃ x wr) 0 [] =
      Function.update (Function.update m x wr) y [] := by
    simp only [hM₃]
    mem_eq'
  rw [hmem₄] at e₄
  exact (EvQ.seq e₁ (EvQ.seq e₂ (EvQ.seq hcore e₄))).mono (by omega)

/-- Apply a unary routine to the slot `x`. -/
def unC (S : ℕ) [NeZero S] (core : Cmd 10 S) (x : ℕ) : Cmd 10 S :=
  .seq (mvC S x 0) (.seq core (mvC S 0 x))

theorem ev_un {W x tc : ℕ} {wa wr : List Bool} {core : Cmd 10 S} {m : Mem} (hS : 11 ≤ S) (hx : x < S)
    (hx11 : 11 ≤ x) (hc : Clean W m) (hmx : m x = wa) (hla : wa.length = W) (hlr : wr.length = W)
    (hcore : Ev core (Function.update (Function.update m x []) 0 wa)
      (Function.update (Function.update m x []) 0 wr) tc) :
    Ev (unC S core x) m (Function.update m x wr) (tc + 2 * (9 * W + 8)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hmod, hrul⟩ := hc
  have e₁ := ev_mv (S := S) (src := x) (dst := 0) (L := W) (m := m) (x := wa) hx (by omega) (by omega) (by omega)
    (by omega) (by norm_num) h8 hmx h0 (by omega)
  have hmem₁ : Function.update (Function.update m 0 wa) x [] =
      Function.update (Function.update m x []) 0 wa := by
    mem_eq'
  rw [hmem₁] at e₁
  set M₃ := Function.update (Function.update m x []) 0 wr with hM₃
  have e₄ := ev_mv (S := S) (src := 0) (dst := x) (L := W) (m := M₃) (x := wr) (by omega) hx (by omega) (by omega)
    (by norm_num) (by omega)
    (by rw [hM₃]; simp only [Function.update_apply]; split_ifs <;> first | (exfalso; omega) | exact h8)
    (by simp [hM₃]) (by rw [hM₃]; simp only [Function.update_apply]; split_ifs <;> first | (exfalso; omega) | rfl)
    (by omega)
  have hmem₄ : Function.update (Function.update M₃ x wr) 0 [] = Function.update m x wr := by
    simp only [hM₃]
    mem_eq'
  rw [hmem₄] at e₄
  exact (EvQ.seq e₁ (EvQ.seq hcore e₄)).mono (by omega)

/-- Compare the slots `x` and `y`, without changing them: the register `0` gets `x < y`. -/
def cmpC (S : ℕ) [NeZero S] (x y : ℕ) : Cmd 10 S :=
  .seq (copyC S x 0) (.seq (copyC S y 1) (ltCore S))

theorem ev_cmp {W x y a b : ℕ} {m : Mem} (hS : 11 ≤ S) (hx : x < S) (hy : y < S) (hx11 : 11 ≤ x) (hy11 : 11 ≤ y)
    (hc : Clean W m) (hmx : m x = wordOf W a) (hmy : m y = wordOf W b) (ha : a < 2 ^ W) (hb : b < 2 ^ W) :
    EvQ (cmpC S x y) m m (46 * W + 63) fun r => r 0 = decide (a < b) := by
  have hc' := hc
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hmod, hrul⟩ := hc
  have e₁ := ev_copy' (S := S) (src := x) (dst := 0) (L := W) (m := m) (x := wordOf W a) hx (by omega) (by omega)
    (by omega) (by omega) (by norm_num) h8 hmx h0 (by simp)
  have e₂ := ev_copy' (S := S) (src := y) (dst := 1) (L := W) (m := Function.update m 0 (wordOf W a))
    (x := wordOf W b) hy (by omega) (by omega) (by omega) (by omega) (by norm_num)
    (by rw [Function.update_of_ne (by omega)]; exact h8)
    (by rw [Function.update_of_ne (by omega)]; exact hmy)
    (by rw [Function.update_of_ne (by omega)]; exact h1) (by simp)
  have e₃ := ev_lt (S := S) hS hc' ha hb
  exact (EvQ.seq e₁ (EvQ.seq e₂ e₃)).mono (by omega)

/-! ### Variables and literals -/

/-- Read a variable: an out-of-range index is known at compile time and gives the word of zero. -/
def varC (S : ℕ) [NeZero S] (j : ℕ) (map : List ℕ) (t : ℕ) : Cmd 10 S :=
  match map[j]? with
  | some s => copyC S (11 + s) (11 + t)
  | none => copyC S 10 (11 + t)

private theorem forall₂_lookup {R : ℕ → ℕ → Prop} {map env : List ℕ} (h : List.Forall₂ R map env) (j : ℕ) :
    (∃ s x, map[j]? = some s ∧ env[j]? = some x ∧ R s x) ∨ (map[j]? = none ∧ env[j]? = none) := by
  induction h generalizing j with
  | nil => exact Or.inr ⟨rfl, rfl⟩
  | @cons a b l₁ l₂ hr _ ih =>
    cases j with
    | zero => exact Or.inl ⟨a, b, rfl, rfl, hr⟩
    | succ j => simpa using ih j

theorem correct_var {W : ℕ} (j : ℕ) : Correct (S := S) W (.var j) (varC S j) := by
  intro map env t m hg ht
  simp only [stack] at ht
  have hc := hg.clean
  have hdst := hg.empty t le_rfl
  have hsrc : ∃ src, varC S j map t = copyC S src (11 + t) ∧ src < 11 + t ∧ src ≠ 8 ∧
      m src = wordOf W (env.getD j 0) := by
    rcases forall₂_lookup hg.vars j with ⟨s, x, h₁, h₂, hs, hm, hx⟩ | ⟨h₁, h₂⟩
    · refine ⟨11 + s, by simp [varC, h₁], by omega, by omega, ?_⟩
      simp [List.getD_eq_getElem?_getD, h₂, hm]
    · refine ⟨10, by simp [varC, h₁], by omega, by norm_num, ?_⟩
      simp [List.getD_eq_getElem?_getD, h₂, wordOf_zero, hc.ruler]
  obtain ⟨src, hC, hlt, hs8, hm⟩ := hsrc
  rw [hC]
  have e := ev_copy' (S := S) (src := src) (dst := 11 + t) (L := W) (m := m) (x := wordOf W (env.getD j 0))
    (by omega) (by omega) (by omega) (by omega) hs8 (by omega) hc.w8 hm hdst (by simp)
  have ho : ops W (.var j) env * T W = T W := by simp [ops]
  rw [ho]
  simp only [eval]
  refine (go_routine e hg.small ?_).mono ?_ <;> (have := square_ge W; simp only [T]; omega)

/-- Write a literal to a slot. -/
def litE (S : ℕ) [NeZero S] (n : ℕ) (_map : List ℕ) (t : ℕ) : Cmd 10 S :=
  .seq (litCore S n) (mvC S 0 (11 + t))

theorem correct_lit {W : ℕ} (n : ℕ) : Correct (S := S) W (.lit n) (litE S n) := by
  intro map env t m hg ht
  simp only [stack] at ht
  have hc := hg.clean
  have hdst := hg.empty t le_rfl
  have e₁ := ev_lit (S := S) (by omega) hc n
  have e₂ := ev_mv (S := S) (src := 0) (dst := 11 + t) (L := W) (m := Function.update m 0 (wordOf W (n % 2 ^ W)))
    (x := wordOf W (n % 2 ^ W)) (by omega) (by omega) (by omega) (by omega) (by norm_num) (by omega)
    (by rw [Function.update_of_ne (by omega)]; exact hc.w8) (by simp)
    (by rw [Function.update_of_ne (by omega)]; exact hdst) (by simp)
  have hmem : Function.update (Function.update (Function.update m 0 (wordOf W (n % 2 ^ W))) (11 + t)
      (wordOf W (n % 2 ^ W))) 0 [] = Function.update m (11 + t) (wordOf W (n % 2 ^ W)) := by
    have := hc.w0
    mem_eq'
  rw [hmem] at e₂
  have ho : ops W (.lit n) env * T W = T W := by simp [ops]
  rw [ho]
  simp only [eval]
  refine (go_routine (EvQ.seq e₁ e₂) hg.small ?_).mono ?_ <;> (have := square_ge W; simp only [T]; omega)

/-! ### Binary and unary operations -/

/-- Evaluate two operands to the slots `t` and `t + 1`, then apply a routine. -/
def binE (S : ℕ) [NeZero S] (core : Cmd 10 S) (Ca Cb : List ℕ → ℕ → Cmd 10 S) (map : List ℕ) (t : ℕ) : Cmd 10 S :=
  .seq (Ca map t) (.seq (Cb map (t + 1)) (binC S core (11 + t) (11 + (t + 1))))

theorem correct_bin {W tc : ℕ} {core : Cmd 10 S} {E a b : Expr} {Ca Cb : List ℕ → ℕ → Cmd 10 S} (val : ℕ → ℕ → ℕ)
    (hcore : ∀ m₀ x y, Clean W m₀ → x < 2 ^ W → y < 2 ^ W →
      Ev core (Function.update (Function.update m₀ 0 (wordOf W x)) 1 (wordOf W y))
        (Function.update m₀ 0 (wordOf W (val x y))) tc)
    (hval : ∀ env, eval W E env = val (eval W a env) (eval W b env))
    (hops : ∀ env, ops W E env = 1 + ops W a env + ops W b env)
    (hstack : stack E = max (stack a) (1 + stack b))
    (htc : tc + 3 * (9 * W + 8) ≤ T W)
    (ha : Correct W a Ca) (hb : Correct W b Cb) : Correct W E (binE S core Ca Cb) := by
  intro map env t m hg ht
  have hs1 := le_max_left (stack a) (1 + stack b)
  have hs2 := le_max_right (stack a) (1 + stack b)
  have hsp := stack_pos b
  rw [hstack] at ht
  have henv := hg.env_lt
  have hA := eval_lt_word W a env henv
  have hB := eval_lt_word W b env henv
  have g₁ := ha map env t m hg (by omega)
  have hg₁ : Good W map env (t + 1) (Function.update m (11 + t) (wordOf W (eval W a env))) := hg.step
  have g₂ := hb map env (t + 1) _ hg₁ (by omega)
  set M := Function.update (Function.update m (11 + t) (wordOf W (eval W a env))) (11 + (t + 1))
    (wordOf W (eval W b env)) with hM
  have hg₂ : Good W map env (t + 1 + 1) M := hg₁.step
  have hne : 11 + t ≠ 11 + (t + 1) := by omega
  have hmem₀ : Function.update (Function.update M (11 + t) []) (11 + (t + 1)) [] = m := by
    have h₁ := hg.empty t le_rfl
    have h₂ := hg.empty (t + 1) (by omega)
    simp only [hM]
    mem_eq'
  have e := ev_bin (S := S) (W := W) (x := 11 + t) (y := 11 + (t + 1)) (wa := wordOf W (eval W a env))
    (wb := wordOf W (eval W b env)) (wr := wordOf W (val (eval W a env) (eval W b env))) (m := M)
    (core := core) (tc := tc) (by omega) (by omega) (by omega) (by omega) (by omega) hne hg₂.clean
    (by simp [hM, Function.update_apply]) (by simp [hM]) (by simp) (by simp) (by simp)
    (by rw [hmem₀]; exact hcore m _ _ hg.clean hA hB)
  have hmem : Function.update (Function.update M (11 + t) (wordOf W (val (eval W a env) (eval W b env))))
      (11 + (t + 1)) [] = Function.update m (11 + t) (wordOf W (eval W E env)) := by
    have h₂ := hg.empty (t + 1) (by omega)
    rw [hval]
    simp only [hM]
    mem_eq'
  rw [hmem] at e
  have g₃ := go_routine e hg₂.small htc
  have hcost : ops W E env * T W = T W + ops W a env * T W + ops W b env * T W := by
    rw [hops]
    ring
  rw [hcost]
  exact (GoQ.seq g₁ (GoQ.seq g₂ g₃)).mono (by omega)

/-- Evaluate an operand to the slot `t`, then apply a unary routine. -/
def unE (S : ℕ) [NeZero S] (core : Cmd 10 S) (Ca : List ℕ → ℕ → Cmd 10 S) (map : List ℕ) (t : ℕ) : Cmd 10 S :=
  .seq (Ca map t) (unC S core (11 + t))

theorem correct_pow2 {W : ℕ} {a : Expr} {Ca : List ℕ → ℕ → Cmd 10 S} (hS : 11 ≤ S)
    (ha : Correct W a Ca) : Correct W (.pow2 a) (unE S (powCore S) Ca) := by
  intro map env t m hg ht
  simp only [stack] at ht
  have hsp := stack_pos a
  have henv := hg.env_lt
  have hA := eval_lt_word W a env henv
  have g₁ := ha map env t m hg ht
  have hg₁ : Good W map env (t + 1) (Function.update m (11 + t) (wordOf W (eval W a env))) := hg.step
  have hc := hg₁.clean
  have hmem₀ : Function.update (Function.update m (11 + t) (wordOf W (eval W a env))) (11 + t) [] = m := by
    have h₁ := hg.empty t le_rfl
    mem_eq'
  have e := ev_un (S := S) (W := W) (x := 11 + t) (wa := wordOf W (eval W a env))
    (wr := wordOf W (if eval W a env < W then 2 ^ eval W a env else 0))
    (m := Function.update m (11 + t) (wordOf W (eval W a env))) (core := powCore S)
    (tc := 41 * (W + 1) ^ 2 + 60 * (W + 1) + 60) hS (by omega) (by omega) hc (by simp) (by simp) (by simp)
    (by rw [hmem₀]; exact ev_pow hS hg.clean hA)
  have hmem : Function.update (Function.update m (11 + t) (wordOf W (eval W a env))) (11 + t)
      (wordOf W (if eval W a env < W then 2 ^ eval W a env else 0)) =
      Function.update m (11 + t) (wordOf W (eval W (.pow2 a) env)) := by
    simp [eval]
  rw [hmem] at e
  have g₃ := go_routine e hg₁.small (by have := square_ge W; simp only [T]; omega)
  have hcost : ops W (.pow2 a) env * T W = T W + ops W a env * T W := by
    simp only [ops]
    ring
  rw [hcost]
  refine (GoQ.seq g₁ g₃).mono ?_
  have := square_ge W
  simp only [T] at *
  omega

end TransposeBase.Machine
