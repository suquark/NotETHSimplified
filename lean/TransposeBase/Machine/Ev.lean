import FormalizationKit.StackCalls
import FormalizationKit.MachineCallFrames
import TransposeBase.Machine.Words

/-!
# Executions on stacks indexed by natural numbers

A command runs on `Fin S` stacks. The proofs describe memory as a function on `ℕ`, and `view` restricts it
to `Fin S`, so a memory update is a `Function.update` at a number and a frame goal is arithmetic. `Ev c m m' t`
says that `c`, from any registers, takes the memory `m` to `m'` in at most `t` instructions.
-/

set_option linter.unusedSectionVars false

namespace TransposeBase.Machine

open OAI.Algorithms.SubexponentialSAT
open BitProgram StructuredCalls
open FormalizationKit

/-- Memory: every stack, by number. Only the numbers below `S` matter. -/
abbrev Mem := ℕ → List Bool

/-- Registers of the compiled program. -/
abbrev Regs := Fin 10 → Bool

variable {S : ℕ} [NeZero S]

/-- The stack with number `i`. -/
def F (S : ℕ) [NeZero S] (i : ℕ) : Fin S := Fin.ofNat S i

theorem F_val {i : ℕ} (h : i < S) : (F S i).val = i := Nat.mod_eq_of_lt h

/-- The stacks of a memory. -/
def view (S : ℕ) (m : Mem) : Fin S → List Bool := fun i => m i.val

theorem view_F (m : Mem) {i : ℕ} (h : i < S) : view S m (F S i) = m i := by
  simp [view, F_val h]

theorem F_ne {i j : ℕ} (hi : i < S) (hj : j < S) (h : i ≠ j) : F S i ≠ F S j := by
  intro e
  have := congrArg Fin.val e
  rw [F_val hi, F_val hj] at this
  exact h this

theorem view_update {i : ℕ} (h : i < S) (m : Mem) (x : List Bool) :
    view S (Function.update m i x) = Function.update (view S m) (F S i) x := by
  funext j
  by_cases hj : j = F S i
  · subst hj
    simp [view, F_val h]
  · have hv : j.val ≠ i := fun e => hj (Fin.ext (by rw [F_val h]; exact e))
    simp [view, Function.update_of_ne hj, Function.update_of_ne hv]

/-- `c` takes the memory `m` to `m'` in at most `t` instructions, from any registers, and the final
registers satisfy `Q`. -/
def EvQ (c : Cmd 10 S) (m m' : Mem) (t : ℕ) (Q : Regs → Prop) : Prop :=
  ∀ regs : Regs, ∃ n rf, Eval c n ⟨regs, view S m⟩ ⟨rf, view S m'⟩ ∧ n ≤ t ∧ Q rf

/-- `EvQ` without a condition on the final registers. -/
abbrev Ev (c : Cmd 10 S) (m m' : Mem) (t : ℕ) : Prop := EvQ c m m' t fun _ => True

theorem EvQ.mono {c : Cmd 10 S} {m m' : Mem} {t t' : ℕ} {Q : Regs → Prop}
    (h : EvQ c m m' t Q) (ht : t ≤ t') : EvQ c m m' t' Q := fun regs => by
  obtain ⟨n, rf, he, hn, hq⟩ := h regs
  exact ⟨n, rf, he, hn.trans ht, hq⟩

theorem EvQ.weaken {c : Cmd 10 S} {m m' : Mem} {t : ℕ} {Q : Regs → Prop}
    (h : EvQ c m m' t Q) : Ev c m m' t := fun regs => by
  obtain ⟨n, rf, he, hn, _⟩ := h regs
  exact ⟨n, rf, he, hn, trivial⟩

theorem EvQ.seq {c₁ c₂ : Cmd 10 S} {m₀ m₁ m₂ : Mem} {t₁ t₂ : ℕ} {Q : Regs → Prop}
    (h₁ : Ev c₁ m₀ m₁ t₁) (h₂ : EvQ c₂ m₁ m₂ t₂ Q) : EvQ (.seq c₁ c₂) m₀ m₂ (t₁ + t₂) Q := fun regs => by
  obtain ⟨n₁, r₁, e₁, b₁, _⟩ := h₁ regs
  obtain ⟨n₂, r₂, e₂, b₂, hq⟩ := h₂ r₁
  exact ⟨n₁ + n₂, r₂, e₁.seq e₂, by omega, hq⟩

/-- A test, then a branch on its register. -/
theorem EvQ.ite {c y n : Cmd 10 S} {f : Fin 10} {v : Bool} {m₀ m₁ m₂ : Mem} {t₁ t₂ : ℕ}
    {Q : Regs → Prop} (h : EvQ c m₀ m₁ t₁ fun r => r f = v)
    (hy : v = true → EvQ y m₁ m₂ t₂ Q) (hn : v = false → EvQ n m₁ m₂ t₂ Q) :
    EvQ (.seq c (.ite f y n)) m₀ m₂ (t₁ + (t₂ + 1)) Q := fun regs => by
  obtain ⟨n₁, r₁, e₁, b₁, hr⟩ := h regs
  cases hv : v
  · obtain ⟨n₂, r₂, e₂, b₂, hq⟩ := hn hv r₁
    exact ⟨n₁ + (n₂ + 1), r₂, e₁.seq (.ite_false (by simpa [hv] using hr) e₂), by omega, hq⟩
  · obtain ⟨n₂, r₂, e₂, b₂, hq⟩ := hy hv r₁
    exact ⟨n₁ + (n₂ + 1), r₂, e₁.seq (.ite_true (by simpa [hv] using hr) e₂), by omega, hq⟩

/-- A loop whose guard is true exactly below `N`. -/
theorem ev_while {test : Fin 10} {body : Cmd 10 S} (M : ℕ → Mem) (N τ : ℕ)
    (h : ∀ k < N, EvQ body (M k) (M (k + 1)) τ fun r => r test = decide (k + 1 < N)) :
    ∀ k ≤ N, ∀ regs : Regs, regs test = decide (k < N) →
      ∃ n rf, Eval (.while test body) n ⟨regs, view S (M k)⟩ ⟨rf, view S (M N)⟩ ∧
        n ≤ (N - k) * (τ + 1) + 1 := by
  intro k hk
  induction hd : N - k generalizing k with
  | zero =>
    have hkN : k = N := by omega
    subst hkN
    intro regs hr
    exact ⟨1, regs, .while_false (by simpa using hr), by simp⟩
  | succ d ih =>
    intro regs hr
    have hlt : k < N := by omega
    obtain ⟨n₁, r₁, e₁, b₁, hg⟩ := h k hlt regs
    obtain ⟨n₂, r₂, e₂, b₂⟩ := ih (k + 1) (by omega) (by omega) r₁ hg
    refine ⟨n₁ + n₂ + 1, r₂, .while_true (by simpa [hlt] using hr) e₁ e₂, ?_⟩
    rw [add_mul]
    omega

/-! ### One-instruction commands -/

theorem ev_atom (a : StructuredProgram.Atom 10 S) {m m' : Mem} {Q : Regs → Prop}
    (hs : ∀ regs : Regs, (a.eval ⟨regs, view S m⟩).stacks = view S m')
    (hq : ∀ regs : Regs, Q (a.eval ⟨regs, view S m⟩).regs) :
    EvQ (.base (.atom a)) m m' 1 Q := fun regs => by
  refine ⟨1, (a.eval ⟨regs, view S m⟩).regs, ?_, le_rfl, hq regs⟩
  have he := Eval.base (StructuredProgram.Eval.atom a (⟨regs, view S m⟩ : State 10 S))
  have hrw : a.eval ⟨regs, view S m⟩ = ⟨(a.eval ⟨regs, view S m⟩).regs, view S m'⟩ := by
    rw [← hs regs]
  rwa [hrw] at he

/-- Push the value `b` on stack `s`. -/
def pushB (S : ℕ) [NeZero S] (s : ℕ) (b : Bool) : Cmd 10 S :=
  .seq (.base (.atom (.set 0 b))) (.base (.atom (.push (F S s) 0)))

theorem ev_pushB {s : ℕ} (hs : s < S) (b : Bool) (m : Mem) :
    Ev (pushB S s b) m (Function.update m s (b :: m s)) 2 := fun regs => by
  have he : Eval (pushB S s b) 2 ⟨regs, view S m⟩
      ⟨Function.update regs 0 b, view S (Function.update m s (b :: m s))⟩ := by
    have e₁ := Eval.base (StructuredProgram.Eval.atom (.set 0 b) (⟨regs, view S m⟩ : State 10 S))
    have e₂ := Eval.base (StructuredProgram.Eval.atom (.push (F S s) 0)
      (StructuredProgram.Atom.eval (.set 0 b) (⟨regs, view S m⟩ : State 10 S)))
    have hstate : StructuredProgram.Atom.eval (.push (F S s) 0)
        (StructuredProgram.Atom.eval (.set 0 b) (⟨regs, view S m⟩ : State 10 S)) =
        ⟨Function.update regs 0 b, view S (Function.update m s (b :: m s))⟩ := by
      simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, execInstr,
        StructuredProgram.State.ofCfg, view_update hs, view_F m hs]
    have := e₁.seq e₂
    rw [hstate] at this
    exact this
  exact ⟨2, _, he, le_rfl, trivial⟩

/-- Pop stack `s` into the registers `0` (value) and `1` (present). -/
def popC (S : ℕ) [NeZero S] (s : ℕ) : Cmd 10 S := .base (.atom (.pop (F S s) 0 1))

theorem ev_pop {s : ℕ} (hs : s < S) (m : Mem) :
    EvQ (popC S s) m (Function.update m s (m s).tail) 1
      fun rf => rf 0 = (m s).head?.getD false ∧ rf 1 = (m s).head?.isSome := by
  refine ev_atom _ (fun regs => ?_) (fun regs => ?_)
  · simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, execInstr,
      StructuredProgram.State.ofCfg, view_F m hs, view_update hs]
  · simp only [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, execInstr,
      StructuredProgram.State.ofCfg, view_F m hs]
    constructor
    · exact readRegs_value _ _ _ _ (by decide)
    · exact readRegs_present _ _ _ _

/-! ### Stack routines -/

/-- Prefix a copy of the stack `src` to the stack `dst`. The stack `8` is its scratch stack. -/
def copyC (S : ℕ) [NeZero S] (src dst : ℕ) : Cmd 10 S := StackCalls.copyCall (F S src) (F S dst) (F S 8)

def clearC (S : ℕ) [NeZero S] (i : ℕ) : Cmd 10 S := StackCalls.clearCall (F S i)

/-- Pop the stack `src` onto the stack `dst`. -/
def xferC (S : ℕ) [NeZero S] (src dst : ℕ) : Cmd 10 S := StackCalls.transferCall (F S src) (F S dst)

theorem ev_copy {src dst : ℕ} (hsrc : src < S) (hdst : dst < S) (h8 : 8 < S) (hne : src ≠ dst)
    (hs8 : src ≠ 8) (hd8 : dst ≠ 8) {m : Mem} (hm : m 8 = []) :
    Ev (copyC S src dst) m (Function.update m dst (m src ++ m dst)) (7 * (m src).length + 5) := fun regs => by
  have he := StackCalls.copy_eval (F S src) (F S dst) (F S 8) (F_ne hsrc hdst hne)
    (F_ne hsrc h8 hs8) (F_ne h8 hdst hd8.symm) regs (view S m) (by rw [view_F m h8, hm])
  have hv : StackRoutines.copyStacks (F S src) (F S dst) (view S m) =
      view S (Function.update m dst (m src ++ m dst)) := by
    rw [view_update hdst, StackRoutines.copyStacks, view_F m hsrc, view_F m hdst]
  rw [hv] at he
  exact ⟨_, _, he, by rw [view_F m hsrc], trivial⟩

theorem ev_clear {i : ℕ} (hi : i < S) (m : Mem) :
    Ev (clearC S i) m (Function.update m i []) (2 * (m i).length + 3) := fun regs => by
  have he := StackCalls.clear_eval (F S i) regs (view S m)
  have hv : StackRoutines.clearStacks (F S i) (view S m) = view S (Function.update m i []) := by
    rw [view_update hi]
  rw [hv] at he
  exact ⟨_, _, he, by rw [view_F m hi], trivial⟩

theorem ev_xfer {src dst : ℕ} (hsrc : src < S) (hdst : dst < S) (hne : src ≠ dst) (m : Mem) :
    Ev (xferC S src dst) m (Function.update (Function.update m src []) dst ((m src).reverse ++ m dst))
      (3 * (m src).length + 3) := fun regs => by
  have he := StackCalls.transfer_eval (F S src) (F S dst) (F_ne hsrc hdst hne) regs (view S m)
  have hv : StackRoutines.transferStacks (F S src) (F S dst) (view S m) =
      view S (Function.update (Function.update m src []) dst ((m src).reverse ++ m dst)) := by
    rw [view_update hdst, view_update hsrc, StackRoutines.transferStacks, view_F m hsrc,
      view_F m hdst]
  rw [hv] at he
  exact ⟨_, _, he, by rw [view_F m hsrc], trivial⟩

/-! ### Calls of fixed programs on fixed stacks -/

/-- Call a fixed smaller program; its stacks are placed at the given numbers. -/
def liftC (S : ℕ) [NeZero S] {r s l : ℕ} (hr : r ≤ 10) (q : Program r s l) (ports : Fin s → ℕ) : Cmd 10 S :=
  .call (ProgramLinking.liftProgram q (Fin.castLE hr) fun j => F S (ports j))

/-- A call from one register state. -/
theorem ev_lift_at {r s l : ℕ} (hr : r ≤ 10) (q : Program r s l) (ports : Fin s → ℕ)
    (hinj : Function.Injective ports) (hlt : ∀ j, ports j < S) {m m' : Mem}
    (hfr : ∀ i, (∀ j, ports j ≠ i) → m' i = m i) {t : ℕ} {Q : (Fin r → Bool) → Prop} (regs : Regs)
    (hrun : ∃ rf n, n ≤ t ∧
      Trace q n ⟨some q.entry, regs ∘ Fin.castLE hr, fun j => m (ports j)⟩
        ⟨none, rf, fun j => m' (ports j)⟩ ∧ Q rf) :
    ∃ n rf, Eval (liftC S hr q ports) n ⟨regs, view S m⟩ ⟨rf, view S m'⟩ ∧ n ≤ t ∧
      Q (rf ∘ Fin.castLE hr) := by
  obtain ⟨rf, n, hn, ht, hq⟩ := hrun
  have hrinj : Function.Injective (Fin.castLE hr) := Fin.castLE_injective hr
  have hsinj : Function.Injective fun j => F S (ports j) := by
    intro a b h
    apply hinj
    have := congrArg Fin.val h
    simpa only [F_val (hlt a), F_val (hlt b)] using this
  have he := MachineCallFrames.eval_lifted_frame q (Fin.castLE hr) (fun j => F S (ports j)) hrinj hsinj
    (localStart := ⟨regs ∘ Fin.castLE hr, fun j => m (ports j)⟩)
    (localFinish := ⟨rf, fun j => m' (ports j)⟩) ht
    (⟨regs, view S m⟩ : State 10 S)
    (⟨Function.extend (Fin.castLE hr) rf regs, view S m'⟩ : State 10 S)
    (fun _ => rfl) (fun j => view_F m (hlt j))
    (fun i => hrinj.extend_apply _ _ _) (fun j => view_F m' (hlt j))
    (fun i hi => Function.extend_apply' _ _ _ hi)
    (fun i hi => hfr i.val fun j e => hi ⟨j, Fin.ext (by rw [F_val (hlt j)]; exact e)⟩)
  refine ⟨n, _, he, hn, ?_⟩
  have hc : Function.extend (Fin.castLE hr) rf regs ∘ Fin.castLE hr = rf := by
    funext i
    exact hrinj.extend_apply _ _ _
  rw [hc]
  exact hq

theorem ev_lift {r s l : ℕ} (hr : r ≤ 10) (q : Program r s l) (ports : Fin s → ℕ)
    (hinj : Function.Injective ports) (hlt : ∀ j, ports j < S) {m m' : Mem}
    (hfr : ∀ i, (∀ j, ports j ≠ i) → m' i = m i) {t : ℕ} {Q : (Fin r → Bool) → Prop}
    (hrun : ∀ regs : Fin r → Bool, ∃ rf n, n ≤ t ∧
      Trace q n ⟨some q.entry, regs, fun j => m (ports j)⟩ ⟨none, rf, fun j => m' (ports j)⟩ ∧ Q rf) :
    EvQ (liftC S hr q ports) m m' t fun rf => Q (rf ∘ Fin.castLE hr) := fun regs =>
  ev_lift_at hr q ports hinj hlt hfr regs (hrun _)

theorem ev_eq {c : Cmd 10 S} {m m' m'' : Mem} {t : ℕ} {Q : Regs → Prop} (h : EvQ c m m' t Q)
    (e : m' = m'') : EvQ c m m'' t Q := e ▸ h

theorem EvQ.mapQ {c : Cmd 10 S} {m m' : Mem} {t : ℕ} {Q Q' : Regs → Prop} (h : EvQ c m m' t Q)
    (hq : ∀ r, Q r → Q' r) : EvQ c m m' t Q' := fun regs => by
  obtain ⟨n, rf, he, hn, q⟩ := h regs
  exact ⟨n, rf, he, hn, hq _ q⟩

theorem ev_skip (m : Mem) : Ev (S := S) (.base .skip) m m 0 := fun regs =>
  ⟨0, regs, .base (.skip _), le_rfl, trivial⟩

/-- Copy with known contents and a bound on the length. -/
theorem ev_copy' {src dst L : ℕ} (hsrc : src < S) (hdst : dst < S) (h8 : 8 < S) (hne : src ≠ dst)
    (hs8 : src ≠ 8) (hd8 : dst ≠ 8) {m : Mem} (hm : m 8 = []) {x : List Bool}
    (hx : m src = x) (hd : m dst = []) (hL : x.length ≤ L) :
    Ev (copyC S src dst) m (Function.update m dst x) (7 * L + 5) := by
  have := ev_copy hsrc hdst h8 hne hs8 hd8 hm
  rw [hx, hd, List.append_nil] at this
  exact this.mono (by omega)

theorem ev_clear' {i L : ℕ} (hi : i < S) (m : Mem) (hL : (m i).length ≤ L) :
    Ev (clearC S i) m (Function.update m i []) (2 * L + 3) :=
  (ev_clear hi m).mono (by omega)

/-- Move a word: copy, then clear the source. -/
def mvC (S : ℕ) [NeZero S] (src dst : ℕ) : Cmd 10 S := .seq (copyC S src dst) (clearC S src)

theorem ev_mv {src dst L : ℕ} (hsrc : src < S) (hdst : dst < S) (h8 : 8 < S) (hne : src ≠ dst)
    (hs8 : src ≠ 8) (hd8 : dst ≠ 8) {m : Mem} (hm : m 8 = []) {x : List Bool}
    (hx : m src = x) (hd : m dst = []) (hL : x.length ≤ L) :
    Ev (mvC S src dst) m (Function.update (Function.update m dst x) src []) (9 * L + 8) := by
  refine (EvQ.seq (ev_copy' hsrc hdst h8 hne hs8 hd8 hm hx hd hL)
    (ev_clear' hsrc _ (L := L) ?_)).mono (by omega)
  rw [Function.update_of_ne hne, hx]
  exact hL

end TransposeBase.Machine
