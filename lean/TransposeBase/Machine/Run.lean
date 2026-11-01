import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace
import OAI.Algorithms.SubexponentialSAT.BitProgramSelectedSpace
import TransposeBase.Machine.Bits

/-!
# Executions with a bound on every prefix

`RunN B c n a b` is an execution of `c` in `n` instructions from `a` to `b` in which, on every prefix of the
compiled program, every stack has at most `B` bits. The bound is proved through the structure of the command:
sequence, conditional and loop keep the same `B`, and only a whole routine with a polynomial number of steps
uses the local estimate "bits at the start of the routine + steps of the routine" (`RunN.of_eval`). So the
bound does not grow with the number of loop iterations.
-/

set_option linter.unusedSectionVars false

namespace TransposeBase.Machine

open OAI.Algorithms.SubexponentialSAT
open BitProgram StructuredCalls
open SqrtLogSpace.StructuredSpace

variable {S : ℕ} [NeZero S]

/-- Every prefix of the compiled program of `c`, from `a`, for at most `n` instructions, has all stacks
of length at most `B`. -/
def Prefix (B : ℕ) (c : Cmd 10 S) (a : State 10 S) (n : ℕ) : Prop :=
  ∀ (ip op : Fin S) (k : ℕ) (x : Cfg 10 S (size c + 1)), k ≤ n →
    Trace (compiled c ip op) k (a.withPC (some (compiled c ip op).entry)) x →
    ∀ i, (x.stacks i).length ≤ B

structure RunN (B : ℕ) (c : Cmd 10 S) (n : ℕ) (a b : State 10 S) : Prop where
  eval : Eval c n a b
  pref : Prefix B c a n

/-- A whole routine: the stacks grow by at most one bit per instruction. -/
theorem RunN.of_eval {B L n : ℕ} {c : Cmd 10 S} {a b : State 10 S} (he : Eval c n a b)
    (hs : ∀ i, (a.stacks i).length ≤ L) (hB : L + n ≤ B) : RunN B c n a b := by
  refine ⟨he, fun ip op k x hk ht i => ?_⟩
  have hg := trace_selectedStackBits (compiled c ip op) {i} ht
  simp only [selectedStackBits, Finset.sum_singleton] at hg
  have ha := hs i
  change (x.stacks i).length ≤ (a.stacks i).length + k at hg
  omega

theorem RunN.seq {B n₁ n₂ : ℕ} {c₁ c₂ : Cmd 10 S} {a b d : State 10 S}
    (h₁ : RunN B c₁ n₁ a b) (h₂ : RunN B c₂ n₂ b d) : RunN B (.seq c₁ c₂) (n₁ + n₂) a d :=
  ⟨h₁.eval.seq h₂.eval, fun ip op =>
    sequence_stack_bound h₁.eval h₂.eval ip op (h₁.pref ip op) (h₂.pref ip op) _ _ _
      (compiled_site _ ip op)⟩

theorem RunN.ite_true {B n : ℕ} {f : Fin 10} {y no : Cmd 10 S} {a b : State 10 S}
    (hf : a.regs f = true) (h : RunN B y n a b) : RunN B (.ite f y no) (n + 1) a b :=
  ⟨.ite_true hf h.eval, fun ip op =>
    conditional_true_stack_bound hf h.eval ip op (h.pref ip op) _ _ _ (compiled_site _ ip op)⟩

theorem RunN.ite_false {B n : ℕ} {f : Fin 10} {y no : Cmd 10 S} {a b : State 10 S}
    (hf : a.regs f = false) (h : RunN B no n a b) : RunN B (.ite f y no) (n + 1) a b :=
  ⟨.ite_false hf h.eval, fun ip op =>
    conditional_false_stack_bound hf h.eval ip op (h.pref ip op) _ _ _ (compiled_site _ ip op)⟩

theorem RunN.while_false {B : ℕ} {f : Fin 10} {body : Cmd 10 S} {a : State 10 S}
    (hf : a.regs f = false) (hs : ∀ i, (a.stacks i).length ≤ B) : RunN B (.while f body) 1 a a :=
  ⟨.while_false hf, fun ip op =>
    while_false_stack_bound body f a hf hs _ _ _ (compiled_site _ ip op)⟩

theorem RunN.while_true {B n m : ℕ} {f : Fin 10} {body : Cmd 10 S} {a b d : State 10 S}
    (hf : a.regs f = true) (h₁ : RunN B body n a b) (h₂ : RunN B (.while f body) m b d) :
    RunN B (.while f body) (n + m + 1) a d :=
  ⟨.while_true hf h₁.eval h₂.eval, fun ip op =>
    while_true_stack_bound hf h₁.eval h₂.eval ip op (h₁.pref ip op) (h₂.pref ip op) _ _ _
      (compiled_site _ ip op)⟩

/-! ### The judgement on memories -/

/-- `c` takes `m` to `m'` in at most `t` instructions, from any registers, with all stacks of length at most
`B` on every prefix. The final registers satisfy `Q`. -/
def GoQ (B : ℕ) (c : Cmd 10 S) (m m' : Mem) (t : ℕ) (Q : Regs → Prop) : Prop :=
  ∀ regs : Regs, ∃ n rf, RunN B c n ⟨regs, view S m⟩ ⟨rf, view S m'⟩ ∧ n ≤ t ∧ Q rf

abbrev Go (B : ℕ) (c : Cmd 10 S) (m m' : Mem) (t : ℕ) : Prop := GoQ B c m m' t fun _ => True

theorem GoQ.of_ev {B L t : ℕ} {c : Cmd 10 S} {m m' : Mem} {Q : Regs → Prop} (h : EvQ c m m' t Q)
    (hs : ∀ i, (m i).length ≤ L) (hB : L + t ≤ B) : GoQ B c m m' t Q := fun regs => by
  obtain ⟨n, rf, he, hn, hq⟩ := h regs
  exact ⟨n, rf, RunN.of_eval he (fun i => hs i.val) (by omega), hn, hq⟩

theorem GoQ.mono {B t t' : ℕ} {c : Cmd 10 S} {m m' : Mem} {Q : Regs → Prop} (h : GoQ B c m m' t Q)
    (ht : t ≤ t') : GoQ B c m m' t' Q := fun regs => by
  obtain ⟨n, rf, he, hn, hq⟩ := h regs
  exact ⟨n, rf, he, hn.trans ht, hq⟩

theorem GoQ.seq {B t₁ t₂ : ℕ} {c₁ c₂ : Cmd 10 S} {m₀ m₁ m₂ : Mem} {Q : Regs → Prop}
    (h₁ : Go B c₁ m₀ m₁ t₁) (h₂ : GoQ B c₂ m₁ m₂ t₂ Q) : GoQ B (.seq c₁ c₂) m₀ m₂ (t₁ + t₂) Q := fun regs => by
  obtain ⟨n₁, r₁, e₁, b₁, _⟩ := h₁ regs
  obtain ⟨n₂, r₂, e₂, b₂, hq⟩ := h₂ r₁
  exact ⟨n₁ + n₂, r₂, e₁.seq e₂, by omega, hq⟩

theorem GoQ.ite {B t₁ t₂ : ℕ} {c y no : Cmd 10 S} {f : Fin 10} {v : Bool} {m₀ m₁ m₂ : Mem} {Q : Regs → Prop}
    (h : GoQ B c m₀ m₁ t₁ fun r => r f = v) (hy : v = true → GoQ B y m₁ m₂ t₂ Q)
    (hn : v = false → GoQ B no m₁ m₂ t₂ Q) :
    GoQ B (.seq c (.ite f y no)) m₀ m₂ (t₁ + (t₂ + 1)) Q := fun regs => by
  obtain ⟨n₁, r₁, e₁, b₁, hr⟩ := h regs
  cases hv : v
  · obtain ⟨n₂, r₂, e₂, b₂, hq⟩ := hn hv r₁
    exact ⟨n₁ + (n₂ + 1), r₂, e₁.seq (.ite_false (by simpa [hv] using hr) e₂), by omega, hq⟩
  · obtain ⟨n₂, r₂, e₂, b₂, hq⟩ := hy hv r₁
    exact ⟨n₁ + (n₂ + 1), r₂, e₁.seq (.ite_true (by simpa [hv] using hr) e₂), by omega, hq⟩

/-- The loop rule. The memories `M k` are the loop invariant at the guard. The body takes `M k` to `M (k + 1)`
under the same bound `B`, and the potential `Φ` pays for the instructions. -/
theorem go_while {B : ℕ} {test : Fin 10} {body : Cmd 10 S} (M : ℕ → Mem) (N : ℕ) (Φ τ : ℕ → ℕ)
    (h : ∀ k < N, GoQ B body (M k) (M (k + 1)) (τ k) fun r => r test = decide (k + 1 < N))
    (hΦ : ∀ k < N, Φ k + τ k + 1 ≤ Φ (k + 1)) (hs : ∀ i, (M N i).length ≤ B) :
    ∀ k ≤ N, ∀ regs : Regs, regs test = decide (k < N) →
      ∃ n rf, RunN B (.while test body) n ⟨regs, view S (M k)⟩ ⟨rf, view S (M N)⟩ ∧ Φ k + n ≤ Φ N + 1 := by
  intro k hk
  induction hd : N - k generalizing k with
  | zero =>
    have hkN : k = N := by omega
    subst hkN
    intro regs hr
    exact ⟨1, regs, RunN.while_false (by simpa using hr) (fun i => hs i.val), le_rfl⟩
  | succ d ih =>
    intro regs hr
    have hlt : k < N := by omega
    obtain ⟨n₁, r₁, e₁, b₁, hg⟩ := h k hlt regs
    obtain ⟨n₂, r₂, e₂, b₂⟩ := ih (k + 1) (by omega) (by omega) r₁ hg
    have := hΦ k hlt
    exact ⟨n₁ + n₂ + 1, r₂, RunN.while_true (by simpa [hlt] using hr) e₁ e₂, by omega⟩

/-- Initialize, then loop. -/
theorem go_for {B t₀ t : ℕ} {test : Fin 10} {g body : Cmd 10 S} {m : Mem} (M : ℕ → Mem) (N : ℕ) (Φ τ : ℕ → ℕ)
    (hg : GoQ B g m (M 0) t₀ fun r => r test = decide (0 < N))
    (h : ∀ k < N, GoQ B body (M k) (M (k + 1)) (τ k) fun r => r test = decide (k + 1 < N))
    (hΦ : ∀ k < N, Φ k + τ k + 1 ≤ Φ (k + 1)) (hs : ∀ i, (M N i).length ≤ B)
    (ht : t₀ + Φ N + 1 ≤ t + Φ 0) :
    Go B (.seq g (.while test body)) m (M N) t := fun regs => by
  obtain ⟨n₁, r₁, e₁, b₁, hr⟩ := hg regs
  obtain ⟨n₂, r₂, e₂, b₂⟩ := go_while M N Φ τ h hΦ hs 0 (Nat.zero_le _) r₁ hr
  exact ⟨n₁ + n₂, r₂, e₁.seq e₂, by omega, trivial⟩

/-- The potential does not decrease. -/
theorem phi_mono {Φ τ : ℕ → ℕ} {N : ℕ} (hΦ : ∀ k < N, Φ k + τ k + 1 ≤ Φ (k + 1)) : Φ 0 ≤ Φ N := by
  induction N with
  | zero => exact le_rfl
  | succ N ih =>
    have h₁ := ih fun k hk => hΦ k (by omega)
    have h₂ := hΦ N (by omega)
    omega

end TransposeBase.Machine
