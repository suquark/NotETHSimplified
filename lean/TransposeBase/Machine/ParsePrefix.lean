import TransposeBase.Machine.Compile

/-!
# The bit-level prefix

The program starts with the input bits `I` on the stack `12`, and all other stacks are empty. `prefixC S c` prepares
the state of `Prepared W [toNat I, I.length]`, with `W = c * (I.length + 1) ^ 4 + I.length`.

A zero word of length `α * β` comes from `mulC`: pop a stack of length `α`, and for each popped bit copy a zero word of
length `β`. The padding `Z g` with `g = c * (I.length + 1) ^ 4` is built first. Then `I ++ Z g` is the input word, and `Z I.length ++ Z g`
is the ruler, so no subtraction is needed.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace TransposeBase.Machine

open OAI.Algorithms.SubexponentialSAT
open StructuredCalls

variable {S : ℕ} [NeZero S]

/-! ### Loops over the bits of a stack -/

/-- A loop whose guard is true exactly below `N`, after an initialization. -/
theorem ev_forQ {test : Fin 10} {g body : Cmd 10 S} {m : Mem} (M : ℕ → Mem) (N t₀ τ : ℕ)
    (hg : EvQ g m (M 0) t₀ fun r => r test = decide (0 < N))
    (h : ∀ k < N, EvQ body (M k) (M (k + 1)) τ fun r => r test = decide (k + 1 < N)) :
    Ev (.seq g (.while test body)) m (M N) (t₀ + (N * (τ + 1) + 1)) := fun regs => by
  obtain ⟨n₁, r₁, e₁, b₁, hr⟩ := hg regs
  obtain ⟨n₂, r₂, e₂, b₂⟩ := ev_while M N τ h 0 (Nat.zero_le _) r₁ hr
  exact ⟨n₁ + n₂, r₂, e₁.seq e₂, by simp only [Nat.sub_zero] at b₂; omega, trivial⟩

/-- Run `inner` once for each bit of the stack `a`. -/
def popLoop (S : ℕ) [NeZero S] (a : ℕ) (inner : Cmd 10 S) : Cmd 10 S :=
  .seq (popC S a) (.while 1 (.seq inner (popC S a)))

/-- The loop over the bits of the stack `a`. The memory other than `a` goes through the family `X`. -/
theorem ev_popLoop {a τ : ℕ} {inner : Cmd 10 S} {m : Mem} (ha : a < S) (X : ℕ → Mem) (hX : X 0 = m)
    (hi : ∀ k < (m a).length, Ev inner (Function.update (X k) a ((m a).drop (k + 1)))
      (Function.update (X (k + 1)) a ((m a).drop (k + 1))) τ) :
    Ev (popLoop S a inner) m (Function.update (X (m a).length) a []) ((m a).length * (τ + 2) + 2) := by
  set as := m a with has
  have hd : as.drop (as.length + 1) = [] := List.drop_eq_nil_of_le (by omega)
  have key := ev_forQ (S := S) (test := 1) (g := popC S a) (body := .seq inner (popC S a)) (m := m)
    (fun k => Function.update (X k) a (as.drop (k + 1))) as.length 1 (τ + 1) ?_ ?_
  · rw [hd] at key
    refine key.mono ?_
    have : as.length * (τ + 1 + 1) = as.length * (τ + 2) := rfl
    omega
  · have e := ev_pop (S := S) (s := a) ha m
    rw [← has] at e
    refine (ev_eq e ?_).mapQ fun r hr => ?_
    · rw [hX]
      simp
    · rw [hr.2]
      cases as <;> simp
  · intro k hk
    have e₁ := hi k hk
    have e₂ := ev_pop (S := S) (s := a) ha (Function.update (X (k + 1)) a (as.drop (k + 1)))
    have e := EvQ.seq e₁ e₂
    simp only [Function.update_self, Function.update_idem] at e
    refine ((ev_eq e ?_).mapQ fun r hr => ?_).mono (by omega)
    · congr 1
      rw [List.tail_drop]
    · rw [hr.2]
      by_cases hk' : k + 1 < as.length
      · rw [List.head?_drop, List.getElem?_eq_getElem hk']
        simp [hk']
      · rw [List.drop_eq_nil_of_le (by omega)]
        simp [hk']

/-- `mulC S a b z` adds to the zero word on `z` one copy of the word on `b` for each bit of `a`. -/
def mulC (S : ℕ) [NeZero S] (a b z : ℕ) : Cmd 10 S := popLoop S a (copyC S b z)

abbrev Z (k : ℕ) : List Bool := List.replicate k false

theorem ev_mulC {a b z α β γ r y : ℕ} {m : Mem} (ha : a < S) (hb : b < S) (hz : z < S) (h8 : 8 < S)
    (hab : a ≠ b) (haz : a ≠ z) (hbz : b ≠ z) (hb8 : b ≠ 8) (hz8 : z ≠ 8) (ha8 : a ≠ 8) (hm8 : m 8 = [])
    (hα : (m a).length = α) (hmb : m b = Z β) (hmz : m z = Z γ) (hr : r = α * β + γ) (hy : α * β ≤ y) (hy2 : α ≤ y) :
    Ev (mulC S a b z) m (Function.update (Function.update m z (Z r)) a []) (14 * y + 2) := by
  have key := ev_popLoop (S := S) (a := a) (τ := 7 * β + 5) (inner := copyC S b z) (m := m) ha
    (fun k => Function.update m z (Z (k * β + γ))) (by
      simp only [zero_mul, zero_add, ← hmz]; simp)
    (fun k hk => by
      set M := Function.update (Function.update m z (Z (k * β + γ))) a ((m a).drop (k + 1)) with hM
      have e := ev_copy (S := S) (src := b) (dst := z) hb hz h8 hbz hb8 hz8 (m := M)
        (by simp [hM, Function.update_apply, hm8, hz8.symm, ha8.symm])
      have hMb : M b = Z β := by simp [hM, Function.update_apply, hab.symm, hbz, hmb]
      have hMz : M z = Z (k * β + γ) := by simp [hM, Function.update_apply, haz.symm]
      rw [hMb, hMz] at e
      refine (ev_eq e ?_).mono (by simp)
      have e2 : Z β ++ Z (k * β + γ) = Z ((k + 1) * β + γ) := by
        simp only [List.replicate_append_replicate]
        congr 1
        ring
      rw [e2, hM, Function.update_comm haz.symm, Function.update_idem]
      exact Function.update_comm haz _ _ _)
  rw [hα] at key
  rw [show α * β + γ = r from hr.symm] at key
  refine key.mono ?_
  have : α * (7 * β + 5 + 2) = 7 * (α * β) + 7 * α := by ring
  omega

/-! ### Zero words of a fixed length -/

/-- Push `c` zeros. -/
def zerosC (S : ℕ) [NeZero S] (s : ℕ) : ℕ → Cmd 10 S
  | 0 => .base .skip
  | c + 1 => .seq (pushB S s false) (zerosC S s c)

theorem ev_zerosC {s : ℕ} (hs : s < S) (c d : ℕ) (m : Mem) (hm : m s = Z d) :
    Ev (zerosC S s c) m (Function.update m s (Z (c + d))) (2 * c) := by
  induction c generalizing d m with
  | zero =>
    refine (ev_eq (ev_skip m) ?_).mono (by simp)
    simp [← hm]
  | succ c ih =>
    have e₁ := ev_pushB (S := S) (s := s) hs false m
    have e₂ := ih (d + 1) (Function.update m s (false :: m s)) (by simp [hm, List.replicate_succ])
    refine (ev_eq (EvQ.seq e₁ e₂) ?_).mono (by omega)
    rw [Function.update_idem]
    congr 2
    omega

/-! ### The prefix -/

/-- Equality of explicit memories on the stacks `0`-`13`. -/
macro "mem_ext" : tactic =>
  `(tactic| (funext i; rcases (show i ≤ 13 ∨ 14 ≤ i by omega) with h | h
             · interval_cases i <;> simp [Function.update_apply, List.replicate_succ]
             · simp [Function.update_apply, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega,
                 show i ≠ 3 by omega, show i ≠ 4 by omega, show i ≠ 5 by omega, show i ≠ 6 by omega,
                 show i ≠ 7 by omega, show i ≠ 9 by omega, show i ≠ 10 by omega, show i ≠ 11 by omega,
                 show i ≠ 12 by omega]))

macro "us" : tactic => `(tactic| simp [Function.update_apply])

/-- The memory with all stacks empty. -/
abbrev E0 : Mem := fun _ => []

/-- The size of the padding. -/
def padOf (c ℓ : ℕ) : ℕ := c * ((ℓ + 1) * ((ℓ + 1) * ((ℓ + 1) * (ℓ + 1))))

/-- The word size for an input of `ℓ` bits. -/
def wOf (c ℓ : ℕ) : ℕ := padOf c ℓ + ℓ

theorem wOf_facts {c ℓ : ℕ} (hc : 1 ≤ c) :
    ℓ + 1 ≤ wOf c ℓ + 1 ∧ (ℓ + 1) * (ℓ + 1) ≤ wOf c ℓ + 1 ∧ (ℓ + 1) * ((ℓ + 1) * (ℓ + 1)) ≤ wOf c ℓ + 1 ∧
      (ℓ + 1) * ((ℓ + 1) * ((ℓ + 1) * (ℓ + 1))) ≤ wOf c ℓ + 1 ∧ c ≤ wOf c ℓ + 1 ∧ padOf c ℓ ≤ wOf c ℓ + 1 := by
  set L := ℓ + 1 with hL
  have hL1 : 1 ≤ L := by omega
  have h4 : L * (L * (L * L)) ≤ padOf c ℓ := by
    rw [padOf]; exact Nat.le_mul_of_pos_left _ hc
  have h3 : L * (L * L) ≤ L * (L * (L * L)) := Nat.le_mul_of_pos_left _ hL1
  have h2 : L * L ≤ L * (L * L) := Nat.le_mul_of_pos_left _ hL1
  have h1 : L ≤ L * L := Nat.le_mul_of_pos_left _ hL1
  have h0 : 1 ≤ L * (L * (L * L)) := by omega
  have hc2 : c ≤ padOf c ℓ := by
    rw [padOf]; exact Nat.le_mul_of_pos_right _ h0
  simp only [wOf]
  omega

/-- The first stage: a zero word of length `ℓ + 1` on the stack `3`, and one zero on the stack `2`. -/
def stage1 (S : ℕ) [NeZero S] : Cmd 10 S :=
  .seq (copyC S 12 1) (.seq (pushB S 2 false) (.seq (mulC S 1 2 3) (pushB S 3 false)))

/-- The memory after the first stage. -/
abbrev M1 (I : List Bool) : Mem :=
  Function.update (Function.update (Function.update E0 3 (Z (I.length + 1))) 2 (Z 1)) 12 I

theorem ev_stage1 (hS : 14 ≤ S) (I : List Bool) {y : ℕ} (hy : I.length ≤ y) :
    Ev (stage1 S) (Function.update E0 12 I) (M1 I) (7 * y + 5 + (2 + (14 * y + 2 + 2))) := by
  have e1 := ev_copy' (S := S) (src := 12) (dst := 1) (L := y) (m := Function.update E0 12 I) (x := I)
    (by omega) (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num) (by us) (by us) (by us) hy
  have e2 := ev_pushB (S := S) (s := 2) (by omega) false (Function.update (Function.update E0 12 I) 1 I)
  have e3 := ev_mulC (S := S) (a := 1) (b := 2) (z := 3) (α := I.length) (β := 1) (γ := 0) (r := I.length) (y := y)
    (m := Function.update (Function.update (Function.update E0 12 I) 1 I) 2
      (false :: Function.update (Function.update E0 12 I) 1 I 2))
    (by omega) (by omega) (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by us) (by us) (by us) (by us) (by ring) (by omega) hy
  have e4 := ev_pushB (S := S) (s := 3) (by omega) false (Function.update (Function.update
    (Function.update (Function.update (Function.update E0 12 I) 1 I) 2
      (false :: Function.update (Function.update E0 12 I) 1 I 2)) 3 (Z I.length)) 1 [])
  refine ev_eq (e1.seq (e2.seq (e3.seq e4))) ?_
  mem_ext

/-- The second stage: the zero words of length `(ℓ + 1) ^ 2`, `(ℓ + 1) ^ 3`, `(ℓ + 1) ^ 4`, and the padding on the
stack `7`. -/
def stage2 (S : ℕ) [NeZero S] (c : ℕ) : Cmd 10 S :=
  .seq (copyC S 3 1) (.seq (mulC S 1 3 4) (.seq (copyC S 3 1) (.seq (mulC S 1 4 5) (.seq (copyC S 3 1)
    (.seq (mulC S 1 5 6) (.seq (zerosC S 1 c) (mulC S 1 6 7)))))))

/-- The memory after the second stage. -/
abbrev M2 (c : ℕ) (I : List Bool) : Mem :=
  Function.update (Function.update (Function.update (Function.update (M1 I) 4
    (Z ((I.length + 1) * (I.length + 1)))) 5 (Z ((I.length + 1) * ((I.length + 1) * (I.length + 1))))) 6
    (Z ((I.length + 1) * ((I.length + 1) * ((I.length + 1) * (I.length + 1)))))) 7 (Z (padOf c I.length))

theorem ev_stage2 (hS : 14 ≤ S) (c : ℕ) (hc : 1 ≤ c) (I : List Bool) :
    Ev (stage2 S c) (M1 I) (M2 c I) (100 * (wOf c I.length + 1) + 100) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := wOf_facts (c := c) (ℓ := I.length) hc
  set y := wOf c I.length + 1 with hy
  refine (ev_eq (EvQ.seq (ev_copy' (S := S) (src := 3) (dst := 1) (L := y) (x := Z (I.length + 1))
      (by omega) (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num) (by us) (by us) (by us) (by simpa using h1))
    (EvQ.seq (ev_mulC (S := S) (a := 1) (b := 3) (z := 4) (α := I.length + 1) (β := I.length + 1) (γ := 0) (r := (I.length + 1) * (I.length + 1)) (y := y)
      (by omega) (by omega) (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by us) (by us) (by us) (by us) (by ring) h2 h1)
    (EvQ.seq (ev_copy' (S := S) (src := 3) (dst := 1) (L := y) (x := Z (I.length + 1))
      (by omega) (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num) (by us) (by us) (by us) (by simpa using h1))
    (EvQ.seq (ev_mulC (S := S) (a := 1) (b := 4) (z := 5) (α := I.length + 1) (β := (I.length + 1) * (I.length + 1)) (γ := 0) (r := (I.length + 1) * ((I.length + 1) * (I.length + 1))) (y := y)
      (by omega) (by omega) (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by us) (by us) (by us) (by us) (by ring) h3 h1)
    (EvQ.seq (ev_copy' (S := S) (src := 3) (dst := 1) (L := y) (x := Z (I.length + 1))
      (by omega) (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num) (by us) (by us) (by us) (by simpa using h1))
    (EvQ.seq (ev_mulC (S := S) (a := 1) (b := 5) (z := 6) (α := I.length + 1) (β := (I.length + 1) * ((I.length + 1) * (I.length + 1))) (γ := 0)
        (r := (I.length + 1) * ((I.length + 1) * ((I.length + 1) * (I.length + 1)))) (y := y)
      (by omega) (by omega) (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by us) (by us) (by us) (by us) (by ring) h4 h1)
    (EvQ.seq (ev_zerosC (S := S) (s := 1) (by omega) c 0 _ (by us))
      (ev_mulC (S := S) (a := 1) (b := 6) (z := 7) (α := c) (β := (I.length + 1) * ((I.length + 1) * ((I.length + 1) * (I.length + 1)))) (γ := 0)
        (r := padOf c I.length) (y := y)
      (by omega) (by omega) (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by us) (by us) (by us) (by us) (by simp [padOf]) (by exact h6) h5)))))))) ?_).mono (by omega)
  mem_ext

/-- The third stage: the ruler on the stack `10`. -/
def stage3 (S : ℕ) [NeZero S] : Cmd 10 S :=
  .seq (clearC S 3) (.seq (clearC S 4) (.seq (clearC S 5) (.seq (clearC S 6)
    (.seq (copyC S 7 10) (.seq (copyC S 12 1) (.seq (mulC S 1 2 10) (clearC S 2)))))))

/-- The memory after the third stage. -/
abbrev M3 (c : ℕ) (I : List Bool) : Mem :=
  Function.update (Function.update (Function.update E0 12 I) 7 (Z (padOf c I.length))) 10 (Z (wOf c I.length))

theorem ev_stage3 (hS : 14 ≤ S) (c : ℕ) (hc : 1 ≤ c) (I : List Bool) :
    Ev (stage3 S) (M2 c I) (M3 c I) (100 * (wOf c I.length + 1) + 100) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := wOf_facts (c := c) (ℓ := I.length) hc
  set y := wOf c I.length + 1 with hy
  have hl : I.length ≤ y := by omega
  refine (ev_eq (EvQ.seq (ev_clear' (S := S) (i := 3) (L := y) (by omega) _ (le_of_eq_of_le (by us) h1))
    (EvQ.seq (ev_clear' (S := S) (i := 4) (L := y) (by omega) _ (le_of_eq_of_le (by us) h2))
    (EvQ.seq (ev_clear' (S := S) (i := 5) (L := y) (by omega) _ (le_of_eq_of_le (by us) h3))
    (EvQ.seq (ev_clear' (S := S) (i := 6) (L := y) (by omega) _ (le_of_eq_of_le (by us) h4))
    (EvQ.seq (ev_copy' (S := S) (src := 7) (dst := 10) (L := y) (x := Z (padOf c I.length))
      (by omega) (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num) (by us) (by us) (by us) (by simpa using h6))
    (EvQ.seq (ev_copy' (S := S) (src := 12) (dst := 1) (L := y) (x := I)
      (by omega) (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num) (by us) (by us) (by us) hl)
    (EvQ.seq (ev_mulC (S := S) (a := 1) (b := 2) (z := 10) (α := I.length) (β := 1) (γ := padOf c I.length)
        (r := wOf c I.length) (y := y)
      (by omega) (by omega) (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by us) (by us) (by us) (by us) (by simp [wOf]; omega) (by omega) hl)
      (ev_clear' (S := S) (i := 2) (L := y) (by omega) _ (by simp [Function.update_apply]; omega))))))))) ?_).mono (by omega)
  mem_ext

/-- Add one to the word on the stack `11` for each bit of the stack `3`. -/
def countC (S : ℕ) [NeZero S] : Cmd 10 S := popLoop S 3 (incC S 11)

theorem ev_countC (hS : 14 ≤ S) {W : ℕ} {m : Mem} (hm3 : (m 3).length < 2 ^ W) (hm1 : m 1 = [])
    (hm11 : m 11 = wordOf W 0) :
    Ev (countC S) m (Function.update (Function.update m 11 (wordOf W (m 3).length)) 3 [])
      ((m 3).length * (8 * W + 8 + 2) + 2) := by
  refine ev_popLoop (S := S) (a := 3) (τ := 8 * W + 8) (inner := incC S 11) (m := m) (by omega)
    (fun k => Function.update m 11 (wordOf W k)) (by rw [← hm11]; simp) (fun k hk => ?_)
  have e := ev_inc (S := S) (W := W) (k := k) (i := 11)
    (m := Function.update (Function.update m 11 (wordOf W k)) 3 ((m 3).drop (k + 1))) (by omega) (by omega) (by norm_num)
    (by us; exact hm1) (by us) (by omega)
  refine ev_eq e ?_
  rw [Function.update_comm (by norm_num : (3 : ℕ) ≠ 11), Function.update_idem]

/-- The fourth stage: the modulus on the stack `9`, and the number of input bits on the stack `11`. -/
def stage4 (S : ℕ) [NeZero S] : Cmd 10 S :=
  .seq (pushB S 9 true) (.seq (copyC S 10 9) (.seq (copyC S 10 11) (.seq (copyC S 12 3) (countC S))))

/-- The memory after the fourth stage. -/
abbrev M4 (c : ℕ) (I : List Bool) : Mem :=
  Function.update (Function.update (M3 c I) 9 (Z (wOf c I.length) ++ [true])) 11
    (wordOf (wOf c I.length) I.length)

theorem ev_stage4 (hS : 14 ≤ S) (c : ℕ) (hc : 1 ≤ c) (I : List Bool) :
    Ev (stage4 S) (M3 c I) (M4 c I) (100 * (wOf c I.length + 1) + 100 +
      I.length * (8 * wOf c I.length + 8 + 2)) := by
  have hl : I.length ≤ wOf c I.length := by simp [wOf]
  have hlt : I.length < 2 ^ wOf c I.length := lt_of_le_of_lt hl Nat.lt_two_pow_self
  refine (ev_eq (EvQ.seq (ev_pushB (S := S) (s := 9) (by omega) true _)
    (EvQ.seq (ev_copy (S := S) (src := 10) (dst := 9) (by omega) (by omega) (by omega) (by norm_num) (by norm_num)
      (by norm_num) (by us))
    (EvQ.seq (ev_copy' (S := S) (src := 10) (dst := 11) (L := wOf c I.length + 1) (x := Z (wOf c I.length))
      (by omega) (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num) (by us) (by us) (by us) (by simp))
    (EvQ.seq (ev_copy' (S := S) (src := 12) (dst := 3) (L := wOf c I.length + 1) (x := I)
      (by omega) (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num) (by us) (by us) (by us) (by omega))
      (ev_countC (S := S) (W := wOf c I.length) hS (by simpa [Function.update_apply] using hlt) (by us)
        (by simp [Function.update_apply, wordOf_zero])))))) ?_).mono ?_
  · simp only [Function.update_self, Function.update_of_ne (by norm_num : (3 : ℕ) ≠ 9)]
    mem_ext
  · simp [Function.update_apply]
    omega

/-- The fifth stage: the padded input word on the stack `12`. -/
def stage5 (S : ℕ) [NeZero S] : Cmd 10 S :=
  .seq (xferC S 12 1) (.seq (xferC S 7 12) (xferC S 1 12))

/-- The memory after the prefix. -/
abbrev M5 (c : ℕ) (I : List Bool) : Mem :=
  Function.update (Function.update (Function.update (Function.update E0 10 (Z (wOf c I.length))) 9
    (Z (wOf c I.length) ++ [true])) 11 (wordOf (wOf c I.length) I.length)) 12 (I ++ Z (padOf c I.length))

theorem ev_stage5 (hS : 14 ≤ S) (c : ℕ) (hc : 1 ≤ c) (I : List Bool) :
    Ev (stage5 S) (M4 c I) (M5 c I) (20 * (wOf c I.length + 1) + 20) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := wOf_facts (c := c) (ℓ := I.length) hc
  refine (ev_eq (EvQ.seq (ev_xfer (S := S) (src := 12) (dst := 1) (by omega) (by omega) (by norm_num) _)
    (EvQ.seq (ev_xfer (S := S) (src := 7) (dst := 12) (by omega) (by omega) (by norm_num) _)
      (ev_xfer (S := S) (src := 1) (dst := 12) (by omega) (by omega) (by norm_num) _))) ?_).mono ?_
  · mem_ext
  · simp [Function.update_apply]
    omega

/-- **The prefix.** -/
def prefixC (S : ℕ) [NeZero S] (c : ℕ) : Cmd 10 S :=
  .seq (stage1 S) (.seq (stage2 S c) (.seq (stage3 S) (.seq (stage4 S) (stage5 S))))

theorem ev_prefix (hS : 14 ≤ S) (c : ℕ) (hc : 1 ≤ c) (I : List Bool) :
    Ev (prefixC S c) (Function.update E0 12 I) (M5 c I) (1000 * (wOf c I.length + 1) ^ 2) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := wOf_facts (c := c) (ℓ := I.length) hc
  have hl : I.length ≤ wOf c I.length + 1 := by omega
  have e := (ev_stage1 (S := S) hS I hl).seq ((ev_stage2 hS c hc I).seq ((ev_stage3 hS c hc I).seq
    ((ev_stage4 hS c hc I).seq (ev_stage5 hS c hc I))))
  refine e.mono ?_
  set W := wOf c I.length
  have h9 : I.length * (8 * W + 8 + 2) ≤ (W + 1) * (10 * (W + 1)) :=
    Nat.mul_le_mul hl (by omega)
  have h10 : (W + 1) * (10 * (W + 1)) = 10 * (W + 1) ^ 2 := by ring
  have h11 : W + 1 ≤ (W + 1) ^ 2 := by nlinarith
  omega

/-! ### The prepared state -/

theorem toNat_append_zeros (xs : List Bool) (k : ℕ) :
    BinaryArithmetic.toNat (xs ++ Z k) = BinaryArithmetic.toNat xs := by
  induction xs with
  | nil => simpa using toNat_replicate_false k
  | cons b xs ih => simp only [List.cons_append, BinaryArithmetic.toNat, ih]

theorem padded_word (c : ℕ) (I : List Bool) :
    I ++ Z (padOf c I.length) = wordOf (wOf c I.length) (BinaryArithmetic.toNat I) :=
  eq_wordOf (by simp [wOf]; omega) (toNat_append_zeros _ _)

theorem toNat_input_lt (c : ℕ) (I : List Bool) : BinaryArithmetic.toNat I < 2 ^ wOf c I.length :=
  lt_of_lt_of_le (toNat_lt I) (Nat.pow_le_pow_right (by norm_num) (by simp [wOf]))

theorem prepared_M5 (hS : 14 ≤ S) (c : ℕ) (I : List Bool) :
    Prepared (wOf c I.length) [BinaryArithmetic.toNat I, I.length] (view S (M5 c I)) := by
  have hmod : wordOf (wOf c I.length + 1) (2 ^ wOf c I.length) = Z (wOf c I.length) ++ [true] := by
    have := wordOf_two_pow (W := wOf c I.length + 1) (a := wOf c I.length) (by omega)
    rw [← this]
    simp
  refine ⟨fun i hi => ?_, ?_, ?_, fun j hj => ?_, fun i hi hS' => ?_⟩
  · rw [view_F _ (by omega)]
    interval_cases i <;> simp [Function.update_apply]
  · rw [view_F _ (by omega), hmod]
    simp [Function.update_apply]
  · rw [view_F _ (by omega)]
    simp [Function.update_apply]
  · simp only [List.length_cons, List.length_nil] at hj
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · rw [view_F _ (by simp; omega)]
      simp [Function.update_apply, padded_word]
    · rw [view_F _ (by simp; omega)]
      simp [Function.update_apply]
  · simp only [List.length_cons, List.length_nil] at hi
    rw [view_F _ hS']
    simp [Function.update_apply, show 11 + i ≠ 9 by omega, show 11 + i ≠ 10 by omega, show 11 + i ≠ 11 by omega,
      show 11 + i ≠ 12 by omega, show i ≠ 0 by omega, show i ≠ 1 by omega]

end TransposeBase.Machine
