import TransposeBase.Pseudo.Tree
import TransposeBase.Pseudo.CnfNet

/-!
# Exhaustive search, as a program

For the finitely many small numbers of variables, the top program of `Pseudo/Final` tries all assignments.

`bruteE` runs on `encF n F :: n :: rest`. It tests each word `z < 2 ^ n`, whose bits are the values of the variables:
for each clause code `k`, bit `k` of the formula word is zero, or some literal of the code `k` holds.
-/

namespace TransposeBase.Pseudo.Final

open SatBase Finset TransposeBase.Pseudo.CnfTree TransposeBase.Pseudo.CnfNet

variable {W n : ℕ} {F : ClauseSet (SignedLiteral n)}

/-- The literal `c + 1` holds at the assignment word in the variable `2`, on `c :: k :: z :: _`. -/
def litHoldsE : Expr :=
  tEq (.letE (.div (.var 0) (.lit 2)) (bitE 3 0)) (.mod (.var 0) (.lit 2))

/-- Clause code `k` is not in the formula, or some literal of it holds. On `k :: z :: f :: n :: _`. -/
def clauseOkE : Expr :=
  tOr (tEq (bitE 2 0) (.lit 0)) (tEx (litsE 3) (tAnd (inLE 1 4) litHoldsE))

/-- Exhaustive search, on `f :: n :: _`. -/
def bruteE : Expr := tEx (.pow2 (.var 1)) (tAll (capE 2) clauseOkE)

/-- The test of `bruteE`, on assignments as functions. -/
theorem holds_iff (hF : Wide3 F) {x : Fin n → Bool} {z : ℕ} (hxz : ∀ i : Fin n, x i = z.testBit i) :
    holdsFormula (literalHolds x) F ↔
      ∀ k < cap n, (encF n F).testBit k = false ∨
        ∃ c < 2 * n, InC n (c + 1) k ∧ (z.testBit (c / 2)).toNat = c % 2 := by
  constructor
  · intro h k hk
    by_cases hb : (encF n F).testBit k = true
    · right
      have hc := (encF_testBit hF hk).mp hb
      obtain ⟨l, hl, hx⟩ := h _ hc.2
      have h1 := litCode_pos l
      have h2 := litCode_le l
      refine ⟨litCode l - 1, by omega, ?_, ?_⟩
      · rw [Nat.sub_add_cancel h1]
        exact mem_decode.mp hl
      · obtain ⟨v, b⟩ := l
        have hb1 : b.toNat ≤ 1 := by cases b <;> simp
        have e1 : (2 * (v : ℕ) + b.toNat + 1 - 1) / 2 = v := by omega
        have e2 : (2 * (v : ℕ) + b.toNat + 1 - 1) % 2 = b.toNat := by omega
        simp only [litCode]
        rw [e1, e2, ← hxz v]
        have : x v = b := hx
        rw [this]
    · left
      simpa using hb
  · intro h C hC
    have hw := hF C hC
    obtain ⟨h1, h2, h3⟩ := code_spec hw
    have hb : (encF n F).testBit (code n C) = true :=
      (encF_testBit hF h1).mpr ⟨h2, by rwa [h3]⟩
    rcases h _ h1 with h4 | ⟨c, hc, h5, h6⟩
    · rw [hb] at h4
      cases h4
    · obtain ⟨l, hl⟩ := exists_lit hc
      refine ⟨l, ?_, ?_⟩
      · rw [← h3, mem_decode, hl]
        exact h5
      · obtain ⟨v, b⟩ := l
        have hb1 : b.toNat ≤ 1 := by cases b <;> simp
        simp only [litCode] at hl
        have e1 : c / 2 = v := by omega
        have e2 : c % 2 = b.toNat := by omega
        rw [e1, e2, ← hxz v] at h6
        show x v = b
        exact CnfNet.bool_toNat_inj h6

/-- Satisfiable means that a word below `2 ^ n` passes the test. -/
theorem sat_iff_word (hF : Wide3 F) :
    (∃ x : Fin n → Bool, holdsFormula (literalHolds x) F) ↔
      ∃ z < 2 ^ n, ∀ k < cap n, (encF n F).testBit k = false ∨
        ∃ c < 2 * n, InC n (c + 1) k ∧ (z.testBit (c / 2)).toNat = c % 2 := by
  constructor
  · rintro ⟨x, hx⟩
    let z := setWord n (fun i => ∃ h : i < n, x ⟨i, h⟩ = true)
    have hxz : ∀ i : Fin n, x i = z.testBit i := fun i => by
      have h1 := setWord_testBit n (fun i => ∃ h : i < n, x ⟨i, h⟩ = true) i
      cases hv : x i with
      | false =>
        symm
        rw [← Bool.not_eq_true, show z.testBit i = true ↔ _ from h1]
        rintro ⟨_, _, h3⟩
        have : x i = true := h3
        simp [hv] at this
      | true =>
        symm
        exact h1.mpr ⟨i.2, i.2, hv⟩
    exact ⟨z, setWord_lt _ _, (holds_iff hF hxz).mp hx⟩
  · rintro ⟨z, _, h⟩
    exact ⟨fun i => z.testBit i, (holds_iff hF (fun _ => rfl)).mpr h⟩

/-- The value of the exhaustive search. -/
theorem bruteE_eval (hC : Ctx W n) (hF : Wide3 F) (rest : List ℕ) :
    eval W bruteE (encF n F :: n :: rest) = ind (∃ x : Fin n → Bool, holdsFormula (literalHolds x) F) := by
  have w := hC.one_le
  have w2 := hC.two_le
  have hG := Ctx.G_le_cap n
  have hcap := hC.cap_lt
  have h2lit : (2 : ℕ) < 2 ^ W := by
    calc 2 < 2 ^ 8 := by norm_num
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hC.eight_le
  set f := encF n F with hf
  have hlit : ∀ (z k : ℕ), z < 2 ^ n → k < cap n → ∀ c < 2 * n,
      ∃ B, Test W (tAnd (inLE 1 4) litHoldsE) (c :: k :: z :: f :: n :: rest)
        (InC n (c + 1) k ∧ (z.testBit (c / 2)).toNat = c % 2) B := by
    intro z k hz hk c hc
    have hn3 : (k :: z :: f :: n :: rest).getD 3 0 = n := by simp
    have t1 := test_inL (k := 1) (kv := k) hC hn3 hc (by simp)
    have a1 : Run W (.div (.var 0) (.lit 2)) (c :: k :: z :: f :: n :: rest) (c / 2) 3 :=
      run_div (run_var (by simp)) (run_lit h2lit)
    have a2 := run_bitE (f := 3) (i := 0) (env := (c / 2) :: c :: k :: z :: f :: n :: rest)
      (fv' := z) (iv := c / 2) w2 (by simp) (by simp) (by omega)
    have a3 := run_let a1 a2
    have a4 : Run W (.mod (.var 0) (.lit 2)) (c :: k :: z :: f :: n :: rest) (c % 2) 3 :=
      run_mod (run_var (by simp)) (run_lit h2lit)
    have t2 := test_eq w a3 a4
    exact ⟨_, test_and w t1 (fun _ => t2)⟩
  have hcl : ∀ (z k : ℕ), z < 2 ^ n → k < cap n →
      ∃ B, Test W clauseOkE (k :: z :: f :: n :: rest)
        (f.testBit k = false ∨ ∃ c < 2 * n, InC n (c + 1) k ∧ (z.testBit (c / 2)).toNat = c % 2) B := by
    intro z k hz hk
    have a1 := run_bitE (f := 2) (i := 0) (env := k :: z :: f :: n :: rest) (fv' := f) (iv := k) w2
      (by simp) (by simp) (by omega)
    have t1 := test_eq w a1 (run_zero w)
    have e1 : (f.testBit k).toNat = 0 ↔ f.testBit k = false := by cases f.testBit k <;> simp
    choose! B hB using hlit z k hz hk
    have hB' : ∀ c < 2 * n, Test W (tAnd (inLE 1 4) litHoldsE) (c :: k :: z :: f :: n :: rest)
        (InC n (c + 1) k ∧ (z.testBit (c / 2)).toNat = c % 2) ((range (2 * n)).sup B) := fun c hc =>
      (hB c hc).mono (Finset.le_sup (f := B) (mem_range.mpr hc))
    have t2 := test_ex (N := 2 * n) w (env := k :: z :: f :: n :: rest)
      (run_lits (nv := 3) hC (by simp)) hB'
    exact ⟨_, (test_or w t1 (fun _ => t2)).iff (by rw [e1])⟩
  have hall : ∀ z < 2 ^ n, ∃ B, Test W (tAll (capE 2) clauseOkE) (z :: f :: n :: rest)
      (∀ k < cap n, f.testBit k = false ∨
        ∃ c < 2 * n, InC n (c + 1) k ∧ (z.testBit (c / 2)).toNat = c % 2) B := by
    intro z hz
    have h3 := fun k hk => hcl z k hz hk
    choose! B hB using h3
    have hB' : ∀ k < cap n, Test W clauseOkE (k :: z :: f :: n :: rest)
        (f.testBit k = false ∨ ∃ c < 2 * n, InC n (c + 1) k ∧ (z.testBit (c / 2)).toNat = c % 2)
        ((range (cap n)).sup B) := fun k hk =>
      (hB k hk).mono (Finset.le_sup (f := B) (mem_range.mpr hk))
    exact ⟨_, test_all w (run_cap (nv := 2) hC (by simp)) hB'⟩
  choose! B hB using hall
  have hB' : ∀ z < 2 ^ n, Test W (tAll (capE 2) clauseOkE) (z :: f :: n :: rest)
      (∀ k < cap n, f.testBit k = false ∨
        ∃ c < 2 * n, InC n (c + 1) k ∧ (z.testBit (c / 2)).toNat = c % 2)
      ((range (2 ^ n)).sup B) := fun z hz =>
    (hB z hz).mono (Finset.le_sup (f := B) (mem_range.mpr hz))
  have hn : (n : ℕ) < W := by omega
  have a0 : Run W (.pow2 (.var 1)) (f :: n :: rest) (2 ^ n) 2 :=
    run_pow2 (run_var (by simp)) hn
  have t := test_ex (N := 2 ^ n) w a0 hB'
  exact t.1.trans (ind_congr (sat_iff_word hF).symm)

end TransposeBase.Pseudo.Final
