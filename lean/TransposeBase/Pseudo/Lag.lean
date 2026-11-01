import TransposeBase.Short
import TransposeBase.Pseudo.Words
import TransposeBase.Pseudo.Enum

/-!
# The grid weights as a program

`N! * lagCoeff N e b` is a signed binomial times a coefficient of `∏_{j ≠ b} (ξ + j)`. Both come from one
product of words, by reading a field: the product at `ξ = 2 ^ B` holds the coefficients in fields of width `B`.
-/

namespace TransposeBase.Pseudo.Lag

open Finset Polynomial Enum

/-- The integer `N! * lagCoeff N e b`. -/
noncomputable def lagZ (N e : ℕ) (b : Fin (N + 1)) : ℤ :=
  (-1) ^ (N - e + (N - (b : ℕ))) * (N.choose (b : ℕ) : ℤ) *
    (((∏ j ∈ (univ : Finset (Fin (N + 1))).erase b, (X + C ((j : ℕ) : ℕ))).coeff e : ℕ) : ℤ)

theorem lagZ_cast (N e : ℕ) (b : Fin (N + 1)) :
    (lagZ N e b : ℚ) = (N.factorial : ℚ) * lagCoeff (k := ℚ) N e b := by
  have h := factorial_mul_coeff_basis (k := ℚ) N e b
  unfold lagCoeff gridPt
  rw [h, lagZ]
  push_cast
  ring

variable (W : ℕ)

/-- The word `∏_{j ≤ N, j ≠ b} (2 ^ B + j)`, for variables `N`, `B`, `b`. -/
def prodE (N B b : ℕ) : Expr :=
  .prod (.add (.var N) (.lit 1))
    (eqE 0 (b + 1) (.lit 1) (.add (.pow2 (.var (B + 1))) (.var 0)))

/-- Field `e` of the word `w` with width `B`. `w` is an expression, `B` and `e` are variables. -/
def fieldE (w : Expr) (B e : ℕ) : Expr :=
  .mod (.div w (.pow2 (.mul (.var B) (.var e)))) (.pow2 (.var B))

/-- The coefficient of `ξ ^ e` in `∏_{j ≠ b} (ξ + j)`. -/
def coefE (N B e b : ℕ) : Expr := fieldE (prodE N B b) B e

/-- `C(N, b)`. -/
def chooseE (N B b : ℕ) : Expr :=
  fieldE (.prod (.var N) (.add (.pow2 (.var (B + 1))) (.lit 1))) B b

/-- `N! * lagCoeff N e b`, as a word modulo `2 ^ W`. -/
def lagE (N B e b : ℕ) : Expr :=
  .ite (.mod (.add (.var e) (.var b)) (.lit 2)) (.lit 0)
    (.mul (chooseE N B b) (coefE N B e b))
    (.sub (.lit 0) (.mul (chooseE N B b) (coefE N B e b)))

section Values

variable {W} {env : List ℕ} {N B e b : ℕ} {n k : ℕ}

/-- The size conditions on the word length. -/
structure Sizes (W n k : ℕ) : Prop where
  hk : (n + 1).factorial < 2 ^ k
  hn : n + 1 < k
  hw : k * (n + 2) < W
  hk1 : 1 ≤ k

theorem one_mod {W : ℕ} (hW : 1 ≤ W) : 1 % 2 ^ W = 1 :=
  Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))

theorem Sizes.W_pos (h : Sizes W n k) : 1 ≤ W := by
  have := h.hw
  have : 1 ≤ k * (n + 2) := Nat.mul_pos h.hk1 (by omega)
  omega

theorem Sizes.k_lt (h : Sizes W n k) : k < W := by
  have := h.hw
  nlinarith [h.hk1]

/-- A product of fewer than `n + 2` numbers below `2 ^ k + n + 1` fits in the word. -/
theorem prod_lt (h : Sizes W n k) (s : Finset (Fin (n + 1))) (hs : s.card ≤ n + 1) :
    ∏ j ∈ s, (2 ^ k + (j : ℕ)) < 2 ^ W := by
  have hb : ∀ j ∈ s, 2 ^ k + (j : ℕ) ≤ 2 ^ (k + 1) := by
    intro j _
    have : (j : ℕ) ≤ n := Nat.lt_succ_iff.mp j.2
    have h2 : n < 2 ^ k := lt_trans (by have := h.hn; omega) (Nat.lt_two_pow_self (n := k))
    rw [pow_succ]
    omega
  have h1 := Finset.prod_le_pow_card s _ _ hb
  have h2 : (2 ^ (k + 1)) ^ s.card ≤ 2 ^ ((k + 1) * (n + 1)) := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hs)
  have h3 : (k + 1) * (n + 1) < W := by
    have := h.hw
    have := h.hn
    nlinarith
  exact lt_of_le_of_lt (h1.trans h2) (Nat.pow_lt_pow_right (by norm_num) h3)

theorem eval_prodE (h : Sizes W n k) (hN : env.getD N 0 = n) (hB : env.getD B 0 = k)
    (hb : env.getD b 0 < n + 1) :
    eval W (prodE N B b) env =
      ∏ j ∈ (univ : Finset (Fin (n + 1))).erase ⟨env.getD b 0, hb⟩, (2 ^ k + (j : ℕ)) := by
  have hW1 := h.W_pos
  have hk := h.k_lt
  have hn1 : n + 1 < 2 ^ W := by
    have : n + 1 < W := by
      have := h.hn
      omega
    exact lt_trans this Nat.lt_two_pow_self
  have hbody : ∀ j, j < n + 1 →
      eval W (eqE 0 (b + 1) (.lit 1) (.add (.pow2 (.var (B + 1))) (.var 0))) (j :: env) =
        if j = env.getD b 0 then 1 else 2 ^ k + j := by
    intro j hj
    rw [eval_eqE]
    have h0 : (j :: env).getD 0 0 = j := rfl
    have h1 : (j :: env).getD (b + 1) 0 = env.getD b 0 := rfl
    rw [h0, h1]
    by_cases hjb : j = env.getD b 0
    · rw [if_pos hjb, if_pos hjb]
      change 1 % 2 ^ W = 1
      exact one_mod hW1
    · rw [if_neg hjb, if_neg hjb]
      have hBv : (j :: env).getD (B + 1) 0 = k := hB
      have hlt : 2 ^ k + j < 2 ^ W := by
        have h2 : 2 ^ k + j ≤ 2 ^ (k + 1) := by
          have hjk : j < k := by have := h.hn; omega
          have : j < 2 ^ k := lt_trans hjk Nat.lt_two_pow_self
          rw [pow_succ]
          omega
        have hk2 : k + 1 < W := by
          have := h.hw
          have := h.hk1
          nlinarith
        exact lt_of_le_of_lt h2 (Nat.pow_lt_pow_right (by norm_num) hk2)
      have hv : eval W (.pow2 (.var (B + 1))) (j :: env) = 2 ^ k := by
        change (if (j :: env).getD (B + 1) 0 < W then 2 ^ (j :: env).getD (B + 1) 0 else 0) = _
        rw [hBv, if_pos hk]
      change (eval W (.pow2 (.var (B + 1))) (j :: env) + (j :: env).getD 0 0) % 2 ^ W = _
      rw [hv, h0, Nat.mod_eq_of_lt hlt]
  have hval : eval W (.add (.var N) (.lit 1)) env = n + 1 := by
    change (env.getD N 0 + 1 % 2 ^ W) % 2 ^ W = _
    rw [hN, one_mod hW1, Nat.mod_eq_of_lt hn1]
  unfold prodE
  rw [Pseudo.eval_prod, hval]
  rw [Finset.prod_congr rfl (fun j hj => hbody j (mem_range.mp hj))]
  have hlast : ∏ j ∈ range (n + 1), (if j = env.getD b 0 then 1 else 2 ^ k + j) =
      ∏ j ∈ (univ : Finset (Fin (n + 1))).erase ⟨env.getD b 0, hb⟩, (2 ^ k + (j : ℕ)) := by
    rw [Finset.prod_range]
    rw [← Finset.mul_prod_erase univ _ (mem_univ (⟨env.getD b 0, hb⟩ : Fin (n + 1)))]
    simp only [if_true, one_mul]
    refine prod_congr rfl fun j hj => ?_
    rw [if_neg]
    intro hE
    exact (mem_erase.mp hj).1 (Fin.ext hE)
  rw [hlast]
  exact Nat.mod_eq_of_lt (prod_lt h _ (by
    rw [card_erase_of_mem (mem_univ _)]
    simp))

theorem fieldE_val (h : Sizes W n k) {w : Expr} (hB : env.getD B 0 = k) {x : ℕ}
    (hx : eval W w env = x) (he : env.getD e 0 ≤ n + 1) :
    eval W (fieldE w B e) env = x / 2 ^ (k * env.getD e 0) % 2 ^ k := by
  have hke : k * env.getD e 0 < W := by
    have := h.hw
    have := h.hk1
    nlinarith
  have hsmall : k * env.getD e 0 < 2 ^ W := lt_trans hke Nat.lt_two_pow_self
  have hm : eval W (.mul (.var B) (.var e)) env = k * env.getD e 0 := by
    change (env.getD B 0 * env.getD e 0) % 2 ^ W = _
    rw [hB, Nat.mod_eq_of_lt hsmall]
  change eval W w env / (if eval W (.mul (.var B) (.var e)) env < W then
      2 ^ eval W (.mul (.var B) (.var e)) env else 0) %
    (if env.getD B 0 < W then 2 ^ env.getD B 0 else 0) = _
  rw [hx, hm, if_pos hke, hB, if_pos h.k_lt]

/-- The coefficient as a word. -/
theorem eval_coefE (h : Sizes W n k) (hN : env.getD N 0 = n) (hB : env.getD B 0 = k)
    (hb : env.getD b 0 < n + 1) (he : env.getD e 0 ≤ n + 1) :
    eval W (coefE N B e b) env =
      ((∏ j ∈ (univ : Finset (Fin (n + 1))).erase ⟨env.getD b 0, hb⟩, (X + C ((j : ℕ) : ℕ))).coeff
        (env.getD e 0) : ℕ) := by
  unfold coefE
  rw [fieldE_val h hB (eval_prodE h hN hB hb) he]
  apply prod_field
  calc ∏ j ∈ (univ : Finset (Fin (n + 1))).erase ⟨env.getD b 0, hb⟩, (1 + (j : ℕ))
      ≤ ∏ j : Fin (n + 1), (1 + (j : ℕ)) := by
        apply Finset.prod_le_prod_of_subset_of_one_le' (erase_subset _ _)
        intro j _ _
        omega
    _ = (n + 1).factorial := by
        rw [Fin.prod_univ_eq_prod_range (fun j => 1 + j) (n + 1)]
        simp only [add_comm 1]
        rw [Finset.prod_range_add_one_eq_factorial]
    _ < 2 ^ k := h.hk

/-- The binomial as a word. -/
theorem eval_chooseE (h : Sizes W n k) (hN : env.getD N 0 = n) (hB : env.getD B 0 = k)
    (hb : env.getD b 0 ≤ n + 1) :
    eval W (chooseE N B b) env = n.choose (env.getD b 0) := by
  have hW1 := h.W_pos
  have hk := h.k_lt
  have hk2 : k + 1 < W := by
    have := h.hw
    have := h.hk1
    nlinarith
  have hbody : ∀ j, eval W (.add (.pow2 (.var (B + 1))) (.lit 1)) (j :: env) = 2 ^ k + 1 := by
    intro j
    have hv : eval W (.pow2 (.var (B + 1))) (j :: env) = 2 ^ k := by
      change (if env.getD B 0 < W then 2 ^ env.getD B 0 else 0) = _
      rw [hB, if_pos hk]
    have hlt : 2 ^ k + 1 < 2 ^ W := by
      have h1 : 2 ^ k + 1 ≤ 2 ^ (k + 1) := by
        have := Nat.one_le_two_pow (n := k)
        rw [pow_succ]
        omega
      exact lt_of_le_of_lt h1 (Nat.pow_lt_pow_right (by norm_num) hk2)
    change (eval W (.pow2 (.var (B + 1))) (j :: env) + 1 % 2 ^ W) % 2 ^ W = _
    rw [hv, one_mod hW1, Nat.mod_eq_of_lt hlt]
  have hp : eval W (.prod (.var N) (.add (.pow2 (.var (B + 1))) (.lit 1))) env = (2 ^ k + 1) ^ n := by
    rw [Pseudo.eval_prod]
    have hn : eval W (.var N) env = n := hN
    rw [hn, Finset.prod_congr rfl (fun j _ => hbody j), prod_const, card_range]
    apply Nat.mod_eq_of_lt
    have h1 : (2 ^ k + 1) ^ n ≤ (2 ^ (k + 1)) ^ n := by
      apply Nat.pow_le_pow_left
      have := Nat.one_le_two_pow (n := k)
      rw [pow_succ]
      omega
    have h2 : (2 ^ (k + 1)) ^ n = 2 ^ ((k + 1) * n) := (pow_mul _ _ _).symm
    have h3 : (k + 1) * n < W := by
      have := h.hw
      have := h.hn
      nlinarith
    exact lt_of_le_of_lt (h1.trans_eq h2) (Nat.pow_lt_pow_right (by norm_num) h3)
  unfold chooseE
  rw [fieldE_val h hB hp hb]
  exact choose_field (by have := h.hn; omega) _

/-- The weight in the ring of words. -/
theorem evalZ_lagE (h : Sizes W n k) (hN : env.getD N 0 = n) (hB : env.getD B 0 = k)
    (hb : env.getD b 0 < n + 1) (he : env.getD e 0 ≤ n) :
    evalZ W (lagE N B e b) env = ((lagZ n (env.getD e 0) ⟨env.getD b 0, hb⟩ : ℤ) : ZMod (2 ^ W)) := by
  have hW1 := h.W_pos
  have hc := eval_chooseE h hN hB (b := b) (by omega)
  have hq := eval_coefE h hN hB hb (e := e) (by omega)
  have hsum : eval W (.add (.var e) (.var b)) env = env.getD e 0 + env.getD b 0 := by
    apply Nat.mod_eq_of_lt
    have : env.getD e 0 + env.getD b 0 < 2 * (n + 1) := by omega
    have h2 : 2 * (n + 1) < W := by
      have := h.hw
      have := h.hn
      nlinarith
    exact lt_trans (this.trans h2) Nat.lt_two_pow_self
  have hW2 : 2 % 2 ^ W = 2 := by
    apply Nat.mod_eq_of_lt
    have : 1 < W := by
      have := h.hw
      have := h.hn
      nlinarith
    calc 2 = 2 ^ 1 := by norm_num
      _ < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) this
  have hsign : ((-1 : ZMod (2 ^ W)) ^ (n - env.getD e 0 + (n - env.getD b 0))) =
      if (env.getD e 0 + env.getD b 0) % 2 ≤ 0 then 1 else -1 := by
    have heq : (n - env.getD e 0 + (n - env.getD b 0)) % 2 = (env.getD e 0 + env.getD b 0) % 2 := by
      omega
    rcases Nat.even_or_odd (n - env.getD e 0 + (n - env.getD b 0)) with hev | hod
    · rw [hev.neg_one_pow, if_pos]
      have := Nat.even_iff.mp hev
      omega
    · rw [hod.neg_one_pow, if_neg]
      have := Nat.odd_iff.mp hod
      omega
  have hcond : eval W (.mod (.add (.var e) (.var b)) (.lit 2)) env = (env.getD e 0 + env.getD b 0) % 2 := by
    change eval W (.add (.var e) (.var b)) env % (2 % 2 ^ W) = _
    rw [hsum, hW2]
  have hzero : eval W (.lit 0) env = 0 := by simp [eval]
  have hmul : evalZ W (.mul (chooseE N B b) (coefE N B e b)) env =
      ((n.choose (env.getD b 0) : ℕ) : ZMod (2 ^ W)) *
        (((∏ j ∈ (univ : Finset (Fin (n + 1))).erase ⟨env.getD b 0, hb⟩,
          (X + C ((j : ℕ) : ℕ))).coeff (env.getD e 0) : ℕ) : ZMod (2 ^ W)) := by
    rw [evalZ_mul]
    simp only [evalZ, hc, hq]
  unfold lagE lagZ
  have hite : evalZ W (.ite (.mod (.add (.var e) (.var b)) (.lit 2)) (.lit 0)
        (.mul (chooseE N B b) (coefE N B e b))
        (.sub (.lit 0) (.mul (chooseE N B b) (coefE N B e b)))) env =
      if (env.getD e 0 + env.getD b 0) % 2 ≤ 0 then
        evalZ W (.mul (chooseE N B b) (coefE N B e b)) env
      else evalZ W (.sub (.lit 0) (.mul (chooseE N B b) (coefE N B e b))) env := by
    simp only [evalZ]
    change ((if eval W (.mod (.add (.var e) (.var b)) (.lit 2)) env ≤ eval W (.lit 0) env then _ else _ : ℕ)
      : ZMod (2 ^ W)) = _
    rw [hcond, hzero]
    split_ifs <;> rfl
  rw [hite]
  push_cast
  rw [hsign]
  split_ifs
  · rw [hmul]; simp
  · rw [evalZ_sub, hmul]; simp

theorem ops_fieldE (w : Expr) (B e : ℕ) : ops W (fieldE w B e) env = ops W w env + 8 := by
  simp only [fieldE, ops]
  omega

/-- The operations of the weight. -/
theorem ops_lagE (h : Sizes W n k) (hN : env.getD N 0 = n) :
    ops W (lagE N B e b) env ≤ 16 * n + 50 := by
  have hW1 := h.W_pos
  have hval : eval W (.add (.var N) (.lit 1)) env = n + 1 := by
    change (env.getD N 0 + 1 % 2 ^ W) % 2 ^ W = _
    rw [hN, one_mod hW1]
    apply Nat.mod_eq_of_lt
    have : n + 1 < W := by
      have := h.hn
      have := h.hw
      nlinarith
    exact lt_trans this Nat.lt_two_pow_self
  have h1 : ops W (prodE N B b) env ≤ 4 + (n + 1) * 11 := by
    have := ops_prod_le W (.add (.var N) (.lit 1))
      (eqE 0 (b + 1) (.lit 1) (.add (.pow2 (.var (B + 1))) (.var 0))) env (B := 10) (fun j _ =>
        ops_eqE W _ _ _ _ _ (B := 4) (by simp [ops]) (by simp [ops]))
    rw [hval] at this
    have h3 : ops W (.add (.var N) (.lit 1)) env = 3 := by simp [ops]
    unfold prodE
    omega
  have h2 : ops W (.prod (.var N) (.add (.pow2 (.var (B + 1))) (.lit 1))) env ≤ 2 + n * 5 := by
    have := ops_prod_le W (.var N) (.add (.pow2 (.var (B + 1))) (.lit 1)) env (B := 4)
      (fun j _ => by simp [ops])
    have hn : eval W (.var N) env = n := hN
    rw [hn] at this
    have h3 : ops W (.var N) env = 1 := rfl
    omega
  have e1 : ops W (chooseE N B b) env = ops W (.prod (.var N) (.add (.pow2 (.var (B + 1))) (.lit 1))) env + 8 :=
    ops_fieldE _ _ _
  have e2 : ops W (coefE N B e b) env = ops W (prodE N B b) env + 8 := ops_fieldE _ _ _
  have hcond : ops W (.mod (.add (.var e) (.var b)) (.lit 2)) env = 5 := by simp [ops]
  have hl : ops W (.lit 0) env = 1 := rfl
  have hm : ops W (.mul (chooseE N B b) (coefE N B e b)) env =
      1 + ops W (chooseE N B b) env + ops W (coefE N B e b) env := rfl
  have hs : ops W (.sub (.lit 0) (.mul (chooseE N B b) (coefE N B e b))) env =
      1 + 1 + ops W (.mul (chooseE N B b) (coefE N B e b)) env := rfl
  change 1 + ops W (.mod (.add (.var e) (.var b)) (.lit 2)) env + ops W (.lit 0) env +
    (if eval W (.mod (.add (.var e) (.var b)) (.lit 2)) env ≤ eval W (.lit 0) env then
      ops W (.mul (chooseE N B b) (coefE N B e b)) env
    else ops W (.sub (.lit 0) (.mul (chooseE N B b) (coefE N B e b))) env) ≤ _
  rw [hcond, hl, hs, hm, e1, e2]
  split_ifs <;> omega

end Values

end TransposeBase.Pseudo.Lag
