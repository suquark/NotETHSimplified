import TransposeBase.Pseudo.CnfSlot

/-!
# Programs for the rule choice and the two children

The rule is a number `r` as in `CnfSlot`. The word of a child is built bit by bit by `setE`, then normalized.
-/

namespace TransposeBase.Pseudo.CnfTree

open SatBase Finset

variable {W : ℕ} {env : List ℕ} {n nv : ℕ}

/-- `ruleCap n`, the number of candidate numbers. -/
def RE (nv : ℕ) : Expr := .mul (.mul (.lit 3) (gE nv)) (gE nv)
def phE (r nv : ℕ) : Expr := .div (.div (.var r) (gE nv)) (gE nv)
/-- The width of the rule in the variable `r`. -/
def wE (r nv : ℕ) : Expr := .ite (phE r nv) (.lit 0) (.lit 2) (.lit 3)
/-- The threshold of the rule in the variable `r`. -/
def thrE (L r nv : ℕ) : Expr := .ite (phE r nv) (.lit 1) (.lit L) (.mul (.lit L) (.lit L))
/-- The literal code `c + 1` is in the core of the rule in the variable `r`. -/
def inSE (r nv : ℕ) : Expr := tOr (tEq cE (d1E r nv)) (tEq cE (d0E r nv))
/-- The core of the rule `r` is contained in the clause `k`. -/
def supE (r k nv : ℕ) : Expr :=
  tAll (litsE nv) (tOr (tNot (inSE (r + 1) (nv + 1))) (inLE (k + 1) (nv + 1)))
/-- The clause `k` is the core of the rule `r`. -/
def eqSE (k r nv : ℕ) : Expr :=
  tAll (litsE nv) (tEq (inLE (k + 1) (nv + 1)) (inSE (r + 1) (nv + 1)))
/-- `decode j \ core = decode k`. -/
def petalE (j k r nv : ℕ) : Expr :=
  tAll (litsE nv)
    (tEq (tAnd (inLE (j + 1) (nv + 1)) (tNot (inSE (r + 1) (nv + 1)))) (inLE (k + 1) (nv + 1)))
/-- The number in the variable `r` is a candidate number. -/
def slotE (r nv : ℕ) : Expr :=
  tAnd (tNot (tEq (d1E r nv) (.lit 0)))
    (tAnd (tOr (tNot (tEq (phE r nv) (.lit 1)))
        (tAnd (tNot (tEq (d0E r nv) (.lit 0))) (tNot (tEq (d0E r nv) (d1E r nv)))))
      (tOr (tEq (phE r nv) (.lit 1)) (tEq (d0E r nv) (.lit 0))))
/-- The test that a clause `k` belongs to the core clauses of the rule `r`. -/
def coreE (f r k nv : ℕ) : Expr :=
  tAnd (bitE f k) (tAnd (tEq (cardE k nv) (wE r nv)) (supE r k nv))
/-- The number of core clauses of the rule `r`. -/
def countE (f r nv : ℕ) : Expr := .sum (capE nv) (coreE (f + 1) (r + 1) 0 (nv + 1))
/-- The number `r` is the number of an eligible rule. -/
def eligE (L f r nv : ℕ) : Expr := tAnd (slotE r nv) (tLe (thrE L r nv) (countE f r nv))
/-- The number of the chosen rule, or `ruleCap n`. -/
def ruleE (L f nv : ℕ) : Expr :=
  .fold (RE nv) (RE nv)
    (.ite (RE (nv + 2)) (.var 0)
      (.ite (eligE L (f + 2) 1 (nv + 2)) (.lit 0) (RE (nv + 2)) (.var 1))
      (.var 0))

/-- The word of `coreLeft F w S` for the core of the rule in the variable `r`. -/
def leftRawE (f r nv : ℕ) : Expr :=
  setE nv (tAnd (validE 0 (nv + 1)) (tOr (bitE (f + 1) 0) (eqSE 0 (r + 1) (nv + 1))))

/-- The word of `coreRight F w S` for the rule in the variable `r`. -/
def rightRawE (f r nv : ℕ) : Expr :=
  setE nv (tAnd (validE 0 (nv + 1)) (tOr (bitE (f + 1) 0)
    (tEx (capE (nv + 1))
      (tAnd (coreE (f + 2) (r + 2) 0 (nv + 2)) (petalE 0 1 (r + 2) (nv + 2))))))

/-- The normalized child of the formula in the variable `f`, for the rule in the variable `r`. The variable
`b` selects the child: `0` for the left child. -/
def childE (f r b nv : ℕ) : Expr :=
  .letE (.ite (.var b) (.lit 0) (leftRawE f r nv) (rightRawE f r nv)) (normE 0 (nv + 1))

section

variable (hC : Ctx W n) (hn : env.getD nv 0 = n)
include hC hn

theorem run_RE : Run W (RE nv) env (ruleCap n) 13 := by
  have h3 : ruleCap n ≤ W := by
    have h1 := hC.big
    have h2 : 3 * (2 * n + 1) * (2 * n + 1) ≤ (2 * n + 2) ^ 3 := by
      have : (2 * n + 2) ^ 3 = (2 * n + 1) * (2 * n + 1) * (2 * n + 1) + 3 * (2 * n + 1) * (2 * n + 1) +
          3 * (2 * n + 1) + 1 := by ring
      omega
    exact h2.trans h1
  have hpow : ruleCap n < 2 ^ W := lt_of_le_of_lt h3 Nat.lt_two_pow_self
  have hG : 1 ≤ 2 * n + 1 := by omega
  have h31 : 3 < 2 ^ W := hC.lt_pow (by have := hC.eight_le; omega)
  have hm : 3 * (2 * n + 1) ≤ ruleCap n := by
    unfold ruleCap
    exact Nat.le_mul_of_pos_right _ (by omega)
  have g := run_g hC hn
  have a := run_mul (run_lit (env := env) h31) g (lt_of_le_of_lt hm hpow)
  exact (run_mul a g hpow).mono (by omega)

theorem run_phE {r rv : ℕ} (hr : env.getD r 0 = rv) : Run W (phE r nv) env (phase n rv) 13 :=
  run_div (run_div (run_var hr) (run_g hC hn)) (run_g hC hn)

theorem run_wE {r rv : ℕ} (hr : env.getD r 0 = rv) : Run W (wE r nv) env (ruleW n rv) 16 := by
  have h2 : (2 : ℕ) < 2 ^ W := hC.lt_pow (by have := hC.eight_le; omega)
  have h3 : (3 : ℕ) < 2 ^ W := hC.lt_pow (by have := hC.eight_le; omega)
  have := run_ite (c := .lit 2) (d := .lit 3) (v := ruleW n rv) (Bc := 1) (run_phE hC hn hr)
    (run_zero hC.one_le)
    (fun h => by
      rw [ruleW, if_pos (by omega)]
      exact run_lit h2)
    (fun h => by
      rw [ruleW, if_neg (by omega)]
      exact run_lit h3)
  exact this.mono (by omega)

theorem run_thrE {L r rv : ℕ} (hL : L * L < 2 ^ W) (hL1 : 1 ≤ L) (hr : env.getD r 0 = rv) :
    Run W (thrE L r nv) env (thrOf L n rv) 18 := by
  have hl : L < 2 ^ W := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by omega)) hL
  have := run_ite (c := .lit L) (d := .mul (.lit L) (.lit L)) (v := thrOf L n rv) (Bc := 3)
    (run_phE hC hn hr) (run_one hC.one_le)
    (fun h => by
      rw [thrOf, if_pos h]
      exact (run_lit hl).mono (by omega))
    (fun h => by
      rw [thrOf, if_neg h]
      exact run_mul (run_lit hl) (run_lit hl) hL)
  exact this.mono (by omega)

theorem test_inS {c r rv : ℕ} (hc : c < 2 * n) (hr : (c :: env).getD r 0 = rv) :
    Test W (inSE r (nv + 1)) (c :: env) (c + 1 = d1 n rv ∨ c + 1 = d0 n rv) 61 := by
  have w := hC.one_le
  have c1 := run_cE hC hn hc
  have hn1 := gd c hn
  have := test_or w (test_eq w c1 (run_d1 hC hn1 hr)) (fun _ => test_eq w c1 (run_d0 hC hn1 hr))
  exact this.mono (by omega)

theorem test_supE {r k rv kv : ℕ} (hr : env.getD r 0 = rv) (hk : env.getD k 0 = kv) :
    Test W (supE r k nv) env (ruleSet n rv ⊆ decode n kv) (400 * (n + 1)) := by
  have w := hC.one_le
  have := test_all (p := fun c => ¬ (c + 1 = d1 n rv ∨ c + 1 = d0 n rv) ∨ InC n (c + 1) kv)
    (B := 3 + (3 + 61) + 118) w (run_lits hC hn)
    (fun c hc => test_or w (test_not w (test_inS hC hn hc (gd c hr)))
      (fun _ => test_inL hC hn hc (gd c hk)))
  refine (this.iff ?_).mono (by omega)
  rw [ruleSet_subset_iff]
  simp only [imp_iff_not_or]

theorem test_eqSE {r k rv kv : ℕ} (hr : env.getD r 0 = rv) (hk : env.getD k 0 = kv) :
    Test W (eqSE k r nv) env (decode n kv = ruleSet n rv) (800 * (n + 1)) := by
  have w := hC.one_le
  have := test_all (p := fun c => ind (InC n (c + 1) kv) = ind (c + 1 = d1 n rv ∨ c + 1 = d0 n rv))
    (B := 3 + 2 * 118 + 2 * 61) w (run_lits hC hn)
    (fun c hc => test_eq w (test_inL hC hn hc (gd c hk)) (test_inS hC hn hc (gd c hr)))
  refine (this.iff ?_).mono (by omega)
  rw [decode_eq_ruleSet_iff]
  simp only [ind_eq_iff]

theorem test_petalE {r j k rv jv kv : ℕ} (hr : env.getD r 0 = rv) (hj : env.getD j 0 = jv)
    (hk : env.getD k 0 = kv) :
    Test W (petalE j k r nv) env (decode n jv \ ruleSet n rv = decode n kv) (1300 * (n + 1)) := by
  have w := hC.one_le
  have := test_all (p := fun c => ind (InC n (c + 1) jv ∧ ¬ (c + 1 = d1 n rv ∨ c + 1 = d0 n rv)) =
      ind (InC n (c + 1) kv))
    (B := 3 + 2 * (3 + 118 + (3 + 61)) + 2 * 118) w (run_lits hC hn)
    (fun c hc => test_eq w (test_and w (test_inL hC hn hc (gd c hj))
        (fun _ => test_not w (test_inS hC hn hc (gd c hr))))
      (test_inL hC hn hc (gd c hk)))
  refine (this.iff ?_).mono (by omega)
  rw [petal_iff]
  simp only [ind_eq_iff]

theorem test_slotE {r rv : ℕ} (hr : env.getD r 0 = rv) : Test W (slotE r nv) env (SlotOK n rv) 210 := by
  have w := hC.one_le
  have z := run_zero (env := env) w
  have one := run_one (env := env) w
  have a0 := run_d0 hC hn hr
  have a1 := run_d1 hC hn hr
  have ph := run_phE hC hn hr
  have t1 := test_not w (test_eq w a1 z)
  have t2 := test_or w (test_not w (test_eq w ph one))
    (fun _ => test_and w (test_not w (test_eq w a0 z)) (fun _ => test_not w (test_eq w a0 a1)))
  have t3 := test_or w (test_eq w ph one) (fun _ => test_eq w a0 z)
  have := test_and w t1 (fun _ => test_and w t2 (fun _ => t3))
  refine (this.iff ?_).mono (by omega)
  simp only [SlotOK, imp_iff_not_or, ne_eq, not_not]

theorem test_coreE {F : ClauseSet (SignedLiteral n)} (hF : Wide3 F) {f r k rv kv : ℕ}
    (hf : env.getD f 0 = encF n F) (hr : env.getD r 0 = rv) (hk : env.getD k 0 = kv) (hkv : kv < cap n) :
    Test W (coreE f r k nv) env
      (Cl n F kv ∧ (decode n kv).card = ruleW n rv ∧ ruleSet n rv ⊆ decode n kv) (1000 * (n + 1)) := by
  have w := hC.one_le
  have t1 := test_bit (nv := nv) hC hn hF hf hk hkv
  have t2 := test_eq w (run_cardE hC hn hk) (run_wE hC hn hr)
  have t3 := test_supE hC hn hr hk
  have := test_and w t1 (fun _ => test_and w t2 (fun _ => t3))
  exact this.mono (by omega)

theorem run_countE {F : ClauseSet (SignedLiteral n)} (hF : Wide3 F) {f r rv : ℕ}
    (hf : env.getD f 0 = encF n F) (hr : env.getD r 0 = rv) :
    Run W (countE f r nv) env (coreClauses F (ruleW n rv) (ruleSet n rv)).card (8100 * (n + 1) ^ 4) := by
  have hsum : ∑ k ∈ range (cap n), ind (Cl n F k ∧ (decode n k).card = ruleW n rv ∧
      ruleSet n rv ⊆ decode n k) ≤ cap n := by
    calc _ ≤ ∑ k ∈ range (cap n), 1 := sum_le_sum (fun k _ => ind_le_one _)
      _ = cap n := by simp
  have := run_sum (f := fun k => ind (Cl n F k ∧ (decode n k).card = ruleW n rv ∧
      ruleSet n rv ⊆ decode n k)) (B := 1000 * (n + 1)) (run_cap hC hn)
    (fun k hk => test_coreE hC (gd k hn) hF (gd k hf) (gd k hr) (gd0 k) hk)
    (hC.cap_pow_lt hsum)
  have e : (coreClauses F (ruleW n rv) (ruleSet n rv)).card = ∑ k ∈ range (cap n),
      ind (Cl n F k ∧ (decode n k).card = ruleW n rv ∧ ruleSet n rv ⊆ decode n k) := by
    unfold coreClauses
    convert card_filter_clause hF (fun D => D.card = ruleW n rv ∧ ruleSet n rv ⊆ D)
  rw [← e] at this
  refine this.mono ?_
  have h : 1 + 17 + cap n * (1000 * (n + 1) + 1) ≤ 8100 * (n + 1) ^ (3 + 1) :=
    loop_le' (a := 8) (c := 1000) (d := 1) (by omega) (cap_le_pow n) (by rw [pow_one]) (by norm_num)
  exact h

theorem test_eligE {F : ClauseSet (SignedLiteral n)} (hF : Wide3 F) {L f r rv : ℕ}
    (hL : L * L < 2 ^ W) (hL1 : 1 ≤ L) (hf : env.getD f 0 = encF n F) (hr : env.getD r 0 = rv)
    (hrv : rv < ruleCap n) :
    Test W (eligE L f r nv) env (Elig F L rv) (8400 * (n + 1) ^ 4) := by
  have w := hC.one_le
  have m : 1 ≤ (n + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have := test_and w (test_slotE hC hn hr)
    (fun _ => test_le w (run_thrE hC hn hL hL1 hr) (run_countE hC hn hF hf hr))
  refine (this.iff ?_).mono (by omega)
  simp only [Elig]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (eligible_iff F hrv h1).mpr h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (eligible_iff F hrv h1).mp h2⟩

/-- **The rule choice.** The program computes the number of the chosen rule. -/
theorem run_ruleE {F : ClauseSet (SignedLiteral n)} (hF : Wide3 F) {L f : ℕ}
    (hL : L * L < 2 ^ W) (hL1 : 1 ≤ L) (hf : env.getD f 0 = encF n F) :
    Run W (ruleE L f nv) env (firstElig F L (ruleCap n)) (102000 * (n + 1) ^ 6) := by
  have w := hC.one_le
  have m : 1 ≤ (n + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hR := run_RE (env := env) hC hn
  have := run_fold (g := firstElig F L) (B := 8430 * (n + 1) ^ 4) hR hR
    (fun k hk => by
      have hn2 := gd (firstElig F L k) (gd k hn)
      have hf2 := gd (firstElig F L k) (gd k hf)
      have hk2 : (firstElig F L k :: k :: env).getD 1 0 = k := by simp
      have hst : (firstElig F L k :: k :: env).getD 0 0 = firstElig F L k := gd0 _
      rw [firstElig_succ F L hk]
      refine (run_ite (c := .ite (eligE L (f + 2) 1 (nv + 2)) (.lit 0) (RE (nv + 2)) (.var 1))
        (d := .var 0) (Bc := 8400 * (n + 1) ^ 4 + 15) (run_RE hC hn2) (run_var hst) ?_ ?_).mono (by omega)
      · intro hle
        rw [if_pos hle]
        by_cases he : Elig F L k
        · rw [if_pos he]
          have := run_ite (c := RE (nv + 2)) (d := .var 1) (v := k) (Bc := 13)
            (test_eligE hC hn2 hF hL hL1 hf2 hk2 hk) (run_zero w)
            (fun h => absurd (ind_pos he) (by omega))
            (fun _ => (run_var hk2).mono (by omega))
          exact this.mono (by omega)
        · rw [if_neg he]
          have := run_ite (c := RE (nv + 2)) (d := .var 1) (v := ruleCap n) (Bc := 13)
            (test_eligE hC hn2 hF hL hL1 hf2 hk2 hk) (run_zero w)
            (fun _ => run_RE hC hn2)
            (fun h => absurd (ind_neg he) (by omega))
          exact this.mono (by omega)
      · intro hle
        rw [if_neg hle]
        exact (run_var hst).mono (by omega))
  refine this.mono ?_
  have hRle : ruleCap n ≤ 12 * (n + 1) ^ 2 := by
    unfold ruleCap
    nlinarith
  have h := loop_le' (K := 1 + 13 + 13) (B := 8430 * (n + 1) ^ 4) (e := 1) (a := 12) (c := 8430) (d := 4)
    (C := 102000) (m := n + 1) (N := ruleCap n) (p := 2) (by omega) hRle le_rfl (by norm_num)
  exact h

end

end TransposeBase.Pseudo.CnfTree
