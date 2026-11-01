import TransposeBase.Pseudo.CnfRule
import SatBase.SparseSearch

/-!
# The children of a formula, and one step of the branching rule

The four main programs on bitset words, each with its value and a polynomial cost. Here `m = n + 1`.

* `run_normE`: `normE` computes `encF n (normalizeClauses F)`, in `93700 * m ^ 7` operations.
* `run_ruleE`: `ruleE` computes the number of the chosen rule (`firstElig`), in `102000 * m ^ 6` operations.
  `chooseSparseRule_none` and `chooseSparseRule_some` say what this number means.
* `run_leftE`, `run_rightE`: the two normalized children, in `244300 * m ^ 7` operations.
* `run_stepE`: one step along a path, as a function of the state, in `350000 * m ^ 7` operations.
-/

namespace TransposeBase.Pseudo.CnfTree

open SatBase Finset

variable {W : ℕ} {env : List ℕ} {n nv : ℕ}

section

variable (hC : Ctx W n) (hn : env.getD nv 0 = n)
include hC hn

theorem run_leftRawE {F : ClauseSet (SignedLiteral n)} (hF : Wide3 F) {f r rv w : ℕ}
    (hf : env.getD f 0 = encF n F) (hr : env.getD r 0 = rv) :
    Run W (leftRawE f r nv) env (encF n (coreLeft F w (ruleSet n rv))) (8050 * (n + 1) ^ 4) := by
  have ww := hC.one_le
  have := run_setE (body := tAnd (validE 0 (nv + 1)) (tOr (bitE (f + 1) 0) (eqSE 0 (r + 1) (nv + 1))))
    (B := 1000 * (n + 1))
    (p := fun k => ValidC n k ∧ (Cl n F k ∨ decode n k = ruleSet n rv))
    hC hn (fun k hk => by
      have hn1 := gd k hn
      have t1 := test_validE hC hn1 (gd0 k)
      have t2 := test_bit (nv := nv + 1) hC hn1 hF (gd k hf) (gd0 k) hk
      have t3 := test_eqSE hC hn1 (gd k hr) (gd0 k)
      have := test_and ww t1 (fun _ => test_or ww t2 (fun _ => t3))
      exact this.mono (by omega))
  have h2 : 18 + cap n * (1000 * (n + 1) + 4) ≤ 8050 * (n + 1) ^ (3 + 1) :=
    loop_le' (a := 8) (c := 1000) (d := 1) (by omega) (cap_le_pow n) (by rw [pow_one]) (by norm_num)
  refine (this.mono h2).val ?_
  exact setWord_eq_encF (hF.coreLeft w) (fun k _ => cl_coreLeft)

theorem run_rightRawE {F : ClauseSet (SignedLiteral n)} (hF : Wide3 F) {f r rv : ℕ}
    (hf : env.getD f 0 = encF n F) (hr : env.getD r 0 = rv) :
    Run W (rightRawE f r nv) env (encF n (coreRight F (ruleW n rv) (ruleSet n rv)))
      (150500 * (n + 1) ^ 7) := by
  have ww := hC.one_le
  have m0 : 1 ≤ n + 1 := by omega
  have m4 : 1 ≤ (n + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have := run_setE (body := tAnd (validE 0 (nv + 1)) (tOr (bitE (f + 1) 0)
      (tEx (capE (nv + 1))
        (tAnd (coreE (f + 2) (r + 2) 0 (nv + 2)) (petalE 0 1 (r + 2) (nv + 2))))))
    (B := 18800 * (n + 1) ^ 4)
    (p := fun k => ValidC n k ∧ (Cl n F k ∨ ∃ j < cap n, Cl n F j ∧
        (decode n j).card = ruleW n rv ∧ ruleSet n rv ⊆ decode n j ∧
        decode n j \ ruleSet n rv = decode n k))
    hC hn (fun k hk => by
      have hn1 := gd k hn
      have hf1 := gd k hf
      have hr1 := gd k hr
      have t1 := test_validE hC hn1 (gd0 k)
      have t2 := test_bit (nv := nv + 1) hC hn1 hF hf1 (gd0 k) hk
      have hinner := test_ex (N := cap n) (B := 2310 * (n + 1))
        (p := fun j => (Cl n F j ∧ (decode n j).card = ruleW n rv ∧ ruleSet n rv ⊆ decode n j) ∧
          decode n j \ ruleSet n rv = decode n k) ww
        (run_cap hC hn1)
        (fun j hj => by
          have hn2 := gd j hn1
          have t3 := test_coreE hC hn2 hF (gd j hf1) (gd j hr1) (gd0 j) hj
          have t4 := test_petalE hC hn2 (gd j hr1) (gd0 j) (gd j (gd0 k))
          have := test_and ww t3 (fun _ => t4)
          exact this.mono (by omega))
      have hb : 4 + 17 + cap n * (2310 * (n + 1) + 4) ≤ 18600 * (n + 1) ^ (3 + 1) :=
        loop_le' (a := 8) (c := 2310) (d := 1) (by omega) (cap_le_pow n) (by rw [pow_one]) (by norm_num)
      have := test_and ww t1 (fun _ => test_or ww t2 (fun _ => hinner))
      refine (this.iff ?_).mono ?_
      · simp only [and_assoc]
      · simp only [show 3 + 1 = 4 from rfl] at hb
        omega)
  have h2 : 18 + cap n * (18800 * (n + 1) ^ 4 + 4) ≤ 150500 * (n + 1) ^ (3 + 4) :=
    loop_le' (a := 8) (c := 18800) (d := 4) (by omega) (cap_le_pow n) le_rfl (by norm_num)
  refine (this.mono h2).val ?_
  exact setWord_eq_encF (hF.coreRight _ _) (fun k _ => cl_coreRight hF)

/-- The child program, for a rule number that names a candidate. -/
theorem run_childE {F : ClauseSet (SignedLiteral n)} (hF : Wide3 F) {f r b rv bv : ℕ}
    (hf : env.getD f 0 = encF n F) (hr : env.getD r 0 = rv) (hb : env.getD b 0 = bv) :
    Run W (childE f r b nv) env
      (encF n (normalizeClauses (if bv = 0 then coreLeft F (ruleW n rv) (ruleSet n rv)
        else coreRight F (ruleW n rv) (ruleSet n rv)))) (244300 * (n + 1) ^ 7) := by
  have m4 : (n + 1) ^ 4 ≤ (n + 1) ^ 7 := pow_le_pow_m n (by norm_num)
  have m1 : 1 ≤ (n + 1) ^ 7 := Nat.one_le_pow _ _ (by omega)
  set G := if bv = 0 then coreLeft F (ruleW n rv) (ruleSet n rv)
    else coreRight F (ruleW n rv) (ruleSet n rv) with hG
  have hGw : Wide3 G := by
    rw [hG]
    split
    · exact hF.coreLeft _
    · exact hF.coreRight _ _
  have ha := run_ite (c := leftRawE f r nv) (d := rightRawE f r nv) (v := encF n G)
    (Bc := 150500 * (n + 1) ^ 7) (run_var hb) (run_zero hC.one_le)
    (fun h => by
      rw [hG, if_pos (by omega)]
      exact (run_leftRawE hC hn hF hf hr).mono (by omega))
    (fun h => by
      rw [hG, if_neg (by omega)]
      exact run_rightRawE hC hn hF hf hr)
  have hc := run_normE (F := G) hC (gd _ hn) hGw (f := 0) (gd0 _)
  exact (run_let ha hc).mono (by omega)

theorem run_leftE {F : ClauseSet (SignedLiteral n)} (hF : Wide3 F) {f r b rv : ℕ}
    (hf : env.getD f 0 = encF n F) (hr : env.getD r 0 = rv) (hb : env.getD b 0 = 0) :
    Run W (childE f r b nv) env (encF n (normalizedCoreLeft F (ruleW n rv) (ruleSet n rv)))
      (244300 * (n + 1) ^ 7) := by
  have := run_childE hC hn hF hf hr hb
  rw [if_pos rfl] at this
  exact this

theorem run_rightE {F : ClauseSet (SignedLiteral n)} (hF : Wide3 F) {f r b rv bv : ℕ}
    (hf : env.getD f 0 = encF n F) (hr : env.getD r 0 = rv) (hb : env.getD b 0 = bv) (hb0 : bv ≠ 0) :
    Run W (childE f r b nv) env (encF n (normalizedCoreRight F (ruleW n rv) (ruleSet n rv)))
      (244300 * (n + 1) ^ 7) := by
  have := run_childE hC hn hF hf hr hb
  rw [if_neg hb0] at this
  exact this

end

/-! ### One step along a path -/

/-- The state after one move. A leaf stays where it is, so that this function is total. -/
noncomputable def stepS {L : ℕ} (hL : 2 ≤ L) (s : SparseState n L) (b : Bool) : SparseState n L :=
  match hr : chooseSparseRule s.formula L with
  | none => s
  | some r => if b then s.right hL r hr else s.left hL r hr

theorem stepS_none {L : ℕ} (hL : 2 ≤ L) (s : SparseState n L) (b : Bool)
    (h : chooseSparseRule s.formula L = none) : stepS hL s b = s := by
  unfold stepS
  split
  · rfl
  · rename_i r hr
    simp [h] at hr

theorem stepS_some {L : ℕ} (hL : 2 ≤ L) (s : SparseState n L) (b : Bool)
    (r : ℕ × Finset (SignedLiteral n)) (h : chooseSparseRule s.formula L = some r) :
    stepS hL s b = if b then s.right hL r h else s.left hL r h := by
  unfold stepS
  split
  · rename_i hn
    simp [h] at hn
  · rename_i r' hr'
    have he : r = r' := by simpa only [h, Option.some.injEq] using hr'
    subst r'
    rfl

/-- The word of the state after the move in the variable `b`, from the word of the state in the variable
`f`: choose the rule, and if there is one, build the child. -/
def stepE (L f b nv : ℕ) : Expr :=
  .letE (ruleE L f nv)
    (.ite (RE (nv + 1)) (.var 0) (.var (f + 1)) (childE (f + 1) 0 (b + 1) (nv + 1)))

theorem run_stepE (hC : Ctx W n) (hn : env.getD nv 0 = n) {L : ℕ} (hL : 2 ≤ L) (hLL : L * L < 2 ^ W)
    (s : SparseState n L) {f b bv : ℕ} (hf : env.getD f 0 = encF n s.formula)
    (hb : env.getD b 0 = bv) :
    Run W (stepE L f b nv) env (encF n (stepS hL s (decide (bv ≠ 0))).formula) (350000 * (n + 1) ^ 7) := by
  have hF : Wide3 s.formula := s.width
  have m6 : (n + 1) ^ 6 ≤ (n + 1) ^ 7 := pow_le_pow_m n (by norm_num)
  have m1 : 1 ≤ (n + 1) ^ 7 := Nat.one_le_pow _ _ (by omega)
  have hr := run_ruleE (L := L) hC hn hF hLL (by omega) hf
  set rv := firstElig s.formula L (ruleCap n) with hrv
  have hn1 := gd rv hn
  have hf1 := gd rv hf
  have hb1 := gd rv hb
  have hr0 : (rv :: env).getD 0 0 = rv := gd0 rv
  have main : Run W (.ite (RE (nv + 1)) (.var 0) (.var (f + 1)) (childE (f + 1) 0 (b + 1) (nv + 1)))
      (rv :: env) (encF n (stepS hL s (decide (bv ≠ 0))).formula) (244300 * (n + 1) ^ 7 + 15) := by
    refine (run_ite (Bc := 244300 * (n + 1) ^ 7) (run_RE hC hn1) (run_var hr0) ?_ ?_).mono (by omega)
    · intro hle
      have hnone : chooseSparseRule s.formula L = none := by
        rw [chooseSparseRule_none]
        cases hs : chooseSparseRule s.formula L with
        | none => exact chooseSparseRule_none.mp hs
        | some r =>
          have := (chooseSparseRule_some hs).1
          omega
      rw [stepS_none hL s _ hnone]
      exact (run_var hf1).mono (by omega)
    · intro hlt
      cases hs : chooseSparseRule s.formula L with
      | none =>
        have := chooseSparseRule_none.mp hs
        omega
      | some r =>
        have hsome := (chooseSparseRule_some hs).2
        rw [stepS_some hL s _ r hs]
        rw [← hrv] at hsome
        by_cases hb0 : bv = 0
        · have := run_leftE (rv := rv) hC hn1 hF hf1 hr0 (b := b + 1) (hb1.trans hb0)
          simpa [hb0, SparseState.left, hsome, ruleOf] using this
        · have := run_rightE (rv := rv) hC hn1 hF hf1 hr0 hb1 hb0
          simpa [hb0, SparseState.right, hsome, ruleOf] using this
  exact (run_let hr main).mono (by omega)

end TransposeBase.Pseudo.CnfTree
