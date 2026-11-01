import TransposeBase.Pseudo.CnfNetTable

/-!
# The network of a bitset formula, as programs: the node function and the bounds

* `nodeE`: the node function. It is `phiN` on the bits of an assignment word (`run_nodeE`).
* `table_costs`, `node_cost_le`, `count_costs`: the operations, polynomial in `n`.
* `fits_of_poly`: a word size polynomial in `n` is enough, for the field width `fwN`.
* `cnf_net_main`: all of this together.
-/

set_option linter.unusedSectionVars false

namespace TransposeBase.Pseudo.CnfNet

open Finset SatBase TransposeBase.General TransposeBase.Sat TransposeBase.Pseudo.CnfTree
  TransposeBase.Pseudo.Place

variable {W n : ℕ} {F : ClauseSet (SignedLiteral n)} {env : List ℕ} {nv fv : ℕ}

/-! ### The node program -/

/-- The variable node `α`: the bits of the wires with tail `α` are equal to the bit of wire `α`. -/
def varTestE : Expr :=
  tAll (.var 2) (tOr (tNot (tEq (fieldE 7 0 6) (.var 1))) (tEq (bitE 2 0) (bitE 2 1)))

/-- The clause node `α`: the `y` bit of some occurrence of this clause has the sign of its literal. -/
def clTestE (nv fv : ℕ) : Expr :=
  .letE (occCapE nv) <| tEx (.var 0) <|
    tAnd (validE (nv + 2) (fv + 2) 0) <|
      tAnd (tEq (.add (.var (nv + 2)) (.letE (.div (.var 0) (.lit 3)) (rkcE (fv + 3) 0))) (.var 2)) <|
        .letE (.add (.var 4) (.add (.var (nv + 2)) (rkE (nv + 2) (fv + 2) 0))) <|
          tEq (bitE 4 0) (.mod (.sub (digitE (nv + 3) 1) (.lit 1)) (.lit 2))

/-- The node function. It is evaluated in `α :: assign :: <core environment>`. The variables `nv`, `fv` hold `n`
and the word of the formula in this environment. -/
def nodeE (nv fv : ℕ) : Expr :=
  .ite (.var nv) (.var 0) (.ite (.var 3) (.add (.var 0) (.var nv)) (.lit 1) (clTestE nv fv)) varTestE

/-- The test of `clTestE` at the occurrence `o`. -/
def occOK (n : ℕ) (F : ClauseSet (SignedLiteral n)) (α A m o : ℕ) : Prop :=
  validN n F o ∧ n + rk (Cl n F) (o / 3) = α ∧
    (A.testBit (m + (n + rk (validN n F) o))).toNat = (dg n (o / 3) (o % 3) - 1) % 2

/-- The bound on the operations of `nodeE`. -/
def nodeCost (n m : ℕ) : ℕ :=
  35 + m * 57 + 3 * cap n * (152 + cap n * 14 + 3 * cap n * 44)

section Node

variable {fw tT c : ℕ} {rest : List ℕ}

theorem test_varTestE (h : Fits W n F fw) (hF : Wide3 F) {α A : ℕ} (hα : α < 2 * (n + 3 * cap n)) :
    Test W varTestE (α :: A :: mN n F :: vN n F :: c :: fw :: tT :: rest)
      (∀ e < mN n F, ¬ fld fw tT e = α ∨ (A.testBit e).toNat = (A.testBit α).toNat)
      (2 + mN n F * 57) := by
  have hw1 := h.big.ctx.one_le
  have hw2 := h.big.ctx.two_le
  have hmle := mN_le n F
  have hmlt := h.big.two_m_lt
  refine (test_all hw1 (run_var (by simp)) (B := 56) fun e he => ?_).mono ?_
  · have hf : (e * fw) < W := by
      calc e * fw < (mN n F + vN n F + 8) * fw := Nat.mul_lt_mul_of_pos_right (by omega) h.pos
        _ ≤ W := h.hfw
    have hfwW : fw < W := by
      calc fw = 1 * fw := by ring
        _ < (mN n F + vN n F + 8) * fw := Nat.mul_lt_mul_of_pos_right (by omega) h.pos
        _ ≤ W := h.hfw
    set E : List ℕ := e :: α :: A :: mN n F :: vN n F :: c :: fw :: tT :: rest with hE
    have r1 : Run W (fieldE 7 0 6) E (fld fw tT e) 9 :=
      ⟨eval_fieldE (by simp [hE]) (by simp [hE]) (by simp [hE]) hf hfwW, (ops_fieldE W 7 0 6 E).le⟩
    have r2 : Run W (.var 1) E α 1 := run_var (by simp [hE])
    have t1 := test_not hw1 (test_eq hw1 r1 r2)
    have b1 := run_bitE (f := 2) (i := 0) (env := E) hw2 (fv' := A) (iv := e) (by simp [hE])
      (by simp [hE]) (by omega)
    have b2 := run_bitE (f := 2) (i := 1) (env := E) hw2 (fv' := A) (iv := α) (by simp [hE])
      (by simp [hE]) (by omega)
    have t2 := test_eq hw1 b1 b2
    exact (test_or hw1 t1 (fun _ => t2)).mono (by norm_num)
  · have e : 1 + 1 + mN n F * (56 + 1) = 2 + mN n F * 57 := by ring
    rw [e]

theorem test_clTestE (h : Fits W n F fw) (hF : Wide3 F) {α A : ℕ}
    (hn : (α :: A :: mN n F :: vN n F :: c :: fw :: tT :: rest).getD nv 0 = n)
    (hf : (α :: A :: mN n F :: vN n F :: c :: fw :: tT :: rest).getD fv 0 = encF n F) :
    Test W (clTestE nv fv) (α :: A :: mN n F :: vN n F :: c :: fw :: tT :: rest)
      (∃ o < 3 * cap n, occOK n F α A (mN n F) o)
      (25 + 3 * cap n * (152 + cap n * 14 + 3 * cap n * 44)) := by
  have hw1 := h.big.ctx.one_le
  have hw2 := h.big.ctx.two_le
  have hmle := mN_le n F
  have hmlt := h.big.two_m_lt
  set env : List ℕ := α :: A :: mN n F :: vN n F :: c :: fw :: tT :: rest with henv
  have hbody : ∀ o < 3 * cap n, Test W (tAnd (validE (nv + 2) (fv + 2) 0) <|
      tAnd (tEq (.add (.var (nv + 2)) (.letE (.div (.var 0) (.lit 3)) (rkcE (fv + 3) 0))) (.var 2)) <|
        .letE (.add (.var 4) (.add (.var (nv + 2)) (rkE (nv + 2) (fv + 2) 0))) <|
          tEq (bitE 4 0) (.mod (.sub (digitE (nv + 3) 1) (.lit 1)) (.lit 2)))
      (o :: (3 * cap n) :: env) (occOK n F α A (mN n F) o) (148 + cap n * 14 + 3 * cap n * 44) := by
    intro o ho
    set E : List ℕ := o :: (3 * cap n) :: env with hE
    have hn2 : E.getD (nv + 2) 0 = n := by simpa [hE] using hn
    have hf2 : E.getD (fv + 2) 0 = encF n F := by simpa [hE] using hf
    have t0 := test_validE (o := 0) (x := o) h.big hF hn2 hf2 (by simp [hE]) ho
    have hk : o / 3 ≤ cap n := by omega
    have hrk : ∀ x, x ≤ cap n → rk (Cl n F) x ≤ cap n := fun x hx => (rk_le _ _).trans hx
    have t1 : Test W (tEq (.add (.var (nv + 2)) (.letE (.div (.var 0) (.lit 3)) (rkcE (fv + 3) 0))) (.var 2)) E
        (n + rk (Cl n F) (o / 3) = α) (21 + cap n * 14) := by
      have a1 : Run W (.div (.var 0) (.lit 3)) E (o / 3) 3 :=
        run_div (run_var (by simp [hE])) (run_three h.big)
      have a2 := run_rkcE (fv := fv + 3) (x := 0) (xv := o / 3) (env := (o / 3) :: E) h.big hF
        (gd _ hf2) (by simp) hk
      have a3 := run_let a1 a2
      have hsum : n + rk (Cl n F) (o / 3) < 2 ^ W := h.big.m_lt_pow (by
        have := hrk _ hk
        have := Ctx.G_le_cap n
        omega)
      have a4 := run_add (run_var hn2) a3 hsum
      have a5 : Run W (.var 2) E α 1 := run_var (by simp [hE, henv])
      refine (test_eq hw1 a4 a5).mono ?_
      have : o / 3 * 7 ≤ cap n * 7 := Nat.mul_le_mul_right _ hk
      omega
    have t2 : validN n F o → Test W (.letE (.add (.var 4) (.add (.var (nv + 2)) (rkE (nv + 2) (fv + 2) 0))) <|
        tEq (bitE 4 0) (.mod (.sub (digitE (nv + 3) 1) (.lit 1)) (.lit 2))) E
        ((A.testBit (mN n F + (n + rk (validN n F) o))).toNat = (dg n (o / 3) (o % 3) - 1) % 2)
        (78 + 3 * cap n * 44) := by
      intro hv
      have hrl : rk (validN n F) o ≤ 3 * cap n := (rk_le _ _).trans ho.le
      have a1 := run_rkE (x := 0) (xv := o) h.big hF hn2 hf2 (by simp [hE]) ho.le
      have a2 := run_add (run_var hn2) a1 (h.big.m_lt_pow (by omega))
      have hidx : mN n F + (n + rk (validN n F) o) < W := by omega
      have a3 := run_add (run_var (i := 4) (env := E) (v := mN n F) (by simp [hE, henv])) a2
        (hidx.trans Nat.lt_two_pow_self)
      set idx := mN n F + (n + rk (validN n F) o) with hidxdef
      have b1 := run_bitE (f := 4) (i := 0) (env := idx :: E) (fv' := A) (iv := idx) hw2
        (by simp [hE, henv]) (by simp) hidx
      have hd := run_digitE (nv := nv + 3) (o := 1) (x := o) (env := idx :: E) h.big (gd _ hn2)
        (by simp [hE])
      have hpos : 1 ≤ dg n (o / 3) (o % 3) := Nat.pos_of_ne_zero hv.2
      have hlt : dg n (o / 3) (o % 3) < 2 ^ W := h.big.lt_pow ((dg_lt _ _ _).le.trans (G_le_three_cap n))
      have h2lit : (2 : ℕ) < 2 ^ W := by
        calc 2 < 2 ^ 2 := by norm_num
          _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hw2
      have b2 := run_mod (run_sub hd (run_one hw1) hpos hlt) (run_lit h2lit)
      have t := test_eq hw1 b1 b2
      refine (run_let a3 t).mono ?_
      have : o * 44 ≤ 3 * cap n * 44 := Nat.mul_le_mul_right _ ho.le
      omega
    refine (test_and hw1 t0 (fun hv => test_and hw1 t1 (fun _ => t2 hv))).mono ?_
    omega
  have hex := test_ex (N := 3 * cap n) hw1 (env := (3 * cap n) :: env) (run_var (gd0 _)) hbody
  refine (run_let (run_occCap h.big hn) hex).mono ?_
  have e : 148 + cap n * 14 + 3 * cap n * 44 + 4 = 152 + cap n * 14 + 3 * cap n * 44 := by ring
  rw [e]
  omega

theorem bool_toNat_inj {a b : Bool} (h : a.toNat = b.toNat) : a = b := by
  cases a <;> cases b <;> simp_all

theorem phi_congr {k : Type*} [CommRing k] {ν₁ ν₂ : Node F} (h : ν₁ = ν₂)
    {f₁ : Inc (tl F) (hd F) ν₁ → Bool} {f₂ : Inc (tl F) (hd F) ν₂ → Bool}
    (hf : ∀ w h₁ h₂, f₁ ⟨w, h₁⟩ = f₂ ⟨w, h₂⟩) : (phi F ν₁ f₁ : k) = phi F ν₂ f₂ := by
  subst h
  congr 1
  funext ⟨w, hw⟩
  exact hf w hw hw

theorem ind_cast {p q : Prop} {_i : Decidable q} (h : p ↔ q) : ((ind p : ℕ) : ℤ) = if q then 1 else 0 := by
  by_cases hq : q
  · rw [ind_pos (h.mpr hq), if_pos hq]
    rfl
  · rw [ind_neg (fun hp => hq (h.mp hp)), if_neg hq]
    rfl

/-- The reading of a wire at a node, from the assignment word `A`. -/
noncomputable abbrev gOf (hF : Wide3 F) (α : Fin (vN n F)) (A : ℕ) : Inc (tailN hF) (headN hF) α → Bool :=
  General.read (tailN hF) (headN hF) α (fun e => A.testBit e) (fun e => A.testBit (mN n F + e))

theorem phiN_eN {k : Type*} [CommRing k] (hF : Wide3 F) (ν : Node F)
    (g : Inc (tailN hF) (headN hF) (eN hF ν) → Bool) :
    (phiN hF (eN hF ν) g : k) = phi F ν (fun w => g ⟨eW hF w.1, by
      rcases w.2 with h | h
      · left
        rw [tailN_eW, h]
      · right
        rw [headN_eW, h]⟩) :=
  phi_congr ((eN hF).symm_apply_apply ν) (fun _ _ _ => rfl)

theorem run_node_var {E : List ℕ} {α Bc : ℕ} {P : Prop} (hw1 : 1 ≤ W) (hn : E.getD nv 0 = n)
    (h0 : E.getD 0 0 = α) (hlt : ¬ n ≤ α)
    (t : Test W varTestE E P Bc) : Run W (nodeE nv fv) E (ind P) (3 + Bc) := by
  exact run_ite (run_var hn) (run_var h0) (fun h => absurd h hlt) (fun _ => t)

theorem run_node_cl {E : List ℕ} {α vv Bc Bd : ℕ} {P : Prop} (hn : E.getD nv 0 = n)
    (h0 : E.getD 0 0 = α) (h3 : E.getD 3 0 = vv) (hle : n ≤ α) (hlt : ¬ vv ≤ α + n)
    (hs : α + n < 2 ^ W) (t : Test W (clTestE nv fv) E P Bd) (hB : 5 + Bd ≤ Bc) :
    Run W (nodeE nv fv) E (ind P) (3 + Bc) := by
  refine run_ite (run_var hn) (run_var h0) (fun _ => ?_) (fun h => absurd hle h)
  have a := run_add (run_var h0) (run_var hn) hs
  exact (run_ite (run_var h3) a (fun h => absurd h hlt) (fun _ => t)).mono (by omega)

theorem run_node_end {E : List ℕ} {α vv Bc : ℕ} (hw1 : 1 ≤ W) (hn : E.getD nv 0 = n)
    (h0 : E.getD 0 0 = α) (h3 : E.getD 3 0 = vv) (hle : n ≤ α) (hge : vv ≤ α + n)
    (hs : α + n < 2 ^ W) (hB : 6 ≤ Bc) : Run W (nodeE nv fv) E 1 (3 + Bc) := by
  refine run_ite (run_var hn) (run_var h0) (fun _ => ?_) (fun h => absurd hle h)
  have a := run_add (run_var h0) (run_var hn) hs
  exact (run_ite (Bc := 1) (run_var h3) a (fun _ => run_one hw1) (fun h => absurd hge h)).mono (by omega)

/-- **The node program.** Its value is `phiN` on the bits of the assignment word, read by `General.read`. -/
theorem run_nodeE {hT : ℕ} (h : Fits W n F fw) (hF : Wide3 F) (N : NetT fw tT hT (tailN hF) (headN hF))
    (α : Fin (vN n F)) (A : ℕ)
    (hn : ((α : ℕ) :: A :: mN n F :: vN n F :: c :: fw :: tT :: rest).getD nv 0 = n)
    (hf : ((α : ℕ) :: A :: mN n F :: vN n F :: c :: fw :: tT :: rest).getD fv 0 = encF n F) :
    ∃ b : ℕ, Run W (nodeE nv fv) ((α : ℕ) :: A :: mN n F :: vN n F :: c :: fw :: tT :: rest) b
        (nodeCost n (mN n F)) ∧ (b : ℤ) = phiN hF α (gOf hF α A) := by
  classical
  have hw1 := h.big.ctx.one_le
  have hmle := mN_le n F
  have hvle := vN_le hF
  have hGc := Ctx.G_le_cap n
  have hmlt := h.big.two_m_lt
  have hα2 : (α : ℕ) < 2 * (n + 3 * cap n) := by have := α.2; omega
  have hs : (α : ℕ) + n < 2 ^ W := h.big.m_lt_pow (by have := α.2; omega)
  have tv := test_varTestE (c := c) (tT := tT) (rest := rest) (A := A) h hF hα2
  have tc := test_clTestE (c := c) (tT := tT) (rest := rest) h hF (A := A) hn hf
  have hcost : nodeCost n (mN n F) = 3 + (32 + mN n F * 57 + 3 * cap n * (152 + cap n * 14 + 3 * cap n * 44)) := by
    simp only [nodeCost]
    omega
  rw [hcost]
  obtain ⟨ν, rfl⟩ := (eN hF).surjective α
  rw [phiN_eN]
  rcases ν with u | e | u
  · -- a variable node
    have hval : ((eN hF (.inl u) : Fin _) : ℕ) = u := rfl
    refine ⟨_, (run_node_var (fv := fv) hw1 hn (gd0 _) (by rw [hval]; exact not_le.mpr u.2) tv).mono
      (by omega), ?_⟩
    refine ind_cast ?_
    have hgv : ∀ a : Inc (tl F) (hd F) (.inl u),
        tailN hF (eW hF a.1) = eN hF (.inl u) := fun a => by
      rw [tailN_eW]
      rcases a.2 with h1 | h1
      · rw [h1]
      · cases hw : a.1 <;> simp [hw, hd] at h1
    constructor
    · intro hP a b
      have key : ∀ a : Inc (tl F) (hd F) (.inl u), A.testBit (eW hF a.1) = A.testBit u := by
        intro a
        have := hP (eW hF a.1) (eW hF a.1).2
        rw [N.tail_eq, hgv a] at this
        rcases this with h1 | h1
        · exact absurd rfl h1
        · rw [hval] at h1
          exact bool_toNat_inj h1
      simp only [General.read, if_pos (hgv a), if_pos (hgv b), key a, key b]
    · intro hP e he
      by_cases h1 : fld fw tT e = ((eN hF (.inl u) : Fin _) : ℕ)
      · right
        have h2 : tailN hF ⟨e, he⟩ = eN hF (.inl u) := Fin.ext ((N.tail_eq ⟨e, he⟩).symm.trans h1)
        set w := (eW hF).symm ⟨e, he⟩ with hw
        have h3 : eW hF w = ⟨e, he⟩ := by simp [hw]
        rw [← h3, tailN_eW] at h2
        have h4 : tl F w = .inl u := (eN hF).injective h2
        have := hP ⟨w, Or.inl h4⟩ ⟨.inl u, Or.inl rfl⟩
        simp only [General.read, if_pos (hgv ⟨w, Or.inl h4⟩), if_pos (hgv ⟨.inl u, Or.inl rfl⟩)] at this
        rw [h3] at this
        have e2 : ((eW hF (.inl u) : Fin _) : ℕ) = u := rfl
        rw [hval, ← e2, ← this]
      · exact Or.inl h1
  · -- a clause node
    have hval : ((eN hF (.inr (.inl e)) : Fin _) : ℕ) = n + rk (Cl n F) (code n e.1) := rfl
    have hr : rk (Cl n F) (code n e.1) < clN n F := rk_lt (cl_code hF e.2) (code_spec (hF _ e.2)).1
    refine ⟨_, run_node_cl (vv := vN n F) hn (gd0 _) (by simp) (by rw [hval]; omega)
      (by rw [hval]; simp only [vN]; omega) hs tc (by omega), ?_⟩
    refine ind_cast ?_
    have hne : ∀ j : OccW F, tailN hF (eW hF (.inr j)) ≠ eN hF (.inr (.inl e)) := fun j h1 => by
      rw [tailN_eW] at h1
      have := (eN hF).injective h1
      simp [tl] at this
    have hrd : ∀ l : LI F e, General.read (tailN hF) (headN hF) (eN hF (.inr (.inl e))) (fun x => A.testBit x)
        (fun x => A.testBit (mN n F + x)) ⟨eW hF (.inr ⟨e, l⟩), by
          right
          rw [headN_eW]
          rfl⟩ = A.testBit (mN n F + (n + rk (validN n F) (occNum (⟨e, l⟩ : OccW F)))) := fun l => by
      simp only [General.read, if_neg (hne ⟨e, l⟩)]
      rfl
    constructor
    · rintro ⟨o, ho, hv, hc, hb⟩
      obtain ⟨⟨e', l⟩, rfl, hd, hdiv⟩ := occ_of_valid hF hv ho
      simp only at hdiv
      rw [hval, hdiv] at hc
      have h1 : rk (Cl n F) (code n e'.1) = rk (Cl n F) (code n e.1) := by omega
      have h2 := rk_inj (cl_code hF e'.2) (cl_code hF e.2) h1
      have h3 : e' = e := Subtype.ext (code_inj hF e'.2 e.2 h2)
      subst h3
      refine ⟨l, ?_⟩
      have h4 := hrd l
      rw [hd, lit_sign] at hb
      exact h4.trans (bool_toNat_inj hb)
    · rintro ⟨l, hl⟩
      have h4 := hrd l
      refine ⟨occNum (⟨e, l⟩ : OccW F), occ_lt hF _, valid_occ hF _, ?_, ?_⟩
      · rw [hval, occ_div]
      · rw [occ_dg hF, lit_sign]
        have h5 := h4.symm.trans hl
        rw [h5]
  · -- an end node
    have hval : ((eN hF (.inr (.inr u)) : Fin _) : ℕ) = n + clN n F + u := rfl
    refine ⟨1, run_node_end (vv := vN n F) hw1 hn (gd0 _) (by simp) (by rw [hval]; omega)
      (by rw [hval]; simp only [vN]; omega) hs (by omega), ?_⟩
    simp only [Nat.cast_one]
    rfl

end Node

/-! ### Costs and sizes -/

theorem tbl_le {n Bf Bo a : ℕ} (hna : n ≤ a) (hca : cap n ≤ 8 * a) (ha : 1 ≤ a) (h1 : Bf + 7 ≤ 100 * a)
    (h2 : Bo ≤ 100 * a) : tblCost n Bf Bo ≤ 30000 * (a * a) := by
  have haa : 1 ≤ a * a := Nat.mul_pos ha ha
  have h3 : n * (Bf + 7) ≤ a * (100 * a) := Nat.mul_le_mul hna h1
  have h4 : 56 + 3 * cap n * 44 + Bo ≤ 1212 * a := by omega
  have h5 : 3 * cap n * (56 + 3 * cap n * 44 + Bo) ≤ (24 * a) * (1212 * a) :=
    Nat.mul_le_mul (by omega) h4
  have e1 : a * (100 * a) = 100 * (a * a) := by ring
  have e2 : (24 * a) * (1212 * a) = 29088 * (a * a) := by ring
  simp only [tblCost]
  omega

theorem pow6_eq (n : ℕ) : (n + 1) ^ 6 = (n + 1) ^ 3 * (n + 1) ^ 3 := by ring

theorem self_le_cube (n : ℕ) : n + 1 ≤ (n + 1) ^ 3 := Nat.le_self_pow (by norm_num) _

/-- The operations of the tables. -/
theorem table_costs (n : ℕ) :
    tblCost n 1 28 ≤ 30000 * (n + 1) ^ 6 ∧
    tblCost n (24 + cap n * 7) (9 + cap n * 7) ≤ 30000 * (n + 1) ^ 6 := by
  have h1 := self_le_cube n
  have hc := cap_le_pow n
  rw [pow6_eq]
  constructor
  · exact tbl_le (by omega) hc (by omega) (by omega) (by omega)
  · exact tbl_le (by omega) hc (by omega) (by omega) (by omega)

/-- The operations of the node program. -/
theorem node_cost_le (n : ℕ) (F : ClauseSet (SignedLiteral n)) :
    nodeCost n (mN n F) ≤ 34000 * (n + 1) ^ 6 := by
  have h1 := self_le_cube n
  have hc := cap_le_pow n
  have hm := mN_le n F
  rw [pow6_eq]
  generalize (n + 1) ^ 3 = a at *
  have haa : 1 ≤ a * a := Nat.mul_pos (by omega) (by omega)
  have h2 : mN n F ≤ 25 * a := by omega
  have ha1 : a ≤ a * a := Nat.le_mul_of_pos_left _ (by omega)
  have h4 : 152 + cap n * 14 + 3 * cap n * 44 ≤ 1320 * a := by omega
  have h5 : 3 * cap n * (152 + cap n * 14 + 3 * cap n * 44) ≤ (24 * a) * (1320 * a) :=
    Nat.mul_le_mul (by omega) h4
  have e2 : (24 * a) * (1320 * a) = 31680 * (a * a) := by ring
  simp only [nodeCost]
  omega

/-- The operations of `mE` and of `vE`. -/
theorem count_costs (n : ℕ) :
    24 + 3 * cap n * 44 ≤ 1080 * (n + 1) ^ 3 ∧ 24 + cap n * 7 ≤ 80 * (n + 1) ^ 3 := by
  have hc := cap_le_pow n
  have h1 : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  omega

/-- The field width. -/
def fwN (K m v : ℕ) : ℕ := K + 3 + m + v

/-- The field width, for variables `m`, `v`. -/
def fwE (K im iv : ℕ) : Expr := .add (.add (.lit (K + 3)) (.var im)) (.var iv)

/-- **The field width and the word size.** For this field width, a word size that is a polynomial in `n` is
enough for the tables and for the placement. -/
theorem fits_of_poly (hF : Wide3 F) {d K : ℕ} (hdeg : ∀ v, variableOccurrences F v ≤ d) (hK : 0 < K)
    (hW : (48 + (2 * d + K + 12) ^ 2) * (n + 1) ^ 3 ≤ W) :
    Fits W n F (fwN K (mN n F) (vN n F)) ∧ Bd W (mN n F) (vN n F) (fwN K (mN n F) (vN n F)) K := by
  obtain ⟨hm1, hm2⟩ := mN_bounds hF hdeg
  have hv := vN_le hF
  set m := mN n F with hmdef
  set v := vN n F with hvdef
  have hsum : m + v ≤ (2 * d + 3) * n + 1 := by
    have : (1 + d) * n = n + d * n := by ring
    have e : (2 * d + 3) * n = 2 * (d * n) + 3 * n := by ring
    omega
  set A := 2 * d + K + 12 with hA
  have h1 : m + v + 8 ≤ A * (n + 1) := by
    have e : (2 * d + 3) * n = 2 * d * n + 3 * n := by ring
    have e2 : A * (n + 1) = 2 * d * n + K * n + 12 * n + A := by rw [hA]; ring
    omega
  have h2 : fwN K m v ≤ A * (n + 1) := by
    have e : (2 * d + 3) * n = 2 * d * n + 3 * n := by ring
    have e2 : A * (n + 1) = 2 * d * n + K * n + 12 * n + A := by rw [hA]; ring
    simp only [fwN]
    omega
  have h3 : (m + v + 8) * fwN K m v ≤ A ^ 2 * (n + 1) ^ 3 := by
    calc (m + v + 8) * fwN K m v ≤ (A * (n + 1)) * (A * (n + 1)) := Nat.mul_le_mul h1 h2
      _ = A ^ 2 * (n + 1) ^ 2 := by ring
      _ ≤ A ^ 2 * (n + 1) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by norm_num))
  have h4 : (48 + A ^ 2) * (n + 1) ^ 3 = 48 * (n + 1) ^ 3 + A ^ 2 * (n + 1) ^ 3 := by ring
  have h5 : 6 * (2 * n + 2) ^ 3 = 48 * (n + 1) ^ 3 := by ring
  have hB : Bd W m v (fwN K m v) K := by
    refine ⟨?_, by omega, hK⟩
    have h6 : K + m + v < 2 ^ (K + m + v) := Nat.lt_two_pow_self
    have h7 : 2 ^ fwN K m v = 8 * 2 ^ (K + m + v) := by
      have : fwN K m v = (K + m + v) + 3 := by simp only [fwN]; omega
      rw [this, pow_add]
      ring
    omega
  exact ⟨⟨⟨by omega⟩, hB.v_lt, hB.hW, hB.fw_pos⟩, hB⟩

theorem run_fwE {K im iv m v fw : ℕ} (hfw : fw = fwN K m v) (B : Bd W m v fw K)
    (hm : env.getD im 0 = m) (hv : env.getD iv 0 = v) : Run W (fwE K im iv) env fw 5 := by
  have hlt : fw < 2 ^ W := B.fw_lt.trans Nat.lt_two_pow_self
  have e1 : fw = K + 3 + m + v := hfw
  have h1 : K + 3 < 2 ^ W := by omega
  have h2 : K + 3 + m < 2 ^ W := by omega
  have h3 : K + 3 + m + v < 2 ^ W := by omega
  have a : Run W (.add (.lit (K + 3)) (.var im)) env (K + 3 + m) 3 :=
    run_add (run_lit h1) (run_var hm) h2
  have b : Run W (fwE K im iv) env (K + 3 + m + v) 5 := run_add a (run_var hv) h3
  rw [e1]
  exact b

open Classical in
/-- **The network of a bitset formula.** Let `F` have clauses of at most three literals and at most `d`
occurrences of each variable, and let the word size be at least the polynomial below. The programs compute the
numbers of wires and of nodes, the field width and the tables, and the tables decode to the network `tailN`,
`headN`. Its network sum is the number of satisfying assignments of `F`, and `nodeE` computes its node
function. -/
theorem cnf_net_main (hF : Wide3 F) {d K : ℕ} (hd3 : 3 ≤ d) (hdeg : ∀ v, variableOccurrences F v ≤ d)
    (hK : 0 < K) (hW : (48 + (2 * d + K + 12) ^ 2) * (n + 1) ^ 3 ≤ W)
    (hn : env.getD nv 0 = n) (hf : env.getD fv 0 = encF n F) :
    let fw := fwN K (mN n F) (vN n F)
    Run W (mE nv fv) env (mN n F) (1080 * (n + 1) ^ 3) ∧
    Run W (vE nv fv) env (vN n F) (80 * (n + 1) ^ 3) ∧
    n ≤ mN n F ∧ mN n F ≤ (1 + d) * n ∧ vN n F ≤ mN n F + n + 1 ∧
    Fits W n F fw ∧ Bd W (mN n F) (vN n F) fw K ∧
    (∀ e, tailN hF e ≠ headN hF e) ∧
    (∀ α, Spread.arity (tailN hF) (headN hF) α ≤ 1 + d) ∧
    NetT fw (tailTN n F fw) (headTN n F fw) (tailN hF) (headN hF) ∧
    tailTN n F fw < 2 ^ (mN n F * fw) ∧ headTN n F fw < 2 ^ (mN n F * fw) ∧
    (∀ {ifw : ℕ}, env.getD ifw 0 = fw →
      Run W (tailTE nv fv ifw) env (tailTN n F fw) (30000 * (n + 1) ^ 6) ∧
      Run W (headTE nv fv ifw) env (headTN n F fw) (30000 * (n + 1) ^ 6)) ∧
    (∑ z : Fin (mN n F) → Bool, ∏ α, (phiN hF α (fun e => z e.1) : ℤ) =
      ((univ.filter fun x : Fin n → Bool => holdsFormula (literalHolds x) F).card : ℤ)) ∧
    (∀ (c tT hT : ℕ) (rest : List ℕ), NetT fw tT hT (tailN hF) (headN hF) →
      ∀ (α : Fin (vN n F)) (A : ℕ) (nv' fv' : ℕ),
        ((α : ℕ) :: A :: mN n F :: vN n F :: c :: fw :: tT :: hT :: rest).getD nv' 0 = n →
        ((α : ℕ) :: A :: mN n F :: vN n F :: c :: fw :: tT :: hT :: rest).getD fv' 0 = encF n F →
        ∃ b : ℕ, Run W (nodeE nv' fv') ((α : ℕ) :: A :: mN n F :: vN n F :: c :: fw :: tT :: hT :: rest) b
            (34000 * (n + 1) ^ 6) ∧ (b : ℤ) = phiN hF α (gOf hF α A)) := by
  intro fw
  obtain ⟨hFits, hB⟩ := fits_of_poly hF hdeg hK hW
  obtain ⟨hm1, hm2⟩ := mN_bounds hF hdeg
  obtain ⟨c1, c2⟩ := count_costs n
  obtain ⟨c3, c4⟩ := table_costs n
  refine ⟨(run_mE hFits.big hF hn hf).mono c1, (run_vE hFits.big hF hn hf).mono c2, hm1, hm2, vN_le hF,
    hFits, hB, tailN_ne_headN hF, arity_le hF hd3 hdeg, netT hFits hF, tailTN_lt hFits hF,
    headTN_lt hFits hF, fun hifw => ⟨(run_tailTE hFits hF hn hf hifw).mono c3,
      (run_headTE hFits hF hn hf hifw).mono c4⟩, net_count hF, ?_⟩
  intro c tT hT rest N α A nv' fv' h1 h2
  obtain ⟨b, hb, he⟩ := run_nodeE hFits hF N α A h1 h2
  exact ⟨b, hb.mono (node_cost_le n F), he⟩

end TransposeBase.Pseudo.CnfNet
