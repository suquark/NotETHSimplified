import OnePigeonhole.Pseudo.LeafWeight

/-!
# The loops

The nested loops over the digit `t`, the grid point `p` and the three masks `MT`, `MS`, `MU`, of equation (5) on the grid.
-/

set_option linter.unusedSectionVars false

namespace OnePigeonhole.Pseudo.Leaf

open Finset TransposeBase TransposeBase.General TransposeBase.Pseudo TransposeBase.Pseudo.Code TransposeBase.Pseudo.Leaf

namespace Cost

def hdr (T : ℕ) : ℕ := 2 + T * 2
/-- The cost of the weight and of the test of the masks. -/
def P1 (T : ℕ) : ℕ := wt T + cTestV T
/-- The body for the three masks. -/
def tBody (T Bx U v Y L : ℕ) : ℕ :=
  1 + (1 + wt T + cTestV T) + (1 + 1 + L * (groupSum T Bx U v Y + 1))
/-- The loop over one mask. -/
def iter (T nS B : ℕ) : ℕ :=
  1 + (1 + (1 + 1 + (1 + 1 + 1))) + 1 + nS * (((1 + (1 + 1) + 1) + (1 + B)) + next T + 1)
def pLoop (T Bx U v Y L YP nS : ℕ) : ℕ :=
  1 + hdr T + YP * (iter T nS (iter T nS (iter T nS (tBody T Bx U v Y L))) + 1)
def tLoop (T Bx U v Y L YP nS Q : ℕ) : ℕ := 1 + 1 + Q * (pLoop T Bx U v Y L YP nS + 1)
/-- The headers of the global values. -/
def lets (T : ℕ) : ℕ := 100 + hdr T + hdr T
def total (T Bx U v Y L YP nS Q : ℕ) : ℕ := lets T + tLoop T Bx U v Y L YP nS Q

end Cost

variable {S : Setup} {c : Ctx} {env : List ℕ}

/-- The term for three masks. -/
def termTopE (l : Loc) : Expr :=
  .mul (.mul (weightE l.c l.t l.p) (cTestE l)) (.prod (.var l.c.L) (groupSumE l.up 0))

/-- The summand for three sets of wires. -/
noncomputable def Setup.sTerm (S : Setup) (t : Fin S.Q) (p : Fin S.Q → Fin (S.M + 1))
    (ST SS SU : Finset (Fin S.M)) : ℤ :=
  S.wZ t p * cTest S.r ST SS SU * ∏ g, ∑ v : BlockBits S.wd S.tail S.head t g → Bool,
    letterZ S.lt.D S.R S.wi S.tail S.head S.wd S.φ t (fun i => (p i : ℕ)) ST SS SU g v

theorem runZ_termTopE {l : Loc} {V : LV S} (h : Frame S l V env) (hT : V.mT < 2 ^ S.M) :
    RunZ S.W (termTopE l) env
      (S.sTerm V.t (S.pOf V.p) (S.setS V.mT) (S.setS V.mS) (S.setS V.mU))
      (Cost.tBody S.T S.Bx S.Unode S.v (2 ^ (S.M / S.m)) S.L) := by
  refine RunZ.mul (RunZ.mul (runZ_weightE h.ag h.t h.p) (runZ_cTestE h hT)) ?_
  refine RunZ.prodFin (Run.var h.ag.L) le_rfl fun g => ?_
  exact runZ_groupSumE (h.up (g : ℕ)) (g := 0) (g' := g) rfl

/-- The loop bound of the masks. -/
abbrev Setup.nS (S : Setup) : ℕ := 2 ^ (clOf S.m * (S.r + 1))

/-- The masks are counted by the loop bound. -/
theorem card_masks_le (S : Setup) : (fewSets (Fin S.M) S.J).card ≤ S.nS := by
  have h := OnePigeonhole.card_few_le (α := Fin S.M) S.hm
  simp only [Fintype.card_fin] at h
  have hL0 : (0 : ℝ) < S.m := by exact_mod_cast S.m_pos
  have hlog : 0 ≤ Real.log S.m + 1 := by
    have := Real.log_natCast_nonneg S.m
    linarith
  have hNJ : (S.M : ℝ) / S.m ≤ ((S.r + 1 : ℕ) : ℝ) := by
    rw [div_le_iff₀ hL0]
    have : S.M < (S.M / S.m + 1) * S.m := (Nat.div_lt_iff_lt_mul S.m_pos).mp (Nat.lt_succ_self _)
    have h2 : ((S.M : ℕ) : ℝ) ≤ (((S.M / S.m + 1) * S.m : ℕ) : ℝ) := by exact_mod_cast this.le
    simpa [Setup.r] using h2
  have h1 : Real.exp (3 * (Real.log S.m + 1) * S.M / S.m) ≤
      Real.exp ((Real.log S.m + 1) * ((3 * (S.r + 1) : ℕ) : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have e : 3 * (Real.log S.m + 1) * (S.M : ℝ) / S.m = (Real.log S.m + 1) * (3 * ((S.M : ℝ) / S.m)) := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ hlog
    push_cast at hNJ ⊢
    linarith
  have h2 : Real.exp ((Real.log S.m + 1) * ((3 * (S.r + 1) : ℕ) : ℝ)) = (S.m * Real.exp 1) ^ (3 * (S.r + 1)) := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_add, Real.exp_log hL0]
  have h3 : (S.m : ℝ) * Real.exp 1 ≤ 2 ^ Nat.clog 2 (3 * S.m) := by
    have h4 : (3 * S.m : ℕ) ≤ 2 ^ Nat.clog 2 (3 * S.m) := Nat.le_pow_clog (by norm_num) _
    have h5 : (((3 * S.m : ℕ)) : ℝ) ≤ ((2 ^ Nat.clog 2 (3 * S.m) : ℕ) : ℝ) := by exact_mod_cast h4
    have h6 : Real.exp 1 ≤ 3 := by
      have := Real.exp_one_lt_d9
      linarith
    push_cast at h5
    nlinarith [Real.exp_pos 1]
  have h7 : (S.m * Real.exp 1) ^ (3 * (S.r + 1)) ≤ ((2 : ℝ) ^ Nat.clog 2 (3 * S.m)) ^ (3 * (S.r + 1)) :=
    pow_le_pow_left₀ (by positivity) h3 _
  have h8 : ((fewSets (Fin S.M) S.J).card : ℝ) ≤ ((S.nS : ℕ) : ℝ) := by
    have e : ((S.nS : ℕ) : ℝ) = ((2 : ℝ) ^ Nat.clog 2 (3 * S.m)) ^ (3 * (S.r + 1)) := by
      simp only [Setup.nS, clOf]
      push_cast
      rw [← pow_mul]
      congr 1
      ring
    rw [e]
    refine le_trans ?_ h7
    rw [← h2]
    exact le_trans h h1
  exact_mod_cast h8

theorem nS_exp_lt (S : Setup) : clOf S.m * (S.r + 1) < S.W := by
  have h5 : clOf S.m * (S.T + 2) < S.W := S.big.hcl
  have h6 : S.r ≤ S.M := Nat.div_le_self _ _
  have h7 : clOf S.m * (S.r + 1) ≤ clOf S.m * (S.T + 2) := Nat.mul_le_mul_left _ (by have := S.M_le_T; omega)
  exact lt_of_le_of_lt h7 h5

/-- The loop over one mask, with the mask as variable `0` of the body. Numbers from `2 ^ M` on give `0`. -/
def maskLoopE (cl : ℕ) (c : Ctx) (b : Expr) : Expr :=
  .sumIter (.pow2 (.mul (.lit cl) (.add (.var c.r) (.lit 1)))) (.lit 0) (nextE c.up 0)
    (.ite (.pow2 (.var c.up.M)) (.var 0) (.lit 0) b)

theorem runZ_maskLoopE (h : Agree S c env) {b : Expr} {B : ℕ} {F : Finset (Fin S.M) → ℤ}
    (hb : ∀ x, x < 2 ^ S.M → RunZ S.W b (x :: env) (F (S.setS x)) B) :
    RunZ S.W (maskLoopE (clOf S.m) c b) env (∑ SS ∈ fewW S.M S.J, F SS) (Cost.iter S.T S.nS B) := by
  have hNW : S.M < S.W := by have := S.M_le_T; have := S.T_lt_W; omega
  have hJ : 1 ≤ S.J := Nat.le_add_left 1 _
  have hsum := sum_it_setOfMask (Equiv.refl (Fin S.M)) hJ (card_masks_le S) F
  have hrw : fewW S.M S.J = fewSets (Fin S.M) S.J := rfl
  rw [hrw, ← hsum]
  have hclW := nS_exp_lt S
  have hrW : S.r + 1 < S.W := by
    have h6 : S.r ≤ S.M := Nat.div_le_self _ _
    have := S.M_le_T
    have := S.T_lt_W
    omega
  have hr1 : Run S.W (.add (.var c.r) (.lit 1)) env (S.r + 1) (1 + 1 + 1) :=
    Run.add (Run.var h.r) (Run.lit (one_lt_W S)) (S.lt_pow_W hrW)
  have hcl1 : clOf S.m < S.W := by
    have : clOf S.m * 1 ≤ clOf S.m * (S.r + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hnS : Run S.W (.pow2 (.mul (.lit (clOf S.m)) (.add (.var c.r) (.lit 1)))) env
      (2 ^ (clOf S.m * (S.r + 1))) (1 + (1 + 1 + (1 + 1 + 1))) :=
    Run.pow2 (Run.mul (Run.lit (S.lt_pow_W hcl1)) hr1 (S.lt_pow_W hclW)) hclW
  have hs0 : Run S.W (.lit 0) env 0 1 := Run.lit (by positivity)
  refine RunZ.sumIter hnS hs0 le_rfl fun k _ => ?_
  set x := iterate S.W (nextE c.up 0) 0 env k with hx
  have hit := iterate_next h k
  have hp : Run S.W (.pow2 (.var c.up.M)) (x :: env) (2 ^ S.M) (1 + 1) :=
    Run.pow2 (Run.var (h.up x).M) hNW
  have hv : Run S.W (.var 0) (x :: env) x 1 := Run.var rfl
  refine ⟨?_, (run_nextE (h.up x) rfl).2⟩
  by_cases hk : Enum.it S.M S.J k < 2 ^ S.M
  · have hxe : x = Enum.it S.M S.J k := hit.1 hk
    rw [if_pos hk]
    refine RunZ.ite (cc := 1) (cd := B) hp hv (fun hle => absurd hle (not_le.mpr (hxe ▸ hk))) (fun _ => ?_)
    rw [hxe]
    exact hb _ hk
  · have hle := hit.2 (not_lt.mp hk)
    rw [if_neg hk]
    exact RunZ.ite (cc := 1) (cd := B) hp hv (fun _ => RunZ.lit0) (fun h3 => absurd hle h3)

/-- The loops: the digit, the grid point and the three masks. -/
def loopsE (cl : ℕ) (c : Ctx) (node : Expr) : Expr :=
  .sum (.var c.Q) (.sum (powE c.up.Nq c.up.Q)
    (maskLoopE cl c.up.up (maskLoopE cl c.up.up.up (maskLoopE cl c.up.up.up.up
      (termTopE ⟨c.up.up.up.up.up, 4, 2, 1, 0, 3, 0, node⟩)))))

/-- The sum of all the loops. -/
noncomputable def Setup.total (S : Setup) : ℤ :=
  ∑ t : Fin S.Q, ∑ p : Fin S.Q → Fin (S.M + 1),
    ∑ ST ∈ fewW S.M S.J, ∑ SS ∈ fewW S.M S.J, ∑ SU ∈ fewW S.M S.J, S.sTerm t p ST SS SU

theorem runZ_loopsE (h : Agree S c env) :
    RunZ S.W (loopsE (clOf S.m) c S.nodeE) env S.total
      (Cost.tLoop S.T S.Bx S.Unode S.v (2 ^ (S.M / S.m)) S.L (S.Nq ^ S.Q) S.nS S.Q) := by
  unfold Setup.total Cost.tLoop
  refine RunZ.sumFin (B := Cost.pLoop S.T S.Bx S.Unode S.v (2 ^ (S.M / S.m)) S.L (S.Nq ^ S.Q) S.nS)
    (Run.var h.Q) le_rfl fun t => ?_
  have h1 := h.up (t : ℕ)
  rw [Code.sum_word_succ]
  unfold Cost.pLoop
  refine RunZ.sum (run_powNq h1) le_rfl fun p _ => ?_
  have h2 := h1.up p
  have hbody : ∀ mT mS mU, mT < 2 ^ S.M →
      RunZ S.W (termTopE ⟨c.up.up.up.up.up, 4, 2, 1, 0, 3, 0, S.nodeE⟩) (mU :: mS :: mT :: p :: (t : ℕ) :: env)
        (S.sTerm t (wordOf (Nat.succ_pos S.M) S.Q p) (S.setS mT) (S.setS mS) (S.setS mU))
        (Cost.tBody S.T S.Bx S.Unode S.v (2 ^ (S.M / S.m)) S.L) := by
    intro mT mS mU hmT
    have hF : Frame S ⟨c.up.up.up.up.up, 4, 2, 1, 0, 3, 0, S.nodeE⟩ ⟨t, mT, mS, mU, p, mU⟩
        (mU :: mS :: mT :: p :: (t : ℕ) :: env) :=
      ⟨(((h2.up mT).up mS).up mU), rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hb := runZ_termTopE hF hmT
    exact hb
  have hU : ∀ mT mS, mT < 2 ^ S.M → RunZ S.W (maskLoopE (clOf S.m) c.up.up.up.up
      (termTopE ⟨c.up.up.up.up.up, 4, 2, 1, 0, 3, 0, S.nodeE⟩)) (mS :: mT :: p :: (t : ℕ) :: env)
      (∑ SU ∈ fewW S.M S.J, S.sTerm t (wordOf (Nat.succ_pos S.M) S.Q p) (S.setS mT) (S.setS mS) SU)
      (Cost.iter S.T S.nS (Cost.tBody S.T S.Bx S.Unode S.v (2 ^ (S.M / S.m)) S.L)) := by
    intro mT mS hmT
    exact runZ_maskLoopE ((h2.up mT).up mS)
      (F := fun SU => S.sTerm t (wordOf (Nat.succ_pos S.M) S.Q p) (S.setS mT) (S.setS mS) SU)
      (fun mU _ => hbody mT mS mU hmT)
  have hS : ∀ mT, mT < 2 ^ S.M → RunZ S.W (maskLoopE (clOf S.m) c.up.up.up (maskLoopE (clOf S.m) c.up.up.up.up
      (termTopE ⟨c.up.up.up.up.up, 4, 2, 1, 0, 3, 0, S.nodeE⟩))) (mT :: p :: (t : ℕ) :: env)
      (∑ SS ∈ fewW S.M S.J, ∑ SU ∈ fewW S.M S.J,
        S.sTerm t (wordOf (Nat.succ_pos S.M) S.Q p) (S.setS mT) SS SU)
      (Cost.iter S.T S.nS (Cost.iter S.T S.nS (Cost.tBody S.T S.Bx S.Unode S.v (2 ^ (S.M / S.m)) S.L))) := by
    intro mT hmT
    exact runZ_maskLoopE (h2.up mT)
      (F := fun SS => ∑ SU ∈ fewW S.M S.J, S.sTerm t (wordOf (Nat.succ_pos S.M) S.Q p) (S.setS mT) SS SU)
      (fun mS _ => hU mT mS hmT)
  exact runZ_maskLoopE h2
    (F := fun ST => ∑ SS ∈ fewW S.M S.J, ∑ SU ∈ fewW S.M S.J,
      S.sTerm t (wordOf (Nat.succ_pos S.M) S.Q p) ST SS SU)
    (fun mT hmT => hS mT hmT)

end OnePigeonhole.Pseudo.Leaf
