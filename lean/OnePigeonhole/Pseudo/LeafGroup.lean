import OnePigeonhole.Pseudo.LeafBlock

/-!
# The bits of a letter

The letter of a bit, the assignment word of a summand, the summand of a letter, and the sum over the assignments of the bits of one
letter. A letter has at most `M / m` bits (`count_card`), by `card_blockBits_mul_le`. These are the sums over the bits of equation (5).
-/

set_option linter.unusedSectionVars false

namespace OnePigeonhole.Pseudo.Leaf

open Finset TransposeBase TransposeBase.General TransposeBase.Pseudo TransposeBase.Pseudo.Code TransposeBase.Pseudo.Leaf

namespace Cost

def group (T : ℕ) : ℕ :=
  1 + (1 + 1 + 1) + 1 + ((1 + field + partDig T) + (1 + (1 + (1 + 1 + 1) + field) + partDig T))
def countBody (T : ℕ) : ℕ := 2 + 2 * (group T + 1) + 2 * (1 + 1)
def count (T : ℕ) : ℕ := 1 + 1 + T * (countBody T + 1)
def assignBody (T : ℕ) : ℕ :=
  2 + 2 * (group T + 1) + 2 * ((1 + (1 + count T + bit) + (1 + 1)) + 1)
def assign (T : ℕ) : ℕ := 1 + 1 + T * (assignBody T + 1)
def term (T Bx U v : ℕ) : ℕ :=
  1 + block T Bx + (1 + 1 + v * ((2 + 2 * (partDig T + 1) + 2 * (U + 1)) + 1))
/-- The body of the sum over the assignments of the bits of one letter. -/
def groupBody (T Bx U v : ℕ) : ℕ := 1 + assign T + term T Bx U v
def groupSum (T Bx U v Y : ℕ) : ℕ := 1 + (1 + count T) + Y * (groupBody T Bx U v + 1)

end Cost

variable {S : Setup} {c : Ctx} {env : List ℕ} {l : Loc} {V : LV S}

namespace Setup

variable (S : Setup)

/-- The letter at the digit `t` of the bit with number `i`. -/
def grpI (t : Fin S.Q) (i : ℕ) : ℕ :=
  if h : i < S.M then (S.wd (S.tail ⟨i, h⟩) t : ℕ)
  else if h2 : i - S.M < S.M then (S.wd (S.head ⟨i - S.M, h2⟩) t : ℕ) else 0

/-- The numbers of the bits: the `x` copies, and then the `y` copies. -/
abbrev code : Fin S.M ⊕ Fin S.M ≃ Fin (2 * S.M) := sumCodeOf (Equiv.refl (Fin S.M))

theorem grpI_code (t : Fin S.Q) (b : Fin S.M ⊕ Fin S.M) :
    S.grpI t (S.code b) = ((bitBlock S.wd S.tail S.head t b : Fin S.L) : ℕ) := by
  rcases b with e | e
  · have h : ((S.code (Sum.inl e) : Fin (2 * S.M)) : ℕ) = e := rfl
    unfold grpI
    rw [h, dif_pos e.2]
    rfl
  · have h : ((S.code (Sum.inr e) : Fin (2 * S.M)) : ℕ) = S.M + e := rfl
    unfold grpI
    rw [h, dif_neg (by omega), dif_pos (by have := e.2; omega)]
    have : (⟨S.M + (e : ℕ) - S.M, by have := e.2; omega⟩ : Fin S.M) = e := Fin.ext (by simp)
    rw [this]
    rfl

/-- The bit with number `k` is a bit of the letter `g` at the digit `t`. -/
def pG (t : Fin S.Q) (g : Fin S.L) (k : ℕ) : Prop := S.grpI t k = g

instance (t : Fin S.Q) (g : Fin S.L) : DecidablePred (S.pG t g) := fun k => by unfold pG; infer_instance

theorem pG_code (t : Fin S.Q) (g : Fin S.L) (b : Fin S.M ⊕ Fin S.M) :
    S.pG t g (S.code b) ↔ bitBlock S.wd S.tail S.head t b = g := by
  rw [pG, grpI_code, Fin.ext_iff]

/-- The assignment word of the number `k`. -/
def asgW (t : Fin S.Q) (g : Fin S.L) (k : ℕ) : ℕ :=
  Enum.mask (univ.filter fun i : Fin (2 * S.M) =>
    S.pG t g i ∧ k.testBit (Nat.count (S.pG t g) i) = true)

theorem asgW_lt (t : Fin S.Q) (g : Fin S.L) (k : ℕ) : S.asgW t g k < 2 ^ (2 * S.M) := Enum.mask_lt _

theorem asgW_eq_sum (t : Fin S.Q) (g : Fin S.L) (k : ℕ) :
    S.asgW t g k = ∑ i ∈ range (2 * S.M),
      if S.pG t g i then (k.testBit (Nat.count (S.pG t g) i)).toNat * 2 ^ i else 0 := by
  rw [asgW, Enum.mask, Finset.sum_filter, Finset.sum_range
    (fun i => if S.pG t g i then (k.testBit (Nat.count (S.pG t g) i)).toNat * 2 ^ i else 0)]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hp : S.pG t g i
  · by_cases hb : k.testBit (Nat.count (S.pG t g) i) = true
    · simp [hp, hb]
    · simp [hp, hb]
  · simp [hp]

theorem testBit_asgW (t : Fin S.Q) (g : Fin S.L) (k : ℕ) (b : Fin S.M ⊕ Fin S.M) :
    (S.asgW t g k).testBit (S.code b) =
      blockExt S.wd S.tail S.head t g
        (fun i => k.testBit (Nat.count (S.pG t g) (S.code i.1))) b := by
  have h1 := (S.code b).2
  rw [Bool.eq_iff_iff, asgW, Enum.testBit_mask]
  unfold blockExt
  by_cases hq : bitBlock S.wd S.tail S.head t b = g
  · rw [dif_pos hq]
    have hp := (S.pG_code t g b).mpr hq
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun ⟨_, h⟩ => h.2, fun h => ⟨h1, hp, h⟩⟩
  · rw [dif_neg hq]
    have hp : ¬ S.pG t g (S.code b) := fun h => hq ((S.pG_code t g b).mp h)
    simp only [mem_filter, mem_univ, true_and, Bool.false_eq_true, iff_false, not_exists, not_and]
    exact fun _ h _ => hp h

theorem ext_inl (t : Fin S.Q) (g : Fin S.L) (k : ℕ) :
    blockExt S.wd S.tail S.head t g (fun i => k.testBit (Nat.count (S.pG t g) (S.code i.1))) ∘ Sum.inl =
      asgX S.M (S.asgW t g k) := by
  funext e
  exact (S.testBit_asgW t g k (Sum.inl e)).symm

theorem ext_inr (t : Fin S.Q) (g : Fin S.L) (k : ℕ) :
    blockExt S.wd S.tail S.head t g (fun i => k.testBit (Nat.count (S.pG t g) (S.code i.1))) ∘ Sum.inr =
      asgY S.M (S.asgW t g k) := by
  funext e
  exact (S.testBit_asgW t g k (Sum.inr e)).symm

/-- A sum over the assignments of the bits of one letter is a sum over numbers. -/
theorem sum_blockBits (t : Fin S.Q) (g : Fin S.L) (F : (BlockBits S.wd S.tail S.head t g → Bool) → ℤ) :
    ∑ v, F v = ∑ k ∈ range (2 ^ Nat.count (S.pG t g) (2 * S.M)),
      F (fun b => k.testBit (Nat.count (S.pG t g) (S.code b.1))) :=
  sum_exc_bool_count S.code (fun i => bitBlock S.wd S.tail S.head t i = g) (S.pG_code t g) F

/-- **A letter has at most `M / m` bits**, since `L = 6 * m ^ 4` and `2 * K ^ 2 * h ≤ m * M`. -/
theorem count_le (t : Fin S.Q) (g : Fin S.L) : Nat.count (S.pG t g) (2 * S.M) ≤ S.M / S.m := by
  have h1 := excCard_eq_count S.code (fun i => bitBlock S.wd S.tail S.head t i = g) (S.pG_code t g)
  have h2 := excCard_eq_fintype_card S.code (fun i => bitBlock S.wd S.tail S.head t i = g)
  have h3 := card_blockBits_mul_le S.hOn t g
  have h4 := h3.trans S.hnum
  rw [← h1, h2, Nat.le_div_iff_mul_le S.m_pos]
  generalize Fintype.card (BlockBits S.wd S.tail S.head t g) = B at h4 ⊢
  have e : B * (6 * S.m ^ 4) = S.m * (B * (6 * S.m ^ 3)) := by ring
  rw [e] at h4
  have h5 := Nat.le_of_mul_le_mul_left h4 S.m_pos
  have h6 : S.m ≤ 6 * S.m ^ 3 := by
    calc S.m = 1 * S.m ^ 1 := by simp
      _ ≤ 6 * S.m ^ 3 := Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_right S.m_pos (by norm_num))
  exact (Nat.mul_le_mul_left _ h6).trans h5

theorem count_card (t : Fin S.Q) (g : Fin S.L) :
    2 ^ Nat.count (S.pG t g) (2 * S.M) ≤ 2 ^ (S.M / S.m) :=
  Nat.pow_le_pow_right (by norm_num) (S.count_le t g)

end Setup

/-! ### Programs -/

/-- The letter of the bit in variable `i`. -/
def groupE (c : Ctx) (t i : ℕ) : Expr :=
  .ite (.add (.var i) (.lit 1)) (.var c.M)
    (.letE (fieldE c c.tailT i) (partDigE c.up (t + 1) 0))
    (.letE (.letE (.sub (.var i) (.var c.M)) (fieldE c.up c.up.headT 0)) (partDigE c.up (t + 1) 0))

theorem run_groupE (h : Agree S c env) {t i I : ℕ} {t' : Fin S.Q} (ht : env.getD t 0 = t')
    (hi : env.getD i 0 = I) (hI : I < 2 * S.M) :
    Run S.W (groupE c t i) env (S.grpI t' I) (Cost.group S.T) := by
  have hTw := S.T_lt_W
  have hm2 : 2 * S.M ≤ S.T := S.two_le_T
  have hIT : I ≤ S.T := by omega
  have hadd : Run S.W (.add (.var i) (.lit 1)) env (I + 1) (1 + 1 + 1) :=
    Run.add (Run.var hi) (Run.lit (one_lt_W S)) (S.lt_pow_W (by omega))
  refine Run.ite hadd (Run.var h.M) (fun hle => ?_) (fun hle => ?_)
  · have hlt : I < S.M := by omega
    have h1 := run_fieldE h h.tailT hi hIT
    rw [show I = ((⟨I, hlt⟩ : Fin S.M) : ℕ) from rfl, S.htail ⟨I, hlt⟩] at h1
    have hup := h.up (S.tail ⟨I, hlt⟩ : ℕ)
    have h2 := run_partDigE hup (t := t + 1) (α := 0) (t' := t') (a := S.tail ⟨I, hlt⟩) ht rfl
    refine (Run.letE h1 h2).eq ?_
    rw [Setup.grpI, dif_pos hlt]
  · have hge : S.M ≤ I := by omega
    have hlt : I - S.M < S.M := by omega
    have hsub : Run S.W (.sub (.var i) (.var c.M)) env (I - S.M) (1 + 1 + 1) :=
      Run.sub (Run.var hi) (Run.var h.M) (S.lt_pow_W (by omega)) hge
    have hup0 := h.up (I - S.M)
    have h1 := run_fieldE hup0 (x := c.up.headT) (i := 0) (I := I - S.M) hup0.headT rfl (by omega)
    rw [show I - S.M = ((⟨I - S.M, hlt⟩ : Fin S.M) : ℕ) from rfl, S.hhead ⟨I - S.M, hlt⟩] at h1
    have hup := h.up (S.head ⟨I - S.M, hlt⟩ : ℕ)
    have h2 := run_partDigE hup (t := t + 1) (α := 0) (t' := t') (a := S.head ⟨I - S.M, hlt⟩) ht rfl
    refine (Run.letE (Run.letE hsub h1) h2).eq ?_
    rw [Setup.grpI, dif_neg (by omega), dif_pos hlt]

/-- The number of the bits of the letter in variable `g` below the number in variable `n`. -/
def countE (c : Ctx) (t g n : ℕ) : Expr :=
  .sum (.var n) (eqX (groupE c.up (t + 1) 0) (.var (g + 1)) (.lit 1) (.lit 0))

theorem run_countE (h : Agree S c env) {t g n N' : ℕ} {t' : Fin S.Q} {g' : Fin S.L}
    (ht : env.getD t 0 = t') (hg : env.getD g 0 = g') (hn : env.getD n 0 = N') (hN : N' ≤ 2 * S.M) :
    Run S.W (countE c t g n) env (Nat.count (S.pG t' g') N') (Cost.count S.T) := by
  have hle := hN.trans S.two_le_T
  rw [Nat.count_eq_card_filter_range, Finset.card_filter]
  refine Run.sum (Run.var hn) hle (fun i hi => ?_) ?_
  · have hup := h.up i
    have h1 : Run S.W (groupE c.up (t + 1) 0) (i :: env) (S.grpI t' i) (Cost.group S.T) :=
      run_groupE hup ht rfl (by omega)
    have h2 : Run S.W (.var (g + 1)) (i :: env) g' 1 := Run.var hg
    exact Run.eqX h1 h2 (fun e1 => (Run.lit (one_lt_W S)).eq (by rw [if_pos (show S.pG t' g' i from e1)]))
      (fun e1 => (Run.lit (by positivity)).eq (by rw [if_neg (show ¬ S.pG t' g' i from e1)]))
  · exact S.small ((sum_ite_le _ _).trans (hle.trans (by omega)))

/-- The assignment word of the number in variable `k`, for the letter in variable `g`. -/
def assignE (c : Ctx) (t g k : ℕ) : Expr :=
  .sum (.var c.two) (eqX (groupE c.up (t + 1) 0) (.var (g + 1))
    (.mul (.letE (countE c.up (t + 1) (g + 1) 0) (bitX (k + 2) (.var 0))) (.pow2 (.var 0))) (.lit 0))

theorem run_assignE (h : Agree S c env) {t g k K' : ℕ} {t' : Fin S.Q} {g' : Fin S.L}
    (ht : env.getD t 0 = t') (hg : env.getD g 0 = g') (hk : env.getD k 0 = K') :
    Run S.W (assignE c t g k) env (S.asgW t' g' K') (Cost.assign S.T) := by
  have hlt : S.asgW t' g' K' < 2 ^ S.W :=
    (S.asgW_lt t' g' K').trans (S.pow_lt_W (by have := S.two_le_T; have := S.T_lt_W; simp only [Setup.two] at *; omega))
  rw [S.asgW_eq_sum] at hlt ⊢
  refine Run.sum (Run.var h.two) S.two_le_T (fun i hi => ?_) hlt
  have hup := h.up i
  have hTw := S.T_lt_W
  have hm2 := S.two_le_T
  have hiW : i < S.W := by simp only [Setup.two] at hm2; omega
  have h1 : Run S.W (groupE c.up (t + 1) 0) (i :: env) (S.grpI t' i) (Cost.group S.T) :=
    run_groupE hup ht rfl hi
  have h2 : Run S.W (.var (g + 1)) (i :: env) g' 1 := Run.var hg
  have hc : Run S.W (countE c.up (t + 1) (g + 1) 0) (i :: env) (Nat.count (S.pG t' g') i) (Cost.count S.T) :=
    run_countE hup ht hg rfl hi.le
  have hcW : Nat.count (S.pG t' g') i < S.W := (Nat.count_le _).trans_lt hiW
  have hb : Run S.W (bitX (k + 2) (.var 0)) (Nat.count (S.pG t' g') i :: i :: env)
      (K'.testBit (Nat.count (S.pG t' g') i)).toNat Cost.bit := run_bitV hk rfl hcW
  have hp : Run S.W (.pow2 (.var 0)) (i :: env) (2 ^ i) (1 + 1) := Run.pow2 (Run.var rfl) hiW
  refine Run.eqX h1 h2 (fun e1 => ?_) (fun e1 => (Run.lit (by positivity)).eq ?_)
  · rw [if_pos (show S.pG t' g' i from e1)]
    refine Run.mul (Run.letE hc hb) hp ?_
    have h3 : (K'.testBit (Nat.count (S.pG t' g') i)).toNat ≤ 1 := by
      cases (K'.testBit (Nat.count (S.pG t' g') i)) <;> simp
    calc _ ≤ 1 * 2 ^ i := Nat.mul_le_mul_right _ h3
      _ = 2 ^ i := one_mul _
      _ < 2 ^ S.W := S.pow_lt_W hiW
  · rw [if_neg (show ¬ S.pG t' g' i from e1)]

/-- The summand of a letter at the assignment word in variable `as` of `l`. -/
def termE (l : Loc) (g mid : ℕ) : Expr :=
  .mul (blockE l g) (.prod (.var l.c.v)
    (eqX (partDigE l.c.up (l.t + 1) 0) (.var (g + 1)) (liftE 2 mid l.node) (.lit 1)))

theorem runZ_node (h : Frame S l V env) {A : ℕ} (a : Fin S.v) (hA : A < 2 ^ (2 * S.M)) {pre : List ℕ}
    (henv : env = A :: pre ++ S.core) :
    RunZ S.W (liftE 2 pre.length l.node) ((a : ℕ) :: env)
      (S.φ a (read S.tail S.head a (asgX S.M A) (asgY S.M A))) S.Unode := by
  rw [h.node, henv]
  exact RunZ.lift (pre := [(a : ℕ), A]) (mid := pre) (post := S.core) (S.hnode a A hA)

theorem runZ_termE (h : Frame S l V env) {g : ℕ} {g' : Fin S.L} (hg : env.getD g 0 = g')
    (hA : V.A < 2 ^ (2 * S.M)) {pre : List ℕ} (henv : env = V.A :: pre ++ S.core) :
    RunZ S.W (termE l g pre.length) env
      (blockZ S.lt.D S.R S.wi V.t (S.pN V.p) (S.setS V.mT) (S.setS V.mS) (S.setS V.mU) g' (asgX S.M V.A) (asgY S.M V.A) *
        ∏ α ∈ univ.filter (fun α => S.wd α V.t = g'),
          S.φ α (read S.tail S.head α (asgX S.M V.A) (asgY S.M V.A)))
      (Cost.term S.T S.Bx S.Unode S.v) := by
  refine RunZ.mul (runZ_blockE h hg) ?_
  rw [Finset.prod_filter]
  refine RunZ.prodFin (B := 2 + 2 * (Cost.partDig S.T + 1) + 2 * (S.Unode + 1)) (Run.var h.ag.v) le_rfl fun a => ?_
  have hup := h.up (a : ℕ)
  have h1 : Run S.W (partDigE l.c.up (l.t + 1) 0) ((a : ℕ) :: env) (S.wd a V.t : ℕ) (Cost.partDig S.T) :=
    run_partDigE hup.ag h.t rfl
  have h2 : Run S.W (.var (g + 1)) ((a : ℕ) :: env) g' 1 := Run.var hg
  refine RunZ.eqX h1 h2 (fun e1 => (runZ_node h a hA henv).eq ?_) (fun e1 => RunZ.lit1.eq ?_)
  · rw [if_pos (Fin.ext e1)]
  · rw [if_neg (fun e2 => e1 (congrArg Fin.val e2))]

/-- The context of the summand, with the assignment word as variable `0`. -/
def Loc.bindAs (l : Loc) : Loc := ⟨l.c.up, l.t + 1, l.mT + 1, l.mS + 1, l.mU + 1, l.p + 1, 0, l.node⟩

/-- The sum over the assignments of the bits of the letter in variable `g`. -/
def groupSumE (l : Loc) (g : ℕ) : Expr :=
  .sum (.pow2 (countE l.c l.t g l.c.two))
    (.letE (assignE l.c.up (l.t + 1) (g + 1) 0) (termE l.up.bindAs (g + 2) (l.c.depth + 1)))

theorem runZ_groupSumE (h : Frame S l V env) {g : ℕ} {g' : Fin S.L} (hg : env.getD g 0 = g') :
    RunZ S.W (groupSumE l g) env
      (∑ v : BlockBits S.wd S.tail S.head V.t g' → Bool,
        letterZ S.lt.D S.R S.wi S.tail S.head S.wd S.φ V.t (S.pN V.p) (S.setS V.mT) (S.setS V.mS) (S.setS V.mU) g' v)
      (Cost.groupSum S.T S.Bx S.Unode S.v (2 ^ (S.M / S.m))) := by
  rw [S.sum_blockBits V.t g']
  have hcnt : Run S.W (countE l.c l.t g l.c.two) env (Nat.count (S.pG V.t g') (2 * S.M)) (Cost.count S.T) :=
    run_countE h.ag h.t hg h.ag.two le_rfl
  have hcW : Nat.count (S.pG V.t g') (2 * S.M) < S.W :=
    (Nat.count_le _).trans_lt (by have := S.two_le_T; have := S.T_lt_W; simp only [Setup.two] at *; omega)
  refine RunZ.sum (B := Cost.groupBody S.T S.Bx S.Unode S.v) (Run.pow2 hcnt hcW) (S.count_card V.t g') fun k hk => ?_
  have hup := h.ag.up k
  have hA : Run S.W (assignE l.c.up (l.t + 1) (g + 1) 0) (k :: env) (S.asgW V.t g' k) (Cost.assign S.T) :=
    run_assignE hup h.t hg rfl
  obtain ⟨pre0, hp1, hp2⟩ := h.ag.core
  have hF : Frame S l.up.bindAs ⟨V.t, V.mT, V.mS, V.mU, V.p, S.asgW V.t g' k⟩ (S.asgW V.t g' k :: k :: env) :=
    ⟨hup.up _, h.t, h.mT, h.mS, h.mU, h.p, rfl, h.node⟩
  have hT := runZ_termE hF (g := g + 2) (g' := g') hg (S.asgW_lt V.t g' k) (pre := k :: pre0) (by rw [hp2]; rfl)
  have hlen : (k :: pre0).length = l.c.depth + 1 := by simp [hp1]
  rw [hlen] at hT
  refine RunZ.letE hA (hT.eq ?_)
  unfold letterZ
  rw [S.ext_inl, S.ext_inr]

end OnePigeonhole.Pseudo.Leaf
