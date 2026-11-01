import TransposeBase.General
import SatBase.SparsificationTree

/-!
# 3-SAT: the network of a formula and the branching tree

The branching tree of `SatBase.SparsificationTree`, and the network of a formula at each leaf.

A leaf formula on `n` variables is a network with one free wire for each variable and one wire for each
occurrence of a literal. So it has at least `n` wires and small arities, with no further conditions on
the formula.

* `net_count`: the network sum of a formula is its number of satisfying assignments.
* `arity_le`: the arities are at most `D₁ = 1 + 4 ℓ ^ 2` at a leaf.
* `sat_iff_leaf`: a formula is satisfiable exactly when some leaf is.
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace TransposeBase
namespace Sat

open scoped BigOperators
open Finset SatBase General

variable {n : ℕ} {k : Type*} [CommRing k]

/-- The clauses of a formula. -/
abbrev LCl (F : ClauseSet (SignedLiteral n)) := {C // C ∈ F}
/-- The literal occurrences of a clause. -/
abbrev LI (F : ClauseSet (SignedLiteral n)) (e : LCl F) := {l // l ∈ e.1}
/-- The occurrences of literals. -/
abbrev OccW (F : ClauseSet (SignedLiteral n)) := Σ e : LCl F, LI F e
/-- The wires: a free wire at each variable, and a wire for each occurrence. -/
abbrev Wire (F : ClauseSet (SignedLiteral n)) := Fin n ⊕ OccW F
/-- The nodes: the variables, the clauses, and an end node for each free wire. -/
abbrev Node (F : ClauseSet (SignedLiteral n)) := Fin n ⊕ LCl F ⊕ Fin n

/-- A fixed decidable equality on wires. -/
noncomputable instance wireDec (F : ClauseSet (SignedLiteral n)) : DecidableEq (Wire F) :=
  Classical.decEq _

/-- A fixed decidable equality on nodes. -/
noncomputable instance nodeDec (F : ClauseSet (SignedLiteral n)) : DecidableEq (Node F) :=
  Classical.decEq _

/-- The variable end of a wire. -/
def tl (F : ClauseSet (SignedLiteral n)) : Wire F → Node F
  | .inl v => .inl v
  | .inr j => .inl j.2.1.1

/-- The other end of a wire. -/
def hd (F : ClauseSet (SignedLiteral n)) : Wire F → Node F
  | .inl v => .inr (.inr v)
  | .inr j => .inr (.inl j.1)

theorem tl_ne_hd (F : ClauseSet (SignedLiteral n)) (e : Wire F) : tl F e ≠ hd F e := by
  cases e <;> simp [tl, hd]

open Classical in
/-- The node functions. A variable requires its bits to be equal, a clause evaluates itself, and an
end node is constant. -/
noncomputable def phi (F : ClauseSet (SignedLiteral n)) :
    (α : Node F) → (Inc (tl F) (hd F) α → Bool) → k
  | .inl _, g => if ∀ a b, g a = g b then 1 else 0
  | .inr (.inl e), g =>
      if ∃ l : LI F e, g ⟨.inr ⟨e, l⟩, Or.inr rfl⟩ = l.1.2 then 1 else 0
  | .inr (.inr _), _ => 1

/-- The assignment of the free wires. -/
def valOf (F : ClauseSet (SignedLiteral n)) (z : Wire F → Bool) : Fin n → Bool := fun v => z (.inl v)

/-- The bits of an assignment. -/
def bitsOf (F : ClauseSet (SignedLiteral n)) (x : Fin n → Bool) : Wire F → Bool
  | .inl v => x v
  | .inr j => x j.2.1.1

open Classical in
/-- The product of the node functions is the indicator of a consistent satisfying choice. -/
theorem prod_phi (F : ClauseSet (SignedLiteral n)) (z : Wire F → Bool) :
    ∏ α, (phi F α (fun e => z e.1) : k) =
      if z = bitsOf F (valOf F z) ∧ holdsFormula (literalHolds (valOf F z)) F then 1 else 0 := by
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [phi, prod_const_one, mul_one]
  have hV : ∀ v : Fin n, (∀ a b : Inc (tl F) (hd F) (.inl v), z a.1 = z b.1) ↔
      ∀ j : OccW F, j.2.1.1 = v → z (.inr j) = z (.inl v) := by
    intro v
    constructor
    · intro h j hj
      exact h ⟨.inr j, Or.inl (by simp [tl, hj])⟩ ⟨.inl v, Or.inl rfl⟩
    · have hform : ∀ a : Inc (tl F) (hd F) (.inl v), (∀ j : OccW F, j.2.1.1 = v →
          z (.inr j) = z (.inl v)) → z a.1 = z (.inl v) := by
        rintro ⟨e | j, ha⟩ h
        · rcases ha with ha | ha
          · simp only [tl, Sum.inl.injEq] at ha
            subst ha
            rfl
          · simp [hd] at ha
        · rcases ha with ha | ha
          · simp only [tl, Sum.inl.injEq] at ha
            exact h j ha
          · simp [hd] at ha
      intro h a b
      rw [hform a h, hform b h]
  simp_rw [hV]
  rw [Finset.prod_ite_zero, Finset.prod_ite_zero]
  simp only [mem_univ, true_imp_iff, prod_const_one]
  have hm : ∀ (P R : Prop) [Decidable P] [Decidable R],
      ((if P then (1 : k) else 0) * if R then 1 else 0) = if P ∧ R then 1 else 0 := by
    intro P R _ _
    by_cases hP : P <;> by_cases hR : R <;> simp [hP, hR]
  rw [hm]
  refine if_congr ?_ rfl rfl
  have hcons : (∀ v : Fin n, ∀ j : OccW F, j.2.1.1 = v → z (.inr j) = z (.inl v)) ↔
      z = bitsOf F (valOf F z) := by
    constructor
    · intro h
      funext e
      cases e with
      | inl v => rfl
      | inr j => exact h _ j rfl
    · intro h v j hj
      subst hj
      have := congrFun h (.inr j)
      exact this
  rw [hcons]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun C hC => ?_⟩
    obtain ⟨l, hl⟩ := h2 ⟨C, hC⟩
    refine ⟨l.1, l.2, ?_⟩
    have := congrFun h1 (.inr ⟨⟨C, hC⟩, l⟩)
    simp only [bitsOf, valOf] at this
    exact this.symm.trans hl
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun e => ?_⟩
    obtain ⟨l, hl, hx⟩ := h2 e.1 e.2
    refine ⟨⟨l, hl⟩, ?_⟩
    have := congrFun h1 (.inr ⟨e, ⟨l, hl⟩⟩)
    simp only [bitsOf, valOf] at this
    rw [this]
    exact hx

open Classical in
/-- **The network sum of a formula is its number of satisfying assignments.** -/
theorem net_count (F : ClauseSet (SignedLiteral n)) :
    ∑ z : Wire F → Bool, ∏ α, (phi F α (fun e => z e.1) : k) =
      ((univ.filter fun x : Fin n → Bool => holdsFormula (literalHolds x) F).card : k) := by
  simp_rw [prod_phi]
  rw [sum_boole]
  congr 1
  refine card_bij (fun z _ => valOf F z) ?_ ?_ ?_
  · intro z hz
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hz).2.2⟩
  · intro z hz z' hz' h
    have h1 := (mem_filter.mp hz).2.1
    have h2 := (mem_filter.mp hz').2.1
    rw [h1, h2, h]
  · intro x hx
    refine ⟨bitsOf F x, mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩, ?_⟩
    · rfl
    · exact (mem_filter.mp hx).2
    · rfl

/-! ### Arities -/

/-- A variable occurs at most `variableOccurrences` times. -/
theorem card_occ_var_le (F : ClauseSet (SignedLiteral n)) (v : Fin n) :
    (univ.filter fun j : OccW F => j.2.1.1 = v).card ≤ variableOccurrences F v := by
  classical
  unfold variableOccurrences
  have hb : ∀ b : Bool, (univ.filter fun j : OccW F => j.2.1 = (v, b)).card ≤
      literalOccurrences F (v, b) := by
    intro b
    unfold literalOccurrences
    apply card_le_card_of_injOn (fun j => j.1.1)
    · intro j hj
      have hj' : j.2.1 = (v, b) := (mem_filter.mp (mem_coe.mp hj)).2
      simp only [coe_filter, Set.mem_setOf_eq]
      refine ⟨j.1.2, ?_⟩
      have := j.2.2
      rwa [hj'] at this
    · rintro ⟨e, l⟩ h ⟨e', l'⟩ h' heq
      have h1 : l.1 = (v, b) := (mem_filter.mp (mem_coe.mp h)).2
      have h2 : l'.1 = (v, b) := (mem_filter.mp (mem_coe.mp h')).2
      have he : e = e' := Subtype.ext heq
      subst he
      have hl : l = l' := Subtype.ext (h1.trans h2.symm)
      rw [hl]
  have hsub : (univ.filter fun j : OccW F => j.2.1.1 = v) ⊆
      (univ.filter fun j : OccW F => j.2.1 = (v, false)) ∪
      (univ.filter fun j : OccW F => j.2.1 = (v, true)) := by
    intro j hj
    have hj' : j.2.1.1 = v := (mem_filter.mp hj).2
    simp only [mem_union, mem_filter, mem_univ, true_and]
    cases hb' : j.2.1.2
    · left
      exact Prod.ext hj' hb'
    · right
      exact Prod.ext hj' hb'
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ _ := Nat.add_le_add (hb false) (hb true)

/-- The arities at a formula with few occurrences. -/
theorem arity_le (F : ClauseSet (SignedLiteral n)) (hw : ∀ C ∈ F, C.card ≤ 3) {d : ℕ}
    (hd3 : 3 ≤ d) (hdeg : ∀ v, variableOccurrences F v ≤ d) (α : Node F) :
    Spread.arity (tl F) (hd F) α ≤ 1 + d := by
  classical
  unfold Spread.arity
  rcases α with v | e | v
  · have hsub : (univ.filter fun w : Wire F => tl F w = .inl v ∨ hd F w = .inl v) ⊆
        insert (.inl v) ((univ.filter fun j : OccW F => j.2.1.1 = v).map
          ⟨Sum.inr, Sum.inr_injective⟩) := by
      intro w hw'
      rcases (mem_filter.mp hw').2 with h | h
      · cases w with
        | inl u =>
            simp only [tl, Sum.inl.injEq] at h
            simp [h]
        | inr j =>
            simp only [tl, Sum.inl.injEq] at h
            exact mem_insert_of_mem (mem_map.mpr ⟨j, mem_filter.mpr ⟨mem_univ _, h⟩, rfl⟩)
      · cases w <;> simp [hd] at h
    refine (card_le_card hsub).trans ((card_insert_le _ _).trans ?_)
    rw [card_map]
    have := (card_occ_var_le F v).trans (hdeg v)
    omega
  · have hcard : (univ.filter fun w : Wire F => tl F w = .inr (.inl e) ∨ hd F w = .inr (.inl e)).card ≤
        (univ : Finset (LI F e)).card := by
      refine card_le_card_of_surjOn (fun l : LI F e => (.inr ⟨e, l⟩ : Wire F)) ?_
      intro w hw'
      have hmem := mem_coe.mp hw'
      rcases (mem_filter.mp hmem).2 with h | h
      · cases w <;> simp [tl] at h
      · cases w with
        | inl u => simp [hd] at h
        | inr j =>
            obtain ⟨e', l⟩ := j
            simp only [hd, Sum.inr.injEq] at h
            have h' : e' = e := Sum.inl.inj h
            subst h'
            exact ⟨l, by simp, rfl⟩
    have h3 : (univ : Finset (LI F e)).card ≤ 3 := by
      simpa using hw e.1 e.2
    omega
  · have hsub : (univ.filter fun w : Wire F => tl F w = .inr (.inr v) ∨ hd F w = .inr (.inr v)) ⊆
        {.inl v} := by
      intro w hw'
      rcases (mem_filter.mp hw').2 with h | h
      · cases w <;> simp [tl] at h
      · cases w with
        | inl u =>
            simp only [hd, Sum.inr.injEq, Sum.inl.injEq] at h
            simp [h]
        | inr j => simp [hd] at h
    have := card_le_card hsub
    simp only [card_singleton] at this
    omega

/-- The number of wires. -/
theorem card_wire_bounds (F : ClauseSet (SignedLiteral n)) {d : ℕ}
    (hdeg : ∀ v, variableOccurrences F v ≤ d) :
    n ≤ Fintype.card (Wire F) ∧ Fintype.card (Wire F) ≤ (1 + d) * n := by
  classical
  have h1 : Fintype.card (Wire F) = n + Fintype.card (OccW F) := by simp
  have h2 : Fintype.card (OccW F) ≤ d * n := by
    rw [← card_univ, card_eq_sum_card_fiberwise (f := fun j : OccW F => j.2.1.1) (t := univ)
      (fun _ _ => mem_univ _)]
    calc _ ≤ ∑ _v : Fin n, d := sum_le_sum fun v _ => (card_occ_var_le F v).trans (hdeg v)
      _ = _ := by simp [mul_comm]
  constructor
  · omega
  · nlinarith

/-! ### The branching tree -/

variable {L : ℕ}

/-- `t` is a leaf reached from `s`. -/
inductive Reach (hL : 2 ≤ L) : SparseState n L → SparseState n L → Prop
  | leaf (s) (h : chooseSparseRule s.formula L = none) : Reach hL s s
  | left (s r hr t) (h : Reach hL (s.left hL r hr) t) : Reach hL s t
  | right (s r hr t) (h : Reach hL (s.right hL r hr) t) : Reach hL s t

theorem Reach.isLeaf {hL : 2 ≤ L} {s t : SparseState n L} (h : Reach hL s t) :
    chooseSparseRule t.formula L = none := by
  induction h with
  | leaf _ h => exact h
  | left _ _ _ _ _ ih => exact ih
  | right _ _ _ _ _ ih => exact ih

/-- A state is satisfiable exactly when some leaf below it is. -/
theorem sat_iff_leaf (hL : 2 ≤ L) (s : SparseState n L) :
    (∃ x, holdsFormula (literalHolds x) s.formula) ↔
      ∃ t, Reach hL s t ∧ ∃ x, holdsFormula (literalHolds x) t.formula := by
  induction hm : s.remaining using Nat.strong_induction_on generalizing s with
  | _ m ih =>
    cases hr : chooseSparseRule s.formula L with
    | none =>
      constructor
      · intro h
        exact ⟨s, Reach.leaf s hr, h⟩
      · rintro ⟨t, ht, hx⟩
        cases ht with
        | leaf _ _ => exact hx
        | left _ r hr' _ _ => simp [hr] at hr'
        | right _ r hr' _ _ => simp [hr] at hr'
    | some r =>
      have hd := s.remaining_decreases hL r hr
      have ihl := ih _ (hm ▸ hd.1) (s.left hL r hr) rfl
      have ihr := ih _ (hm ▸ hd.2) (s.right hL r hr) rfl
      constructor
      · rintro ⟨x, hx⟩
        rcases (normalizedCoreBranch_equivalent s.formula r.1 r.2 x).mp hx with h | h
        · obtain ⟨t, ht, hxt⟩ := ihl.mp ⟨x, h⟩
          exact ⟨t, Reach.left s r hr t ht, hxt⟩
        · obtain ⟨t, ht, hxt⟩ := ihr.mp ⟨x, h⟩
          exact ⟨t, Reach.right s r hr t ht, hxt⟩
      · rintro ⟨t, ht, hxt⟩
        cases ht with
        | leaf _ h => simp [hr] at h
        | left _ r' hr' _ h =>
          have he : r' = r := by simpa [hr] using hr'.symm
          subst he
          obtain ⟨x, hx⟩ := ihl.mpr ⟨t, h, hxt⟩
          exact ⟨x, (normalizedCoreBranch_equivalent s.formula r'.1 r'.2 x).mpr (Or.inl hx)⟩
        | right _ r' hr' _ h =>
          have he : r' = r := by simpa [hr] using hr'.symm
          subst he
          obtain ⟨x, hx⟩ := ihr.mpr ⟨t, h, hxt⟩
          exact ⟨x, (normalizedCoreBranch_equivalent s.formula r'.1 r'.2 x).mpr (Or.inr hx)⟩

/-! ### The rate of the tree -/

theorem exists_ell {ε : ℝ} (hε : 0 < ε) : ∃ ℓ : ℕ, 2 ≤ ℓ ∧ (20 * Real.log ℓ + 10) / ℓ ≤ ε / 4 := by
  obtain ⟨ℓ, h80, h⟩ := exists_good_L (D := 1) (le_refl 1) (ε := ε / 4) (by positivity)
  refine ⟨ℓ, by omega, ?_⟩
  have hℓ : (0 : ℝ) < ℓ := by
    have : 0 < ℓ := by omega
    exact_mod_cast this
  have hlog : 0 ≤ Real.log ℓ := Real.log_natCast_nonneg ℓ
  have h' : 10 * ((Real.log ℓ + 2) / ℓ) ≤ ε / 4 / 2 := by simpa using h
  have hle : (20 * Real.log ℓ + 10) / ℓ ≤ 2 * (10 * ((Real.log ℓ + 2) / ℓ)) := by
    rw [div_le_iff₀ hℓ]
    field_simp
    nlinarith
  linarith

end Sat
end TransposeBase
