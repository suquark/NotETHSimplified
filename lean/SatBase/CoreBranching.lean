import SatBase.ClauseNormalization

/-! The actual core/petal replacement. The two children preserve the union
of satisfying assignments; their satisfying sets need not be disjoint. -/
namespace SatBase

variable {A : Type*} [DecidableEq A]

def coreClauses (F : ClauseSet A) (w : ℕ) (S : Finset A) : ClauseSet A :=
  F.filter (fun C => C.card=w ∧ S⊆C)

def corePetals (F : ClauseSet A) (w : ℕ) (S : Finset A) : ClauseSet A :=
  (coreClauses F w S).image (fun C => C\S)

def coreLeft (F : ClauseSet A) (_w : ℕ) (S : Finset A) : ClauseSet A :=
  insert S F

def coreRight (F : ClauseSet A) (w : ℕ) (S : Finset A) : ClauseSet A :=
  F∪corePetals F w S

/-- The replacement is an exact union identity for every assignment. -/
theorem coreBranch_equivalent (p : A → Prop) (F : ClauseSet A) (w : ℕ) (S : Finset A) :
    holdsFormula p F ↔ holdsFormula p (coreLeft F w S) ∨ holdsFormula p (coreRight F w S) := by
  constructor
  · intro h
    by_cases hS : holdsClause p S
    · left
      intro C hC
      rcases Finset.mem_insert.mp hC with he | hC
      · simpa only [he] using hS
      · exact h C hC
    · right
      intro P hP
      rcases Finset.mem_union.mp hP with hP | hP
      · exact h P hP
      · obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hP
        obtain ⟨a,ha,hpa⟩ := h C (Finset.mem_filter.mp hC).1
        refine ⟨a,Finset.mem_sdiff.mpr ⟨ha,?_⟩,hpa⟩
        exact fun haS => hS ⟨a,haS,hpa⟩
  · rintro (h | h) C hC
    · exact h C (Finset.mem_insert_of_mem hC)
    · exact h C (Finset.mem_union_left _ hC)

def normalizedCoreLeft {n : ℕ} (F : ClauseSet (SignedLiteral n)) (w : ℕ)
    (S : Finset (SignedLiteral n)) : ClauseSet (SignedLiteral n) :=
  normalizeClauses (coreLeft F w S)

def normalizedCoreRight {n : ℕ} (F : ClauseSet (SignedLiteral n)) (w : ℕ)
    (S : Finset (SignedLiteral n)) : ClauseSet (SignedLiteral n) :=
  normalizeClauses (coreRight F w S)

theorem normalizedCoreBranch_equivalent {n : ℕ} (F : ClauseSet (SignedLiteral n))
    (w : ℕ) (S : Finset (SignedLiteral n)) (x : Fin n → Bool) :
    holdsFormula (literalHolds x) F ↔
      holdsFormula (literalHolds x) (normalizedCoreLeft F w S) ∨
      holdsFormula (literalHolds x) (normalizedCoreRight F w S) := by
  simp only [normalizedCoreLeft,normalizedCoreRight,normalizeClauses_equivalent]
  exact coreBranch_equivalent _ _ _ _

/-- Removing the same core from containing clauses is injective. -/
theorem corePetal_injective (F : ClauseSet A) (w : ℕ) (S : Finset A) :
    Set.InjOn (fun C => C\S) (coreClauses F w S) := by
  intro C hC D hD he
  change C\S=D\S at he
  have hc := (Finset.mem_filter.mp hC).2.2
  have hd := (Finset.mem_filter.mp hD).2.2
  calc
    C = C\S∪S := (Finset.sdiff_union_of_subset hc).symm
    _ = D\S∪S := by rw [he]
    _ = D := Finset.sdiff_union_of_subset hd

theorem corePetals_card (F : ClauseSet A) (w : ℕ) (S : Finset A) :
    (corePetals F w S).card=(coreClauses F w S).card :=
  Finset.card_image_iff.mpr (corePetal_injective F w S)

theorem corePetal_width (F : ClauseSet A) (w : ℕ) (S : Finset A)
    {P : Finset A} (hP : P∈corePetals F w S) : P.card=w-S.card := by
  obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hP
  have hp := (Finset.mem_filter.mp hC).2
  rw [Finset.card_sdiff_of_subset hp.2,hp.1]

end SatBase
