import SatBase.SparsificationPotential

/-! Potential changes for batches of new unit or binary clauses. The
normalization formula supplies the surviving old clauses exactly. -/
namespace SatBase
open scoped BigOperators

variable {n : ℕ}

def remainingOld (F N : ClauseSet (SignedLiteral n)) : ClauseSet (SignedLiteral n) :=
  F.filter (fun C => ∀ D∈N,¬D⊆C)

theorem fresh_disjoint (F N : ClauseSet (SignedLiteral n))
    (hnew : ∀ C∈N,∀ D∈F,¬D⊆C) : Disjoint N (remainingOld F N) := by
  apply Finset.disjoint_left.mpr
  intro C hCN hCR
  exact hnew C hCN C (Finset.mem_filter.mp hCR).1 (Finset.Subset.refl _)

theorem widthCount_disjoint_union (F N : ClauseSet (SignedLiteral n))
    (h : Disjoint F N) (w : ℕ) : widthCount (F∪N) w=widthCount F w+widthCount N w := by
  unfold widthCount
  rw [Finset.filter_union,Finset.card_union_of_disjoint]
  exact h.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem widthCount_uniform (N : ClauseSet (SignedLiteral n)) (k : ℕ)
    (hw : ∀ C∈N,C.card=k) : widthCount N k=N.card := by
  unfold widthCount
  rw [Finset.filter_true_of_mem hw]

theorem widthCount_uniform_other (N : ClauseSet (SignedLiteral n)) (k w : ℕ)
    (hw : ∀ C∈N,C.card=k) (hne : w≠k) : widthCount N w=0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro C hC he
  exact hne (he.symm.trans (hw C hC))

theorem remainingOld_low_width (F N : ClauseSet (SignedLiteral n)) (k w : ℕ)
    (hw : ∀ C∈N,C.card=k) (hwk : w≤k)
    (hnew : ∀ C∈N,∀ D∈F,¬D⊆C) :
    widthCount (remainingOld F N) w=widthCount F w := by
  apply congrArg Finset.card
  apply Finset.ext
  intro C
  constructor
  · intro hC
    obtain ⟨hC,hcard⟩ := Finset.mem_filter.mp hC
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hC).1,hcard⟩
  · intro hC
    obtain ⟨hCF,hcard⟩ := Finset.mem_filter.mp hC
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hCF,?_⟩,hcard⟩
    intro D hD hDC
    have he : D=C := Finset.eq_of_subset_of_card_le hDC (by rw [hcard,hw D hD];exact hwk)
    exact hnew D hD C hCF (by rw [he])

theorem remainingOld_binary_loss (F N : ClauseSet (SignedLiteral n)) (L : ℕ)
    (hw : ∀ C∈N,C.card=1) (hdeg : ∀ a,(coreClauses F 2 {a}).card<2*L) :
    widthCount F 2≤widthCount (remainingOld F N) 2+2*L*N.card := by
  let cover := N.biUnion (fun D => coreClauses F 2 D)
  have hs : F.filter (fun C => C.card=2)⊆
      (remainingOld F N).filter (fun C => C.card=2)∪cover := by
    intro C hC
    obtain ⟨hCF,hcard⟩ := Finset.mem_filter.mp hC
    by_cases hkeep : ∀ D∈N,¬D⊆C
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hCF,hkeep⟩,hcard⟩)
    · push Not at hkeep
      obtain ⟨D,hDN,hDC⟩ := hkeep
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨D,hDN,Finset.mem_filter.mpr ⟨hCF,hcard,hDC⟩⟩)
  have hc : cover.card≤2*L*N.card := by
    calc
      _ ≤ ∑ D∈N,(coreClauses F 2 D).card := Finset.card_biUnion_le
      _ ≤ ∑ _D∈N,2*L := by
        apply Finset.sum_le_sum
        intro D hD
        obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp (hw D hD)
        exact (hdeg a).le
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id];ring
  have hb := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  exact hb.trans (Nat.add_le_add_left hc _)

/-- Equal-width clauses cannot strictly contain one another. -/
theorem uniform_antichain (N : ClauseSet (SignedLiteral n)) (k : ℕ)
    (hw : ∀ C∈N,C.card=k) : ∀ C∈N,∀ D∈N,C⊆D → C=D := by
  intro C hC D hD hCD
  exact Finset.eq_of_subset_of_card_le hCD (by rw [hw C hC,hw D hD])

end SatBase
