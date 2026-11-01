import SatBase.BinaryDegree
import SatBase.InsertionPotential
import Mathlib.Data.Finset.Lattice.Fold

/-! A bounded binary-clause packing gives a potential for every normalized
formula. It is used only in proofs; the algorithm never computes a packing.
Unlike the binary count, its bound requires no invariant on the full formula. -/
namespace SatBase
open scoped BigOperators
variable {n : ℕ}

def binaryPackings (F : ClauseSet (SignedLiteral n)) (L : ℕ) :
    Finset (ClauseSet (SignedLiteral n)) :=
  (F.filter (fun C => C.card=2)).powerset.filter
    (fun P => ∀ a,(coreClauses P 2 {a}).card<2*L)

noncomputable def binaryPackingRank (F : ClauseSet (SignedLiteral n)) (L : ℕ) : ℕ :=
  (binaryPackings F L).sup Finset.card

noncomputable def packingPotential (F : ClauseSet (SignedLiteral n)) (L : ℕ) : ℕ :=
  4*L*widthCount F 1+binaryPackingRank F L

theorem binaryPacking_mem {F P : ClauseSet (SignedLiteral n)} {L : ℕ} :
    P∈binaryPackings F L ↔
      P⊆F.filter (fun C => C.card=2) ∧ ∀ a,(coreClauses P 2 {a}).card<2*L := by
  simp only [binaryPackings,Finset.mem_filter,Finset.mem_powerset]

theorem binaryPackingRank_le_total (F : ClauseSet (SignedLiteral n)) (L : ℕ) :
    binaryPackingRank F L≤widthCount F 2 := by
  apply Finset.sup_le
  intro P hP
  exact Finset.card_le_card (binaryPacking_mem.mp hP).1

theorem binaryPackingRank_eq_total (F : ClauseSet (SignedLiteral n)) (L : ℕ)
    (hdeg : ∀ a,(coreClauses F 2 {a}).card<2*L) :
    binaryPackingRank F L=widthCount F 2 := by
  apply Nat.le_antisymm (binaryPackingRank_le_total F L)
  change (F.filter (fun C => C.card=2)).card≤(binaryPackings F L).sup Finset.card
  apply Finset.le_sup
  apply binaryPacking_mem.mpr
  refine ⟨Finset.Subset.refl _,?_⟩
  intro a
  exact (binaryDegree_mono (Finset.filter_subset _ _) a).trans_lt (hdeg a)

theorem binaryPackingRank_bound (F : ClauseSet (SignedLiteral n)) (L : ℕ) :
    binaryPackingRank F L≤2*n*L := by
  apply Finset.sup_le
  intro P hP
  have hp := binaryPacking_mem.mp hP
  have hw : ∀ C∈P,C.card=2 := fun C hC => (Finset.mem_filter.mp (hp.1 hC)).2
  rw [←widthCount_uniform P 2 hw]
  exact binaryCount_bound P L hp.2

theorem packingPotential_bound (F : ClauseSet (SignedLiteral n)) (L : ℕ) :
    packingPotential F L≤10*n*L := by
  have hu := unitCount_bound F
  have hb := binaryPackingRank_bound F L
  unfold packingPotential
  nlinarith

theorem binaryPackingRank_attained (F : ClauseSet (SignedLiteral n)) (L : ℕ)
    (hL : 0<L) :
    ∃ P∈binaryPackings F L,binaryPackingRank F L=P.card := by
  have he : (∅ : ClauseSet (SignedLiteral n))∈binaryPackings F L := by
    apply binaryPacking_mem.mpr
    refine ⟨Finset.empty_subset _,?_⟩
    intro a
    simp only [coreClauses,Finset.filter_empty,Finset.card_empty]
    omega
  exact Finset.exists_mem_eq_sup _ ⟨∅,he⟩ Finset.card

theorem add_units_packingPotential (F N : ClauseSet (SignedLiteral n)) (L : ℕ)
    (hL : 0<L)
    (hF : ∀ C∈F,∀ D∈F,C⊆D → C=D) (hw : ∀ C∈N,C.card=1)
    (hnew : ∀ C∈N,∀ D∈F,¬D⊆C)
    (htF : ∀ C∈F,¬tautological C) (htN : ∀ C∈N,¬tautological C) :
    packingPotential F L+2*L*N.card≤packingPotential (normalizeClauses (F∪N)) L := by
  have he := normalizeClauses_addition F N hF (uniform_antichain N 1 hw) hnew htF htN
  change normalizeClauses (F∪N)=N∪remainingOld F N at he
  have hu : widthCount (normalizeClauses (F∪N)) 1=N.card+widthCount F 1 := by
    rw [he,widthCount_disjoint_union N _ (fresh_disjoint F N hnew),
      widthCount_uniform N 1 hw,remainingOld_low_width F N 1 1 hw (by omega) hnew]
  obtain ⟨P,hP,hmax⟩ := binaryPackingRank_attained F L hL
  have hp := binaryPacking_mem.mp hP
  have hPF : P⊆F := fun C hC => (Finset.mem_filter.mp (hp.1 hC)).1
  have hwP : ∀ C∈P,C.card=2 := fun C hC => (Finset.mem_filter.mp (hp.1 hC)).2
  have hsurv : remainingOld P N⊆P := Finset.filter_subset _ _
  have hwR : ∀ C∈remainingOld P N,C.card=2 := fun C hC => hwP C (hsurv hC)
  have hnewP : remainingOld P N∈binaryPackings (normalizeClauses (F∪N)) L := by
    apply binaryPacking_mem.mpr
    refine ⟨?_,?_⟩
    · intro C hC
      apply Finset.mem_filter.mpr
      refine ⟨?_,hwR C hC⟩
      rw [he]
      apply Finset.mem_union_right
      obtain ⟨hCP,hkeep⟩ := Finset.mem_filter.mp hC
      exact Finset.mem_filter.mpr ⟨hPF hCP,hkeep⟩
    · intro a
      exact (binaryDegree_mono hsurv a).trans_lt (hp.2 a)
  have hlower : (remainingOld P N).card≤binaryPackingRank (normalizeClauses (F∪N)) L :=
    Finset.le_sup hnewP
  have hloss := remainingOld_binary_loss P N L hw hp.2
  rw [widthCount_uniform P 2 hwP,widthCount_uniform _ 2 hwR] at hloss
  unfold packingPotential
  rw [hu,hmax]
  nlinarith

/-- A binary insertion preserves units and adds exactly its cardinality to
the binary count. A degree bound is needed only for the resulting formula. -/
theorem add_binaries_packingPotential (F N : ClauseSet (SignedLiteral n)) (L : ℕ)
    (hF : ∀ C∈F,∀ D∈F,C⊆D → C=D) (hw : ∀ C∈N,C.card=2)
    (hnew : ∀ C∈N,∀ D∈F,¬D⊆C)
    (htF : ∀ C∈F,¬tautological C) (htN : ∀ C∈N,¬tautological C)
    (hdeg : ∀ a,(coreClauses (normalizeClauses (F∪N)) 2 {a}).card<2*L) :
    packingPotential F L+N.card≤packingPotential (normalizeClauses (F∪N)) L := by
  have he := normalizeClauses_addition F N hF (uniform_antichain N 2 hw) hnew htF htN
  change normalizeClauses (F∪N)=N∪remainingOld F N at he
  have hdis := fresh_disjoint F N hnew
  have hu : widthCount (normalizeClauses (F∪N)) 1=widthCount F 1 := by
    rw [he,widthCount_disjoint_union N _ hdis,
      widthCount_uniform_other N 2 1 hw (by decide),zero_add,
      remainingOld_low_width F N 2 1 hw (by omega) hnew]
  have hb : widthCount (normalizeClauses (F∪N)) 2=N.card+widthCount F 2 := by
    rw [he,widthCount_disjoint_union N _ hdis,widthCount_uniform N 2 hw,
      remainingOld_low_width F N 2 2 hw (by omega) hnew]
  have hbound := binaryPackingRank_le_total F L
  unfold packingPotential
  rw [hu,binaryPackingRank_eq_total _ L hdeg,hb]
  omega

/-- The selected rule increases one potential on arbitrary normalized
states. Only binary insertions require the local ternary degree bound. -/
theorem chosen_packing_gains (G : ClauseSet (SignedLiteral n)) (L : ℕ) (hL : 2≤L)
    (r : ℕ × Finset (SignedLiteral n))
    (hr : chooseSparseRule (normalizeClauses G) L=some r) :
    packingPotential (normalizeClauses G) L+1≤
        packingPotential (normalizedCoreLeft (normalizeClauses G) r.1 r.2) L ∧
    packingPotential (normalizeClauses G) L+L^2≤
        packingPotential (normalizedCoreRight (normalizeClauses G) r.1 r.2) L := by
  let F := normalizeClauses G
  change packingPotential F L+1≤packingPotential (normalizedCoreLeft F r.1 r.2) L ∧
    packingPotential F L+L^2≤packingPotential (normalizedCoreRight F r.1 r.2) L
  have hanti : ∀ C∈F,∀ D∈F,C⊆D → C=D :=
    fun _ hC _ hD hCD => normalizeClauses_antichain G hC hD hCD
  have htF : ∀ C∈F,¬tautological C :=
    fun _ hC => normalizeClauses_not_tautological G hC
  obtain ⟨hmem,hcore,hproper,hcount⟩ := chooseSparseRule_sound F L r hr
  have hwidth : r.1≤3 := by
    rcases sparseCandidate_width r hmem with h | h <;> omega
  have hcpos : 0<r.2.card := Finset.card_pos.mpr hcore
  have ha : (coreClauses F r.1 r.2).Nonempty := by
    apply Finset.card_pos.mp
    have hp : 1≤L^(r.1-r.2.card) := one_le_pow₀ (by omega)
    omega
  have hfresh := chosen_rule_fresh G L (by omega) r hr
  have hnewL : ∀ C∈({r.2} : ClauseSet (SignedLiteral n)),∀ D∈F,¬D⊆C := by
    intro C hC D hD
    rw [Finset.mem_singleton.mp hC]
    exact hfresh.1 D hD
  have htL : ∀ C∈({r.2} : ClauseSet (SignedLiteral n)),¬tautological C := by
    intro C hC
    rw [Finset.mem_singleton.mp hC]
    exact core_not_tautological F htF _ _ ha
  have htR := corePetals_not_tautological F htF r.1 r.2
  constructor
  · have hcases : r.2.card=1 ∨ r.2.card=2 := by omega
    rcases hcases with hunit | hbinary
    · have hw : ∀ C∈({r.2} : ClauseSet (SignedLiteral n)),C.card=1 := by
        intro C hC
        simpa only [Finset.mem_singleton.mp hC] using hunit
      have hg := add_units_packingPotential F {r.2} L (by omega) hanti hw hnewL htF htL
      have he : normalizeClauses (F∪{r.2})=normalizedCoreLeft F r.1 r.2 := by
        simp only [Finset.union_singleton,normalizedCoreLeft,coreLeft]
      rw [he,Finset.card_singleton] at hg
      omega
    · have hw : ∀ C∈({r.2} : ClauseSet (SignedLiteral n)),C.card=2 := by
        intro C hC
        simpa only [Finset.mem_singleton.mp hC] using hbinary
      have hr3 : r.1=3 := by omega
      have hd := ternary_left_binaryDegree F L r.2 (by
        have he : r=(3,r.2) := Prod.ext hr3 rfl
        rw [←he]
        exact hr)
      have hg := add_binaries_packingPotential F {r.2} L hanti hw hnewL htF htL
        (fun a => by simpa only [Finset.union_singleton,normalizedCoreLeft,coreLeft,hr3] using hd a)
      simpa only [Finset.union_singleton,normalizedCoreLeft,coreLeft,Finset.card_singleton] using hg
  · have hcases : r.1-r.2.card=1 ∨ r.1-r.2.card=2 := by omega
    rcases hcases with hunit | hbinary
    · have hw : ∀ C∈corePetals F r.1 r.2,C.card=1 := by
        intro C hC
        simpa only [hunit] using corePetal_width F r.1 r.2 hC
      have hsize : L≤(corePetals F r.1 r.2).card := by
        rw [corePetals_card]
        simpa only [hunit,pow_one] using hcount
      have hg := add_units_packingPotential F (corePetals F r.1 r.2) L (by omega)
        hanti hw hfresh.2 htF htR
      change packingPotential F L+2*L*(corePetals F r.1 r.2).card≤
        packingPotential (normalizedCoreRight F r.1 r.2) L at hg
      nlinarith
    · have hw : ∀ C∈corePetals F r.1 r.2,C.card=2 := by
        intro C hC
        simpa only [hbinary] using corePetal_width F r.1 r.2 hC
      have hsize : L^2≤(corePetals F r.1 r.2).card := by
        rw [corePetals_card]
        simpa only [hbinary] using hcount
      have hr3 : r.1=3 := by omega
      have hcore1 : r.2.card=1 := by omega
      obtain ⟨b,hb⟩ := Finset.card_eq_one.mp hcore1
      have hd := singleton_ternary_right_binaryDegree F L b (by
        have he : r=(3,{b}) := Prod.ext hr3 hb
        rw [←he]
        exact hr)
      have hg := add_binaries_packingPotential F (corePetals F r.1 r.2) L hanti hw hfresh.2 htF htR
        (fun a => by simpa only [normalizedCoreRight,coreRight,hr3,hb] using hd a)
      change packingPotential F L+(corePetals F r.1 r.2).card≤
        packingPotential (normalizedCoreRight F r.1 r.2) L at hg
      exact (Nat.add_le_add_left hsize _).trans hg

end SatBase
