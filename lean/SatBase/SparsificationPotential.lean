import SatBase.CoreFreshness

/-! The numerical potential has one definition at every node. Its upper
bound permits contradictory unit clauses; it assumes only the binary
literal-degree invariant, which is to be proved across rule applications. -/
namespace SatBase
open scoped BigOperators

def widthCount {n : ℕ} (F : ClauseSet (SignedLiteral n)) (w : ℕ) : ℕ :=
  (F.filter (fun C => C.card=w)).card

/-- There are only two possible unit clauses per declared variable. -/
theorem unitCount_bound {n : ℕ} (F : ClauseSet (SignedLiteral n)) :
    widthCount F 1≤2*n := by
  have hs : F.filter (fun C => C.card=1)⊆
      (Finset.univ : Finset (SignedLiteral n)).image (fun a => {a}) := by
    intro C hC
    obtain ⟨a,ha⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hC).2
    exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,ha.symm⟩
  calc
    _ ≤ ((Finset.univ : Finset (SignedLiteral n)).image (fun a => {a})).card :=
      Finset.card_le_card hs
    _ ≤ (Finset.univ : Finset (SignedLiteral n)).card := Finset.card_image_le
    _ = _ := by simp [SignedLiteral,Nat.mul_comm]

/-- Counting a width-w clause once at each of its w literals. -/
theorem sum_literalDegrees {n : ℕ} (F : ClauseSet (SignedLiteral n)) (w : ℕ) :
    (∑ a : SignedLiteral n,(coreClauses F w {a}).card)=w*widthCount F w := by
  calc
    _ = ∑ a : SignedLiteral n,∑ C∈F,if C.card=w ∧ a∈C then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      simp only [coreClauses,Finset.card_eq_sum_ones,Finset.sum_filter,
        Finset.singleton_subset_iff]
    _ = ∑ C∈F,∑ a : SignedLiteral n,if C.card=w ∧ a∈C then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ C∈F,if C.card=w then w else 0 := by
      apply Finset.sum_congr rfl
      intro C _
      by_cases hc : C.card=w
      · simp only [hc,true_and]
        have h : (∑ a : SignedLiteral n,if a∈C then 1 else 0)=C.card := by
          simp only [Finset.sum_boole,Nat.cast_id,Finset.filter_mem_eq_inter,Finset.univ_inter]
        rw [h,hc,if_true]
      · simp [hc]
    _ = w*widthCount F w := by
      rw [←Finset.sum_filter]
      simp [widthCount,Nat.mul_comm]

theorem binaryCount_bound {n : ℕ} (F : ClauseSet (SignedLiteral n)) (L : ℕ)
    (hdeg : ∀ a,(coreClauses F 2 {a}).card<2*L) : widthCount F 2≤2*n*L := by
  have hsum : (∑ a : SignedLiteral n,(coreClauses F 2 {a}).card)≤(2*n)*(2*L) := by
    calc
      _ ≤ ∑ _a : SignedLiteral n,2*L := Finset.sum_le_sum (fun a _ => (hdeg a).le)
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,SignedLiteral,Fintype.card_prod,
          Fintype.card_fin,Fintype.card_bool,nsmul_eq_mul,Nat.cast_id]
        ring
  rw [sum_literalDegrees] at hsum
  nlinarith

end SatBase
