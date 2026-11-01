import TransposeBase.Pseudo.CnfTest
import SatBase.SparseSearch

/-!
# The rule candidates as numbers

`sparseCandidates n` is a fixed list. A candidate is one number `r` below `3 * (2 * n + 1) ^ 2`:

* digit `d1 n r` is the first literal code `a`,
* digit `d0 n r` is the second literal code `b`, or `0` if there is none,
* `phase n r = r / (2 * n + 1) / (2 * n + 1)` is `0` for `(2, {a})`, `1` for `(3, {a, b})`, `2` for `(3, {a})`.

The numbers increase along `sparseCandidates n`, so the chosen rule is the least valid number that is eligible.
This is a specification file: the program is in `CnfRule`.
-/

namespace TransposeBase.Pseudo.CnfTree

open SatBase Finset

def phase (n r : ℕ) : ℕ := r / (2 * n + 1) / (2 * n + 1)

/-- The number `r` is the number of a candidate, when `r` is below `ruleCap n`. -/
def SlotOK (n r : ℕ) : Prop :=
  d1 n r ≠ 0 ∧ (phase n r = 1 → d0 n r ≠ 0 ∧ d0 n r ≠ d1 n r) ∧ (phase n r ≠ 1 → d0 n r = 0)

instance (n r : ℕ) : Decidable (SlotOK n r) := by unfold SlotOK; infer_instance

/-- The number of candidate numbers. It is also the value that means "no rule". -/
def ruleCap (n : ℕ) : ℕ := 3 * (2 * n + 1) * (2 * n + 1)

def ruleSet (n r : ℕ) : Finset (SignedLiteral n) :=
  univ.filter fun l => litCode l = d1 n r ∨ litCode l = d0 n r

def ruleW (n r : ℕ) : ℕ := if phase n r = 0 then 2 else 3

def ruleOf (n r : ℕ) : ℕ × Finset (SignedLiteral n) := (ruleW n r, ruleSet n r)

def thrOf (L n r : ℕ) : ℕ := if phase n r ≤ 1 then L else L * L

theorem mem_ruleSet {n r : ℕ} {l : SignedLiteral n} :
    l ∈ ruleSet n r ↔ litCode l = d1 n r ∨ litCode l = d0 n r := by simp [ruleSet]

theorem mk_phase {n a b c : ℕ} (ha : a < 2 * n + 1) (hb : b < 2 * n + 1) : phase n (mk n a b c) = c := by
  have h1 : mk n a b c / (2 * n + 1) = b + (2 * n + 1) * c := by
    rw [mk, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt ha, zero_add]
  rw [phase, h1, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hb, zero_add]

theorem mk_digits' {n a b c : ℕ} (ha : a < 2 * n + 1) (hb : b < 2 * n + 1) :
    d0 n (mk n a b c) = a ∧ d1 n (mk n a b c) = b := by
  have h0 : mk n a b c % (2 * n + 1) = a := by
    rw [mk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  have h1 : mk n a b c / (2 * n + 1) = b + (2 * n + 1) * c := by
    rw [mk, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt ha, zero_add]
  have h2 : (b + (2 * n + 1) * c) % (2 * n + 1) = b := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  exact ⟨h0, by rw [d1, h1, h2]⟩

theorem eq_mk_phase (n r : ℕ) : r = mk n (d0 n r) (d1 n r) (phase n r) := by
  have e1 := Nat.div_add_mod r (2 * n + 1)
  have e2 := Nat.div_add_mod (r / (2 * n + 1)) (2 * n + 1)
  simp only [mk, d0, d1, phase]
  calc r = (2 * n + 1) * (r / (2 * n + 1)) + r % (2 * n + 1) := e1.symm
    _ = _ := by
      rw [add_comm]
      congr 2
      rw [add_comm] at e2
      exact e2.symm

theorem mk_lt_ruleCap {n a b c : ℕ} (ha : a < 2 * n + 1) (hb : b < 2 * n + 1) (hc : c < 3) :
    mk n a b c < ruleCap n := by
  have h1 : b + (2 * n + 1) * c < (2 * n + 1) * 3 := by nlinarith
  have h2 : a + (2 * n + 1) * (b + (2 * n + 1) * c) < (2 * n + 1) * ((2 * n + 1) * 3) := by nlinarith
  calc mk n a b c < (2 * n + 1) * ((2 * n + 1) * 3) := h2
    _ = ruleCap n := by unfold ruleCap; ring

theorem phase_lt {n r : ℕ} (hr : r < ruleCap n) : phase n r < 3 := by
  unfold phase
  rw [Nat.div_div_eq_div_mul]
  apply Nat.div_lt_of_lt_mul
  calc r < ruleCap n := hr
    _ = (2 * n + 1) * (2 * n + 1) * 3 := by unfold ruleCap; ring

/-- Comparison of numbers by digits. -/
theorem mk_lt_mk_of_phase {n a b c a' b' c' : ℕ} (ha : a < 2 * n + 1) (hb : b < 2 * n + 1)
    (hc : c < c') : mk n a b c < mk n a' b' c' := by
  unfold mk
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hc
  have h1 : a + (2 * n + 1) * b < (2 * n + 1) * (2 * n + 1) := by nlinarith
  have : (2 * n + 1) * (b' + (2 * n + 1) * (c + d + 1)) =
      (2 * n + 1) * b' + (2 * n + 1) * (2 * n + 1) * c + (2 * n + 1) * (2 * n + 1) * d +
        (2 * n + 1) * (2 * n + 1) := by ring
  have h2 : (2 * n + 1) * (b + (2 * n + 1) * c) = (2 * n + 1) * b + (2 * n + 1) * (2 * n + 1) * c := by
    ring
  rw [this, h2]
  omega

theorem mk_lt_mk_of_mid {n a b c a' b' : ℕ} (ha : a < 2 * n + 1) (hb : b < b') :
    mk n a b c < mk n a' b' c := by
  unfold mk
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hb
  have h1 : (2 * n + 1) * (b + d + 1 + (2 * n + 1) * c) =
      (2 * n + 1) * (b + (2 * n + 1) * c) + (2 * n + 1) * d + (2 * n + 1) := by ring
  rw [h1]
  omega

theorem mk_lt_mk_of_low {n a b c a' : ℕ} (ha : a < a') : mk n a b c < mk n a' b c := by
  unfold mk
  omega

/-! ### The list of candidate numbers -/

def cA {n : ℕ} (a : SignedLiteral n) : ℕ := mk n 0 (litCode a) 0
def cB {n : ℕ} (a b : SignedLiteral n) : ℕ := mk n (litCode b) (litCode a) 1
def cC {n : ℕ} (a : SignedLiteral n) : ℕ := mk n 0 (litCode a) 2

/-- The candidate numbers, in the order of `sparseCandidates`. -/
def slots (n : ℕ) : List ℕ :=
  (literalOrder n).map cA ++
    (literalOrder n).flatMap (fun a => ((literalOrder n).filter (fun b => a ≠ b)).map (cB a)) ++
    (literalOrder n).map cC

theorem litCode_lt {n : ℕ} (l : SignedLiteral n) : litCode l < 2 * n + 1 := by
  have := litCode_le l
  omega

theorem ruleOf_cA {n : ℕ} (a : SignedLiteral n) : ruleOf n (cA a) = (2, {a}) := by
  have h0 : 0 < 2 * n + 1 := by omega
  have hd := mk_digits' (n := n) (c := 0) h0 (litCode_lt a)
  have hp := mk_phase (n := n) (c := 0) h0 (litCode_lt a)
  simp only [ruleOf, ruleW, cA, hp, if_true]
  congr 1
  ext l
  rw [mem_ruleSet, hd.1, hd.2, mem_singleton]
  have := litCode_pos l
  constructor
  · rintro (h | h)
    · exact litCode_injective h
    · omega
  · rintro rfl
    exact Or.inl rfl

theorem ruleOf_cB {n : ℕ} (a b : SignedLiteral n) : ruleOf n (cB a b) = (3, {a, b}) := by
  have hd := mk_digits' (n := n) (c := 1) (litCode_lt b) (litCode_lt a)
  have hp := mk_phase (n := n) (c := 1) (litCode_lt b) (litCode_lt a)
  simp only [ruleOf, ruleW, cB, hp]
  congr 1
  ext l
  rw [mem_ruleSet, hd.1, hd.2, mem_insert, mem_singleton]
  constructor
  · rintro (h | h)
    · exact Or.inl (litCode_injective h)
    · exact Or.inr (litCode_injective h)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem ruleOf_cC {n : ℕ} (a : SignedLiteral n) : ruleOf n (cC a) = (3, {a}) := by
  have h0 : 0 < 2 * n + 1 := by omega
  have hd := mk_digits' (n := n) (c := 2) h0 (litCode_lt a)
  have hp := mk_phase (n := n) (c := 2) h0 (litCode_lt a)
  simp only [ruleOf, ruleW, cC, hp]
  congr 1
  ext l
  rw [mem_ruleSet, hd.1, hd.2, mem_singleton]
  have := litCode_pos l
  constructor
  · rintro (h | h)
    · exact litCode_injective h
    · omega
  · rintro rfl
    exact Or.inl rfl

theorem sparseCandidates_eq (n : ℕ) : sparseCandidates n = (slots n).map (ruleOf n) := by
  simp only [sparseCandidates, slots, List.map_append, List.map_map, List.map_flatMap]
  congr 1
  · congr 1
    · apply List.map_congr_left
      intro a _
      simp [ruleOf_cA]
    · apply List.flatMap_congr
      intro a _
      apply List.map_congr_left
      intro b _
      simp [ruleOf_cB]
  · apply List.map_congr_left
    intro a _
    simp [ruleOf_cC]

theorem pairwise_literalOrder (n : ℕ) :
    (literalOrder n).Pairwise (fun a b => litCode a < litCode b) := by
  unfold literalOrder
  rw [List.pairwise_flatMap]
  constructor
  · intro v _
    simp [litCode]
  · have := (List.sortedLT_finRange n).pairwise
    refine this.imp ?_
    intro v w hvw a ha b hb
    have hvw' : (v : ℕ) < w := hvw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [litCode] <;> omega

theorem pairwise_slots (n : ℕ) : (slots n).Pairwise (· < ·) := by
  have h0 : 0 < 2 * n + 1 := by omega
  have po := pairwise_literalOrder n
  unfold slots
  rw [List.pairwise_append, List.pairwise_append]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [List.pairwise_map]
    exact po.imp (fun h => mk_lt_mk_of_mid h0 h)
  · rw [List.pairwise_flatMap]
    constructor
    · intro a _
      rw [List.pairwise_map]
      exact (po.filter _).imp (fun h => mk_lt_mk_of_low h)
    · refine po.imp ?_
      intro a a' h x hx y hy
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨b', _, rfl⟩ := List.mem_map.mp hy
      exact mk_lt_mk_of_mid (litCode_lt b) h
  · intro x hx y hy
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨c, _, hc⟩ := List.mem_flatMap.mp hy
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hc
    exact mk_lt_mk_of_phase h0 (litCode_lt a) (by norm_num)
  · rw [List.pairwise_map]
    exact po.imp (fun h => mk_lt_mk_of_mid h0 h)
  · intro x hx y hy
    obtain ⟨a', _, rfl⟩ := List.mem_map.mp hy
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
      exact mk_lt_mk_of_phase h0 (litCode_lt a) (by norm_num)
    · obtain ⟨c, _, hc⟩ := List.mem_flatMap.mp hx
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hc
      exact mk_lt_mk_of_phase (litCode_lt b) (litCode_lt c) (by norm_num)

theorem mem_slots {n r : ℕ} : r ∈ slots n ↔ r < ruleCap n ∧ SlotOK n r := by
  have h0 : 0 < 2 * n + 1 := by omega
  constructor
  · intro h
    unfold slots at h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨a, _, rfl⟩ := List.mem_map.mp h
        have hd := mk_digits' (n := n) (c := 0) h0 (litCode_lt a)
        have hp := mk_phase (n := n) (c := 0) h0 (litCode_lt a)
        refine ⟨mk_lt_ruleCap h0 (litCode_lt a) (by norm_num), ?_⟩
        simp only [SlotOK, cA, hd.1, hd.2, hp]
        have := litCode_pos a
        simp; omega
      · obtain ⟨a, _, hc⟩ := List.mem_flatMap.mp h
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
        have hd := mk_digits' (n := n) (c := 1) (litCode_lt b) (litCode_lt a)
        have hp := mk_phase (n := n) (c := 1) (litCode_lt b) (litCode_lt a)
        refine ⟨mk_lt_ruleCap (litCode_lt b) (litCode_lt a) (by norm_num), ?_⟩
        simp only [SlotOK, cB, hd.1, hd.2, hp]
        have hab : a ≠ b := by simpa using (List.mem_filter.mp hb).2
        have h1 := litCode_pos a
        have h2 := litCode_pos b
        refine ⟨by omega, fun _ => ⟨by omega, fun e => hab (litCode_injective e.symm)⟩, by simp⟩
    · obtain ⟨a, _, rfl⟩ := List.mem_map.mp h
      have hd := mk_digits' (n := n) (c := 2) h0 (litCode_lt a)
      have hp := mk_phase (n := n) (c := 2) h0 (litCode_lt a)
      refine ⟨mk_lt_ruleCap h0 (litCode_lt a) (by norm_num), ?_⟩
      simp only [SlotOK, cC, hd.1, hd.2, hp]
      have := litCode_pos a
      simp; omega
  · rintro ⟨hr, h1, h2, h3⟩
    have hph := phase_lt hr
    have ha1 := d1_lt n r
    have hb1 := d0_lt n r
    obtain ⟨a, ha⟩ := exists_lit (n := n) (c := d1 n r - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega)] at ha
    have he := eq_mk_phase n r
    have hpc : phase n r = 0 ∨ phase n r = 1 ∨ phase n r = 2 := by omega
    unfold slots
    rcases hpc with hp | hp | hp
    · refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ?_)))
      refine List.mem_map.mpr ⟨a, mem_literalOrder a, ?_⟩
      rw [he, hp, h3 (by omega), ← ha]
      simp [cA, ha, hp, h3 (by omega : phase n r ≠ 1)]
    · refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr ?_)))
      obtain ⟨hb0, hne⟩ := h2 hp
      obtain ⟨b, hb⟩ := exists_lit (n := n) (c := d0 n r - 1) (by omega)
      rw [Nat.sub_add_cancel (by omega)] at hb
      refine List.mem_flatMap.mpr ⟨a, mem_literalOrder a, List.mem_map.mpr ⟨b, ?_, ?_⟩⟩
      · refine List.mem_filter.mpr ⟨mem_literalOrder b, ?_⟩
        have : a ≠ b := by
          rintro rfl
          exact hne (by omega)
        simpa using this
      · conv_rhs => rw [he, hp, ← hb, ← ha]
        simp [cB, ha, hb]
    · refine List.mem_append.mpr (Or.inr ?_)
      refine List.mem_map.mpr ⟨a, mem_literalOrder a, ?_⟩
      have h3' := h3 (by omega)
      conv_rhs => rw [he, hp, h3', ← ha]
      simp [cC, ha]

theorem slots_eq (n : ℕ) : slots n = (List.range (ruleCap n)).filter (fun r => decide (SlotOK n r)) := by
  apply List.Pairwise.eq_of_mem_iff (r := (· < ·)) (pairwise_slots n)
    (List.pairwise_lt_range.filter _)
  intro r
  rw [mem_slots]
  simp

/-! ### The chosen rule -/

/-- The number `r` is the number of an eligible candidate. -/
def Elig {n : ℕ} (F : ClauseSet (SignedLiteral n)) (L r : ℕ) : Prop :=
  SlotOK n r ∧ sparseEligible F L (ruleOf n r)

instance {n : ℕ} (F : ClauseSet (SignedLiteral n)) (L r : ℕ) : Decidable (Elig F L r) := by
  unfold Elig; infer_instance

/-- The least eligible number below `m`, and `ruleCap n` if there is none. -/
def firstElig {n : ℕ} (F : ClauseSet (SignedLiteral n)) (L m : ℕ) : ℕ :=
  ((List.range m).find? (fun r => decide (Elig F L r))).getD (ruleCap n)

theorem firstElig_succ {n : ℕ} (F : ClauseSet (SignedLiteral n)) (L : ℕ) {m : ℕ} (hm : m < ruleCap n) :
    firstElig F L (m + 1) =
      if ruleCap n ≤ firstElig F L m then (if Elig F L m then m else ruleCap n) else firstElig F L m := by
  unfold firstElig
  rw [List.range_succ, List.find?_append]
  cases h : (List.range m).find? (fun r => decide (Elig F L r)) with
  | none =>
    simp only [Option.none_or, Option.getD_none, le_refl, if_true]
    by_cases he : Elig F L m <;> simp [List.find?_cons, he]
  | some r =>
    have hr : r ∈ List.range m := List.mem_of_find?_eq_some h
    have hr' : r < m := List.mem_range.mp hr
    simp only [Option.some_or, Option.getD_some]
    rw [if_neg (by omega)]

/-- The rule of the chosen number is the rule that `chooseSparseRule` picks. -/
theorem chooseSparseRule_eq {n : ℕ} (F : ClauseSet (SignedLiteral n)) (L : ℕ) :
    chooseSparseRule F L =
      ((List.range (ruleCap n)).find? (fun r => decide (Elig F L r))).map (ruleOf n) := by
  unfold chooseSparseRule
  rw [sparseCandidates_eq, List.find?_map, slots_eq, List.find?_filter]
  congr 2
  funext r
  by_cases h1 : SlotOK n r <;> by_cases h2 : sparseEligible F L (ruleOf n r) <;> simp [Elig, h1, h2]

theorem chooseSparseRule_none {n : ℕ} {F : ClauseSet (SignedLiteral n)} {L : ℕ} :
    chooseSparseRule F L = none ↔ firstElig F L (ruleCap n) = ruleCap n := by
  rw [chooseSparseRule_eq, firstElig]
  cases h : (List.range (ruleCap n)).find? (fun r => decide (Elig F L r)) with
  | none => simp
  | some r =>
    have hr := List.mem_range.mp (List.mem_of_find?_eq_some h)
    simp
    omega

theorem chooseSparseRule_some {n : ℕ} {F : ClauseSet (SignedLiteral n)} {L : ℕ}
    {r : ℕ × Finset (SignedLiteral n)} (h : chooseSparseRule F L = some r) :
    firstElig F L (ruleCap n) < ruleCap n ∧ r = ruleOf n (firstElig F L (ruleCap n)) := by
  rw [chooseSparseRule_eq] at h
  rw [firstElig]
  cases hf : (List.range (ruleCap n)).find? (fun r => decide (Elig F L r)) with
  | none => simp [hf] at h
  | some q =>
    have hr := List.mem_range.mp (List.mem_of_find?_eq_some hf)
    simp only [hf, Option.map_some, Option.some.injEq] at h
    simp [hr, h]

/-! ### Eligibility of a number -/

theorem ruleSet_singleton {n r : ℕ} {a : SignedLiteral n} (h0 : d0 n r = 0) (h1 : d1 n r = litCode a) :
    ruleSet n r = {a} := by
  ext l
  have := litCode_pos l
  rw [mem_ruleSet, h0, h1, mem_singleton]
  constructor
  · rintro (h | h)
    · exact litCode_injective h
    · omega
  · rintro rfl
    exact Or.inl rfl

theorem ruleSet_pair {n r : ℕ} {a b : SignedLiteral n} (h0 : d0 n r = litCode b) (h1 : d1 n r = litCode a) :
    ruleSet n r = {a, b} := by
  ext l
  rw [mem_ruleSet, h0, h1, mem_insert, mem_singleton]
  constructor
  · rintro (h | h)
    · exact Or.inl (litCode_injective h)
    · exact Or.inr (litCode_injective h)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- For a valid number, eligibility is one comparison with a threshold. -/
theorem eligible_iff {n r L : ℕ} (F : ClauseSet (SignedLiteral n)) (hr : r < ruleCap n) (hs : SlotOK n r) :
    sparseEligible F L (ruleOf n r) ↔ thrOf L n r ≤ (coreClauses F (ruleW n r) (ruleSet n r)).card := by
  obtain ⟨h1, h2, h3⟩ := hs
  have hph := phase_lt hr
  have ha1 := d1_lt n r
  have hb1 := d0_lt n r
  obtain ⟨a, ha⟩ := exists_lit (n := n) (c := d1 n r - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega)] at ha
  have hpc : phase n r = 0 ∨ phase n r = 1 ∨ phase n r = 2 := by omega
  simp only [sparseEligible, ruleOf, thrOf, ruleW]
  rcases hpc with hp | hp | hp
  · rw [ruleSet_singleton (h3 (by omega)) ha.symm, hp]
    simp
  · obtain ⟨hb0, hne⟩ := h2 hp
    obtain ⟨b, hb⟩ := exists_lit (n := n) (c := d0 n r - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega)] at hb
    have hab : a ≠ b := by
      rintro rfl
      exact hne (by omega)
    rw [ruleSet_pair hb.symm ha.symm, hp, card_pair hab]
    simp
  · rw [ruleSet_singleton (h3 (by omega)) ha.symm, hp]
    simp [sq]

theorem card_ruleSet_le (n r : ℕ) : (ruleSet n r).card ≤ 2 := by
  have hs : (ruleSet n r).image litCode ⊆ ({d1 n r, d0 n r} : Finset ℕ) := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := mem_image.mp hx
    simpa using mem_ruleSet.mp hl
  have h1 : ((ruleSet n r).image litCode).card = (ruleSet n r).card :=
    card_image_of_injective _ litCode_injective
  have h2 := card_le_card hs
  have h3 : ({d1 n r, d0 n r} : Finset ℕ).card ≤ 2 := card_le_two
  omega

theorem ruleSet_subset_iff {n r k : ℕ} :
    ruleSet n r ⊆ decode n k ↔ ∀ c < 2 * n, (c + 1 = d1 n r ∨ c + 1 = d0 n r) → InC n (c + 1) k := by
  have := forall_lit_iff (n := n) (fun x => (x = d1 n r ∨ x = d0 n r) → InC n x k)
  rw [← this]
  simp only [Finset.subset_iff, mem_ruleSet, mem_decode]

theorem decode_eq_ruleSet_iff {n r k : ℕ} :
    decode n k = ruleSet n r ↔
      ∀ c < 2 * n, (InC n (c + 1) k ↔ (c + 1 = d1 n r ∨ c + 1 = d0 n r)) := by
  have := forall_lit_iff (n := n) (fun x => InC n x k ↔ (x = d1 n r ∨ x = d0 n r))
  rw [← this, Finset.ext_iff]
  simp only [mem_ruleSet, mem_decode]

theorem petal_iff {n r j k : ℕ} :
    decode n j \ ruleSet n r = decode n k ↔
      ∀ c < 2 * n, ((InC n (c + 1) j ∧ ¬ (c + 1 = d1 n r ∨ c + 1 = d0 n r)) ↔ InC n (c + 1) k) := by
  have := forall_lit_iff (n := n) (fun x => (InC n x j ∧ ¬ (x = d1 n r ∨ x = d0 n r)) ↔ InC n x k)
  rw [← this, Finset.ext_iff]
  simp only [mem_sdiff, mem_ruleSet, mem_decode]

/-! ### The clause sets of the two children -/

theorem Wide3.coreLeft {n r : ℕ} {F : ClauseSet (SignedLiteral n)} (hF : Wide3 F) (w : ℕ) :
    Wide3 (SatBase.coreLeft F w (ruleSet n r)) := by
  intro C hC
  rcases mem_insert.mp hC with rfl | h
  · have := card_ruleSet_le n r
    omega
  · exact hF C h

theorem Wide3.coreRight {n : ℕ} {F : ClauseSet (SignedLiteral n)} (hF : Wide3 F) (w : ℕ)
    (S : Finset (SignedLiteral n)) : Wide3 (SatBase.coreRight F w S) := by
  intro C hC
  rcases mem_union.mp hC with h | h
  · exact hF C h
  · obtain ⟨D, hD, rfl⟩ := mem_image.mp h
    exact (card_le_card sdiff_subset).trans (hF D (mem_filter.mp hD).1)

theorem cl_coreLeft {n r w k : ℕ} {F : ClauseSet (SignedLiteral n)} :
    (ValidC n k ∧ (Cl n F k ∨ decode n k = ruleSet n r)) ↔
      Cl n (SatBase.coreLeft F w (ruleSet n r)) k := by
  simp only [Cl, SatBase.coreLeft, mem_insert]
  tauto

theorem cl_coreRight {n w k : ℕ} {S : Finset (SignedLiteral n)} {F : ClauseSet (SignedLiteral n)}
    (hF : Wide3 F) :
    (ValidC n k ∧ (Cl n F k ∨ ∃ j < cap n, Cl n F j ∧
        (decode n j).card = w ∧ S ⊆ decode n j ∧ decode n j \ S = decode n k)) ↔
      Cl n (SatBase.coreRight F w S) k := by
  have e := exists_clause hF (fun D => D.card = w ∧ S ⊆ D ∧ D \ S = decode n k)
  rw [← e]
  simp only [Cl, SatBase.coreRight, corePetals, coreClauses, mem_union, mem_image, mem_filter]
  constructor
  · rintro ⟨hv, h | ⟨D, hD, h1, h2, h3⟩⟩
    · exact ⟨hv, Or.inl h.2⟩
    · exact ⟨hv, Or.inr ⟨D, ⟨hD, h1, h2⟩, h3⟩⟩
  · rintro ⟨hv, h | ⟨D, ⟨hD, h1, h2⟩, h3⟩⟩
    · exact ⟨hv, Or.inl ⟨hv, h⟩⟩
    · exact ⟨hv, Or.inr ⟨D, hD, h1, h2, h3⟩⟩

end TransposeBase.Pseudo.CnfTree
