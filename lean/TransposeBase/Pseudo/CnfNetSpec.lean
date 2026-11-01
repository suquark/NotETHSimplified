import TransposeBase.Sat
import TransposeBase.Pseudo.CnfRun
import TransposeBase.Pseudo.PlaceCore

/-!
# The network of a bitset formula, on numbers

The network of `Sat`, transported to numbers.

* An occurrence of a literal is the number `o = 3 * k + i`, where `k` is a clause code and `i` is a position
  among its digits. It is valid (`validN`) if `k` is a code of a clause of `F` and the digit `i` of `k` is not
  the padding digit `0`.
* `rk p x`: the rank, the number of `k < x` with `p k`.
* The wires are `n` free wires and then the valid occurrences by rank (`eW`).
* The nodes are `n` variable nodes, the clauses by rank, and `n` end nodes (`eN`).
* `net_count`: the network sum is the number of satisfying assignments.
* `arity_le`, `mN_bounds`, `vN_le`: the sizes.

This file holds only specifications. The programs are in `CnfNet.lean`.
-/

set_option linter.unusedSectionVars false

namespace TransposeBase.Pseudo.CnfNet

open Finset SatBase TransposeBase.General TransposeBase.Sat TransposeBase.Pseudo.CnfTree

/-! ### Ranks -/

/-- The rank: the number of `k < x` with `p k`. -/
noncomputable def rk (p : ℕ → Prop) (x : ℕ) : ℕ := ∑ k ∈ range x, ind (p k)

theorem rk_succ (p : ℕ → Prop) (x : ℕ) : rk p (x + 1) = rk p x + ind (p x) := by
  simp [rk, sum_range_succ]

theorem rk_le (p : ℕ → Prop) (x : ℕ) : rk p x ≤ x := by
  calc rk p x ≤ ∑ _k ∈ range x, 1 := sum_le_sum fun k _ => ind_le_one _
    _ = x := by simp

theorem rk_mono (p : ℕ → Prop) {x y : ℕ} (h : x ≤ y) : rk p x ≤ rk p y := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← add_assoc, rk_succ]
    have := ih (by omega)
    omega

theorem rk_lt {p : ℕ → Prop} {x y : ℕ} (hx : p x) (h : x < y) : rk p x < rk p y := by
  have h1 := rk_mono p (show x + 1 ≤ y from h)
  rw [rk_succ, ind_pos hx] at h1
  omega

theorem rk_inj {p : ℕ → Prop} {x y : ℕ} (hx : p x) (hy : p y) (h : rk p x = rk p y) : x = y := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact absurd h (rk_lt hx hlt).ne
  · exact heq
  · exact absurd h (rk_lt hy hgt).ne'

theorem exists_rk {p : ℕ → Prop} {r N : ℕ} (h : r < rk p N) : ∃ x < N, p x ∧ rk p x = r := by
  induction N with
  | zero => simp [rk] at h
  | succ N ih =>
    rw [rk_succ] at h
    by_cases hr : r < rk p N
    · obtain ⟨x, hx, hp, he⟩ := ih hr
      exact ⟨x, by omega, hp, he⟩
    · have h1 := ind_le_one (p N)
      have hpN : p N := by
        by_contra hn
        rw [ind_neg hn] at h
        omega
      exact ⟨N, by omega, hpN, by rw [ind_pos hpN] at h; omega⟩

/-! ### Digits and occurrences -/

/-- The digit `i` of the clause code `k`. -/
def dg (n k i : ℕ) : ℕ := k / (2 * n + 1) ^ i % (2 * n + 1)

theorem dg_zero (n k : ℕ) : dg n k 0 = d0 n k := by simp [dg, d0]
theorem dg_one (n k : ℕ) : dg n k 1 = d1 n k := by simp [dg, d1]
theorem dg_two (n k : ℕ) : dg n k 2 = d2 n k := by simp [dg, d2, Nat.div_div_eq_div_mul, sq]

theorem dg_lt (n k i : ℕ) : dg n k i < 2 * n + 1 := Nat.mod_lt _ (by omega)

/-- The position of the digit `c` in `k`. -/
def posOf (n k c : ℕ) : ℕ := if c = d0 n k then 0 else if c = d1 n k then 1 else 2

theorem posOf_lt (n k c : ℕ) : posOf n k c < 3 := by
  unfold posOf
  split_ifs <;> omega

theorem dg_posOf {n k c : ℕ} (h : InC n c k) : dg n k (posOf n k c) = c := by
  unfold posOf
  split_ifs with h0 h1
  · rw [dg_zero, h0]
  · rw [dg_one, h1]
  · rw [dg_two]
    rcases h with h | h | h
    · exact absurd h h0
    · exact absurd h h1
    · exact h.symm

theorem posOf_dg {n k i : ℕ} (hv : ValidC n k) (hi : i < 3) (h : dg n k i ≠ 0) :
    posOf n k (dg n k i) = i := by
  obtain ⟨v1, v2⟩ := hv
  unfold posOf
  interval_cases i
  · rw [dg_zero, if_pos rfl]
  · rw [dg_one] at h ⊢
    rw [if_neg (by omega), if_pos rfl]
  · rw [dg_two] at h ⊢
    rw [if_neg (by omega), if_neg (by omega)]

variable {n : ℕ} {F : ClauseSet (SignedLiteral n)}

/-- The number `o = 3 * k + i` is an occurrence: `k` is the code of a clause of `F`, and the digit `i` of `k` is
not the padding digit. -/
def validN (n : ℕ) (F : ClauseSet (SignedLiteral n)) (o : ℕ) : Prop :=
  Cl n F (o / 3) ∧ dg n (o / 3) (o % 3) ≠ 0

/-- The number of an occurrence. -/
def occNum (j : OccW F) : ℕ := 3 * code n j.1.1 + posOf n (code n j.1.1) (litCode j.2.1)

theorem occ_div (j : OccW F) : occNum j / 3 = code n j.1.1 := by
  have := posOf_lt n (code n j.1.1) (litCode j.2.1)
  unfold occNum
  omega

theorem occ_mod (j : OccW F) : occNum j % 3 = posOf n (code n j.1.1) (litCode j.2.1) := by
  have := posOf_lt n (code n j.1.1) (litCode j.2.1)
  unfold occNum
  omega

theorem occ_dg (hF : Wide3 F) (j : OccW F) : dg n (occNum j / 3) (occNum j % 3) = litCode j.2.1 := by
  rw [occ_div, occ_mod]
  apply dg_posOf
  have h := (code_spec (hF _ j.1.2)).2.2
  rw [← mem_decode, h]
  exact j.2.2

theorem cl_code (hF : Wide3 F) {C : Finset (SignedLiteral n)} (hC : C ∈ F) : Cl n F (code n C) := by
  obtain ⟨-, h2, h3⟩ := code_spec (hF C hC)
  exact ⟨h2, by rwa [h3]⟩

theorem valid_occ (hF : Wide3 F) (j : OccW F) : validN n F (occNum j) := by
  refine ⟨?_, ?_⟩
  · rw [occ_div]
    exact cl_code hF j.1.2
  · rw [occ_dg hF]
    exact (litCode_pos _).ne'

theorem occ_lt (hF : Wide3 F) (j : OccW F) : occNum j < 3 * cap n := by
  have h1 := (code_spec (hF _ j.1.2)).1
  have := posOf_lt n (code n j.1.1) (litCode j.2.1)
  unfold occNum
  omega

theorem code_inj (hF : Wide3 F) {C D : Finset (SignedLiteral n)} (hC : C ∈ F) (hD : D ∈ F)
    (h : code n C = code n D) : C = D := by
  rw [← (code_spec (hF C hC)).2.2, ← (code_spec (hF D hD)).2.2, h]

theorem occ_inj (hF : Wide3 F) {j j' : OccW F} (h : occNum j = occNum j') : j = j' := by
  obtain ⟨⟨C, hC⟩, ⟨l, hl⟩⟩ := j
  obtain ⟨⟨D, hD⟩, ⟨l', hl'⟩⟩ := j'
  have h1 : code n C = code n D := by
    have := congrArg (· / 3) h
    simpa only [occ_div] using this
  have hCD : C = D := code_inj hF hC hD h1
  subst hCD
  have h2 := occ_dg hF ⟨⟨C, hC⟩, ⟨l, hl⟩⟩
  have h3 := occ_dg hF ⟨⟨C, hC⟩, ⟨l', hl'⟩⟩
  rw [h] at h2
  have h4 : l = l' := litCode_injective (h2.symm.trans h3)
  subst h4
  rfl

/-- Every valid number below the bound is the number of an occurrence. -/
theorem exists_occ (hF : Wide3 F) {o : ℕ} (ho : validN n F o) (hlt : o < 3 * cap n) :
    ∃ j : OccW F, occNum j = o := by
  obtain ⟨⟨hv, hmem⟩, hd⟩ := ho
  set k := o / 3 with hk
  set i := o % 3 with hi
  have hi3 : i < 3 := Nat.mod_lt _ (by norm_num)
  have hkc : k < cap n := by omega
  have hdec := code_decode hkc hv (card_decode_le n k)
  obtain ⟨l, hl⟩ := exists_lit (n := n) (c := dg n k i - 1) (by have := dg_lt n k i; omega)
  rw [Nat.sub_add_cancel (by omega)] at hl
  have hin : InC n (litCode l) k := by
    rw [hl]
    interval_cases i
    · exact Or.inl (dg_zero n k)
    · exact Or.inr (Or.inl (dg_one n k))
    · exact Or.inr (Or.inr (dg_two n k))
  refine ⟨⟨⟨decode n k, hmem⟩, ⟨l, mem_decode.mpr hin⟩⟩, ?_⟩
  simp only [occNum]
  rw [hdec, hl, posOf_dg hv hi3 hd]
  omega

/-! ### Wires and nodes -/

/-- The number of wires. -/
noncomputable def mN (n : ℕ) (F : ClauseSet (SignedLiteral n)) : ℕ := n + rk (validN n F) (3 * cap n)

/-- The number of clauses. -/
noncomputable def clN (n : ℕ) (F : ClauseSet (SignedLiteral n)) : ℕ := rk (Cl n F) (cap n)

/-- The number of nodes. -/
noncomputable def vN (n : ℕ) (F : ClauseSet (SignedLiteral n)) : ℕ := n + clN n F + n

/-- The number of a wire. -/
noncomputable def wireNum (F : ClauseSet (SignedLiteral n)) : Wire F → ℕ
  | .inl v => v
  | .inr j => n + rk (validN n F) (occNum j)

/-- The number of a node. -/
noncomputable def nodeNum (F : ClauseSet (SignedLiteral n)) : Node F → ℕ
  | .inl v => v
  | .inr (.inl e) => n + rk (Cl n F) (code n e.1)
  | .inr (.inr v) => n + clN n F + v

theorem wireNum_lt (hF : Wide3 F) (w : Wire F) : wireNum F w < mN n F := by
  cases w with
  | inl v => have := v.2; simp only [wireNum, mN]; omega
  | inr j =>
    have := rk_lt (valid_occ hF j) (occ_lt hF j)
    simp only [wireNum, mN]
    omega

theorem wireNum_inj (hF : Wide3 F) : Function.Injective (wireNum F) := by
  intro w w' h
  cases w with
  | inl v =>
    cases w' with
    | inl v' =>
      simp only [wireNum] at h
      rw [Fin.ext h]
    | inr j =>
      have := v.2
      simp only [wireNum] at h
      omega
  | inr j =>
    cases w' with
    | inl v' =>
      have := v'.2
      simp only [wireNum] at h
      omega
    | inr j' =>
      simp only [wireNum] at h
      rw [occ_inj hF (rk_inj (valid_occ hF j) (valid_occ hF j') (by omega))]

theorem wireNum_surj (hF : Wide3 F) {e : ℕ} (he : e < mN n F) : ∃ w, wireNum F w = e := by
  by_cases h : e < n
  · exact ⟨.inl ⟨e, h⟩, rfl⟩
  · obtain ⟨x, hx, hv, hr⟩ := exists_rk (p := validN n F) (r := e - n) (N := 3 * cap n)
      (by simp only [mN] at he; omega)
    obtain ⟨j, rfl⟩ := exists_occ hF hv hx
    refine ⟨.inr j, ?_⟩
    simp only [wireNum, hr]
    omega

/-- The wires, numbered. -/
noncomputable def eW (hF : Wide3 F) : Wire F ≃ Fin (mN n F) :=
  Equiv.ofBijective (fun w => ⟨wireNum F w, wireNum_lt hF w⟩)
    ⟨fun _ _ h => wireNum_inj hF (congrArg Fin.val h), fun e => by
      obtain ⟨w, hw⟩ := wireNum_surj hF e.2
      exact ⟨w, Fin.ext hw⟩⟩

@[simp] theorem eW_val (hF : Wide3 F) (w : Wire F) : (eW hF w : ℕ) = wireNum F w := rfl

theorem nodeNum_lt (hF : Wide3 F) (w : Node F) : nodeNum F w < vN n F := by
  rcases w with v | e | v
  · have := v.2
    simp only [nodeNum, vN]
    omega
  · have := rk_lt (cl_code hF e.2) (code_spec (hF _ e.2)).1
    simp only [nodeNum, vN, clN]
    omega
  · have := v.2
    simp only [nodeNum, vN]
    omega

theorem nodeNum_inj (hF : Wide3 F) : Function.Injective (nodeNum F) := by
  have hcl : ∀ e : LCl F, rk (Cl n F) (code n e.1) < clN n F := fun e =>
    rk_lt (cl_code hF e.2) (code_spec (hF _ e.2)).1
  intro w w' h
  rcases w with v | e | v <;> rcases w' with v' | e' | v' <;> simp only [nodeNum] at h
  · rw [Fin.ext h]
  · have := v.2; omega
  · have := v.2; omega
  · have := v'.2; omega
  · have h1 := rk_inj (cl_code hF e.2) (cl_code hF e'.2) (by omega)
    rw [Subtype.ext (code_inj hF e.2 e'.2 h1)]
  · have := hcl e; omega
  · have := v'.2; omega
  · have := hcl e'; omega
  · rw [Fin.ext (show (v : ℕ) = v' by omega)]

theorem nodeNum_surj (hF : Wide3 F) {a : ℕ} (ha : a < vN n F) : ∃ w, nodeNum F w = a := by
  simp only [vN] at ha
  by_cases h : a < n
  · exact ⟨.inl ⟨a, h⟩, rfl⟩
  by_cases h2 : a < n + clN n F
  · obtain ⟨x, hx, hv, hr⟩ := exists_rk (p := Cl n F) (r := a - n) (N := cap n)
      (by simp only [clN] at h2; omega)
    have hdec := code_decode hx hv.1 (card_decode_le n x)
    refine ⟨.inr (.inl ⟨decode n x, hv.2⟩), ?_⟩
    simp only [nodeNum, hdec, hr]
    omega
  · refine ⟨.inr (.inr ⟨a - n - clN n F, by omega⟩), ?_⟩
    simp only [nodeNum]
    omega

/-- The nodes, numbered. -/
noncomputable def eN (hF : Wide3 F) : Node F ≃ Fin (vN n F) :=
  Equiv.ofBijective (fun w => ⟨nodeNum F w, nodeNum_lt hF w⟩)
    ⟨fun _ _ h => nodeNum_inj hF (congrArg Fin.val h), fun e => by
      obtain ⟨w, hw⟩ := nodeNum_surj hF e.2
      exact ⟨w, Fin.ext hw⟩⟩

@[simp] theorem eN_val (hF : Wide3 F) (w : Node F) : (eN hF w : ℕ) = nodeNum F w := rfl

/-- The node at the tail of a wire. -/
noncomputable def tailN (hF : Wide3 F) (e : Fin (mN n F)) : Fin (vN n F) := eN hF (tl F ((eW hF).symm e))

/-- The node at the head of a wire. -/
noncomputable def headN (hF : Wide3 F) (e : Fin (mN n F)) : Fin (vN n F) := eN hF (hd F ((eW hF).symm e))

@[simp] theorem tailN_eW (hF : Wide3 F) (w : Wire F) : tailN hF (eW hF w) = eN hF (tl F w) := by
  simp [tailN]

@[simp] theorem headN_eW (hF : Wide3 F) (w : Wire F) : headN hF (eW hF w) = eN hF (hd F w) := by
  simp [headN]

theorem tailN_ne_headN (hF : Wide3 F) (e : Fin (mN n F)) : tailN hF e ≠ headN hF e := fun h =>
  tl_ne_hd F _ ((eN hF).injective h)

/-! ### The node functions and the count -/

theorem inc_transport (hF : Wide3 F) {α : Fin (vN n F)} (w : Inc (tl F) (hd F) ((eN hF).symm α)) :
    tailN hF (eW hF w.1) = α ∨ headN hF (eW hF w.1) = α := by
  rcases w.2 with h | h
  · left
    rw [tailN_eW, h, Equiv.apply_symm_apply]
  · right
    rw [headN_eW, h, Equiv.apply_symm_apply]

/-- The node function on numbers: `Sat.phi` at the node with this number. -/
noncomputable def phiN {k : Type*} [CommRing k] (hF : Wide3 F) (α : Fin (vN n F))
    (g : Inc (tailN hF) (headN hF) α → Bool) : k :=
  phi F ((eN hF).symm α) (fun w => g ⟨eW hF w.1, inc_transport hF w⟩)

open Classical in
/-- **The network sum is the number of satisfying assignments.** -/
theorem net_count {k : Type*} [CommRing k] (hF : Wide3 F) :
    ∑ z : Fin (mN n F) → Bool, ∏ α, (phiN hF α (fun e => z e.1) : k) =
      ((univ.filter fun x : Fin n → Bool => holdsFormula (literalHolds x) F).card : k) := by
  rw [← Sat.net_count (k := k) F, ← Equiv.sum_comp ((eW hF).arrowCongr (Equiv.refl Bool))]
  refine sum_congr rfl fun z _ => ?_
  rw [← Equiv.prod_comp (eN hF).symm]
  refine prod_congr rfl fun α _ => ?_
  unfold phiN
  congr 1
  funext w
  simp

/-! ### Sizes -/

theorem arity_eq (hF : Wide3 F) (α : Fin (vN n F)) :
    Spread.arity (tailN hF) (headN hF) α = Spread.arity (tl F) (hd F) ((eN hF).symm α) := by
  unfold Spread.arity
  refine Finset.card_equiv (eW hF).symm fun e => ?_
  rw [mem_filter, mem_filter]
  simp only [mem_univ, true_and, tailN, headN, Equiv.eq_symm_apply]

/-- The arities are at most `1 + d` when each variable has at most `d` occurrences. -/
theorem arity_le (hF : Wide3 F) {d : ℕ} (hd3 : 3 ≤ d) (hdeg : ∀ v, variableOccurrences F v ≤ d)
    (α : Fin (vN n F)) : Spread.arity (tailN hF) (headN hF) α ≤ 1 + d := by
  rw [arity_eq]
  exact Sat.arity_le F hF hd3 hdeg _

theorem card_wire (hF : Wide3 F) : Fintype.card (Wire F) = mN n F := by
  simpa using Fintype.card_congr (eW hF)

theorem card_node (hF : Wide3 F) : Fintype.card (Node F) = vN n F := by
  simpa using Fintype.card_congr (eN hF)

theorem mN_bounds (hF : Wide3 F) {d : ℕ} (hdeg : ∀ v, variableOccurrences F v ≤ d) :
    n ≤ mN n F ∧ mN n F ≤ (1 + d) * n := by
  rw [← card_wire hF]
  exact card_wire_bounds F hdeg

/-- The clauses without the empty clause inject into the occurrences. -/
theorem clN_le (hF : Wide3 F) : clN n F + n ≤ mN n F + 1 := by
  classical
  have h1 : Fintype.card (Wire F) = n + Fintype.card (OccW F) := by simp
  have h2 : Fintype.card (Node F) = n + (F.card + n) := by simp
  have hv := card_node hF
  have hw := card_wire hF
  have hc : F.card ≤ Fintype.card (OccW F) + 1 := by
    have hs : F.card ≤ (F.erase ∅).card + 1 := by
      by_cases h : ∅ ∈ F
      · rw [card_erase_of_mem h]
        omega
      · rw [erase_eq_of_notMem h]
        omega
    have hne : ∀ C : {C // C ∈ F.erase ∅}, C.1.Nonempty := fun C =>
      nonempty_iff_ne_empty.mpr (mem_erase.mp C.2).1
    have hinj : Function.Injective (fun C : {C // C ∈ F.erase ∅} =>
        (⟨⟨C.1, (mem_erase.mp C.2).2⟩, ⟨(hne C).choose, (hne C).choose_spec⟩⟩ : OccW F)) := by
      intro C C' h
      exact Subtype.ext (congrArg (fun j : OccW F => j.1.1) h)
    have h3 : Fintype.card {C // C ∈ F.erase ∅} ≤ Fintype.card (OccW F) :=
      Fintype.card_le_of_injective _ hinj
    rw [Fintype.card_coe] at h3
    omega
  simp only [vN] at hv
  omega

theorem vN_le (hF : Wide3 F) : vN n F ≤ mN n F + n + 1 := by
  have := clN_le hF
  simp only [vN]
  omega

theorem mN_le (n : ℕ) (F : ClauseSet (SignedLiteral n)) : mN n F ≤ n + 3 * cap n := by
  have := rk_le (validN n F) (3 * cap n)
  simp only [mN]
  omega

theorem clN_le_cap (n : ℕ) (F : ClauseSet (SignedLiteral n)) : clN n F ≤ cap n := rk_le _ _

/-! ### The literal of a code -/

theorem lit_var {n : ℕ} (l : SignedLiteral n) : (litCode l - 1) / 2 = l.1 := by
  obtain ⟨v, b⟩ := l
  cases b <;> simp [litCode] <;> omega

theorem lit_sign {n : ℕ} (l : SignedLiteral n) : (litCode l - 1) % 2 = l.2.toNat := by
  obtain ⟨v, b⟩ := l
  cases b <;> simp [litCode]

/-- The numbers of the ends of the wires. -/
theorem tail_inl (hF : Wide3 F) (u : Fin n) : (tailN hF (eW hF (.inl u)) : ℕ) = u := by
  rw [tailN_eW]
  rfl

theorem head_inl (hF : Wide3 F) (u : Fin n) : (headN hF (eW hF (.inl u)) : ℕ) = n + clN n F + u := by
  rw [headN_eW]
  rfl

theorem tail_inr (hF : Wide3 F) (j : OccW F) : (tailN hF (eW hF (.inr j)) : ℕ) = j.2.1.1 := by
  rw [tailN_eW]
  rfl

theorem head_inr (hF : Wide3 F) (j : OccW F) :
    (headN hF (eW hF (.inr j)) : ℕ) = n + rk (Cl n F) (code n j.1.1) := by
  rw [headN_eW]
  rfl

end TransposeBase.Pseudo.CnfNet
