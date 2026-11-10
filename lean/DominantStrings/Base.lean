import DominantStrings.Step
import TransposeBase.General

/-!
# The network of a formula, as a level

A network of `TransposeBase` has wires `e < m`, nodes `α`, and a function `φ α` of the bits of the wires at `α`. Its sum is
`∑ z, ∏ α, φ α (fun e => z e)`. Each node gets a word `rOf α`. This file writes the sum as `val K w0 F0`.

Each end of a wire reads a bit of a number. `B x y` holds the bits of the wires between the words `x` and `y`, and the
wire `e` is the bit number `rk e` among them. `w0 x x` counts the wires with both ends on `x`: their bits are free,
because the condition `B x x = B x x` is empty.

The node program of `TransposeBase` reads one word `A < 2 ^ (2 * m)`: bit `e` is the bit of the wire `e` at its tail, and
bit `m + e` the bit at its head. `aWord` builds this word from the numbers at one word.
-/

namespace DominantStrings

open Finset TransposeBase.General

/-! ### From equality tests to difference marks

A network with *equality tests* holds one number `B x y` at each end of the bundle of wires between `x` and `y`, and its
value `valEq` tests that the two ends of every wire agree. Complementing the head ends and moving the signs `(-1)` of the
tail ends into the node functions (`flipF`) gives a network with difference marks and the same value (`val_flip`). -/

/-- The value of a level with equality tests. -/
noncomputable def valEq (K : ℕ) (w : ℕ → ℕ → ℕ) (F : ℕ → (ℕ → ℕ) → ℤ) : ℤ :=
  ∑ B ∈ cube K (fun x => cube K (fun y => range (2 ^ w x y))),
    (if ∀ x < K, ∀ y < K, B x y = B y x then 1 else 0) * ∏ x ∈ range K, F x (B x)

/-- The node functions of the difference marks for the node functions `F` of equality tests: the node `x` reads the
complement of its head ends (towards `y < x`), and it has the sign of its tail ends (towards `y > x`). -/
def flipF (K : ℕ) (w : ℕ → ℕ → ℕ) (F : ℕ → (ℕ → ℕ) → ℤ) (x : ℕ) (Bx : ℕ → ℕ) : ℤ :=
  (∏ y ∈ range K, if x < y then sgnP (w x y) (Bx y) else 1) *
    F x (fun y => if y < x then compN (w x y) (Bx y) else Bx y)

/-- **Equality tests and difference marks.** -/
theorem val_flip (K : ℕ) (w : ℕ → ℕ → ℕ) (hsym : ∀ x y, w x y = w y x) (F : ℕ → (ℕ → ℕ) → ℤ) :
    val K w (flipF K w F) = valEq K w F := by
  classical
  set Θ : (ℕ → ℕ → ℕ) → (ℕ → ℕ → ℕ) := fun B x y =>
    if y < x ∧ x < K then compN (w x y) (B x y) else B x y with hΘ
  have hmem : ∀ B ∈ cube K (fun x => cube K (fun y => range (2 ^ w x y))),
      ∀ x < K, ∀ y < K, B x y < 2 ^ w x y := by
    intro B hB x hx y hy
    exact mem_range.1 ((mem_cube.1 ((mem_cube.1 hB).1 x hx)).1 y hy)
  have hmaps : ∀ B ∈ cube K (fun x => cube K (fun y => range (2 ^ w x y))),
      Θ B ∈ cube K (fun x => cube K (fun y => range (2 ^ w x y))) := by
    intro B hB
    have hB1 := (mem_cube.1 hB).1
    have hB2 := (mem_cube.1 hB).2
    rw [mem_cube]
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [mem_cube]
      refine ⟨fun y hy => ?_, fun y hy => ?_⟩
      · by_cases h : y < x
        · simp only [hΘ, h, hx, and_self, if_true, mem_range]
          exact compN_lt _ _
        · simp only [hΘ, h, false_and, if_false]
          exact (mem_cube.1 (hB1 x hx)).1 y hy
      · have : ¬ y < x := by omega
        simp only [hΘ, this, false_and, if_false]
        exact (mem_cube.1 (hB1 x hx)).2 y hy
    · funext y
      have : ¬ (y < x ∧ x < K) := fun h => by omega
      simp only [hΘ, this, if_false, hB2 x hx]
  have hinv : ∀ B ∈ cube K (fun x => cube K (fun y => range (2 ^ w x y))), Θ (Θ B) = B := by
    intro B hB
    funext x y
    by_cases h : y < x ∧ x < K
    · simp only [hΘ, h, and_self, if_true]
      exact compN_compN (hmem B hB x h.2 y (by omega))
    · simp only [hΘ, h, if_false]
  unfold val valEq
  refine sum_nbij' Θ Θ hmaps hmaps hinv hinv fun B hB => ?_
  have hlt := hmem B hB
  -- the node functions
  have hF : ∏ x ∈ range K, flipF K w F x (B x) =
      (∏ x ∈ range K, ∏ y ∈ range K, if x < y then sgnP (w x y) (B x y) else 1) *
        ∏ x ∈ range K, F x (Θ B x) := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun x hx => ?_
    have hx' := mem_range.1 hx
    unfold flipF
    congr 2
    funext y
    by_cases h : y < x
    · simp [hΘ, h, hx']
    · simp [hΘ, h]
  -- the marks and the signs are the test of the flipped numbers
  have hM : marks K w B * ∏ x ∈ range K, ∏ y ∈ range K, (if x < y then sgnP (w x y) (B x y) else 1) =
      if ∀ x < K, ∀ y < K, Θ B x y = Θ B y x then 1 else 0 := by
    unfold marks
    rw [← prod_mul_distrib]
    have h1 : ∀ x ∈ range K, (∏ y ∈ range K, if x < y then mkW (w x y) (B x y) (B y x) else 1) *
        (∏ y ∈ range K, if x < y then sgnP (w x y) (B x y) else 1) =
        ∏ y ∈ range K, if (x < y → B y x = compN (w x y) (B x y)) then (1 : ℤ) else 0 := by
      intro x hx
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun y hy => ?_
      have hx' := mem_range.1 hx
      have hy' := mem_range.1 hy
      by_cases hxy : x < y
      · have hb1 := hlt x hx' y hy'
        have hb2 := hlt y hy' x hx'
        rw [hsym] at hb2
        rw [if_pos hxy, if_pos hxy, mk_eq hb1 hb2]
        by_cases he : B y x = compN (w x y) (B x y)
        · rw [if_pos he, if_pos (fun _ => he), sgnP_mul_self]
        · rw [if_neg he, if_neg (fun h => he (h hxy)), zero_mul]
      · simp [hxy]
    rw [prod_congr rfl h1]
    simp only [prod_test, mem_range]
    refine if_congr ?_ rfl rfl
    constructor
    · intro h x hx y hy
      rcases lt_trichotomy x y with hxy | rfl | hxy
      · have e := h x hx y hy hxy
        have hb := hlt x hx y hy
        simp only [hΘ, not_lt.2 hxy.le, false_and, if_false, hxy, hy, and_self, if_true]
        rw [e, hsym y x, compN_compN hb]
      · rfl
      · have e := h y hy x hx hxy
        have hb := hlt y hy x hx
        simp only [hΘ, not_lt.2 hxy.le, false_and, if_false, hxy, hx, and_self, if_true]
        rw [e, hsym x y, compN_compN hb]
    · intro h x hx y hy hxy
      have e := h x hx y hy
      simp only [hΘ, not_lt.2 hxy.le, false_and, if_false, hxy, hy, and_self, if_true] at e
      rw [e, hsym y x, compN_compN (hsym x y ▸ hlt y hy x hx)]
  rw [hF, ← mul_assoc, hM]

variable {m v : ℕ}

/-- The data of a network with a word for each node. -/
structure BaseNet (m v : ℕ) where
  tail : Fin m → Fin v
  head : Fin m → Fin v
  rOf : Fin v → ℕ
  φ : (α : Fin v) → (Inc tail head α → Bool) → ℤ

namespace BaseNet

variable (N : BaseNet m v)

/-- The word of the tail of a wire. The value is zero outside the range. -/
def tw (e : ℕ) : ℕ := if h : e < m then N.rOf (N.tail ⟨e, h⟩) else 0

/-- The word of the head of a wire. -/
def hw (e : ℕ) : ℕ := if h : e < m then N.rOf (N.head ⟨e, h⟩) else 0

/-- The wire `e` joins the words `x` and `y`. -/
def joins (e x y : ℕ) : Prop := (N.tw e = x ∧ N.hw e = y) ∨ (N.tw e = y ∧ N.hw e = x)

instance (e x y : ℕ) : Decidable (N.joins e x y) := by
  unfold joins
  infer_instance

/-- The weights of the network. -/
def w0 (x y : ℕ) : ℕ := ∑ e ∈ range m, if N.joins e x y then 1 else 0

/-- The number of the wire `e` among the wires between its two words. -/
def rk (e : ℕ) : ℕ := ∑ f ∈ range e, if N.joins f (N.tw e) (N.hw e) then 1 else 0

/-- The word that the node program reads, for the numbers `Bx` at the word `x`. Bits of ends on other words are zero. -/
def aWord (x : ℕ) (Bx : ℕ → ℕ) : ℕ :=
  ∑ e ∈ range m,
    ((if N.tw e = x then ((Bx (N.hw e)).testBit (N.rk e)).toNat * 2 ^ e else 0) +
      (if N.hw e = x then ((Bx (N.tw e)).testBit (N.rk e)).toNat * 2 ^ (m + e) else 0))

/-- The bit `e` of the `X` copy of a word. -/
def asgX (m A : ℕ) : Fin m → Bool := fun e => A.testBit e

/-- The bit `e` of the `Y` copy of a word. -/
def asgY (m A : ℕ) : Fin m → Bool := fun e => A.testBit (m + e)

/-- The word function of the network: the product of the nodes on the word. -/
def F0 (x : ℕ) (Bx : ℕ → ℕ) : ℤ :=
  ∏ α : Fin v, if N.rOf α = x then
    N.φ α (read N.tail N.head α (asgX m (N.aWord x Bx)) (asgY m (N.aWord x Bx))) else 1

/-! ### The bits of a sum of powers of two -/

/-- The bits of a sum of distinct powers of two. -/
theorem testBit_sum_pow (S : Finset ℕ) (r : ℕ → ℕ) (hr : Set.InjOn r (S : Set ℕ)) (a : ℕ → Bool) (i : ℕ) :
    (∑ e ∈ S, (a e).toNat * 2 ^ r e).testBit i = true ↔ ∃ e ∈ S, r e = i ∧ a e = true := by
  have h1 : ∑ e ∈ S, (a e).toNat * 2 ^ r e = ∑ j ∈ (S.filter (fun e => a e = true)).image r, 2 ^ j := by
    rw [sum_image (fun x hx y hy hxy => hr (mem_filter.mp hx).1 (mem_filter.mp hy).1 hxy), sum_filter]
    refine sum_congr rfl fun e _ => ?_
    cases a e <;> simp
  rw [h1, ← Nat.mem_bitIndices, ← List.mem_toFinset, Finset.toFinset_bitIndices_sum_two_pow]
  simp only [mem_image, mem_filter]
  constructor
  · rintro ⟨e, ⟨he, ha⟩, rfl⟩
    exact ⟨e, he, rfl, ha⟩
  · rintro ⟨e, he, rfl, ha⟩
    exact ⟨e, ⟨he, ha⟩, rfl⟩

/-- The number with the bits `a e`, for `e < n`. -/
def bnum (a : ℕ → Bool) (n : ℕ) : ℕ := ∑ e ∈ range n, (a e).toNat * 2 ^ e

theorem testBit_bnum_iff (a : ℕ → Bool) (n i : ℕ) :
    (bnum a n).testBit i = true ↔ i < n ∧ a i = true := by
  have h := testBit_sum_pow (range n) (fun e => e) (fun _ _ _ _ h => h) a i
  rw [bnum, h]
  constructor
  · rintro ⟨e, he, rfl, ha⟩
    exact ⟨mem_range.mp he, ha⟩
  · rintro ⟨hi, ha⟩
    exact ⟨i, mem_range.mpr hi, rfl, ha⟩

theorem testBit_bnum (a : ℕ → Bool) {n i : ℕ} (hi : i < n) : (bnum a n).testBit i = a i := by
  rw [Bool.eq_iff_iff, testBit_bnum_iff]
  exact ⟨fun h => h.2, fun h => ⟨hi, h⟩⟩

theorem bnum_lt (a : ℕ → Bool) (n : ℕ) : bnum a n < 2 ^ n := by
  refine Nat.lt_pow_two_of_testBit _ fun i hi => ?_
  by_contra h
  have := ((testBit_bnum_iff a n i).mp (Bool.eq_true_of_not_eq_false h)).1
  omega

/-! ### The word of the node program -/

/-- The word of the node program holds two numbers of `m` bits: the bits at the heads above the bits at the tails. -/
theorem aWord_eq (x : ℕ) (Bx : ℕ → ℕ) :
    N.aWord x Bx =
      2 ^ m * bnum (fun e => decide (N.hw e = x) && (Bx (N.tw e)).testBit (N.rk e)) m +
        bnum (fun e => decide (N.tw e = x) && (Bx (N.hw e)).testBit (N.rk e)) m := by
  simp only [aWord, bnum, sum_add_distrib, mul_sum]
  rw [add_comm]
  congr 1
  · refine sum_congr rfl fun e _ => ?_
    by_cases h : N.hw e = x
    · simp only [h, if_true, decide_true, Bool.true_and, pow_add]
      ring
    · simp [h]
  · refine sum_congr rfl fun e _ => ?_
    by_cases h : N.tw e = x
    · simp [h]
    · simp [h]

theorem aWord_testBit_low (x : ℕ) (Bx : ℕ → ℕ) {e : ℕ} (he : e < m) :
    (N.aWord x Bx).testBit e = (decide (N.tw e = x) && (Bx (N.hw e)).testBit (N.rk e)) := by
  rw [aWord_eq, Nat.testBit_two_pow_mul_add _ (bnum_lt _ _), if_pos he, testBit_bnum _ he]

theorem aWord_testBit_high (x : ℕ) (Bx : ℕ → ℕ) {e : ℕ} (he : e < m) :
    (N.aWord x Bx).testBit (m + e) = (decide (N.hw e = x) && (Bx (N.tw e)).testBit (N.rk e)) := by
  rw [aWord_eq, Nat.testBit_two_pow_mul_add _ (bnum_lt _ _), if_neg (by omega), Nat.add_sub_cancel_left,
    testBit_bnum _ he]

/-! ### The numbers of the wires -/

theorem tw_val (e : Fin m) : N.tw e = N.rOf (N.tail e) := by
  simp [tw]

theorem hw_val (e : Fin m) : N.hw e = N.rOf (N.head e) := by
  simp [hw]

theorem joins_comm (e x y : ℕ) : N.joins e x y ↔ N.joins e y x := by
  unfold joins
  tauto

/-- If the wire `e` joins `x` and `y`, then the wires that join its two words are the wires that join `x` and `y`. -/
theorem joins_congr {e x y : ℕ} (h : N.joins e x y) (f : ℕ) : N.joins f (N.tw e) (N.hw e) ↔ N.joins f x y := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact N.joins_comm _ _ _

theorem joins_self (e : ℕ) : N.joins e (N.tw e) (N.hw e) := Or.inl ⟨rfl, rfl⟩

/-- The wires that join `x` and `y`. -/
def wires (x y : ℕ) : Finset ℕ := (range m).filter fun e => N.joins e x y

theorem mem_wires {x y e : ℕ} : e ∈ N.wires x y ↔ e < m ∧ N.joins e x y := by
  simp [wires]

theorem wires_comm (x y : ℕ) : N.wires x y = N.wires y x :=
  filter_congr fun e _ => N.joins_comm e x y

theorem w0_eq_card (x y : ℕ) : N.w0 x y = #(N.wires x y) := by
  rw [w0, wires, card_filter]

/-- The number of a wire that joins `x` and `y` counts the earlier wires that join `x` and `y`. -/
theorem rk_eq {e x y : ℕ} (h : N.joins e x y) :
    N.rk e = #((range e).filter fun f => N.joins f x y) := by
  rw [rk, card_filter]
  exact sum_congr rfl fun f _ => if_congr (N.joins_congr h f) rfl rfl

theorem rk_lt_rk {e e' x y : ℕ} (he : N.joins e x y) (he' : N.joins e' x y) (h : e < e') : N.rk e < N.rk e' := by
  rw [N.rk_eq he, N.rk_eq he']
  refine card_lt_card ⟨fun f hf => ?_, fun hsub => ?_⟩
  · rw [mem_filter, mem_range] at hf ⊢
    exact ⟨hf.1.trans h, hf.2⟩
  · have := hsub (mem_filter.mpr ⟨mem_range.mpr h, he⟩)
    rw [mem_filter, mem_range] at this
    exact lt_irrefl _ this.1

theorem rk_injOn (x y : ℕ) : Set.InjOn N.rk (N.wires x y : Set ℕ) := by
  intro e he e' he' h
  have h1 := (N.mem_wires.mp (mem_coe.mp he)).2
  have h2 := (N.mem_wires.mp (mem_coe.mp he')).2
  rcases lt_trichotomy e e' with hlt | heq | hlt
  · exact absurd h (N.rk_lt_rk h1 h2 hlt).ne
  · exact heq
  · exact absurd h.symm (N.rk_lt_rk h2 h1 hlt).ne

theorem rk_lt_w0 {e x y : ℕ} (he : e ∈ N.wires x y) : N.rk e < N.w0 x y := by
  obtain ⟨hem, hj⟩ := N.mem_wires.mp he
  rw [N.rk_eq hj, w0_eq_card]
  refine card_lt_card ⟨fun f hf => ?_, fun hsub => ?_⟩
  · rw [mem_filter, mem_range] at hf
    exact N.mem_wires.mpr ⟨hf.1.trans hem, hf.2⟩
  · have := hsub he
    rw [mem_filter, mem_range] at this
    exact lt_irrefl _ this.1

/-- `rk` sends the wires of a pair onto `range (w0 x y)`. -/
theorem rk_image (x y : ℕ) : (N.wires x y).image N.rk = range (N.w0 x y) := by
  apply eq_of_subset_of_card_le
  · intro r hr
    obtain ⟨e, he, rfl⟩ := mem_image.mp hr
    exact mem_range.mpr (N.rk_lt_w0 he)
  · rw [card_image_of_injOn (N.rk_injOn x y), card_range, w0_eq_card]

/-! ### The bijection between symmetric families and assignments of the wires -/

/-- The bit of the wire `e`. It is `false` outside the range. -/
def zE (z : Fin m → Bool) (e : ℕ) : Bool := if h : e < m then z ⟨e, h⟩ else false

/-- The bits of the wires, for a family of numbers. -/
def zOf (B : ℕ → ℕ → ℕ) : Fin m → Bool := fun e => (B (N.tw e) (N.hw e)).testBit (N.rk e)

/-- The family of numbers, for the bits of the wires. -/
def bOf (K : ℕ) (z : Fin m → Bool) : ℕ → ℕ → ℕ := fun x y =>
  if x < K ∧ y < K then ∑ e ∈ N.wires x y, (zE z e).toNat * 2 ^ N.rk e else 0

theorem bOf_testBit {K x y : ℕ} (hx : x < K) (hy : y < K) (z : Fin m → Bool) (i : ℕ) :
    (N.bOf K z x y).testBit i = true ↔ ∃ e ∈ N.wires x y, N.rk e = i ∧ zE z e = true := by
  rw [bOf, if_pos ⟨hx, hy⟩]
  exact testBit_sum_pow _ _ (N.rk_injOn x y) _ _

theorem bOf_lt (K : ℕ) (z : Fin m → Bool) (x y : ℕ) : N.bOf K z x y < 2 ^ N.w0 x y := by
  by_cases h : x < K ∧ y < K
  · refine Nat.lt_pow_two_of_testBit _ fun i hi => ?_
    by_contra hb
    obtain ⟨e, he, rfl, -⟩ := (N.bOf_testBit h.1 h.2 z i).mp (Bool.eq_true_of_not_eq_false hb)
    have := N.rk_lt_w0 he
    omega
  · rw [bOf, if_neg h]
    exact Nat.two_pow_pos _

theorem bOf_symm (K : ℕ) (z : Fin m → Bool) (x y : ℕ) : N.bOf K z x y = N.bOf K z y x := by
  simp only [bOf, N.wires_comm x y, and_comm]

theorem bOf_mem (K : ℕ) (z : Fin m → Bool) :
    N.bOf K z ∈ cube K (fun x => cube K (fun y => range (2 ^ N.w0 x y))) := by
  rw [mem_cube]
  refine ⟨fun x _ => ?_, fun x hx => ?_⟩
  · rw [mem_cube]
    refine ⟨fun y _ => mem_range.mpr (N.bOf_lt K z x y), fun y hy => ?_⟩
    rw [bOf, if_neg (by omega)]
  · funext y
    rw [bOf, if_neg (by omega)]
    rfl

theorem zOf_bOf {K : ℕ} (hr : ∀ α, N.rOf α < K) (z : Fin m → Bool) : N.zOf (N.bOf K z) = z := by
  funext e
  have hx : N.tw e < K := by rw [tw_val]; exact hr _
  have hy : N.hw e < K := by rw [hw_val]; exact hr _
  have hwe : (e : ℕ) ∈ N.wires (N.tw e) (N.hw e) := N.mem_wires.mpr ⟨e.2, N.joins_self e⟩
  have hze : zE z e = z e := by simp [zE]
  rw [zOf, Bool.eq_iff_iff, N.bOf_testBit hx hy]
  constructor
  · rintro ⟨f, hf, hrk, hzf⟩
    rw [N.rk_injOn _ _ (mem_coe.mpr hf) (mem_coe.mpr hwe) hrk, hze] at hzf
    exact hzf
  · intro h
    exact ⟨e, hwe, rfl, by rw [hze]; exact h⟩

/-- If `B` is symmetric and the wire `e` joins `x` and `y`, then the number at its tail towards its head is `B x y`. -/
theorem B_of_joins {K : ℕ} {B : ℕ → ℕ → ℕ} (hB : ∀ x < K, ∀ y < K, B x y = B y x) {e x y : ℕ} (hx : x < K)
    (hy : y < K) (h : N.joins e x y) : B (N.tw e) (N.hw e) = B x y := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact (hB _ hx _ hy).symm

theorem bOf_zOf {K : ℕ} {B : ℕ → ℕ → ℕ}
    (hc : B ∈ cube K (fun x => cube K (fun y => range (2 ^ N.w0 x y))))
    (hB : ∀ x < K, ∀ y < K, B x y = B y x) : N.bOf K (N.zOf B) = B := by
  rw [mem_cube] at hc
  funext x y
  by_cases hx : x < K
  · have hc' := hc.1 x hx
    rw [mem_cube] at hc'
    by_cases hy : y < K
    · have hlt := mem_range.mp (hc'.1 y hy)
      refine Nat.eq_of_testBit_eq fun i => ?_
      rw [Bool.eq_iff_iff, N.bOf_testBit hx hy]
      constructor
      · rintro ⟨e, he, rfl, hze⟩
        obtain ⟨hem, hj⟩ := N.mem_wires.mp he
        have hz : zE (N.zOf B) e = (B (N.tw e) (N.hw e)).testBit (N.rk e) := by simp [zE, hem, zOf]
        rw [hz, N.B_of_joins hB hx hy hj] at hze
        exact hze
      · intro hbit
        have hi : i < N.w0 x y := by
          by_contra hi
          have h2 : B x y < 2 ^ i := hlt.trans_le (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hi))
          rw [Nat.testBit_lt_two_pow h2] at hbit
          exact absurd hbit (by simp)
        have hmem : i ∈ (N.wires x y).image N.rk := by
          rw [N.rk_image]
          exact mem_range.mpr hi
        obtain ⟨e, he, rfl⟩ := mem_image.mp hmem
        obtain ⟨hem, hj⟩ := N.mem_wires.mp he
        refine ⟨e, he, rfl, ?_⟩
        have hz : zE (N.zOf B) e = (B (N.tw e) (N.hw e)).testBit (N.rk e) := by simp [zE, hem, zOf]
        rw [hz, N.B_of_joins hB hx hy hj]
        exact hbit
    · rw [bOf, if_neg (by omega), hc'.2 y (by omega)]
  · rw [bOf, if_neg (by omega), hc.2 x (by omega)]
    rfl

/-- The node program reads the bit of each wire, for a symmetric family. -/
theorem read_aWord {K : ℕ} (hr : ∀ α, N.rOf α < K) {B : ℕ → ℕ → ℕ} (hs : ∀ x < K, ∀ y < K, B x y = B y x)
    (α : Fin v) :
    read N.tail N.head α (asgX m (N.aWord (N.rOf α) (B (N.rOf α)))) (asgY m (N.aWord (N.rOf α) (B (N.rOf α)))) =
      fun e => N.zOf B e.1 := by
  funext ⟨e, he⟩
  simp only [TransposeBase.General.read]
  by_cases ht : N.tail e = α
  · rw [if_pos ht]
    simp only [asgX, zOf]
    rw [N.aWord_testBit_low _ _ e.2]
    have h1 : N.tw e = N.rOf α := by rw [tw_val, ht]
    rw [h1]
    simp
  · rw [if_neg ht]
    have hh : N.head e = α := he.resolve_left ht
    simp only [asgY, zOf]
    rw [N.aWord_testBit_high _ _ e.2]
    have h1 : N.hw e = N.rOf α := by rw [hw_val, hh]
    have h2 : N.tw e < K := by rw [tw_val]; exact hr _
    rw [h1, hs (N.tw e) h2 _ (hr α)]
    simp

/-- The product of the word functions is the product of the nodes. -/
theorem prod_F0 {K : ℕ} (hr : ∀ α, N.rOf α < K) {B : ℕ → ℕ → ℕ} (hs : ∀ x < K, ∀ y < K, B x y = B y x) :
    ∏ x ∈ range K, N.F0 x (B x) = ∏ α, N.φ α (fun e => N.zOf B e.1) := by
  simp only [F0]
  rw [prod_comm]
  refine prod_congr rfl fun α _ => ?_
  rw [prod_ite_eq, if_pos (mem_range.mpr (hr α)), N.read_aWord hr hs α]

theorem w0_symm (x y : ℕ) : N.w0 x y = N.w0 y x := by
  rw [w0_eq_card, w0_eq_card, wires_comm]

theorem aWord_lt (x : ℕ) (Bx : ℕ → ℕ) : N.aWord x Bx < 2 ^ (2 * m) := by
  rw [aWord_eq, two_mul, pow_add]
  have h1 := bnum_lt (fun e => decide (N.hw e = x) && (Bx (N.tw e)).testBit (N.rk e)) m
  have h2 := bnum_lt (fun e => decide (N.tw e = x) && (Bx (N.hw e)).testBit (N.rk e)) m
  nlinarith

/-- The sum of the network is the value of the level with equality tests, when all words are below `K`. -/
theorem valEq_base {K : ℕ} (hr : ∀ α, N.rOf α < K) :
    valEq K N.w0 N.F0 = ∑ z : Fin m → Bool, ∏ α, N.φ α (fun e => z e.1) := by
  unfold valEq
  simp only [ite_mul, one_mul, zero_mul]
  rw [← sum_filter]
  refine sum_nbij' N.zOf (N.bOf K) (fun _ _ => mem_univ _) ?_ ?_ ?_ ?_
  · intro z _
    exact mem_filter.mpr ⟨N.bOf_mem K z, fun x _ y _ => N.bOf_symm K z x y⟩
  · intro B hB
    obtain ⟨hc, hs⟩ := mem_filter.mp hB
    exact N.bOf_zOf hc hs
  · intro z _
    exact N.zOf_bOf hr z
  · intro B hB
    obtain ⟨-, hs⟩ := mem_filter.mp hB
    exact N.prod_F0 hr hs

/-- **The base.** The sum of the network is the value of the level with difference marks, for the node functions
`flipF K N.w0 N.F0`. -/
theorem val_base {K : ℕ} (hr : ∀ α, N.rOf α < K) :
    val K N.w0 (flipF K N.w0 N.F0) = ∑ z : Fin m → Bool, ∏ α, N.φ α (fun e => z e.1) := by
  rw [val_flip K N.w0 N.w0_symm, N.valEq_base hr]

/-- One ordered pair of words is counted at most once. -/
theorem sum_ite_and_le (K a b : ℕ) :
    ∑ x ∈ range K, ∑ y ∈ range K, (if a = x ∧ b = y then 1 else 0) ≤ 1 := by
  have h : ∀ x, ∑ y ∈ range K, (if a = x ∧ b = y then 1 else 0) =
      if a = x then (if b ∈ range K then 1 else 0) else 0 := by
    intro x
    by_cases hx : a = x
    · simp [hx]
    · simp [hx]
  simp only [h]
  rw [sum_ite_eq]
  split_ifs <;> simp

set_option linter.unusedVariables false in
/-- The sum of the weights. -/
theorem w0_total {K : ℕ} (hr : ∀ α, N.rOf α < K) :
    ∑ x ∈ range K, ∑ y ∈ range K, N.w0 x y ≤ 2 * m := by
  simp only [w0]
  calc ∑ x ∈ range K, ∑ y ∈ range K, ∑ e ∈ range m, (if N.joins e x y then 1 else 0)
      = ∑ x ∈ range K, ∑ e ∈ range m, ∑ y ∈ range K, (if N.joins e x y then 1 else 0) :=
        sum_congr rfl fun x _ => sum_comm
    _ = ∑ e ∈ range m, ∑ x ∈ range K, ∑ y ∈ range K, (if N.joins e x y then 1 else 0) := sum_comm
    _ ≤ ∑ _e ∈ range m, 2 := by
        refine sum_le_sum fun e _ => ?_
        have h1 := sum_ite_and_le K (N.tw e) (N.hw e)
        have h2 := sum_ite_and_le K (N.hw e) (N.tw e)
        calc ∑ x ∈ range K, ∑ y ∈ range K, (if N.joins e x y then 1 else 0)
            ≤ ∑ x ∈ range K, ∑ y ∈ range K,
                ((if N.tw e = x ∧ N.hw e = y then 1 else 0) + (if N.hw e = x ∧ N.tw e = y then 1 else 0)) := by
              refine sum_le_sum fun x _ => sum_le_sum fun y _ => ?_
              by_cases hj : N.joins e x y
              · rw [if_pos hj]
                rcases hj with h | h
                · rw [if_pos h]
                  omega
                · rw [if_pos (show N.hw e = x ∧ N.tw e = y from ⟨h.2, h.1⟩)]
                  omega
              · rw [if_neg hj]
                omega
          _ ≤ 2 := by
              simp only [sum_add_distrib]
              omega
    _ = 2 * m := by simp [mul_comm]

end BaseNet

end DominantStrings
