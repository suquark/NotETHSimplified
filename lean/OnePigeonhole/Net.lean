import TransposeBase.General
import OnePigeonhole.Theorem

/-!
# The sum over the bits

Equation (5) of `papers/one-pigeonhole/proof.tex`, for a network: the wires are `Fin M`, each wire has a tail and a head among the
nodes `V`, each node `α` has a function `φ α` of the bits of its wires, and each node has a word. The network of a formula has
the variables as tails and the clauses as heads. Equation (1) is then the sum `∑ z, ∏ α, φ α (fun e => z e)`, as
`TransposeBase.Sat.net_count` states. The bits `x`, `y` of the text become two copies of `z`: the copy `x e` is read at the tail
of `e`, and the copy `y e` at its head. So a letter holds the copies `x e` of the wires whose tail has this letter, where the text has the
variables with this letter.

* `OnNodes`: the words of the wires are the words of their tail and their head.
* `glue_eqv`: `∑ z, ∏ α, φ α z = ∑ x, ∑ y, ∏ j, [x_j = y_j] * ∏ α, φ α (x, y)`.
* `letterTerm`: the summand of the letter `g`, a function of the bits of `g`. It is `Φ` times the functions of the nodes on `g`. With
  `psiZ` for `Φ`, it is `Ψ_g` of the text, whose clause factors are among the functions of the nodes.
* `sum_letterProduct`: the sum over all bits of a product over the letters is the product over the letters of the sums over the bits
  of each letter.
* `net_decomp_sumT`: equation (5).
* `net_decomp`, `net_decomp_masks`: equation (5) on the grid, with `blockF` or `blockS` in place of `psiZ`.
* `card_blockBits_mul_le`: the number of bits of a letter.
-/

set_option linter.unusedSectionVars false

namespace OnePigeonhole

open Finset TransposeBase TransposeBase.General MvPolynomial

variable {Q L h M : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- The words of the wires are the words of their tail and their head. -/
structure OnNodes (W : Wires Q L h M) (tail head : Fin M → V) (wd : V → Fin Q → Fin L) : Prop where
  /-- The word of the tail. -/
  tw_eq : ∀ e, W.tw e = wd (tail e)
  /-- The word of the head. -/
  hw_eq : ∀ e, W.hw e = wd (head e)

/-! ### The two copies of the bits -/

theorem eqv_bit (a b : Bool) : eqv (bit a) (bit b) = if b = a then 1 else 0 := by
  cases a <;> cases b <;> simp [bit]

theorem prod_eqv_bit (x y : Fin M → Bool) :
    ∏ j, eqv (bit (x j)) (bit (y j)) = if y = x then 1 else 0 := by
  simp_rw [eqv_bit]
  rw [Finset.prod_ite_zero]
  simp only [mem_univ, true_imp_iff, prod_const_one, funext_iff]

/-- The tests force the two copies of the bits to agree. -/
theorem glue_eqv (tail head : Fin M → V) (φ : (α : V) → (Inc tail head α → Bool) → ℚ) :
    ∑ z : Fin M → Bool, ∏ α, φ α (fun e => z e.1) =
      ∑ x : Fin M → Bool, ∑ y : Fin M → Bool,
        (∏ j, eqv (bit (x j)) (bit (y j))) * ∏ α, φ α (read tail head α x y) := by
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [prod_eqv_bit, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', mem_univ, if_true]
  refine Finset.prod_congr rfl fun α _ => ?_
  congr 1
  funext e
  simp [General.read]

/-! ### The bits of a letter -/

/-- The summand of the letter `g`, for an assignment `v` of the bits of `g`: the function `Φ`, with the bits of the other letters
set to `0`, times the functions of the nodes whose word has the letter `g` at the digit `t`. The values lie in the ring `β`, which is
`ℚ` or the polynomials in `z`. -/
noncomputable def letterTerm {β : Type*} [CommRing β] (tail head : Fin M → V) (wd : V → Fin Q → Fin L)
    (φ : (α : V) → (Inc tail head α → Bool) → β) (t : Fin Q) (g : Fin L)
    (Φ : (Fin M → ℚ) → (Fin M → ℚ) → β) (v : BlockBits wd tail head t g → Bool) : β :=
  Φ (fun i => bit (blockExt wd tail head t g v (Sum.inl i)))
      (fun j => bit (blockExt wd tail head t g v (Sum.inr j))) *
    ∏ α ∈ univ.filter (fun α => wd α t = g),
      φ α (read tail head α (blockExt wd tail head t g v ∘ Sum.inl) (blockExt wd tail head t g v ∘ Sum.inr))

/-- The summand of a letter sees only the bits of this letter. -/
theorem letterTerm_restrict {β : Type*} [CommRing β] {W : Wires Q L h M} {tail head : Fin M → V}
    {wd : V → Fin Q → Fin L} (hW : OnNodes W tail head wd) (φ : (α : V) → (Inc tail head α → Bool) → β)
    {t : Fin Q} {g : Fin L} {Φ : (Fin M → ℚ) → (Fin M → ℚ) → β} (hΦ : ReadsLetter W t g Φ)
    (u : Fin M ⊕ Fin M → Bool) :
    letterTerm tail head wd φ t g Φ (fun i => u i.1) =
      Φ (fun i => bit (u (Sum.inl i))) (fun j => bit (u (Sum.inr j))) *
        ∏ α ∈ univ.filter (fun α => wd α t = g), φ α (read tail head α (u ∘ Sum.inl) (u ∘ Sum.inr)) := by
  have hu : ∀ i, bitBlock wd tail head t i = g → blockExt wd tail head t g (fun i => u i.1) i = u i := by
    intro i hi
    simp [blockExt, hi]
  unfold letterTerm
  congr 1
  · refine hΦ _ _ _ _ (fun i hi => ?_) (fun j hj => ?_)
    · have hb : bitBlock wd tail head t (Sum.inl i) = g := by
        show wd (tail i) t = g
        rw [← hW.tw_eq, hi]
      rw [hu _ hb]
    · have hb : bitBlock wd tail head t (Sum.inr j) = g := by
        show wd (head j) t = g
        rw [← hW.hw_eq, hj]
      rw [hu _ hb]
  · refine Finset.prod_congr rfl fun α hα => ?_
    have hαg : wd α t = g := (Finset.mem_filter.mp hα).2
    congr 1
    funext e
    by_cases hc : tail e.1 = α
    · simp only [General.read, if_pos hc, Function.comp]
      refine hu (Sum.inl e.1) ?_
      show wd (tail e.1) t = g
      rw [hc, hαg]
    · have hc' : head e.1 = α := e.2.resolve_left hc
      simp only [General.read, if_neg hc, Function.comp]
      refine hu (Sum.inr e.1) ?_
      show wd (head e.1) t = g
      rw [hc', hαg]

/-- **Factorization.** Each bit belongs to one letter, each node belongs to one letter, and each `Φ g` reads only the bits of `g`. So
the sum over all bits of the product over the letters is the product over the letters of the sums over the bits of each letter. -/
theorem sum_letterProduct {β : Type*} [CommRing β] {W : Wires Q L h M} {tail head : Fin M → V}
    {wd : V → Fin Q → Fin L} (hW : OnNodes W tail head wd) (φ : (α : V) → (Inc tail head α → Bool) → β)
    {t : Fin Q} {Φ : Fin L → (Fin M → ℚ) → (Fin M → ℚ) → β} (hΦ : ∀ g, ReadsLetter W t g (Φ g)) :
    ∑ x : Fin M → Bool, ∑ y : Fin M → Bool,
        (∏ g, Φ g (fun i => bit (x i)) (fun j => bit (y j))) * ∏ α, φ α (read tail head α x y) =
      ∏ g, ∑ v : BlockBits wd tail head t g → Bool, letterTerm tail head wd φ t g (Φ g) v := by
  rw [sum_bool_pair, ← sum_prod_fibers (bitBlock wd tail head t)
    (fun g v => letterTerm tail head wd φ t g (Φ g) v)]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [letterTerm_restrict hW φ (hΦ _) u]
  rw [Finset.prod_mul_distrib]
  congr 1
  exact (Finset.prod_fiberwise _ (fun α => wd α t) _).symm

/-! ### The formula -/

theorem sum_bits_comm {ι : Type*} (s : Finset ι) (f : (Fin M → Bool) → (Fin M → Bool) → ι → ℚ) :
    ∑ x, ∑ y, ∑ q ∈ s, f x y q = ∑ q ∈ s, ∑ x, ∑ y, f x y q :=
  (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm

/-- The sum `Sum_t` of the product over the letters of the sums over the bits is the sum over all bits of `Sum_t` of the product
of the polynomials of the letters, times the functions of the nodes. -/
theorem sumT_prod_letters {W : Wires Q L h M} {tail head : Fin M → V} {wd : V → Fin Q → Fin L}
    (hW : OnNodes W tail head wd) (κ : ℕ → ℚ) (R J : ℕ) (t : Fin Q) (T S U : Finset (Fin M))
    (φ : (α : V) → (Inc tail head α → Bool) → ℚ) :
    sumT J t (∏ g : Fin L, ∑ v : BlockBits wd tail head t g → Bool,
        letterTerm tail head wd (fun α u => C (φ α u)) t g (psiZ W κ R t T S U g) v) =
      ∑ x : Fin M → Bool, ∑ y : Fin M → Bool,
        sumT J t (∏ g : Fin L, psiZ W κ R t T S U g (fun i => bit (x i)) (fun j => bit (y j))) *
          ∏ α, φ α (read tail head α x y) := by
  rw [← sum_letterProduct hW _ fun g => psiZ_congr W κ R t T S U g, sumT_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [sumT_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← map_prod, mul_comm, sumT_C_mul, mul_comm]

/-- **Equation (5).** The number of the network is a fixed combination, over `|T| ≤ r`, the digits `t`, `|S| < J` and `U ⊆ S`, of
`Sum_t` of a product over the letters of the sums over the bits of each letter. -/
theorem net_decomp_sumT {W : Wires Q L h M} {tail head : Fin M → V} {wd : V → Fin Q → Fin L}
    (hW : OnNodes W tail head wd) {R r J : ℕ} (hr : 2 * rankBound Q L h R ≤ r)
    (hJ : M * R + r * Q < Q * J) (φ : (α : V) → (Inc tail head α → Bool) → ℚ) :
    ∑ z : Fin M → Bool, ∏ α, φ α (fun e => z e.1) =
      ∑ T ∈ fewW M (r + 1), (-1) ^ T.card *
        ∑ t, ∑ S ∈ fewW M J, ((signOf W t S : ℤ) : ℚ) * ∑ U ∈ S.powerset,
          sumT J t (∏ g : Fin L, ∑ v : BlockBits wd tail head t g → Bool,
            letterTerm tail head wd (fun α u => C (φ α u)) t g (psiZ W (kappa Q R) R t T S U g) v) := by
  have hd : ∀ x y : Fin M → Bool, ∏ j, eqv (bit (x j)) (bit (y j)) = _ := fun x y =>
    det_decomp_sumT W hr hJ (fun j => bit (x j)) (fun j => bit (y j))
  rw [glue_eqv tail head φ]
  simp only [hd, sumT_prod_letters hW, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [sum_bits_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [sum_bits_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [sum_bits_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [sum_bits_comm]

/-- **Equation (5), on the grid.** The weights, the signs and the functions `blockF` come before the function `φ` of the nodes. -/
theorem net_decomp {W : Wires Q L h M} {tail head : Fin M → V} {wd : V → Fin Q → Fin L}
    (hW : OnNodes W tail head wd) {R r J : ℕ} (hr : 2 * rankBound Q L h R ≤ r)
    (hJ : M * R + r * Q < Q * J) (φ : (α : V) → (Inc tail head α → Bool) → ℚ) :
    ∑ z : Fin M → Bool, ∏ α, φ α (fun e => z e.1) =
      ∑ T ∈ fewW M (r + 1), ∑ t, ∑ p : Fin Q → Fin (M + 1), ∑ S ∈ fewW M J, ∑ U ∈ S.powerset,
        (-1) ^ T.card * digitWeight (k := ℚ) M J t p * ((signOf W t S : ℤ) : ℚ) *
          ∏ g : Fin L, ∑ v : BlockBits wd tail head t g → Bool,
            letterTerm tail head wd φ t g
              (blockF W (kappa Q R) R t (fun i => gridPt (k := ℚ) M (p i)) T S U g) v := by
  have hd : ∀ x y : Fin M → Bool, ∏ j, eqv (bit (x j)) (bit (y j)) = _ := fun x y =>
    det_decomp W hr hJ (fun j => bit (x j)) (fun j => bit (y j))
  rw [glue_eqv tail head φ]
  simp only [hd, Finset.sum_mul]
  rw [sum_bits_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [sum_bits_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [sum_bits_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [sum_bits_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [sum_bits_comm]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [← sum_letterProduct hW φ fun g => blockF_reads W _ R t _ T S U g, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

/-- **Equation (5), on the grid, with one range of masks.** The signs of the cubes sit in the sides. -/
theorem net_decomp_masks {W : Wires Q L h M} {tail head : Fin M → V} {wd : V → Fin Q → Fin L}
    (hW : OnNodes W tail head wd) {R r J : ℕ} (hr : 2 * rankBound Q L h R ≤ r)
    (hJ : M * R + r * Q < Q * J) (φ : (α : V) → (Inc tail head α → Bool) → ℚ) :
    ∑ z : Fin M → Bool, ∏ α, φ α (fun e => z e.1) =
      ∑ t, ∑ p : Fin Q → Fin (M + 1), ∑ T ∈ fewW M J, ∑ S ∈ fewW M J, ∑ U ∈ fewW M J,
        digitWeight (k := ℚ) M J t p * (if T.card ≤ r ∧ U ⊆ S then (-1) ^ T.card else 0) *
          ∏ g : Fin L, ∑ v : BlockBits wd tail head t g → Bool,
            letterTerm tail head wd φ t g
              (blockS W (kappa Q R) R t (fun i => gridPt (k := ℚ) M (p i)) T S U g) v := by
  have hd : ∀ x y : Fin M → Bool, ∏ j, eqv (bit (x j)) (bit (y j)) = _ := fun x y =>
    det_decomp_masks W hr hJ (fun j => bit (x j)) (fun j => bit (y j))
  rw [glue_eqv tail head φ]
  simp only [hd, Finset.sum_mul]
  rw [sum_bits_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [sum_bits_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [sum_bits_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [sum_bits_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [sum_bits_comm]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [← sum_letterProduct hW φ fun g => blockS_reads W _ R t _ T S U g, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

/-! ### The number of bits of a letter -/

/-- Few triples of two words and a layer have a given letter at a digit of the first word, so few wires do. -/
theorem card_letter_mul_le (a b : Fin M → Fin Q → Fin L) (c : Fin M → Fin h)
    (hinj : Function.Injective fun e => (a e, b e, c e)) (t : Fin Q) (g : Fin L) :
    (univ.filter fun e => a e t = g).card * L ≤ (L ^ Q) ^ 2 * h := by
  classical
  have hsub : (univ.filter fun e => a e t = g).card ≤
      ((univ.filter fun u : Word Q (Fin L) => u t = g) ×ˢ
        (univ : Finset (Word Q (Fin L) × Fin h))).card := by
    refine Finset.card_le_card_of_injOn (fun e => (a e, b e, c e)) (fun e he => ?_)
      (fun e _ e' _ he => hinj he)
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2⟩, Finset.mem_univ _⟩
  have hd : (univ.filter fun u : Word Q (Fin L) => u t = g).card * L = L ^ Q := by
    simpa using card_words_digit (Q := Q) (A := Fin L) t g
  have hc : (univ : Finset (Word Q (Fin L) × Fin h)).card = L ^ Q * h := by
    simp
  rw [Finset.card_product, hc] at hsub
  calc (univ.filter fun e => a e t = g).card * L
      ≤ ((univ.filter fun u : Word Q (Fin L) => u t = g).card * (L ^ Q * h)) * L :=
        Nat.mul_le_mul_right _ hsub
    _ = ((univ.filter fun u : Word Q (Fin L) => u t = g).card * L) * (L ^ Q * h) := by ring
    _ = (L ^ Q) ^ 2 * h := by rw [hd]; ring

/-- **The number of bits of a letter.** The wires are different cells, so at most `K ^ 2 h / L` wires have the letter `g` at the
digit `t` of a given word. A letter has at most twice this number of bits, with `K = L ^ Q`. -/
theorem card_blockBits_mul_le {W : Wires Q L h M} {tail head : Fin M → V} {wd : V → Fin Q → Fin L}
    (hW : OnNodes W tail head wd) (t : Fin Q) (g : Fin L) :
    Fintype.card (BlockBits wd tail head t g) * L ≤ 2 * ((L ^ Q) ^ 2 * h) := by
  classical
  have hcard : Fintype.card (BlockBits wd tail head t g) =
      (univ.filter fun e => W.tw e t = g).card + (univ.filter fun e => W.hw e t = g).card := by
    rw [Fintype.card_congr Equiv.subtypeSum, Fintype.card_sum, Fintype.card_subtype, Fintype.card_subtype]
    simp only [bitBlock, bitVertex, Sum.elim_inl, Sum.elim_inr, hW.tw_eq, hW.hw_eq]
    congr!
  have h1 := card_letter_mul_le W.tw W.hw W.lay W.inj t g
  have h2 := card_letter_mul_le W.hw W.tw W.lay (fun e e' he => by
    have h3 : (W.tw e, W.hw e, W.lay e) = (W.tw e', W.hw e', W.lay e') := by
      have h4 := Prod.ext_iff.mp he
      have h5 := Prod.ext_iff.mp h4.2
      exact Prod.ext h5.1 (Prod.ext h4.1 h5.2)
    exact W.inj h3) t g
  rw [hcard, add_mul, two_mul]
  exact Nat.add_le_add h1 h2

end OnePigeonhole
