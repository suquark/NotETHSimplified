import TransposeBase.Defs
import TransposeBase.Arith
import TransposeBase.General
import OnePigeonhole.Helpers
import TransposeBase.Pseudo.Code
import TransposeBase.Pseudo.Lag
import TransposeBase.Pseudo.LeafRun

/-! Facts on words, bit fields, literal tables and loop costs used by the program of this library. -/

section

set_option linter.unusedSectionVars false

namespace OnePigeonhole.Pseudo

open Finset TransposeBase MvPolynomial General TransposeBase.Pseudo.Code
open TransposeBase.Pseudo

variable {Q : ℕ}

variable {A : Type*} [Fintype A] [LinearOrder A]

/-- The value of a polynomial with small exponents is a sum over a box. -/
theorem eval_eq_box {b : ℕ} (p : P (Fin Q)) (hp : ∀ m ∈ p.support, ∀ i, m i ≤ b) (pt : Fin Q → ℚ) :
    eval pt p = ∑ e : Fin Q → Fin (b + 1), coeff (expOf e) p * ∏ i, pt i ^ (e i : ℕ) := by
  classical
  rw [eval_eq']
  have hsub : p.support ⊆ (univ : Finset (Fin Q → Fin (b + 1))).image expOf := by
    intro m hm
    refine Finset.mem_image.mpr ⟨fun i => ⟨m i, Nat.lt_succ_of_le (hp m hm i)⟩, Finset.mem_univ _, ?_⟩
    ext i
    rfl
  rw [Finset.sum_subset hsub (fun m _ hm => by rw [notMem_support_iff.mp hm, zero_mul])]
  rw [Finset.sum_image (fun a _ c _ h => expOf_inj h)]
  rfl

/-- The set of digits with the mask `x`. -/
def setE (Q x : ℕ) : Pos Q := setOfMask (Equiv.refl (Fin Q)) x

theorem mem_setE {x : ℕ} {i : Fin Q} : i ∈ setE Q x ↔ x.testBit i = true := by
  simp [setE]

theorem setE_mask (E : Pos Q) : setE Q (Enum.mask E) = E := by
  ext i
  rw [mem_setE, Enum.testBit_mask]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨i.2, h⟩⟩

/-- A position as a number below `2 ^ Q`. -/
def posCode : Pos Q ↪ Fin (2 ^ Q) :=
  ⟨fun a => ⟨Enum.mask a, Enum.mask_lt a⟩, fun a b h => by
    have := congrArg Fin.val h
    simp only at this
    rw [← setE_mask a, ← setE_mask b, this]⟩

/-- The word of a set of positions. -/
def patWord (P' : Finset (Pos Q)) : ℕ := Enum.mask (P'.map posCode)

theorem patWord_lt (P' : Finset (Pos Q)) : patWord P' < 2 ^ 2 ^ Q := Enum.mask_lt _

/-- The set of positions of a word. -/
def posSet (w : ℕ) : Finset (Pos Q) := univ.filter fun a => w.testBit (Enum.mask a) = true

theorem testBit_patWord (P' : Finset (Pos Q)) (a : Pos Q) :
    (patWord P').testBit (Enum.mask a) = true ↔ a ∈ P' := by
  unfold patWord
  rw [Enum.testBit_mask]
  constructor
  · rintro ⟨h, hmem⟩
    obtain ⟨b, hb, hbe⟩ := Finset.mem_map.mp hmem
    have : posCode b = posCode a := by
      rw [hbe]
      rfl
    rwa [← posCode.injective this]
  · intro h
    exact ⟨Enum.mask_lt a, Finset.mem_map.mpr ⟨a, h, rfl⟩⟩

theorem posSet_patWord (P' : Finset (Pos Q)) : posSet (patWord P') = P' := by
  ext a
  simp [posSet, testBit_patWord]

/-- The value of a bit at a position. -/
def bitVal (w : ℕ) (a : Pos Q) : ℚ := if w.testBit (Enum.mask a) = true then 1 else 0

/-- The number of exponent vectors of a side. -/
abbrev Box (Q : ℕ) := Fin Q → Fin (2 ^ Q + 1)

end OnePigeonhole.Pseudo

end

section

set_option linter.unusedSectionVars false

namespace OnePigeonhole.Pseudo.Leaf

open Finset TransposeBase General TransposeBase.Pseudo TransposeBase.Pseudo.Code
 TransposeBase.Pseudo.Leaf

/-- The field `I` of width `fw` of the word `X`. -/
def fld (fw X I : ℕ) : ℕ := X / 2 ^ (I * fw) % 2 ^ fw

/-- Mixed radix: the number `x` followed by the digit `y` below `n`. -/
def pk (n x y : ℕ) : ℕ := x * n + y

theorem pk_lt {n x y X : ℕ} (hx : x < X) (hy : y < n) : pk n x y < X * n := by
  have h : (x + 1) * n ≤ X * n := Nat.mul_le_mul_right _ hx
  rw [add_mul, one_mul] at h
  unfold pk
  omega

theorem pk_inj {n x y x' y' : ℕ} (hy : y < n) (hy' : y' < n) (h : pk n x y = pk n x' y') :
    x = x' ∧ y = y' := by
  have hn : 0 < n := by omega
  have h1 : pk n x y / n = x := by
    unfold pk
    rw [add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hy, zero_add]
  have h2 : pk n x y % n = y := by
    unfold pk
    rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy]
  have h1' : pk n x' y' / n = x' := by
    unfold pk
    rw [add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hy', zero_add]
  have h2' : pk n x' y' % n = y' := by
    unfold pk
    rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy']
  exact ⟨by rw [← h1, h, h1'], by rw [← h2, h, h2']⟩

/-- The number of exponent vectors. -/
abbrev boxN (Q : ℕ) : ℕ := (2 ^ Q + 1) ^ Q

/-- The exponent of the loop bound of the masks. -/
def clOf (L : ℕ) : ℕ := 3 * Nat.clog 2 (3 * L)

/-- The `x` copy of an assignment word. -/
def asgX (m A : ℕ) : Fin m → Bool := fun e => A.testBit e

/-- The `y` copy of an assignment word. -/
def asgY (m A : ℕ) : Fin m → Bool := fun e => A.testBit (m + e)

/-- A function on `range n` with small values is a packed word. -/
theorem exists_packed (f n : ℕ) (val : ℕ → ℕ) :
    ∃ T : ℕ, T < 2 ^ (f * n) ∧ ∀ i < n, val i < 2 ^ f → fld f T i = val i := by
  have h2 : 0 < 2 ^ f := by positivity
  let u : Fin n → Fin (2 ^ f) := fun i => ⟨val i % 2 ^ f, Nat.mod_lt _ h2⟩
  refine ⟨wordIdx u, ?_, fun i hi hv => ?_⟩
  · have := wordIdx_lt u
    rwa [← pow_mul] at this
  · have h3 := congrFun (wordOf_wordIdx h2 u) ⟨i, hi⟩
    have h4 := congrArg Fin.val h3
    simp only [wordOf_val, u] at h4
    rw [Nat.mod_eq_of_lt hv] at h4
    unfold fld
    rw [← h4, mul_comm i f, pow_mul]

/-- A function on a type with an injective index is a packed word. -/
theorem exists_packed_inj {ι : Type*} (f n : ℕ) (idx : ι → ℕ) (hinj : Function.Injective idx)
    (hlt : ∀ x, idx x < n) (v : ι → ℕ) :
    ∃ T : ℕ, T < 2 ^ (f * n) ∧ ∀ x, v x < 2 ^ f → fld f T (idx x) = v x := by
  classical
  obtain ⟨T, hT, h⟩ := exists_packed f n (fun i => if h : ∃ x, idx x = i then v h.choose else 0)
  refine ⟨T, hT, fun x hx => ?_⟩
  have hex : ∃ y, idx y = idx x := ⟨x, rfl⟩
  have he : hex.choose = x := hinj hex.choose_spec
  have h1 := h (idx x) (hlt x)
  simp only [dif_pos hex, he] at h1
  exact h1 hx

/-- The value of the bits of a set of positions. -/
def indV {Q : ℕ} (Z : Finset (Pos Q)) : Pos Q → ℚ := fun a => if a ∈ Z then 1 else 0

theorem bitVal_eq_ind {Q : ℕ} (w : ℕ) : (bitVal w : Pos Q → ℚ) = indV (posSet w) := by
  funext a
  simp [bitVal, indV, posSet]

theorem wordIdx_inj {G Q : ℕ} (hG : 0 < G) {u v : Fin Q → Fin G} (h : wordIdx u = wordIdx v) : u = v := by
  rw [← wordOf_wordIdx hG u, ← wordOf_wordIdx hG v, h]

theorem mask_setE {Q x : ℕ} (hx : x < 2 ^ Q) : Enum.mask (setE Q x) = x := by
  obtain ⟨S', rfl⟩ := Enum.exists_mask_eq hx
  congr 1
  ext i
  rw [mem_setE, Enum.testBit_mask]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨i.2, h⟩⟩

/-- A sum over the sets of digits is a sum over masks. -/
theorem sum_setE {Q : ℕ} {M : Type*} [AddCommMonoid M] (f : Finset (Fin Q) → M) :
    ∑ E, f E = ∑ x ∈ range (2 ^ Q), f (setE Q x) := by
  refine Finset.sum_bij (fun E _ => Enum.mask E) (fun E _ => mem_range.mpr (Enum.mask_lt E))
    (fun a _ b _ h => Enum.mask_injective Q h) (fun x hx => ?_) (fun E _ => by rw [setE_mask])
  obtain ⟨S', rfl⟩ := Enum.exists_mask_eq (mem_range.mp hx)
  exact ⟨S', mem_univ _, rfl⟩

theorem geom_lt (n : ℕ) : ∑ i ∈ range n, 2 ^ i < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

/-- A sum of bits at their weights is below the power of two. -/
theorem sum_bit_lt (n : ℕ) (g : ℕ → ℕ) (hg : ∀ i, g i ≤ 1) : ∑ i ∈ range n, g i * 2 ^ i < 2 ^ n := by
  refine lt_of_le_of_lt (Finset.sum_le_sum fun i _ => ?_) (geom_lt n)
  calc g i * 2 ^ i ≤ 1 * 2 ^ i := Nat.mul_le_mul_right _ (hg i)
    _ = 2 ^ i := one_mul _

variable {env : List ℕ}

end OnePigeonhole.Pseudo.Leaf

end

section

set_option linter.unusedSectionVars false

namespace OnePigeonhole.Pseudo

open Finset TransposeBase MvPolynomial General TransposeBase.Pseudo.Code
open TransposeBase.Pseudo

variable {Q : ℕ} {A : Type*} [Fintype A] [LinearOrder A]

/-- The word of a set of positions is a sum over the numbers of the positions. -/
theorem patWord_filter (p : Pos Q → Prop) [DecidablePred p] :
    patWord (univ.filter p) = ∑ c ∈ range (2 ^ Q), (decide (p (setE Q c))).toNat * 2 ^ c := by
  unfold patWord Enum.mask
  rw [Finset.sum_map, Finset.sum_filter, Leaf.sum_setE]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' := mem_range.mp hx
  show (if p (setE Q x) then 2 ^ (Enum.mask (setE Q x)) else 0) = _
  rw [Leaf.mask_setE hx']
  by_cases h : p (setE Q x) <;> simp [h]

end OnePigeonhole.Pseudo

namespace OnePigeonhole.Pseudo.Leaf

open Finset TransposeBase General TransposeBase.Pseudo TransposeBase.Pseudo.Code
 TransposeBase.Pseudo.Leaf

variable {env : List ℕ}

theorem toNat_decide_le (p : Prop) [Decidable p] : (decide p).toNat ≤ 1 := by
  cases decide p <;> simp

/-- The number `x` followed by the digit `y` below `n`. -/
def pkE (n x y : Expr) : Expr := .add (.mul x n) y

variable {W : ℕ}

theorem run_pkE {n x y : Expr} {cn cx cy X Nn Y : ℕ} (hx : Run W x env X cx) (hn : Run W n env Nn cn)
    (hy : Run W y env Y cy) (h : pk Nn X Y < 2 ^ W) :
    Run W (pkE n x y) env (pk Nn X Y) (1 + (1 + cx + cn) + cy) :=
  Run.add (Run.mul hx hn (lt_of_le_of_lt (Nat.le_add_right _ _) h)) hy h

theorem pk_le {n x : ℕ} (y : ℕ) (hn : 0 < n) : x ≤ pk n x y := by
  have : x * 1 ≤ x * n := Nat.mul_le_mul_left _ hn
  unfold pk
  omega

variable {env : List ℕ}

theorem sum_ite_le (k : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ∑ i ∈ range k, (if P i then 1 else 0) ≤ k := by
  calc ∑ i ∈ range k, (if P i then 1 else 0) ≤ ∑ _i ∈ range k, 1 :=
        Finset.sum_le_sum fun i _ => by split_ifs <;> omega
    _ = k := by simp

variable {env : List ℕ}

theorem lowbit_lt {X N : ℕ} (hX0 : 0 < X) (hX : X < 2 ^ N) : Enum.lowbit X < 2 ^ N := by
  rw [Enum.lowbit_eq_sum hX0 hX]
  refine lt_of_le_of_lt (Finset.sum_le_sum fun i _ => ?_) (geom_lt N)
  have h1 : (X.testBit i).toNat ≤ 1 := by cases X.testBit i <;> simp
  have h2 : ∏ j ∈ range i, (1 - (X.testBit j).toNat) ≤ 1 := by
    refine Finset.prod_le_one' fun j _ => by omega
  calc _ ≤ 1 * 1 * 2 ^ i := Nat.mul_le_mul_right _ (Nat.mul_le_mul h1 h2)
    _ = 2 ^ i := by simp

/-- The step of the enumeration, stopped from `2 ^ N` on. -/
def progNext (N J x : ℕ) : ℕ := if 2 ^ N ≤ x then x else Enum.next N J x

theorem loop_step {k c x d : ℕ} (hk : 1 ≤ k) : 1 + c + k * (x + 1) + d ≤ k * (x + (c + d + 2)) := by
  have h : k * (x + (c + d + 2)) = k * (x + 1) + k * (c + d + 1) := by ring
  have h2 : 1 * (c + d + 1) ≤ k * (c + d + 1) := Nat.mul_le_mul_right _ hk
  omega

theorem loop_step' {k c x d Z : ℕ} (hk : 1 ≤ k) (h : x + (c + d + 2) ≤ Z) : 1 + c + k * (x + 1) + d ≤ k * Z :=
  (loop_step hk).trans (Nat.mul_le_mul_left _ h)

/-- `f` is bounded by a monomial in its argument. -/
def PolyB (f : ℕ → ℕ) : Prop := ∃ K d, ∀ T, 1 ≤ T → f T ≤ K * T ^ d

theorem PolyB.const (a : ℕ) : PolyB fun _ => a :=
  ⟨a, 0, fun T _ => by simp⟩

theorem PolyB.id : PolyB fun T => T :=
  ⟨1, 1, fun T _ => by simp⟩

theorem PolyB.add {f g : ℕ → ℕ} (hf : PolyB f) (hg : PolyB g) : PolyB fun T => f T + g T := by
  obtain ⟨K, d, h⟩ := hf
  obtain ⟨K', d', h'⟩ := hg
  refine ⟨K + K', d + d', fun T hT => ?_⟩
  have h1 : T ^ d ≤ T ^ (d + d') := Nat.pow_le_pow_right hT (by omega)
  have h2 : T ^ d' ≤ T ^ (d + d') := Nat.pow_le_pow_right hT (by omega)
  calc f T + g T ≤ K * T ^ (d + d') + K' * T ^ (d + d') :=
        Nat.add_le_add ((h T hT).trans (Nat.mul_le_mul_left _ h1)) ((h' T hT).trans (Nat.mul_le_mul_left _ h2))
    _ = (K + K') * T ^ (d + d') := by ring

theorem PolyB.mul {f g : ℕ → ℕ} (hf : PolyB f) (hg : PolyB g) : PolyB fun T => f T * g T := by
  obtain ⟨K, d, h⟩ := hf
  obtain ⟨K', d', h'⟩ := hg
  refine ⟨K * K', d + d', fun T hT => ?_⟩
  calc f T * g T ≤ (K * T ^ d) * (K' * T ^ d') := Nat.mul_le_mul (h T hT) (h' T hT)
    _ = K * K' * T ^ (d + d') := by ring

macro "poly_step" : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact PolyB.id
    | with_reducible exact PolyB.const _
    | with_reducible apply PolyB.add
    | with_reducible apply PolyB.mul)

end OnePigeonhole.Pseudo.Leaf

end
