import DominantStrings.Cube

/-!
# One rectangle: the dominant strings

Four numbers `x`, `y`, `u`, `v` hold `m` bits each: `x`, `y` are the tail ends and `v`, `u` the head ends of `m` pairs of
crossing wires, the wire of position `j` from `x` to `v` and the wire from `y` to `u`. A wire is marked by the difference
of its two ends (`mkW`), so the crossing is `cross m x y u v = mkW m x v * mkW m y u`, the product over the positions of
`X = (v - x) (u - y)`. On bits, `X = V - H` with `V = (u - x) (v - y)` and `H = (x - y) (u - v)`.

Expanding the product gives one term per set `I` of positions, the positions that take `-H`. A *string* has the letter `H`
on `I` and `V` elsewhere. It is `H`-dominant (`adm m I`) if it has more letters `H` than `V`, or as many and the letter
`H` at the last position `m - 1`. `Ppol true` collects the `H`-dominant strings and `Ppol false` the others; the two add
up to the crossing (`Ppol_add`).

Each piece is a sum over strings of letters of products across a cut. The letters `0, 1, 2, 3` are `P`, `Q`, `R` and the
special letter, with the top functions `p q`, `1`, `p + q`, `p - q` and the bottom functions `1`, `r s`, `r + s`, `r - s`.
Across the rows the arguments are `(x, y | u, v)` and the special letter is `H`; across the columns they are
`(x, u | y, v)` and the special letter is `V`. The index `ξ` of a piece has `dLen` bits (`seed_sum`). In the cheap
direction it has `m - 1` bits for the string and one base-`3` number for its letters `P`, `Q`, `R`.
-/

namespace DominantStrings

open Finset

/-! ### The pieces -/

/-- A bit as an integer. -/
def b2z (a : Bool) : ℤ := if a then 1 else 0

/-- `V = (u - x) (v - y)`: the vertical pair. -/
def Vpos (x y u v : Bool) : ℤ := (b2z u - b2z x) * (b2z v - b2z y)

/-- `H = (x - y) (u - v)`: the horizontal pair. -/
def Hpos (x y u v : Bool) : ℤ := (b2z x - b2z y) * (b2z u - b2z v)

/-- The marks of `w` wires with the tail ends `t` and the head ends `h`: the product of the differences of the bits. -/
def mkW (w t h : ℕ) : ℤ := ∏ j ∈ range w, (b2z (h.testBit j) - b2z (t.testBit j))

/-- A set `I` of positions below `m` is *admissible* (`H`-dominant) if it has more than half of the positions, or exactly
half of them together with the last position `m - 1`. -/
def adm (m : ℕ) (I : Finset ℕ) : Prop := m < 2 * I.card ∨ (2 * I.card = m ∧ m - 1 ∈ I)

instance (m : ℕ) (I : Finset ℕ) : Decidable (adm m I) := by
  unfold adm
  infer_instance

/-- The condition on `I`: `pol = true` is the piece with the admissible sets. -/
def condS (pol : Bool) (m : ℕ) (I : Finset ℕ) : Prop := if pol then adm m I else ¬ adm m I

instance (pol : Bool) (m : ℕ) (I : Finset ℕ) : Decidable (condS pol m I) := by
  unfold condS
  cases pol <;> simp only [Bool.false_eq_true, if_true, if_false] <;> infer_instance

/-- A threshold test on a size: `pol = true` asks `t ≤ r`, and `pol = false` asks `r < t`. -/
def condT (pol : Bool) (t r : ℕ) : Prop := if pol then t ≤ r else r < t

instance (pol : Bool) (t r : ℕ) : Decidable (condT pol t r) := by
  unfold condT
  cases pol <;> simp only [Bool.false_eq_true, if_true, if_false] <;> infer_instance

/-- The term of the string with the letters `H` on `I`, for the positions below `m`. -/
def termI (I : Finset ℕ) (m x y u v : ℕ) : ℤ :=
  ∏ j ∈ range m, if j ∈ I then - Hpos (x.testBit j) (y.testBit j) (u.testBit j) (v.testBit j)
    else Vpos (x.testBit j) (y.testBit j) (u.testBit j) (v.testBit j)

/-- One of the two pieces of the crossing: `D_H` for `pol = true`, `D_V` for `pol = false`. -/
def Ppol (pol : Bool) (m x y u v : ℕ) : ℤ :=
  ∑ I ∈ (range m).powerset, if condS pol m I then termI I m x y u v else 0

/-- The crossing of `m` pairs: the marks of the wires from `x` to `v` and from `y` to `u`. -/
def cross (m x y u v : ℕ) : ℤ := mkW m x v * mkW m y u

/-! The sum over the sets `I`, weighted by a function of the size of `I`, in one recursion on the top position. -/

/-- The sum over the sets `I` of positions below `m`, with the weight `f` on the size of `I`, the factor `a j` for the
positions in `I` and the factor `b j` for the other positions. -/
private def PI (f a b : ℕ → ℤ) (m : ℕ) : ℤ :=
  ∑ I ∈ (range m).powerset, f I.card * ∏ j ∈ range m, if j ∈ I then a j else b j

private theorem PI_succ (f a b : ℕ → ℤ) (m : ℕ) :
    PI f a b (m + 1) = b m * PI f a b m + a m * PI (fun r => f (r + 1)) a b m := by
  unfold PI
  rw [Finset.range_add_one, Finset.sum_powerset_insert Finset.notMem_range_self, Finset.mul_sum,
    Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun I hI => ?_
    have hmI : m ∉ I := fun h => Finset.notMem_range_self (Finset.mem_powerset.mp hI h)
    rw [Finset.prod_insert Finset.notMem_range_self]
    simp only [hmI, if_false]
    ring
  · refine Finset.sum_congr rfl fun I hI => ?_
    have hmI : m ∉ I := fun h => Finset.notMem_range_self (Finset.mem_powerset.mp hI h)
    rw [Finset.prod_insert Finset.notMem_range_self, Finset.card_insert_of_notMem hmI]
    have hp : ∏ j ∈ range m, (if j ∈ insert m I then a j else b j) =
        ∏ j ∈ range m, (if j ∈ I then a j else b j) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      have hjm : j ≠ m := (Finset.mem_range.mp hj).ne
      simp [Finset.mem_insert, hjm]
    rw [hp]
    simp only [Finset.mem_insert_self, if_true]
    ring

private theorem PI_one (a b : ℕ → ℤ) (m : ℕ) :
    PI (fun _ => 1) a b m = ∏ j ∈ range m, (a j + b j) := by
  induction m with
  | zero => simp [PI]
  | succ m ih =>
    rw [PI_succ, Finset.prod_range_succ, ih]
    ring

/-- The sum over the sets `I` of positions below `m`, with the weight `g I`. -/
private def PIS (g : Finset ℕ → ℤ) (a b : ℕ → ℤ) (m : ℕ) : ℤ :=
  ∑ I ∈ (range m).powerset, g I * ∏ j ∈ range m, if j ∈ I then a j else b j

private theorem PIS_succ (g : Finset ℕ → ℤ) (a b : ℕ → ℤ) (m : ℕ) :
    PIS g a b (m + 1) = b m * PIS g a b m + a m * PIS (fun I => g (insert m I)) a b m := by
  unfold PIS
  rw [Finset.range_add_one, Finset.sum_powerset_insert Finset.notMem_range_self, Finset.mul_sum,
    Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun I hI => ?_
    have hmI : m ∉ I := fun h => Finset.notMem_range_self (Finset.mem_powerset.mp hI h)
    rw [Finset.prod_insert Finset.notMem_range_self]
    simp only [hmI, if_false]
    ring
  · refine Finset.sum_congr rfl fun I hI => ?_
    have hmI : m ∉ I := fun h => Finset.notMem_range_self (Finset.mem_powerset.mp hI h)
    rw [Finset.prod_insert Finset.notMem_range_self]
    have hp : ∏ j ∈ range m, (if j ∈ insert m I then a j else b j) =
        ∏ j ∈ range m, (if j ∈ I then a j else b j) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      have hjm : j ≠ m := (Finset.mem_range.mp hj).ne
      simp [Finset.mem_insert, hjm]
    rw [hp]
    simp only [Finset.mem_insert_self, if_true]
    ring

/-- A weight that depends only on the size of `I`. -/
private theorem PIS_card (f : ℕ → ℤ) (a b : ℕ → ℤ) (m : ℕ) : PIS (fun I => f I.card) a b m = PI f a b m := rfl

/-- The two thresholds below the top position `k`. -/
def thr0 (k : ℕ) : ℕ := (k + 3) / 2

def thr1 (k : ℕ) : ℕ := k / 2

/-- Below the top position, a set is admissible exactly when its size reaches `thr0`. -/
theorem adm_low {k : ℕ} {I : Finset ℕ} (hI : I ⊆ range k) : adm (k + 1) I ↔ thr0 k ≤ I.card := by
  have hk : k ∉ I := fun h => Finset.notMem_range_self (hI h)
  simp only [adm, thr0, Nat.add_sub_cancel, hk, and_false, or_false]
  omega

/-- With the top position, a set is admissible exactly when the rest reaches `thr1`. -/
theorem adm_top {k : ℕ} {I : Finset ℕ} (hI : I ⊆ range k) : adm (k + 1) (insert k I) ↔ thr1 k ≤ I.card := by
  have hk : k ∉ I := fun h => Finset.notMem_range_self (hI h)
  simp only [adm, thr1, Nat.add_sub_cancel, Finset.card_insert_of_notMem hk, Finset.mem_insert_self, and_true]
  omega

/-- The weight of a piece on `k + 1` positions, split at the top position. -/
private theorem PIS_split (pol : Bool) (a b : ℕ → ℤ) (k : ℕ) :
    PIS (fun I => if condS pol (k + 1) I then 1 else 0) a b (k + 1) =
      b k * PI (fun r => if condT pol (thr0 k) r then 1 else 0) a b k +
        a k * PI (fun r => if condT pol (thr1 k) r then 1 else 0) a b k := by
  rw [PIS_succ, ← PIS_card, ← PIS_card]
  congr 2
  · unfold PIS
    refine Finset.sum_congr rfl fun I hI => ?_
    have h := adm_low (Finset.mem_powerset.mp hI)
    cases pol <;> simp [condS, condT, h]
  · unfold PIS
    refine Finset.sum_congr rfl fun I hI => ?_
    have h := adm_top (Finset.mem_powerset.mp hI)
    cases pol <;> simp [condS, condT, h]

private theorem pos_cross (a b c d : Bool) :
    -Hpos a b c d + Vpos a b c d = (b2z d - b2z a) * (b2z c - b2z b) := by
  revert a b c d
  decide

/-- The two pieces add up to the crossing. -/
theorem Ppol_add (m x y u v : ℕ) : Ppol true m x y u v + Ppol false m x y u v = cross m x y u v := by
  have h1 : Ppol true m x y u v + Ppol false m x y u v =
      PI (fun _ => 1) (fun j => -Hpos (x.testBit j) (y.testBit j) (u.testBit j) (v.testBit j))
        (fun j => Vpos (x.testBit j) (y.testBit j) (u.testBit j) (v.testBit j)) m := by
    unfold Ppol PI termI
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun I _ => ?_
    by_cases h : adm m I
    · simp [condS, h]
    · simp [condS, h]
  rw [h1, PI_one]
  simp only [pos_cross]
  rw [Finset.prod_mul_distrib]
  rfl

/-- The piece, in the coordinates of a direction: `(p, q)` is one side and `(r, s)` the other. -/
def PP (dir pol : Bool) (m p q r s : ℕ) : ℤ :=
  if dir then Ppol pol m p q r s else Ppol pol m p r q s

/-! ### The letters -/

/-- The top functions of the letters `P`, `Q`, `R` and the special letter. -/
def topL : ℕ → Bool → Bool → ℤ
  | 0, a, b => b2z a * b2z b
  | 1, _, _ => 1
  | 2, a, b => b2z a + b2z b
  | _, a, b => b2z a - b2z b

/-- The bottom functions of the letters. -/
def botL : ℕ → Bool → Bool → ℤ
  | 0, _, _ => 1
  | 1, a, b => b2z a * b2z b
  | 2, a, b => b2z a + b2z b
  | _, a, b => b2z a - b2z b

/-- The product of the top functions over the positions, for a string `π` of letters. -/
def fpatT (m : ℕ) (π : ℕ → ℕ) (p q : ℕ) : ℤ :=
  ∏ j ∈ range m, topL (π j) (p.testBit j) (q.testBit j)

/-- The product of the bottom functions over the positions. -/
def fpatB (m : ℕ) (π : ℕ → ℕ) (r s : ℕ) : ℤ :=
  ∏ j ∈ range m, botL (π j) (r.testBit j) (s.testBit j)

/-- The number of letters `l` of `π`. -/
def cnt (m : ℕ) (π : ℕ → ℕ) (l : ℕ) : ℕ := ∑ j ∈ range m, if π j = l then 1 else 0

/-- Twice the weights of the letters across the rows: `aR` on the positions of `I` (from `-H`), `bR` on the others
(from `V`). -/
def aR (c : ℕ) : ℤ := if c = 3 then -2 else 0

def bR (c : ℕ) : ℤ := if c = 0 ∨ c = 1 then 2 else if c = 2 then -1 else 1

/-- Twice the weights of the letters across the columns. -/
def aC (c : ℕ) : ℤ := if c = 0 ∨ c = 1 then -2 else if c = 2 then 1 else -1

def bC (c : ℕ) : ℤ := if c = 3 then 2 else 0

/-- The product of `bR` over the letters other than `3` below `k`. -/
def wR (k : ℕ) (π : ℕ → ℕ) : ℤ := 2 ^ (cnt k π 0 + cnt k π 1) * (-1) ^ cnt k π 2

/-- The product of `aC` over the letters other than `3` below `k`. -/
def wC (k : ℕ) (π : ℕ → ℕ) : ℤ := (-2) ^ (cnt k π 0 + cnt k π 1)

/-- The coefficient across the rows, for the threshold `t` and `n3` special letters. -/
def coefRt (pol : Bool) (t n3 : ℕ) : ℤ :=
  ∑ r ∈ range (n3 + 1), if condT pol t r then (n3.choose r : ℤ) * (-2) ^ r else 0

/-- The coefficient across the columns, for the threshold `t`, `k` positions and `n3` special letters. -/
def coefCt (pol : Bool) (t k n3 : ℕ) : ℤ :=
  ∑ r ∈ range (n3 + 1),
    if condT pol t (k - n3 + r) then (n3.choose r : ℤ) * 2 ^ (n3 - r) * (-1) ^ r else 0

/-- The coefficient of a string of letters, for a direction, times `2 ^ m`. On `k + 1` positions it splits at the last
position `k`. -/
def rectCoef (dir pol : Bool) : ℕ → (ℕ → ℕ) → ℤ
  | 0, _ => if pol then 0 else 1
  | k + 1, π =>
    if dir then
      bR (π k) * wR k π * coefRt pol (thr0 k) (cnt k π 3) +
        aR (π k) * wR k π * coefRt pol (thr1 k) (cnt k π 3)
    else
      bC (π k) * wC k π * coefCt pol (thr0 k) k (cnt k π 3) +
        aC (π k) * wC k π * coefCt pol (thr1 k) k (cnt k π 3)

/-! The expansion of a term of `Ppol` in the letters. -/

private theorem two_pow_termI (a b : ℕ → ℤ) (m x y u v p q r s : ℕ) (I : Finset ℕ)
    (hS : ∀ j, 2 * (-Hpos (x.testBit j) (y.testBit j) (u.testBit j) (v.testBit j)) =
      ∑ c ∈ range 4, a c * (topL c (p.testBit j) (q.testBit j) * botL c (r.testBit j) (s.testBit j)))
    (hU : ∀ j, 2 * Vpos (x.testBit j) (y.testBit j) (u.testBit j) (v.testBit j) =
      ∑ c ∈ range 4, b c * (topL c (p.testBit j) (q.testBit j) * botL c (r.testBit j) (s.testBit j))) :
    2 ^ m * termI I m x y u v =
      ∑ π ∈ cube m (fun _ => range 4),
        (∏ j ∈ range m, if j ∈ I then a (π j) else b (π j)) * (fpatT m π p q * fpatB m π r s) := by
  have h := sum_cube_prod m (fun _ => range 4) (fun j c => (if j ∈ I then a c else b c) *
    (topL c (p.testBit j) (q.testBit j) * botL c (r.testBit j) (s.testBit j)))
  have hL : 2 ^ m * termI I m x y u v =
      ∏ j ∈ range m, ∑ c ∈ range 4, (if j ∈ I then a c else b c) *
        (topL c (p.testBit j) (q.testBit j) * botL c (r.testBit j) (s.testBit j)) := by
    unfold termI
    have h2 : (2 : ℤ) ^ m = ∏ _j ∈ range m, 2 := by simp
    rw [h2, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    by_cases hj : j ∈ I
    · simp only [hj, if_true]
      exact hS j
    · simp only [hj, if_false]
      exact hU j
  rw [hL, ← h]
  refine Finset.sum_congr rfl fun π _ => ?_
  unfold fpatT fpatB
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]

private theorem expand_piece (pol : Bool) (a b : ℕ → ℤ) (m x y u v p q r s : ℕ)
    (hS : ∀ j, 2 * (-Hpos (x.testBit j) (y.testBit j) (u.testBit j) (v.testBit j)) =
      ∑ c ∈ range 4, a c * (topL c (p.testBit j) (q.testBit j) * botL c (r.testBit j) (s.testBit j)))
    (hU : ∀ j, 2 * Vpos (x.testBit j) (y.testBit j) (u.testBit j) (v.testBit j) =
      ∑ c ∈ range 4, b c * (topL c (p.testBit j) (q.testBit j) * botL c (r.testBit j) (s.testBit j))) :
    2 ^ m * Ppol pol m x y u v =
      ∑ π ∈ cube m (fun _ => range 4),
        PIS (fun I => if condS pol m I then 1 else 0) (fun j => a (π j)) (fun j => b (π j)) m *
          fpatT m π p q * fpatB m π r s := by
  unfold Ppol
  rw [Finset.mul_sum]
  have hterm : ∀ I ∈ (range m).powerset,
      2 ^ m * (if condS pol m I then termI I m x y u v else 0) =
        ∑ π ∈ cube m (fun _ => range 4), (if condS pol m I then 1 else 0) *
          ((∏ j ∈ range m, if j ∈ I then a (π j) else b (π j)) * (fpatT m π p q * fpatB m π r s)) := by
    intro I _
    rw [← Finset.mul_sum, ← two_pow_termI a b m x y u v p q r s I hS hU]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  unfold PIS
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun I _ => ?_
  ring

private theorem pos_rows_S (a b c d : Bool) :
    2 * (-Hpos a b c d) = ∑ l ∈ range 4, aR l * (topL l a b * botL l c d) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  revert a b c d
  decide

private theorem pos_rows_U (a b c d : Bool) :
    2 * Vpos a b c d = ∑ l ∈ range 4, bR l * (topL l a b * botL l c d) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  revert a b c d
  decide

private theorem pos_cols_S (a b c d : Bool) :
    2 * (-Hpos a b c d) = ∑ l ∈ range 4, aC l * (topL l a c * botL l b d) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  revert a b c d
  decide

private theorem pos_cols_U (a b c d : Bool) :
    2 * Vpos a b c d = ∑ l ∈ range 4, bC l * (topL l a c * botL l b d) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  revert a b c d
  decide

private theorem cnt_succ (m : ℕ) (π : ℕ → ℕ) (l : ℕ) :
    cnt (m + 1) π l = cnt m π l + if π m = l then 1 else 0 :=
  Finset.sum_range_succ _ _

private theorem cnt_le (m : ℕ) (π : ℕ → ℕ) (l : ℕ) : cnt m π l ≤ m := by
  induction m with
  | zero => simp [cnt]
  | succ m ih =>
    rw [cnt_succ]
    split_ifs <;> omega

/-- Pascal's rule for a sum with binomial weights. -/
private theorem sum_choose_succ (n : ℕ) (h : ℕ → ℤ) :
    ∑ r ∈ range (n + 2), ((n + 1).choose r : ℤ) * h r =
      ∑ r ∈ range (n + 1), (n.choose r : ℤ) * h r +
        ∑ r ∈ range (n + 1), (n.choose r : ℤ) * h (r + 1) := by
  rw [Finset.sum_range_succ' _ (n + 1), Finset.sum_range_succ' (fun r => (n.choose r : ℤ) * h r) n]
  have h1 : ∑ r ∈ range (n + 1), ((n + 1).choose (r + 1) : ℤ) * h (r + 1) =
      ∑ r ∈ range (n + 1), (n.choose r : ℤ) * h (r + 1) +
        ∑ r ∈ range (n + 1), (n.choose (r + 1) : ℤ) * h (r + 1) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Nat.choose_succ_succ]
    push_cast
    ring
  rw [h1, Finset.sum_range_succ (fun r => (n.choose (r + 1) : ℤ) * h (r + 1)) n]
  simp
  ring

private theorem PI_rows (π : ℕ → ℕ) (m : ℕ) (hπ : ∀ j < m, π j < 4) (f : ℕ → ℤ) :
    PI f (fun j => aR (π j)) (fun j => bR (π j)) m =
      wR m π * ∑ r ∈ range (cnt m π 3 + 1), ((cnt m π 3).choose r : ℤ) * ((-2) ^ r * f r) := by
  induction m generalizing f with
  | zero => simp [PI, cnt, wR]
  | succ m ih =>
    have hπ' : ∀ j < m, π j < 4 := fun j hj => hπ j (Nat.lt_succ_of_lt hj)
    have h4 := hπ m (Nat.lt_succ_self m)
    rw [PI_succ, ih hπ', ih hπ']
    rcases (by omega : π m = 0 ∨ π m = 1 ∨ π m = 2 ∨ π m = 3) with hm | hm | hm | hm
    · have e0 : cnt (m + 1) π 0 = cnt m π 0 + 1 := by simp [cnt_succ, hm]
      have e1 : cnt (m + 1) π 1 = cnt m π 1 := by simp [cnt_succ, hm]
      have e2 : cnt (m + 1) π 2 = cnt m π 2 := by simp [cnt_succ, hm]
      have e3 : cnt (m + 1) π 3 = cnt m π 3 := by simp [cnt_succ, hm]
      have ea : aR (π m) = 0 := by simp [aR, hm]
      have eb : bR (π m) = 2 := by simp [bR, hm]
      rw [ea, eb]
      simp only [wR, e0, e1, e2, e3]
      ring
    · have e0 : cnt (m + 1) π 0 = cnt m π 0 := by simp [cnt_succ, hm]
      have e1 : cnt (m + 1) π 1 = cnt m π 1 + 1 := by simp [cnt_succ, hm]
      have e2 : cnt (m + 1) π 2 = cnt m π 2 := by simp [cnt_succ, hm]
      have e3 : cnt (m + 1) π 3 = cnt m π 3 := by simp [cnt_succ, hm]
      have ea : aR (π m) = 0 := by simp [aR, hm]
      have eb : bR (π m) = 2 := by simp [bR, hm]
      rw [ea, eb]
      simp only [wR, e0, e1, e2, e3]
      ring
    · have e0 : cnt (m + 1) π 0 = cnt m π 0 := by simp [cnt_succ, hm]
      have e1 : cnt (m + 1) π 1 = cnt m π 1 := by simp [cnt_succ, hm]
      have e2 : cnt (m + 1) π 2 = cnt m π 2 + 1 := by simp [cnt_succ, hm]
      have e3 : cnt (m + 1) π 3 = cnt m π 3 := by simp [cnt_succ, hm]
      have ea : aR (π m) = 0 := by simp [aR, hm]
      have eb : bR (π m) = -1 := by simp [bR, hm]
      rw [ea, eb]
      simp only [wR, e0, e1, e2, e3]
      ring
    · have e0 : cnt (m + 1) π 0 = cnt m π 0 := by simp [cnt_succ, hm]
      have e1 : cnt (m + 1) π 1 = cnt m π 1 := by simp [cnt_succ, hm]
      have e2 : cnt (m + 1) π 2 = cnt m π 2 := by simp [cnt_succ, hm]
      have e3 : cnt (m + 1) π 3 = cnt m π 3 + 1 := by simp [cnt_succ, hm]
      have ea : aR (π m) = -2 := by simp [aR, hm]
      have eb : bR (π m) = 1 := by simp [bR, hm]
      have hS : ∑ r ∈ range (cnt m π 3 + 1), ((cnt m π 3).choose r : ℤ) * ((-2) ^ (r + 1) * f (r + 1)) =
          -2 * ∑ r ∈ range (cnt m π 3 + 1), ((cnt m π 3).choose r : ℤ) * ((-2) ^ r * f (r + 1)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        ring
      rw [ea, eb, e3, sum_choose_succ, hS]
      simp only [wR, e0, e1, e2]
      ring

private theorem PI_cols (π : ℕ → ℕ) (m : ℕ) (hπ : ∀ j < m, π j < 4) (f : ℕ → ℤ) :
    PI f (fun j => aC (π j)) (fun j => bC (π j)) m =
      wC m π * ∑ r ∈ range (cnt m π 3 + 1),
        ((cnt m π 3).choose r : ℤ) * (2 ^ (cnt m π 3 - r) * (-1) ^ r * f (m - cnt m π 3 + r)) := by
  induction m generalizing f with
  | zero => simp [PI, cnt, wC]
  | succ m ih =>
    have hπ' : ∀ j < m, π j < 4 := fun j hj => hπ j (Nat.lt_succ_of_lt hj)
    have h4 := hπ m (Nat.lt_succ_self m)
    have hn := cnt_le m π 3
    rw [PI_succ, ih hπ', ih hπ']
    have hsum : ∑ r ∈ range (cnt m π 3 + 1),
          ((cnt m π 3).choose r : ℤ) * (2 ^ (cnt m π 3 - r) * (-1) ^ r * f (m + 1 - cnt m π 3 + r)) =
        ∑ r ∈ range (cnt m π 3 + 1),
          ((cnt m π 3).choose r : ℤ) * (2 ^ (cnt m π 3 - r) * (-1) ^ r * f (m - cnt m π 3 + r + 1)) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      have e : m + 1 - cnt m π 3 + r = m - cnt m π 3 + r + 1 := by omega
      rw [e]
    rcases (by omega : π m = 0 ∨ π m = 1 ∨ π m = 2 ∨ π m = 3) with hm | hm | hm | hm
    · have e0 : cnt (m + 1) π 0 = cnt m π 0 + 1 := by simp [cnt_succ, hm]
      have e1 : cnt (m + 1) π 1 = cnt m π 1 := by simp [cnt_succ, hm]
      have e3 : cnt (m + 1) π 3 = cnt m π 3 := by simp [cnt_succ, hm]
      have ea : aC (π m) = -2 := by simp [aC, hm]
      have eb : bC (π m) = 0 := by simp [bC, hm]
      rw [e3, hsum, ea, eb]
      simp only [wC, e0, e1]
      ring
    · have e0 : cnt (m + 1) π 0 = cnt m π 0 := by simp [cnt_succ, hm]
      have e1 : cnt (m + 1) π 1 = cnt m π 1 + 1 := by simp [cnt_succ, hm]
      have e3 : cnt (m + 1) π 3 = cnt m π 3 := by simp [cnt_succ, hm]
      have ea : aC (π m) = -2 := by simp [aC, hm]
      have eb : bC (π m) = 0 := by simp [bC, hm]
      rw [e3, hsum, ea, eb]
      simp only [wC, e0, e1]
      ring
    · have e0 : cnt (m + 1) π 0 = cnt m π 0 := by simp [cnt_succ, hm]
      have e1 : cnt (m + 1) π 1 = cnt m π 1 := by simp [cnt_succ, hm]
      have e3 : cnt (m + 1) π 3 = cnt m π 3 := by simp [cnt_succ, hm]
      have ea : aC (π m) = 1 := by simp [aC, hm]
      have eb : bC (π m) = 0 := by simp [bC, hm]
      rw [e3, hsum, ea, eb]
      simp only [wC, e0, e1]
      ring
    · have e0 : cnt (m + 1) π 0 = cnt m π 0 := by simp [cnt_succ, hm]
      have e1 : cnt (m + 1) π 1 = cnt m π 1 := by simp [cnt_succ, hm]
      have e3 : cnt (m + 1) π 3 = cnt m π 3 + 1 := by simp [cnt_succ, hm]
      have ea : aC (π m) = -1 := by simp [aC, hm]
      have eb : bC (π m) = 2 := by simp [bC, hm]
      have hsum1 : ∑ r ∈ range (cnt m π 3 + 1), ((cnt m π 3).choose r : ℤ) *
            (2 ^ (cnt m π 3 + 1 - r) * (-1) ^ r * f (m + 1 - (cnt m π 3 + 1) + r)) =
          2 * ∑ r ∈ range (cnt m π 3 + 1),
            ((cnt m π 3).choose r : ℤ) * (2 ^ (cnt m π 3 - r) * (-1) ^ r * f (m - cnt m π 3 + r)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r hr => ?_
        have hr' := Finset.mem_range.mp hr
        have e1 : cnt m π 3 + 1 - r = (cnt m π 3 - r) + 1 := by omega
        have e2 : m + 1 - (cnt m π 3 + 1) = m - cnt m π 3 := by omega
        rw [e1, e2, pow_succ]
        ring
      have hsum2 : ∑ r ∈ range (cnt m π 3 + 1), ((cnt m π 3).choose r : ℤ) *
            (2 ^ (cnt m π 3 + 1 - (r + 1)) * (-1) ^ (r + 1) * f (m + 1 - (cnt m π 3 + 1) + (r + 1))) =
          -∑ r ∈ range (cnt m π 3 + 1),
            ((cnt m π 3).choose r : ℤ) * (2 ^ (cnt m π 3 - r) * (-1) ^ r * f (m - cnt m π 3 + r + 1)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun r _ => ?_
        have e1 : cnt m π 3 + 1 - (r + 1) = cnt m π 3 - r := by omega
        have e2 : m + 1 - (cnt m π 3 + 1) + (r + 1) = m - cnt m π 3 + r + 1 := by omega
        rw [e1, e2, pow_succ]
        ring
      rw [e3, sum_choose_succ, hsum1, hsum2, ea, eb]
      simp only [wC, e0, e1]
      ring

/-- Across the rows, the piece is a sum over strings of letters, up to the factor `2 ^ m`. -/
theorem seed_rows (pol : Bool) (m x y u v : ℕ) :
    2 ^ m * Ppol pol m x y u v =
      ∑ π ∈ cube m (fun _ => range 4), rectCoef true pol m π * fpatT m π x y * fpatB m π u v := by
  rw [expand_piece pol aR bR m x y u v x y u v (fun j => pos_rows_S _ _ _ _)
    (fun j => pos_rows_U _ _ _ _)]
  refine Finset.sum_congr rfl fun π hπ => ?_
  have hπ4 : ∀ j < m, π j < 4 := by
    rw [mem_cube] at hπ
    exact fun j hj => Finset.mem_range.mp (hπ.1 j hj)
  congr 2
  cases m with
  | zero =>
    simp only [PIS, Finset.range_zero, Finset.powerset_empty, Finset.sum_singleton, Finset.prod_empty, mul_one]
    cases pol <;> simp [condS, adm, rectCoef]
  | succ k =>
    have hπ' : ∀ j < k, π j < 4 := fun j hj => hπ4 j (by omega)
    rw [PIS_split, PI_rows π k hπ', PI_rows π k hπ']
    simp only [rectCoef, if_true, coefRt, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun r _ => ?_
      split_ifs <;> simp; ring
    · refine Finset.sum_congr rfl fun r _ => ?_
      split_ifs <;> simp; ring

/-- Across the columns, the piece is a sum over strings of letters, up to the factor `2 ^ m`. -/
theorem seed_cols (pol : Bool) (m x y u v : ℕ) :
    2 ^ m * Ppol pol m x y u v =
      ∑ π ∈ cube m (fun _ => range 4), rectCoef false pol m π * fpatT m π x u * fpatB m π y v := by
  rw [expand_piece pol aC bC m x y u v x u y v (fun j => pos_cols_S _ _ _ _)
    (fun j => pos_cols_U _ _ _ _)]
  refine Finset.sum_congr rfl fun π hπ => ?_
  have hπ4 : ∀ j < m, π j < 4 := by
    rw [mem_cube] at hπ
    exact fun j hj => Finset.mem_range.mp (hπ.1 j hj)
  congr 2
  cases m with
  | zero =>
    simp only [PIS, Finset.range_zero, Finset.powerset_empty, Finset.sum_singleton, Finset.prod_empty, mul_one]
    cases pol <;> simp [condS, adm, rectCoef]
  | succ k =>
    have hπ' : ∀ j < k, π j < 4 := fun j hj => hπ4 j (by omega)
    rw [PIS_split, PI_cols π k hπ', PI_cols π k hπ']
    simp only [rectCoef, Bool.false_eq_true, if_false, coefCt, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun r _ => ?_
      split_ifs <;> simp; ring
    · refine Finset.sum_congr rfl fun r _ => ?_
      split_ifs <;> simp; ring

/-! ### The number of bits -/

/-- The width of the index. `cheap` is the direction in which the piece has few strings of letters. There the index has
`m - 1` bits for the string and `⌈8 ⌊m / 2⌋ / 5⌉` bits for its letters, which bound a number below `3 ^ ⌊m / 2⌋`. -/
def dLen (cheap : Bool) (m : ℕ) : ℕ :=
  if cheap then (if m = 0 then 0 else m - 1 + (8 * (m / 2) + 4) / 5) else 2 * m

/-- The number of paired wires of two diagonals: the smaller weight. -/
def pairMin (a b : ℕ) : ℕ := min a b

/-- The number of set bits of `M` below `j`. -/
def popB (M j : ℕ) : ℕ := ∑ i ∈ range j, (M.testBit i).toNat

/-- The letter `j` of the index `ξ`, when all letters have two bits. -/
def letterPlain (ξ j : ℕ) : ℕ := ξ / 4 ^ j % 4

/-- The set bits of `M` below `m` form an admissible set. -/
def admB (m M : ℕ) : Prop := m < 2 * popB M m ∨ (2 * popB M m = m ∧ M.testBit (m - 1) = true)

instance (m M : ℕ) : Decidable (admB m M) := by
  unfold admB
  infer_instance

/-- The mark of the short code. The low `m - 1` bits of `ξ` and the top bit `m - 1` give a set `B`; the mark is `B` if
`B` is admissible, and its complement within `m` bits if not. Exactly one of the two is admissible. -/
def markOf (m ξ : ℕ) : ℕ :=
  if admB m (ξ % 2 ^ (m - 1) + 2 ^ (m - 1)) then ξ % 2 ^ (m - 1) + 2 ^ (m - 1)
  else 2 ^ m - 1 - (ξ % 2 ^ (m - 1) + 2 ^ (m - 1))

/-- The letter `j` of the index `ξ`, in the short code. The mark gives the special letters `3`. The other letters are
the digits of the high part in base `3`. -/
def letterCheap (m ξ j : ℕ) : ℕ :=
  if (markOf m ξ).testBit j then 3
  else ξ / 2 ^ (m - 1) / 3 ^ (j - popB (markOf m ξ) j) % 3

/-- The string of letters of an index. -/
def letterOf (cheap : Bool) (m ξ j : ℕ) : ℕ :=
  if j < m then (if cheap then letterCheap m ξ j else letterPlain ξ j) else 0

/-- An index of the short code is valid if its high part has no extra digit. -/
def validIdx (cheap : Bool) (m ξ : ℕ) : Prop :=
  cheap = true → ξ / 2 ^ (m - 1) < 3 ^ (m - popB (markOf m ξ) m)

instance (cheap : Bool) (m ξ : ℕ) : Decidable (validIdx cheap m ξ) := by
  unfold validIdx
  infer_instance

/-- The positions of the letter `l` of `π` below `m` form an admissible set. -/
def admL (m : ℕ) (π : ℕ → ℕ) (l : ℕ) : Prop := m < 2 * cnt m π l ∨ (2 * cnt m π l = m ∧ π (m - 1) = l)

/-- The function of one side of the rectangle: the side `u` of a pair `u < u'`. It holds the scale and the coefficient. -/
def rectA (dir pol : Bool) (scale m ξ p q : ℕ) : ℤ :=
  if validIdx (pol == dir) m ξ then
    2 ^ (scale - m) * rectCoef dir pol m (letterOf (pol == dir) m ξ) * fpatT m (letterOf (pol == dir) m ξ) p q
  else 0

/-- The function of the other side of the rectangle. -/
def rectB (dir pol : Bool) (m ξ r s : ℕ) : ℤ :=
  if validIdx (pol == dir) m ξ then fpatB m (letterOf (pol == dir) m ξ) r s else 0

/-! The sum over the indices of the short code. -/

private theorem three_pow_le (k : ℕ) : 3 ^ k ≤ 2 ^ ((8 * k + 4) / 5) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k < 5
    · interval_cases k <;> norm_num
    · obtain ⟨t, rfl⟩ : ∃ t, k = t + 5 := ⟨k - 5, by omega⟩
      have h1 := ih t (by omega)
      have h2 : (8 * (t + 5) + 4) / 5 = (8 * t + 4) / 5 + 8 := by omega
      rw [h2, pow_add, pow_add]
      calc 3 ^ t * 3 ^ 5 ≤ 2 ^ ((8 * t + 4) / 5) * 3 ^ 5 := Nat.mul_le_mul_right _ h1
        _ ≤ 2 ^ ((8 * t + 4) / 5) * 2 ^ 8 := Nat.mul_le_mul_left _ (by norm_num)

private theorem popB_succ (M j : ℕ) : popB M (j + 1) = popB M j + (M.testBit j).toNat :=
  Finset.sum_range_succ _ _

private theorem popB_le (M j : ℕ) : popB M j ≤ j := by
  induction j with
  | zero => simp [popB]
  | succ j ih =>
    rw [popB_succ]
    have := Bool.toNat_le (M.testBit j)
    omega

private theorem popB_gap {M j m : ℕ} (hj : j < m) (hb : M.testBit j = false) :
    popB M m + j + 1 ≤ popB M j + m := by
  induction m, Nat.succ_le_of_lt hj using Nat.le_induction with
  | base => simp [popB_succ, hb]
  | succ m hm ih =>
    rw [popB_succ]
    have := Bool.toNat_le (M.testBit m)
    have := ih (Nat.lt_of_succ_le hm)
    omega

private theorem popB_congr {M M' j : ℕ} (h : ∀ i < j, M.testBit i = M'.testBit i) :
    popB M j = popB M' j :=
  Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.mp hi)]

/-- The letters given by the mark `M` and the digits `c`. -/
private def lettersOf (m M c j : ℕ) : ℕ :=
  if j < m then
    if M.testBit j then 3 else c / 3 ^ (j - popB M j) % 3
  else 0

private theorem digit_low {i N : ℕ} (hi : i < N) (c0 d : ℕ) :
    (c0 + 3 ^ N * d) / 3 ^ i % 3 = c0 / 3 ^ i % 3 := by
  obtain ⟨e, rfl⟩ : ∃ e, N = i + 1 + e := ⟨N - (i + 1), by omega⟩
  rw [pow_add, pow_succ, mul_assoc, mul_assoc, Nat.add_mul_div_left _ _ (by positivity),
    Nat.add_mul_mod_self_left]

private theorem letters_zero {m M c0 d : ℕ} (hM : M < 2 ^ m)
    (hc : c0 < 3 ^ (m - popB M m)) (hd : d < 3) :
    lettersOf (m + 1) M (c0 + 3 ^ (m - popB M m) * d) = Function.update (lettersOf m M c0) m d := by
  funext j
  rcases lt_trichotomy j m with h | rfl | h
  · rw [Function.update_of_ne h.ne]
    simp only [lettersOf, h, Nat.lt_succ_of_lt h, if_true]
    by_cases hb : M.testBit j = true
    · simp [hb]
    · have hb' : M.testBit j = false := by simpa using hb
      simp only [hb', Bool.false_eq_true, if_false]
      have h1 := popB_gap h hb'
      have h2 := popB_le M j
      have h3 := popB_le M m
      rw [digit_low (by omega)]
  · have hb : M.testBit j = false := Nat.testBit_lt_two_pow hM
    simp only [lettersOf, Nat.lt_succ_self, if_true, Function.update_self, hb, Bool.false_eq_true,
      if_false]
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hc, Nat.zero_add,
      Nat.mod_eq_of_lt hd]
  · rw [Function.update_of_ne h.ne']
    simp [lettersOf, Nat.not_lt.mpr h.le, Nat.not_lt.mpr (Nat.succ_le_of_lt h)]

private theorem letters_one {m M : ℕ} (hM : M < 2 ^ m) (c : ℕ) :
    popB (M + 2 ^ m * 1) (m + 1) = popB M m + 1 ∧
    lettersOf (m + 1) (M + 2 ^ m * 1) c = Function.update (lettersOf m M c) m 3 := by
  have hbit : ∀ j < m, (M + 2 ^ m * 1).testBit j = M.testBit j := by
    intro j hj
    rw [mul_one, Nat.add_comm, Nat.testBit_two_pow_add_gt hj]
  have hpop : ∀ j ≤ m, popB (M + 2 ^ m * 1) j = popB M j :=
    fun j hj => popB_congr fun i hi => hbit i (by omega)
  have htop : (M + 2 ^ m * 1).testBit m = true := by
    rw [mul_one, Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hM]
    rfl
  refine ⟨?_, ?_⟩
  · rw [popB_succ, hpop m le_rfl, htop]
    rfl
  · funext j
    rcases lt_trichotomy j m with h | rfl | h
    · rw [Function.update_of_ne h.ne]
      simp only [lettersOf, h, Nat.lt_succ_of_lt h, if_true, hbit j h, hpop j h.le]
    · simp only [lettersOf, Nat.lt_succ_self, if_true, htop, Function.update_self]
    · rw [Function.update_of_ne h.ne']
      simp [lettersOf, Nat.not_lt.mpr h.le, Nat.not_lt.mpr (Nat.succ_le_of_lt h)]

private theorem sum_range_mul_aux {β : Type*} [AddCommMonoid β] (A B : ℕ) (G : ℕ → β) :
    ∑ Z ∈ range (A * B), G Z = ∑ y ∈ range B, ∑ x ∈ range A, G (x + A * y) := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Nat.add_comm]

private theorem sum_four {β : Type*} [AddCommMonoid β] (h : ℕ → β) :
    ∑ x ∈ range 4, h x = ∑ d ∈ range 3, h d + h 3 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]

/-- The strings of letters are in bijection with the marks and their digits. -/
private theorem sum_letters {β : Type*} [AddCommMonoid β] (m : ℕ) (G : (ℕ → ℕ) → β) :
    ∑ M ∈ range (2 ^ m), ∑ c ∈ range (3 ^ (m - popB M m)), G (lettersOf m M c) =
      ∑ π ∈ cube m (fun _ => range 4), G π := by
  induction m generalizing G with
  | zero =>
    have hc : cube 0 (fun _ => range 4) = ({0} : Finset (ℕ → ℕ)) := by
      ext f
      simp [mem_cube, funext_iff]
    have hl : lettersOf 0 0 0 = 0 := by
      funext j
      simp [lettersOf]
    simp [hc, popB, hl]
  | succ m ih =>
    rw [sum_cube_succ, ← ih (fun π => ∑ x ∈ range 4, G (Function.update π m x)), sum_split m 1,
      pow_one, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun M hM => ?_
    have hM' := Finset.mem_range.mp hM
    have hbit : M.testBit m = false := Nat.testBit_lt_two_pow hM'
    have hp := popB_le M m
    have h0 : ∑ c ∈ range (3 ^ (m + 1 - popB (M + 2 ^ m * 0) (m + 1))),
          G (lettersOf (m + 1) (M + 2 ^ m * 0) c) =
        ∑ d ∈ range 3, ∑ c0 ∈ range (3 ^ (m - popB M m)),
          G (Function.update (lettersOf m M c0) m d) := by
      have e1 : M + 2 ^ m * 0 = M := by simp
      have e2 : m + 1 - popB M (m + 1) = (m - popB M m) + 1 := by
        rw [popB_succ, hbit]
        simp only [Bool.toNat_false, add_zero]
        omega
      rw [e1, e2, pow_succ, sum_range_mul_aux]
      refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun c0 hc0 => ?_
      rw [letters_zero hM' (Finset.mem_range.mp hc0) (Finset.mem_range.mp hd)]
    have h1 : ∑ c ∈ range (3 ^ (m + 1 - popB (M + 2 ^ m * 1) (m + 1))),
          G (lettersOf (m + 1) (M + 2 ^ m * 1) c) =
        ∑ c ∈ range (3 ^ (m - popB M m)), G (Function.update (lettersOf m M c) m 3) := by
      have e2 : m + 1 - popB (M + 2 ^ m * 1) (m + 1) = m - popB M m := by
        rw [(letters_one hM' 0).1]
        omega
      rw [e2]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [(letters_one hM' c).2]
    rw [h0, h1, Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [sum_four (fun x => G (Function.update (lettersOf m M c) m x))]

private theorem cnt_letters (m M c : ℕ) : cnt m (lettersOf m M c) 3 = popB M m := by
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  by_cases hb : M.testBit j = true
  · simp [lettersOf, hj', hb]
  · have hb' : M.testBit j = false := by simpa using hb
    have hd := Nat.mod_lt (c / 3 ^ (j - popB M j)) (by norm_num : 3 > 0)
    simp [lettersOf, hj', hb']
    omega

/-! The complement of a mark, and the marks of the short code. -/

theorem testBit_comp {m B j : ℕ} (hB : B < 2 ^ m) (hj : j < m) :
    (2 ^ m - 1 - B).testBit j = !B.testBit j := by
  induction m generalizing B j with
  | zero => omega
  | succ m ih =>
    have hB2 : B / 2 < 2 ^ m := by
      rw [pow_succ] at hB
      omega
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    have hmod := Nat.mod_lt B (by norm_num : 2 > 0)
    have e : 2 ^ (m + 1) - 1 - B = 2 * (2 ^ m - 1 - B / 2) + (1 - B % 2) := by
      have := Nat.div_add_mod B 2
      rw [pow_succ]
      omega
    rcases j with _ | j
    · rw [Nat.testBit_zero, Nat.testBit_zero, e]
      rcases (by omega : B % 2 = 0 ∨ B % 2 = 1) with h | h
      · simp [h, Nat.add_mod]
      · simp [h, Nat.mul_mod_right]
    · rw [Nat.testBit_succ, Nat.testBit_succ, e]
      have e2 : (2 * (2 ^ m - 1 - B / 2) + (1 - B % 2)) / 2 = 2 ^ m - 1 - B / 2 := by omega
      rw [e2]
      exact ih hB2 (by omega)

private theorem popB_comp {m B : ℕ} (hB : B < 2 ^ m) : popB (2 ^ m - 1 - B) m + popB B m = m := by
  unfold popB
  rw [← Finset.sum_add_distrib]
  have h : ∀ i ∈ range m, ((2 ^ m - 1 - B).testBit i).toNat + (B.testBit i).toNat = 1 := by
    intro i hi
    rw [testBit_comp hB (Finset.mem_range.mp hi)]
    cases B.testBit i <;> rfl
  rw [Finset.sum_congr rfl h]
  simp

/-- Of a set with the top position and its complement, exactly one is admissible. -/
private theorem admB_comp {k B : ℕ} (hB : B < 2 ^ (k + 1)) (htop : B.testBit k = true) :
    admB (k + 1) (2 ^ (k + 1) - 1 - B) ↔ ¬ admB (k + 1) B := by
  have hp := popB_comp hB
  have hc : (2 ^ (k + 1) - 1 - B).testBit k = false := by
    rw [testBit_comp hB (by omega), htop]
    rfl
  simp only [admB, Nat.add_sub_cancel, hc, htop, Bool.false_eq_true, and_false, or_false, and_true]
  omega

private theorem mark_eq {k M' : ℕ} (hM : M' < 2 ^ k) :
    markOf (k + 1) M' = if admB (k + 1) (M' + 2 ^ k) then M' + 2 ^ k else 2 ^ k - 1 - M' := by
  have e1 : M' % 2 ^ k = M' := Nat.mod_eq_of_lt hM
  have e2 : 2 ^ (k + 1) - 1 - (M' + 2 ^ k) = 2 ^ k - 1 - M' := by
    rw [pow_succ]
    omega
  simp only [markOf, Nat.add_sub_cancel, e1, e2]

private theorem top_bit {k M' : ℕ} (hM : M' < 2 ^ k) : (M' + 2 ^ k).testBit k = true := by
  rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hM]
  rfl

/-- Every mark is admissible. -/
private theorem markOf_adm (k ξ : ℕ) : admB (k + 1) (markOf (k + 1) ξ) := by
  have hM : ξ % 2 ^ k < 2 ^ k := Nat.mod_lt _ (by positivity)
  have hB : ξ % 2 ^ k + 2 ^ k < 2 ^ (k + 1) := by
    rw [pow_succ]
    omega
  have e2 : 2 ^ (k + 1) - 1 - (ξ % 2 ^ k + 2 ^ k) = 2 ^ k - 1 - ξ % 2 ^ k := by
    rw [pow_succ]
    omega
  have hcomp := admB_comp hB (top_bit hM)
  rw [e2] at hcomp
  simp only [markOf, Nat.add_sub_cancel, e2]
  split_ifs with h
  · exact h
  · exact hcomp.mpr h

private theorem markOf_lt (k ξ : ℕ) : markOf (k + 1) ξ < 2 ^ (k + 1) := by
  have hM : ξ % 2 ^ k < 2 ^ k := Nat.mod_lt _ (by positivity)
  simp only [markOf, Nat.add_sub_cancel]
  rw [pow_succ]
  split_ifs <;> omega

/-- The marks of the short code are the admissible sets, each once. -/
private theorem sum_marks {β : Type*} [AddCommMonoid β] (k : ℕ) (F : ℕ → β) :
    ∑ M' ∈ range (2 ^ k), F (markOf (k + 1) M') =
      ∑ M ∈ range (2 ^ (k + 1)), if admB (k + 1) M then F M else 0 := by
  rw [pow_succ, mul_two, Finset.sum_range_add,
    ← Finset.sum_range_reflect (fun M => if admB (k + 1) M then F M else 0) (2 ^ k),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun M' hM => ?_
  have hM' := Finset.mem_range.mp hM
  have hB : M' + 2 ^ k < 2 ^ (k + 1) := by
    rw [pow_succ]
    omega
  have e2 : 2 ^ (k + 1) - 1 - (M' + 2 ^ k) = 2 ^ k - 1 - M' := by
    rw [pow_succ]
    omega
  have hcomp := admB_comp hB (top_bit hM')
  rw [e2] at hcomp
  rw [mark_eq hM', Nat.add_comm (2 ^ k) M']
  by_cases h : admB (k + 1) (M' + 2 ^ k)
  · rw [if_pos h, if_pos h, if_neg (fun h' => hcomp.mp h' h), zero_add]
  · rw [if_neg h, if_neg h, if_pos (hcomp.mpr h), add_zero]

/-- The last letter of the letters of a mark is special exactly when the top bit is set. -/
private theorem letters_top (k M c : ℕ) : lettersOf (k + 1) M c k = 3 ↔ M.testBit k = true := by
  have hd := Nat.mod_lt (c / 3 ^ (k - popB M k)) (by norm_num : 3 > 0)
  by_cases hb : M.testBit k = true
  · simp [lettersOf, hb]
  · have hb' : M.testBit k = false := by simpa using hb
    have hne : lettersOf (k + 1) M c k ≠ 3 := by
      simp only [lettersOf, Nat.lt_succ_self, if_true, hb', Bool.false_eq_true, if_false]
      omega
    simp only [hne, hb', Bool.false_eq_true]

theorem admL_letters (k M c : ℕ) : admL (k + 1) (lettersOf (k + 1) M c) 3 ↔ admB (k + 1) M := by
  simp only [admL, admB, Nat.add_sub_cancel, cnt_letters, letters_top]

/-- The sum over the indices of the short code. The strings of letters whose special letters are not admissible have no
index, but they do not count: `G` vanishes on them. -/
theorem sum_cheap (m : ℕ) (G : (ℕ → ℕ) → ℤ) (hG : ∀ k π, m = k + 1 → ¬ admL (k + 1) π 3 → G π = 0) :
    ∑ ξ ∈ range (2 ^ dLen true m), (if validIdx true m ξ then G (letterOf true m ξ) else 0) =
      ∑ π ∈ cube m (fun _ => range 4), G π := by
  rcases m with _ | k
  · have hc : cube 0 (fun _ => range 4) = ({0} : Finset (ℕ → ℕ)) := by
      ext f
      simp [mem_cube, funext_iff]
    have hl : letterOf true 0 0 = 0 := by
      funext j
      simp [letterOf]
    have hv : validIdx true 0 0 := fun _ => by simp
    simp [dLen, hc, hl, hv]
  rw [← sum_letters (k + 1) G]
  have hF : ∀ M ∈ range (2 ^ (k + 1)), ∑ c ∈ range (3 ^ (k + 1 - popB M (k + 1))), G (lettersOf (k + 1) M c) =
      if admB (k + 1) M then ∑ c ∈ range (3 ^ (k + 1 - popB M (k + 1))), G (lettersOf (k + 1) M c) else 0 := by
    intro M _
    split_ifs with h
    · rfl
    · exact Finset.sum_eq_zero fun c _ => hG k _ rfl ((admL_letters k M c).not.mpr h)
  rw [Finset.sum_congr rfl hF, ← sum_marks k]
  have hd : dLen true (k + 1) = k + (8 * ((k + 1) / 2) + 4) / 5 := by simp [dLen]
  rw [hd, sum_split, Finset.sum_comm]
  refine Finset.sum_congr rfl fun M' hM => ?_
  have hM' := Finset.mem_range.mp hM
  have ht : ∀ c, (if validIdx true (k + 1) (M' + 2 ^ k * c) then
      G (letterOf true (k + 1) (M' + 2 ^ k * c)) else 0) =
      if c < 3 ^ (k + 1 - popB (markOf (k + 1) M') (k + 1)) then
        G (lettersOf (k + 1) (markOf (k + 1) M') c) else 0 := by
    intro c
    have h1 : (M' + 2 ^ k * c) % 2 ^ k = M' % 2 ^ k := by
      rw [Nat.add_mul_mod_self_left]
    have hmk : markOf (k + 1) (M' + 2 ^ k * c) = markOf (k + 1) M' := by
      simp only [markOf, Nat.add_sub_cancel, h1]
    have h2 : (M' + 2 ^ k * c) / 2 ^ k = c := by
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hM', Nat.zero_add]
    have h3 : letterOf true (k + 1) (M' + 2 ^ k * c) = lettersOf (k + 1) (markOf (k + 1) M') c := by
      funext j
      simp only [letterOf, letterCheap, lettersOf, hmk, h2, Nat.add_sub_cancel, if_true]
    have h4 : validIdx true (k + 1) (M' + 2 ^ k * c) ↔ c < 3 ^ (k + 1 - popB (markOf (k + 1) M') (k + 1)) := by
      simp only [validIdx, hmk, h2, Nat.add_sub_cancel, forall_const]
    simp only [h3, h4]
  simp only [ht]
  have hadm := markOf_adm k M'
  have hsmall : k + 1 - popB (markOf (k + 1) M') (k + 1) ≤ (k + 1) / 2 := by
    simp only [admB] at hadm
    omega
  have hN : 3 ^ (k + 1 - popB (markOf (k + 1) M') (k + 1)) ≤ 2 ^ ((8 * ((k + 1) / 2) + 4) / 5) :=
    (Nat.pow_le_pow_right (by norm_num) hsmall).trans (three_pow_le _)
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext c
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

private theorem sum_plain {β : Type*} [AddCommMonoid β] (m : ℕ) (G : (ℕ → ℕ) → β) :
    ∑ ξ ∈ range (2 ^ (2 * m)), G (letterOf false m ξ) = ∑ π ∈ cube m (fun _ => range 4), G π := by
  have h := sum_viewL m (fun _ => 2) G
  have hs : ∑ _t ∈ range m, 2 = 2 * m := by simp [mul_comm]
  have hv : ∀ ξ, letterOf false m ξ = viewL m (fun _ => 2) ξ := by
    intro ξ
    funext j
    by_cases hj : j < m
    · have hs' : ∑ _t ∈ range j, 2 = 2 * j := by simp [mul_comm]
      simp only [letterOf, letterPlain, viewL, hj, if_true, Bool.false_eq_true, if_false, hs',
        pow_mul]
      norm_num
    · simp [letterOf, viewL, hj]
  simp only [hv]
  rw [hs] at h
  exact h

private theorem coefRt_zero {pol : Bool} {t n : ℕ} (hp : pol = true) (h : n < t) : coefRt pol t n = 0 := by
  subst hp
  refine Finset.sum_eq_zero fun r hr => ?_
  have hr' := Finset.mem_range.mp hr
  rw [if_neg (by simp only [condT, if_true]; omega)]

private theorem coefCt_zero {pol : Bool} {t k n3 : ℕ} (hp : pol = false) (h : t ≤ k - n3) :
    coefCt pol t k n3 = 0 := by
  subst hp
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [if_neg (by simp only [condT, Bool.false_eq_true, if_false]; omega)]

/-- In the cheap direction across the rows, a string whose letters `3` are not admissible has the coefficient `0`. -/
private theorem rectCoef_rows_zero {k : ℕ} {π : ℕ → ℕ} (h : ¬ admL (k + 1) π 3) :
    rectCoef true true (k + 1) π = 0 := by
  simp only [admL, Nat.add_sub_cancel, cnt_succ] at h
  simp only [rectCoef, if_true]
  by_cases hk : π k = 3
  · simp [hk] at h
    rw [coefRt_zero rfl (by simp only [thr0]; omega), coefRt_zero rfl (by simp only [thr1]; omega)]
    ring
  · simp [hk] at h
    rw [show aR (π k) = 0 by simp [aR, hk], coefRt_zero rfl (by simp only [thr0]; omega)]
    ring

/-- In the cheap direction across the columns, a string whose letters `3` are not admissible has the coefficient `0`. -/
private theorem rectCoef_cols_zero {k : ℕ} {π : ℕ → ℕ} (h : ¬ admL (k + 1) π 3) :
    rectCoef false false (k + 1) π = 0 := by
  simp only [admL, Nat.add_sub_cancel, cnt_succ] at h
  have hn := cnt_le k π 3
  simp only [rectCoef, Bool.false_eq_true, if_false]
  by_cases hk : π k = 3
  · simp [hk] at h
    rw [coefCt_zero rfl (by simp only [thr0]; omega), coefCt_zero rfl (by simp only [thr1]; omega)]
    ring
  · simp [hk] at h
    rw [show bC (π k) = 0 by simp [bC, hk], coefCt_zero (t := thr1 k) rfl (by simp only [thr1]; omega)]
    ring

/-- The sum over the indices, in both codes. -/
private theorem sum_index (dir pol : Bool) (m p q r s : ℕ) :
    ∑ ξ ∈ range (2 ^ dLen (pol == dir) m), (if validIdx (pol == dir) m ξ then
        rectCoef dir pol m (letterOf (pol == dir) m ξ) *
          fpatT m (letterOf (pol == dir) m ξ) p q * fpatB m (letterOf (pol == dir) m ξ) r s
      else 0) =
      ∑ π ∈ cube m (fun _ => range 4), rectCoef dir pol m π * fpatT m π p q * fpatB m π r s := by
  by_cases hc : (pol == dir) = true
  · rw [hc]
    have hpd : pol = dir := by simpa using hc
    subst hpd
    cases pol
    · refine sum_cheap m (fun π => rectCoef false false m π * fpatT m π p q * fpatB m π r s)
        fun k π hm hπ => ?_
      subst hm
      rw [rectCoef_cols_zero hπ]
      simp
    · refine sum_cheap m (fun π => rectCoef true true m π * fpatT m π p q * fpatB m π r s)
        fun k π hm hπ => ?_
      subst hm
      rw [rectCoef_rows_zero hπ]
      simp
  · have hc' : (pol == dir) = false := by simpa using hc
    rw [hc']
    have hv : ∀ ξ, validIdx false m ξ := fun ξ h => by simp at h
    simp only [hv, if_true]
    have hd : dLen false m = 2 * m := by simp [dLen]
    rw [hd]
    exact sum_plain m (fun π => rectCoef dir pol m π * fpatT m π p q * fpatB m π r s)

/-- **The seed.** The piece of the crossing factors through `dLen` bits, for each direction. -/
theorem seed_sum (dir pol : Bool) {scale m : ℕ} (hm : m ≤ scale) (p q r s : ℕ) :
    ∑ ξ ∈ range (2 ^ dLen (pol == dir) m), rectA dir pol scale m ξ p q * rectB dir pol m ξ r s =
      2 ^ scale * PP dir pol m p q r s := by
  have hPP : ∑ π ∈ cube m (fun _ => range 4), rectCoef dir pol m π * fpatT m π p q * fpatB m π r s =
      2 ^ m * PP dir pol m p q r s := by
    cases dir
    · simp only [PP, Bool.false_eq_true, if_false]
      rw [seed_cols pol m p r q s]
    · simp only [PP, if_true]
      rw [seed_rows pol m p q r s]
  have hterm : ∀ ξ, rectA dir pol scale m ξ p q * rectB dir pol m ξ r s =
      2 ^ (scale - m) * (if validIdx (pol == dir) m ξ then
        rectCoef dir pol m (letterOf (pol == dir) m ξ) *
          fpatT m (letterOf (pol == dir) m ξ) p q * fpatB m (letterOf (pol == dir) m ξ) r s
      else 0) := by
    intro ξ
    unfold rectA rectB
    split_ifs
    · ring
    · simp
  simp only [hterm]
  rw [← Finset.mul_sum, sum_index, hPP, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hm]

/-- The width of a pair of diagonals, for `m = pairMin w1 w2`: the two widths are at most `w1 + w2` and
`max w1 w2 + (4 / 5) min w1 w2`. -/
theorem dLen_cheap_le (w1 w2 : ℕ) :
    5 * (w1 + w2 - 2 * pairMin w1 w2 + dLen true (pairMin w1 w2)) ≤ 5 * max w1 w2 + 4 * min w1 w2 := by
  simp only [dLen, if_true]
  by_cases h0 : pairMin w1 w2 = 0
  · rw [if_pos h0]
    simp only [pairMin] at h0 ⊢
    omega
  · rw [if_neg h0]
    simp only [pairMin] at h0 ⊢
    omega

theorem dLen_le (b : Bool) (w1 w2 : ℕ) : dLen b (pairMin w1 w2) ≤ 2 * pairMin w1 w2 := by
  cases b
  · simp [dLen]
  · simp only [dLen, if_true]
    by_cases h0 : pairMin w1 w2 = 0
    · rw [if_pos h0]
      omega
    · rw [if_neg h0]
      omega

theorem pairMin_le_left (a b : ℕ) : pairMin a b ≤ a := min_le_left a b

theorem pairMin_le_right (a b : ℕ) : pairMin a b ≤ b := min_le_right a b

theorem pairMin_comm (a b : ℕ) : pairMin a b = pairMin b a := min_comm a b

end DominantStrings
