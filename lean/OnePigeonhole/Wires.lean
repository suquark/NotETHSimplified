import OnePigeonhole.Walsh

/-!
# Wires, cells, cubes and corners

The objects of Sections 1 and 2 of `papers/one-pigeonhole/proof.tex`.

A cell is a pair of words with `Q` digits over `L` letters, and a layer below `h`. `tau E` exchanges the letters of the two words
in the digits of `E`.

A key `k` gives each digit two letters `(k.1 t).1 < (k.1 t).2`, and a layer. `corner k F` is the cell obtained from the base of `k`
by the exchange of `F`, and the cube of `k` is the set of these `2 ^ Q` cells. `keyOf` and `cornerOf` invert `corner`.

* `tau_corner`: `τ_E (corner k F) = corner k (F ∆ E)`.
* `card_keys_mul_le`: `#keys * 2 ^ Q ≤ (L ^ Q) ^ 2 * h`.
* `Wires`: the wires, with `tw`, `hw`, `lay`.
* `Wires.tau_c_eq_d_iff`: `τ_E (c i) = d j` exactly when `i` and `j` have one key and `E = F i ∆ (F j)ᶜ`.
* `Wires.Eij`: the set `E_ij = F i ∆ (F j)ᶜ`.
* `letter`, `Wires.tw_eq_letter`, `Wires.hw_eq_letter`: the letters of a digit of a wire, by the corner of the wire.
-/

set_option linter.unusedSectionVars false

namespace OnePigeonhole

open Finset

variable {Q L h M : ℕ}

/-! ### Cells and exchanges -/

/-- A cell: two words and a layer. -/
abbrev LCell (Q L h : ℕ) := TransposeBase.Cell Q (Fin L) × Fin h

/-- `τ_E`: exchange the letters of the two words in the digits of `E`. The layer stays. -/
def tau (E : Finset (Fin Q)) (c : LCell Q L h) : LCell Q L h := (TransposeBase.swap E c.1, c.2)

@[simp] theorem tau_fst_fst (E : Finset (Fin Q)) (c : LCell Q L h) (t : Fin Q) :
    (tau E c).1.1 t = if t ∈ E then c.1.2 t else c.1.1 t := rfl

@[simp] theorem tau_fst_snd (E : Finset (Fin Q)) (c : LCell Q L h) (t : Fin Q) :
    (tau E c).1.2 t = if t ∈ E then c.1.1 t else c.1.2 t := rfl

@[simp] theorem tau_snd (E : Finset (Fin Q)) (c : LCell Q L h) : (tau E c).2 = c.2 := rfl

theorem lcell_ext {c c' : LCell Q L h} (h1 : ∀ t, c.1.1 t = c'.1.1 t) (h2 : ∀ t, c.1.2 t = c'.1.2 t)
    (h3 : c.2 = c'.2) : c = c' :=
  Prod.ext (Prod.ext (funext h1) (funext h2)) h3

/-- `τ_E τ_F = τ_{F ∆ E}`. -/
theorem tau_tau (E F : Finset (Fin Q)) (c : LCell Q L h) : tau E (tau F c) = tau (symmDiff F E) c := by
  refine lcell_ext (fun t => ?_) (fun t => ?_) rfl <;>
  · by_cases h1 : t ∈ E <;> by_cases h2 : t ∈ F <;> simp [Finset.mem_symmDiff, h1, h2]

/-! ### Keys and corners -/

/-- The key of a cube: the ordered pair of letters at each digit, and the layer. -/
abbrev Key (Q L h : ℕ) := (Fin Q → Fin L × Fin L) × Fin h

/-- At each digit the first letter of the key is smaller than the second. -/
def IsKey (k : Key Q L h) : Prop := ∀ t, (k.1 t).1 < (k.1 t).2

instance : DecidablePred (IsKey (Q := Q) (L := L) (h := h)) := fun k => by
  unfold IsKey
  infer_instance

/-- All the keys. -/
def keys (Q L h : ℕ) : Finset (Key Q L h) := univ.filter IsKey

theorem mem_keys {k : Key Q L h} : k ∈ keys Q L h ↔ IsKey k := by simp [keys]

/-- The base of a cube: at each digit the first word has the smaller letter. -/
def baseOf (k : Key Q L h) : LCell Q L h := ((fun t => (k.1 t).1, fun t => (k.1 t).2), k.2)

/-- The cell of a cube at the corner `F`. -/
def corner (k : Key Q L h) (F : Finset (Fin Q)) : LCell Q L h := tau F (baseOf k)

@[simp] theorem corner_fst_fst (k : Key Q L h) (F : Finset (Fin Q)) (t : Fin Q) :
    (corner k F).1.1 t = if t ∈ F then (k.1 t).2 else (k.1 t).1 := rfl

@[simp] theorem corner_fst_snd (k : Key Q L h) (F : Finset (Fin Q)) (t : Fin Q) :
    (corner k F).1.2 t = if t ∈ F then (k.1 t).1 else (k.1 t).2 := rfl

@[simp] theorem corner_snd (k : Key Q L h) (F : Finset (Fin Q)) : (corner k F).2 = k.2 := rfl

/-- The key of a cell. -/
def keyOf (c : LCell Q L h) : Key Q L h :=
  (fun t => (min (c.1.1 t) (c.1.2 t), max (c.1.1 t) (c.1.2 t)), c.2)

/-- The corner of a cell: the digits where the first word has the larger letter. -/
def cornerOf (c : LCell Q L h) : Finset (Fin Q) := univ.filter fun t => c.1.2 t < c.1.1 t

theorem mem_cornerOf {c : LCell Q L h} {t : Fin Q} : t ∈ cornerOf c ↔ c.1.2 t < c.1.1 t := by
  simp [cornerOf]

theorem keyOf_corner {k : Key Q L h} (hk : IsKey k) (F : Finset (Fin Q)) : keyOf (corner k F) = k := by
  refine Prod.ext (funext fun t => ?_) rfl
  have hlt := hk t
  refine Prod.ext ?_ ?_
  · by_cases hF : t ∈ F <;> simp [keyOf, hF, min_eq_left hlt.le, min_eq_right hlt.le]
  · by_cases hF : t ∈ F <;> simp [keyOf, hF, max_eq_left hlt.le, max_eq_right hlt.le]

theorem cornerOf_corner {k : Key Q L h} (hk : IsKey k) (F : Finset (Fin Q)) : cornerOf (corner k F) = F := by
  ext t
  have hlt := hk t
  rw [mem_cornerOf, corner_fst_fst, corner_fst_snd]
  by_cases hF : t ∈ F
  · simp [hF, hlt]
  · simp [hF, not_lt.mpr hlt.le]

theorem corner_keyOf_cornerOf (c : LCell Q L h) : corner (keyOf c) (cornerOf c) = c := by
  refine lcell_ext (fun t => ?_) (fun t => ?_) rfl
  · rw [corner_fst_fst]
    by_cases hF : c.1.2 t < c.1.1 t
    · simp [mem_cornerOf, hF, keyOf, max_eq_left hF.le]
    · simp [mem_cornerOf, hF, keyOf, min_eq_left (not_lt.mp hF)]
  · rw [corner_fst_snd]
    by_cases hF : c.1.2 t < c.1.1 t
    · simp [mem_cornerOf, hF, keyOf, min_eq_right hF.le]
    · simp [mem_cornerOf, hF, keyOf, max_eq_right (not_lt.mp hF)]

theorem isKey_keyOf {c : LCell Q L h} (hc : ∀ t, c.1.1 t ≠ c.1.2 t) : IsKey (keyOf c) := fun t =>
  min_lt_max.mpr (hc t)

/-- `τ_E (corner F) = corner (F ∆ E)`. -/
theorem tau_corner (E : Finset (Fin Q)) (k : Key Q L h) (F : Finset (Fin Q)) :
    tau E (corner k F) = corner k (symmDiff F E) :=
  tau_tau E F (baseOf k)

theorem corner_inj {k k' : Key Q L h} (hk : IsKey k) (hk' : IsKey k') {F F' : Finset (Fin Q)} :
    corner k F = corner k' F' ↔ k = k' ∧ F = F' := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← keyOf_corner hk F, ← keyOf_corner hk' F', h]
    · rw [← cornerOf_corner hk F, ← cornerOf_corner hk' F', h]
  · rintro ⟨rfl, rfl⟩
    rfl

/-- `#keys * 2 ^ Q ≤ (L ^ Q) ^ 2 * h`: different pairs of a key and a corner are different cells. -/
theorem card_keys_mul_le (Q L h : ℕ) : (keys Q L h).card * 2 ^ Q ≤ (L ^ Q) ^ 2 * h := by
  classical
  have hinj : Set.InjOn (fun p : Key Q L h × Finset (Fin Q) => corner p.1 p.2)
      ((keys Q L h ×ˢ (univ : Finset (Finset (Fin Q))) : Finset _) : Set _) := by
    intro p hp p' hp' he
    have h1 : IsKey p.1 := mem_keys.mp (Finset.mem_product.mp hp).1
    have h2 : IsKey p'.1 := mem_keys.mp (Finset.mem_product.mp hp').1
    have h3 := (corner_inj h1 h2).mp he
    exact Prod.ext h3.1 h3.2
  have hc := Finset.card_le_card_of_injOn (s := keys Q L h ×ˢ (univ : Finset (Finset (Fin Q))))
    (t := (univ : Finset (LCell Q L h))) _ (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) hinj
  rw [Finset.card_product, Finset.card_univ, Finset.card_univ] at hc
  simp only [Fintype.card_finset, Fintype.card_fin, Fintype.card_prod, Fintype.card_fun] at hc
  calc (keys Q L h).card * 2 ^ Q ≤ L ^ Q * L ^ Q * h := hc
    _ = (L ^ Q) ^ 2 * h := by ring

/-! ### Wires -/

/-- The wires: for each of the `M` wires the words of its tail and of its head, which differ in every digit, and a layer.
Different wires have different triples. In Section 1, a wire is an occurrence `j` of `v` in `e`, with `tw j = s(v)`,
`hw j = o(e)` and `lay j = ℓ`, so `c j` and `d j` below are the cells `c_j` and `d_j`. -/
structure Wires (Q L h M : ℕ) where
  /-- The word of the tail. -/
  tw : Fin M → Fin Q → Fin L
  /-- The word of the head. -/
  hw : Fin M → Fin Q → Fin L
  /-- The layer. -/
  lay : Fin M → Fin h
  /-- The two words differ in every digit. -/
  differ : ∀ e t, tw e t ≠ hw e t
  /-- Different wires have different cells. -/
  inj : Function.Injective fun e => (tw e, hw e, lay e)

namespace Wires

variable (W : Wires Q L h M)

/-- The cell `c_e = (tw e, hw e, lay e)`. -/
def c (e : Fin M) : LCell Q L h := ((W.tw e, W.hw e), W.lay e)

/-- The transposed cell `d_e = (hw e, tw e, lay e)`. -/
def d (e : Fin M) : LCell Q L h := ((W.hw e, W.tw e), W.lay e)

/-- The key of the cube of a wire. -/
def key (e : Fin M) : Key Q L h := keyOf (W.c e)

/-- The corner of the cell of a wire in its cube. -/
def F (e : Fin M) : Finset (Fin Q) := cornerOf (W.c e)

theorem isKey_key (e : Fin M) : IsKey (W.key e) := isKey_keyOf (W.differ e)

theorem key_mem_keys (e : Fin M) : W.key e ∈ keys Q L h := mem_keys.mpr (W.isKey_key e)

theorem c_eq_corner (e : Fin M) : W.c e = corner (W.key e) (W.F e) :=
  (corner_keyOf_cornerOf (W.c e)).symm

theorem tau_univ_c (e : Fin M) : tau univ (W.c e) = W.d e := by
  refine lcell_ext (fun t => ?_) (fun t => ?_) rfl <;> simp [c, d]

/-- The transposed cell lies at the complement of the corner. -/
theorem d_eq_corner (e : Fin M) : W.d e = corner (W.key e) (W.F e)ᶜ := by
  rw [← W.tau_univ_c e, W.c_eq_corner e, tau_corner]
  congr 1
  ext t
  simp [Finset.mem_symmDiff]

theorem c_inj {i j : Fin M} (he : W.c i = W.c j) : i = j := by
  apply W.inj
  have h1 : W.tw i = W.tw j := congrArg (fun c : LCell Q L h => c.1.1) he
  have h2 : W.hw i = W.hw j := congrArg (fun c : LCell Q L h => c.1.2) he
  have h3 : W.lay i = W.lay j := congrArg (fun c : LCell Q L h => c.2) he
  simp [h1, h2, h3]

/-- Two wires of one cube with one corner are the same wire. -/
theorem F_inj {i j : Fin M} (hk : W.key i = W.key j) (hF : W.F i = W.F j) : i = j := by
  apply W.c_inj
  rw [W.c_eq_corner i, W.c_eq_corner j, hk, hF]

/-- **The exchanges between two wires.** There is at most one `E` with `τ_E (c i) = d j`. -/
theorem tau_c_eq_d_iff (E : Finset (Fin Q)) (i j : Fin M) :
    tau E (W.c i) = W.d j ↔ W.key i = W.key j ∧ E = symmDiff (W.F i) (W.F j)ᶜ := by
  rw [W.d_eq_corner j, W.c_eq_corner i, tau_corner, corner_inj (W.isKey_key i) (W.isKey_key j)]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    rw [← h]
    simp
  · intro h
    rw [h]
    simp

/-- The long set reaches exactly the transposed cell of the wire. -/
theorem tau_univ_c_eq_d_iff (i j : Fin M) : tau univ (W.c i) = W.d j ↔ i = j := by
  rw [W.tau_univ_c i]
  constructor
  · intro he
    apply W.inj
    have h1 : W.hw i = W.hw j := congrArg (fun c : LCell Q L h => c.1.1) he
    have h2 : W.tw i = W.tw j := congrArg (fun c : LCell Q L h => c.1.2) he
    have h3 : W.lay i = W.lay j := congrArg (fun c : LCell Q L h => c.2) he
    simp [h1, h2, h3]
  · rintro rfl
    rfl

/-- The exchange between two wires: `E_ij = F_i ∆ (F_j)ᶜ`. If `i` and `j` have one key, it is the only set with
`τ_{E_ij} c_i = d_j`. -/
def Eij (i j : Fin M) : Finset (Fin Q) := symmDiff (W.F i) (W.F j)ᶜ

theorem tau_c_eq_d_iff_Eij (E : Finset (Fin Q)) (i j : Fin M) :
    tau E (W.c i) = W.d j ↔ W.key i = W.key j ∧ E = W.Eij i j :=
  W.tau_c_eq_d_iff E i j

/-- The long set reaches the column `j` from the row `i` exactly when `i = j`. -/
theorem eq_iff_key_Eij (i j : Fin M) : i = j ↔ W.key i = W.key j ∧ univ = W.Eij i j := by
  rw [← W.tau_univ_c_eq_d_iff, W.tau_c_eq_d_iff_Eij]

end Wires

/-! ### Letters -/

/-- The letter of a side of a digit: the larger letter of the pair if `b`, the smaller letter otherwise. -/
def letter (k : Key Q L h) (t : Fin Q) (b : Bool) : Fin L := if b then (k.1 t).2 else (k.1 t).1

namespace Wires

variable (W : Wires Q L h M)

/-- The letter of the tail word: the larger letter of the pair exactly at the digits of the corner. -/
theorem tw_eq_letter (e : Fin M) (t : Fin Q) : W.tw e t = letter (W.key e) t (decide (t ∈ W.F e)) := by
  have h1 : (W.c e).1.1 t = W.tw e t := rfl
  rw [← h1, W.c_eq_corner e, corner_fst_fst]
  by_cases h : t ∈ W.F e <;> simp [letter, h]

/-- The letter of the head word: the smaller letter of the pair exactly at the digits of the corner. -/
theorem hw_eq_letter (e : Fin M) (t : Fin Q) : W.hw e t = letter (W.key e) t (!decide (t ∈ W.F e)) := by
  have h1 : (W.c e).1.2 t = W.hw e t := rfl
  rw [← h1, W.c_eq_corner e, corner_fst_snd]
  by_cases h : t ∈ W.F e <;> simp [letter, h]

end Wires

end OnePigeonhole
