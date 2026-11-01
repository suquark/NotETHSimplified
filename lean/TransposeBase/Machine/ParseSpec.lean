import OAI.Algorithms.SubexponentialSAT.Encoding
import TransposeBase.Pseudo.CnfCode

/-!
# Reading the fixed CNF encoding: the automaton

`encodeCNF F` is unary `n`, then a list of framed clauses. A framed clause is `true`, then the clause
bits with an escape bit `true` before each of them, then `false`. The clause bits of a literal code `a` are
`1 ^ (2 * a + 2) 0 0`, and a clause ends with one more `0`.

`stepP` reads the bits after the unary field one at a time. Its state is a mode `m`, a run length `r` of data ones,
the code `k` of the clause so far, and the word `f` of the formula so far. The result is `encF n (toCNF F)`, where
`toCNF` translates the syntax of `SAT.CNF (Fin n)` to `ClauseSet (SignedLiteral n)`. The sign conventions agree:
`SAT.Literal.eval a l` is `a l.variable == l.positive`, and `literalHolds x (v, b)` is `x v = b`.
-/

namespace TransposeBase.Machine.Parse

open OAI.Algorithms.SubexponentialSAT
open Encoding Finset SatBase
open TransposeBase.Pseudo.CnfTree

/-! ### The translation of formulas -/

variable {n : ℕ}

/-- The literal in the convention of the branching layer. -/
def toSigned (l : SAT.Literal (Fin n)) : SignedLiteral n := (l.variable, l.positive)

theorem toSigned_injective : Function.Injective (toSigned (n := n)) := by
  rintro ⟨v, b⟩ ⟨w, c⟩ h
  simp only [toSigned, Prod.mk.injEq] at h
  rw [h.1, h.2]

/-- The clause in the convention of the branching layer. -/
def toClause (C : SAT.Clause (Fin n)) : Finset (SignedLiteral n) := C.image toSigned

theorem toClause_injective : Function.Injective (toClause (n := n)) :=
  Finset.image_injective toSigned_injective

/-- The formula in the convention of the branching layer. -/
def toCNF (F : SAT.CNF (Fin n)) : ClauseSet (SignedLiteral n) := F.image toClause

theorem toCNF_wide {F : SAT.CNF (Fin n)} (h : SAT.WidthAtMost 3 F) : ∀ C ∈ toCNF F, C.card ≤ 3 := by
  intro C hC
  obtain ⟨D, hD, rfl⟩ := mem_image.mp hC
  exact card_image_le.trans (h D hD)

/-- The sign conventions agree. -/
theorem sat_iff (F : SAT.CNF (Fin n)) :
    SAT.Satisfiable F ↔ ∃ x, holdsFormula (literalHolds x) (toCNF F) := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, fun C hC => ?_⟩
    obtain ⟨D, hD, rfl⟩ := mem_image.mp hC
    obtain ⟨l, hl, hv⟩ := (SAT.Clause.eval_eq_true a D).mp ((SAT.CNF.eval_eq_true a F).mp ha D hD)
    exact ⟨toSigned l, mem_image_of_mem _ hl, (SAT.Literal.eval_eq_true a l).mp hv⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, (SAT.CNF.eval_eq_true x F).mpr fun C hC => ?_⟩
    obtain ⟨l', hl', hv⟩ := hx _ (mem_image_of_mem _ hC)
    obtain ⟨l, hl, rfl⟩ := mem_image.mp hl'
    exact (SAT.Clause.eval_eq_true x C).mpr ⟨l, hl, (SAT.Literal.eval_eq_true x l).mpr hv⟩

theorem litCode_toSigned (l : SAT.Literal (Fin n)) : litCode (toSigned l) = literalCode l + 1 := by
  obtain ⟨v, b⟩ := l
  cases b <;> simp [litCode, toSigned, literalCode]

/-- The literal codes of the translated clause are the numbers of the clause, plus one. -/
theorem sort_toClause (C : SAT.Clause (Fin n)) :
    ((toClause C).image litCode).sort (· ≤ ·) = (clauseNumbers C).map (· + 1) := by
  have himg : (toClause C).image litCode = (C.image literalCode).image (· + 1) := by
    simp only [toClause, image_image]
    exact image_congr fun l _ => litCode_toSigned l
  rw [himg]
  apply List.Perm.eq_of_pairwise (le := (· ≤ ·)) (fun a b _ _ h1 h2 => le_antisymm h1 h2)
  · exact pairwise_sort _ _
  · have : (clauseNumbers C).Pairwise (· ≤ ·) := pairwise_sort _ _
    exact List.pairwise_map.mpr (this.imp (fun h => by omega))
  · rw [List.perm_ext_iff_of_nodup (sort_nodup _ _)]
    · intro a
      simp [clauseNumbers]
    · refine List.Nodup.map (fun a b h => by simpa using h) (sort_nodup _ _)

theorem code_toClause (C : SAT.Clause (Fin n)) :
    code n (toClause C) = tripleOf n ((clauseNumbers C).map (· + 1)) := by
  rw [code, sort_toClause]

/-- The word of the formula, as a sum over the list of clause numbers. -/
theorem encF_toCNF (F : SAT.CNF (Fin n)) :
    encF n (toCNF F) = ((cnfNumbers F).map fun L => 2 ^ tripleOf n (L.map (· + 1))).sum := by
  have h1 : ((cnfNumbers F).map fun L => 2 ^ tripleOf n (L.map (· + 1))).sum =
      ∑ L ∈ F.image clauseNumbers, 2 ^ tripleOf n (L.map (· + 1)) := by
    have := List.sum_toFinset (fun L => 2 ^ tripleOf n (L.map (· + 1))) (sort_nodup (F.image clauseNumbers) (· ≤ ·))
    simp only [sort_toFinset] at this
    rw [this]
    rfl
  rw [h1, encF, toCNF, sum_image toClause_injective.injOn,
    sum_image clauseNumbers_injective.injOn]
  exact sum_congr rfl fun C _ => by rw [code_toClause]

/-! ### The automaton -/

/-- The state of the automaton. -/
@[ext] structure PS where
  m : ℕ
  r : ℕ
  k : ℕ
  f : ℕ

/-- One clause bit: count the ones, and a zero that ends a run adds a literal code to the clause code. -/
def dstep (G : ℕ) (p : ℕ × ℕ) (b : Bool) : ℕ × ℕ :=
  if b then (p.1 + 1, p.2)
  else if p.1 = 0 then (0, p.2)
  else (0, p.2 / G + G ^ 2 * (p.1 / 2))

/-- One bit of the input. Mode `0`: before a clause. Mode `1`: an escape bit. Mode `2`: a clause bit. -/
def stepP (G : ℕ) (s : PS) (b : Bool) : PS :=
  match s.m with
  | 0 => if b then ⟨1, s.r, s.k, s.f⟩ else s
  | 1 => if b then ⟨2, s.r, s.k, s.f⟩ else ⟨0, s.r, 0, s.f + 2 ^ s.k⟩
  | _ => ⟨1, (dstep G (s.r, s.k) b).1, (dstep G (s.r, s.k) b).2, s.f⟩

/-- A frame: the clause bits go through `dstep`, and the end of the frame adds the clause code to the word. -/
theorem foldl_frame (G : ℕ) (bits rest : List Bool) (r k f : ℕ) :
    (frame bits ++ rest).foldl (stepP G) ⟨1, r, k, f⟩ =
      rest.foldl (stepP G) ⟨0, (bits.foldl (dstep G) (r, k)).1, 0, f + 2 ^ (bits.foldl (dstep G) (r, k)).2⟩ := by
  induction bits generalizing r k with
  | nil => simp [stepP]
  | cons b bits ih =>
    simp only [frame_cons, List.cons_append, List.foldl_cons]
    exact ih _ _

/-- The clause bits of one literal, after its leading `1`. -/
theorem foldl_literal (G a r k : ℕ) :
    (frame (encodeNat a)).foldl (dstep G) (r + 1, k) = (0, k / G + G ^ 2 * ((r + 1 + 2 * a + 1) / 2)) := by
  induction a generalizing r with
  | zero => simp [encodeNat, dstep]
  | succ a ih =>
    have := ih (r + 2)
    have e : frame (encodeNat (a + 1)) = true :: true :: frame (encodeNat a) := by
      simp [encodeNat, List.replicate_succ]
    rw [e]
    simp only [List.foldl_cons, dstep, if_true]
    rw [show r + 1 + 1 + 1 = r + 2 + 1 by omega, this]
    congr 3
    omega

/-- The new clause code when a literal arrives. -/
def addLit (G k a : ℕ) : ℕ := k / G + G ^ 2 * (a + 1)

/-- The clause bits of a clause. -/
theorem foldl_clause (G : ℕ) (as : List ℕ) (k : ℕ) :
    (encodeList encodeNat as).foldl (dstep G) (0, k) = (0, as.foldl (addLit G) k) := by
  induction as generalizing k with
  | nil => simp [encodeList, dstep]
  | cons a as ih =>
    simp only [encodeList, List.foldl_cons, List.foldl_append]
    have h1 : dstep G (0, k) true = (0 + 1, k) := by simp [dstep]
    rw [h1, foldl_literal, ih]
    congr 2
    simp only [addLit]
    congr 2
    omega

/-- The clause code of a sorted list of at most three literal codes. -/
theorem foldl_addLit (as : List ℕ) (h : as.length ≤ 3) :
    as.foldl (addLit (2 * n + 1)) 0 = tripleOf n (as.map (· + 1)) := by
  have hG : 0 < 2 * n + 1 := by omega
  match as, h with
  | [], _ => simp [tripleOf]
  | [a], _ => simp [addLit, tripleOf, Pseudo.CnfTree.mk]; ring
  | [a, b], _ =>
    simp only [List.foldl_cons, List.foldl_nil, addLit, List.map_cons, List.map_nil, tripleOf, Pseudo.CnfTree.mk]
    have e : (0 / (2 * n + 1) + (2 * n + 1) ^ 2 * (a + 1)) / (2 * n + 1) = (2 * n + 1) * (a + 1) := by
      rw [Nat.zero_div, zero_add, pow_two, mul_assoc, Nat.mul_div_cancel_left _ hG]
    rw [e]
    ring
  | [a, b, c], _ =>
    simp only [List.foldl_cons, List.foldl_nil, addLit, List.map_cons, List.map_nil, tripleOf, Pseudo.CnfTree.mk]
    have e : (0 / (2 * n + 1) + (2 * n + 1) ^ 2 * (a + 1)) / (2 * n + 1) = (2 * n + 1) * (a + 1) := by
      rw [Nat.zero_div, zero_add, pow_two, mul_assoc, Nat.mul_div_cancel_left _ hG]
    rw [e]
    have e2 : ((2 * n + 1) * (a + 1) + (2 * n + 1) ^ 2 * (b + 1)) / (2 * n + 1) =
        (a + 1) + (2 * n + 1) * (b + 1) := by
      rw [show (2 * n + 1) * (a + 1) + (2 * n + 1) ^ 2 * (b + 1) =
        (2 * n + 1) * ((a + 1) + (2 * n + 1) * (b + 1)) by ring, Nat.mul_div_cancel_left _ hG]
    rw [e2]
    ring
  | _ :: _ :: _ :: _ :: _, h => simp at h; omega

/-- The list of clauses. -/
theorem foldl_clauses (LL : List (List ℕ)) (hL : ∀ L ∈ LL, L.length ≤ 3) (rest : List Bool) (f : ℕ) :
    (encodeList (encodeList encodeNat) LL ++ rest).foldl (stepP (2 * n + 1)) ⟨0, 0, 0, f⟩ =
      rest.foldl (stepP (2 * n + 1))
        ⟨0, 0, 0, f + (LL.map fun L => 2 ^ tripleOf n (L.map (· + 1))).sum⟩ := by
  induction LL generalizing f with
  | nil => simp [encodeList, stepP]
  | cons L LL ih =>
    simp only [encodeList, List.cons_append, List.foldl_cons, List.append_assoc]
    have h1 : stepP (2 * n + 1) ⟨0, 0, 0, f⟩ true = ⟨1, 0, 0, f⟩ := by simp [stepP]
    rw [h1, foldl_frame, foldl_clause, foldl_addLit L (hL L (by simp))]
    rw [ih (fun L' h' => hL L' (by simp [h']))]
    simp [add_assoc]

/-- Padding changes nothing. -/
theorem foldl_zeros (G z f : ℕ) :
    (List.replicate z false).foldl (stepP G) ⟨0, 0, 0, f⟩ = ⟨0, 0, 0, f⟩ := by
  induction z with
  | zero => rfl
  | succ z ih =>
    simp only [List.replicate_succ, List.foldl_cons]
    have : stepP G ⟨0, 0, 0, f⟩ false = ⟨0, 0, 0, f⟩ := by simp [stepP]
    rw [this, ih]

/-- **The automaton computes the word of the formula.** -/
theorem parse_spec {F : SAT.CNF (Fin n)} (hw : SAT.WidthAtMost 3 F) (z : ℕ) :
    (encodeCNFBody F ++ List.replicate z false).foldl (stepP (2 * n + 1)) ⟨0, 0, 0, 0⟩ =
      ⟨0, 0, 0, encF n (toCNF F)⟩ := by
  have hL : ∀ L ∈ cnfNumbers F, L.length ≤ 3 := by
    intro L hL
    have hi : L ∈ F.image clauseNumbers := by simpa [cnfNumbers] using hL
    obtain ⟨C, hC, rfl⟩ := mem_image.mp hi
    rw [length_clauseNumbers]
    exact hw C hC
  rw [encodeCNFBody, foldl_clauses _ hL, foldl_zeros, encF_toCNF, zero_add]

end TransposeBase.Machine.Parse
