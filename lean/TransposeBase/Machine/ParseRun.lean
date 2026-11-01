import TransposeBase.Machine.ParseExpr
import OAI.Algorithms.SubexponentialSAT.BinaryArithmetic

/-!
# The parser in the word language

On the environment `[x, N]`, where `x` is the value of the input bits and `N` is their number, `nE` computes the
number `n` of variables, and on `[n, x, N]`, `encE` computes the word `encF n (toCNF F)` (`parse_main`). Both are one
loop over `N` positions.

The size of the state word is bounded for all inputs, not only for the encoding: after `t` steps the run length is
at most `t`, the clause code grows by at most `G * G * N` per step, and the formula word grows by at most `2 ^ Q`.
-/

namespace TransposeBase.Machine.Parse

open OAI.Algorithms.SubexponentialSAT
open BinaryArithmetic (bitVal)
open Encoding
open TransposeBase.Pseudo TransposeBase.Pseudo.CnfTree

/-! ### Bits of the input -/

theorem testBit_toNat (xs : List Bool) (i : ℕ) : (BinaryArithmetic.toNat xs).testBit i = xs.getD i false := by
  induction xs generalizing i with
  | nil => simp [BinaryArithmetic.toNat]
  | cons b xs ih =>
    cases i with
    | zero => cases b <;> simp [BinaryArithmetic.toNat, bitVal, Nat.testBit_zero]
    | succ i =>
      rw [Nat.testBit_succ]
      have : BinaryArithmetic.toNat (b :: xs) / 2 = BinaryArithmetic.toNat xs := by
        cases b <;> simp [BinaryArithmetic.toNat, bitVal] <;> omega
      rw [this, ih]
      simp

/-! ### The number of variables -/

/-- The first position with a zero bit: move while the bit at the state is one. -/
def nE : Expr :=
  .fold (.var 1) (.lit 0) (.ite (bitE 2 0) (.lit 0) (.var 0) (.add (.var 0) (.lit 1)))

theorem run_nE {W n x N : ℕ} (hW : 2 ≤ W) (hx : ∀ i < n, x.testBit i = true) (hxn : x.testBit n = false)
    (hn : n ≤ N) (hNW : N < W) : Run W nE [x, N] n (3 + N * 12) := by
  have hlt : ∀ {y : ℕ}, y ≤ N → y < 2 ^ W := fun h => (lt_of_le_of_lt h hNW).trans Nat.lt_two_pow_self
  have := run_fold (W := W) (env := [x, N]) (b := .ite (bitE 2 0) (.lit 0) (.var 0) (.add (.var 0) (.lit 1)))
    (n := .var 1) (s := .lit 0) (B := 11) (g := fun k => min k n) (N := N) (Bn := 1) (Bs := 1)
    (run_var (by simp)) (by simpa using run_zero (W := W) (env := [x, N]) (by omega)) (fun k hk => by
      have hb := run_bit (W := W) (env := min k n :: k :: x :: N :: []) (f := 2) (i := 0) (fv := x)
        (iv := min k n) hW (by simp) (by simp) (by omega)
      refine (run_ite (Bc := 3) hb (run_zero (by omega)) (fun h => ?_) (fun h => ?_)).mono (by omega)
      · have hk' : ¬ min k n < n := fun h' => by
          have := hx _ h'
          simp [this] at h
        have e : min (k + 1) n = min k n := by omega
        simp only [e]
        exact (run_var (by simp)).mono (by omega)
      · have hk' : min k n < n := by
          by_contra h'
          have e : min k n = n := by omega
          rw [e, hxn] at h
          simp at h
        have e : min (k + 1) n = min k n + 1 := by omega
        simp only [e]
        exact run_add (run_var (by simp)) (run_one (by omega)) (hlt (by omega)))
  have e : min N n = n := by omega
  simp only [e] at this
  exact this.mono (by omega)

/-! ### Bounds on the state -/

/-- The state after `t` positions. -/
def stateAt (G x n t : ℕ) : PS :=
  (List.range t).foldl (fun s p => stepP G s (x.testBit (p + n + 1))) ⟨0, 0, 0, 0⟩

theorem stateAt_succ (G x n t : ℕ) :
    stateAt G x n (t + 1) = stepP G (stateAt G x n t) (x.testBit (t + n + 1)) := by
  simp only [stateAt, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The bounds after `t` steps. -/
structure Fit (G N Q t : ℕ) (s : PS) : Prop where
  m : s.m ≤ 2
  r : s.r ≤ t
  k : s.k ≤ t * (G * G * N)
  f : s.f ≤ t * 2 ^ Q

theorem Fit.step {G N Q t : ℕ} {s : PS} (h : Fit G N Q t s) (ht : t < N) (hQ : N * (G * G * N) < Q) (b : Bool) :
    Fit G N Q (t + 1) (stepP G s b) := by
  obtain ⟨m, r, k, f⟩ := s
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only at h1 h2 h3 h4
  have hk : k < Q := lt_of_le_of_lt (h3.trans (Nat.mul_le_mul_right _ ht.le)) hQ
  have hp : 2 ^ k ≤ 2 ^ Q := Nat.pow_le_pow_right (by norm_num) hk.le
  have e1 : (t + 1) * (G * G * N) = t * (G * G * N) + G * G * N := by ring
  have e2 : (t + 1) * 2 ^ Q = t * 2 ^ Q + 2 ^ Q := by ring
  have hpQ : 0 < 2 ^ Q := by positivity
  have h3' : k ≤ (t + 1) * (G * G * N) := by omega
  have h4' : f ≤ (t + 1) * 2 ^ Q := by omega
  have hm : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  rcases hm with rfl | rfl | rfl
  · cases b <;> simp [stepP] <;> exact ⟨by simp, by simp; omega, h3', h4'⟩
  · cases b
    · simp only [stepP, Bool.false_eq_true, if_false]
      exact ⟨by simp, by simp; omega, by simp, by simp; omega⟩
    · simp only [stepP, if_true]
      exact ⟨by simp, by simp; omega, h3', h4'⟩
  · cases b
    · simp only [stepP, dstep, Bool.false_eq_true, if_false]
      by_cases hr : r = 0
      · simp only [hr, if_true]
        exact ⟨by simp, by simp, h3', h4'⟩
      · simp only [hr, if_false]
        refine ⟨by simp, by simp, ?_, h4'⟩
        simp only
        have h5 : k / G ≤ k := Nat.div_le_self _ _
        have h6 : G ^ 2 * (r / 2) ≤ G * G * N := by
          rw [pow_two]
          exact Nat.mul_le_mul_left _ (by omega)
        omega
    · simp only [stepP, dstep, if_true]
      exact ⟨by simp, by simp; omega, h3', h4'⟩

theorem fit_stateAt {G N Q x n t : ℕ} (ht : t ≤ N) (hQ : N * (G * G * N) < Q) :
    Fit G N Q t (stateAt G x n t) := by
  induction t with
  | zero => exact ⟨by simp [stateAt], by simp [stateAt], by simp [stateAt], by simp [stateAt]⟩
  | succ t ih =>
    rw [stateAt_succ]
    exact (ih (by omega)).step (by omega) hQ _

/-- The word of a state fits. -/
theorem pack_lt {G N Q t W : ℕ} {s : PS} (h : Fit G N Q t s) (ht : t ≤ N) (hNQ : N < Q)
    (hQ : N * (G * G * N) < Q) (hW : 3 * Q + N + 3 ≤ W) : pack Q s < 2 ^ W := by
  obtain ⟨m, r, k, f⟩ := s
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only at h1 h2 h3 h4
  have hr : r < Q := by omega
  have hk : k < Q := lt_of_le_of_lt (h3.trans (Nat.mul_le_mul_right _ ht)) hQ
  have hf : f + 1 ≤ 2 ^ N * 2 ^ Q := by
    have a1 : f ≤ N * 2 ^ Q := h4.trans (Nat.mul_le_mul_right _ ht)
    have a2 : N + 1 ≤ 2 ^ N := Nat.lt_two_pow_self
    have a3 : 1 ≤ 2 ^ Q := Nat.one_le_two_pow
    calc f + 1 ≤ N * 2 ^ Q + 1 * 2 ^ Q := by omega
      _ = (N + 1) * 2 ^ Q := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ a2
  have hQ2 : Q ≤ 2 ^ Q := Nat.lt_two_pow_self.le
  have b1 : k + Q * f + 1 ≤ Q * (f + 1) := by nlinarith
  have b2 : r + Q * (k + Q * f) + 1 ≤ Q * (Q * (f + 1)) := by nlinarith
  have b3 : m + 4 * (r + Q * (k + Q * f)) < 4 * (Q * (Q * (f + 1))) := by omega
  calc pack Q ⟨m, r, k, f⟩ < 4 * (Q * (Q * (f + 1))) := b3
    _ ≤ 2 ^ 2 * (2 ^ Q * (2 ^ Q * (2 ^ N * 2 ^ Q))) := by
      refine Nat.mul_le_mul (by norm_num) (Nat.mul_le_mul hQ2 (Nat.mul_le_mul hQ2 hf))
    _ = 2 ^ (2 + Q + Q + N + Q) := by ring
    _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)

/-! ### The loop -/

/-- The base of the fields of the state word. -/
def Qof (N : ℕ) : ℕ := (2 * N + 1) * (2 * N + 1) * ((2 * N + 1) * (2 * N + 1)) + 1

/-- The base of the fields, on `n :: x :: N :: _`. -/
def qE : Expr :=
  .letE (.add (.mul (.lit 2) (.var 2)) (.lit 1))
    (.add (.mul (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0))) (.lit 1))

/-- The word of the formula, on `n :: x :: N :: _`. -/
def encE : Expr :=
  .letE qE (.div (.div (.div (.fold (.var 3) (.lit 0) bodyE) (.lit 4)) (.var 0)) (.var 0))

theorem N_lt_Qof (N : ℕ) : N < Qof N := by
  simp only [Qof]
  nlinarith [Nat.zero_le N, Nat.zero_le (N * N), Nat.zero_le (N * N * N), Nat.zero_le (N * N * N * N)]

theorem bound_lt_Qof {n N : ℕ} (hn : n ≤ N) :
    N * ((2 * n + 1) * (2 * n + 1) * N) < Qof N := by
  have h1 : 2 * n + 1 ≤ 2 * N + 1 := by omega
  have h2 : N ≤ 2 * N + 1 := by omega
  have h3 : N * ((2 * n + 1) * (2 * n + 1) * N) ≤
      (2 * N + 1) * ((2 * N + 1) * (2 * N + 1) * (2 * N + 1)) :=
    Nat.mul_le_mul h2 (Nat.mul_le_mul (Nat.mul_le_mul h1 h1) h2)
  have h4 : (2 * N + 1) * ((2 * N + 1) * (2 * N + 1) * (2 * N + 1)) =
      (2 * N + 1) * (2 * N + 1) * ((2 * N + 1) * (2 * N + 1)) := by ring
  simp only [Qof]
  omega

theorem run_qE {W x n N : ℕ} {T : List ℕ} (hW : 8 ≤ W) (hQ : Qof N < 2 ^ W) :
    Run W qE (n :: x :: N :: T) (Qof N) 16 := by
  have h2 : (2 : ℕ) < 2 ^ W := by
    calc 2 < 2 ^ 8 := by norm_num
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW
  have hG : 2 * N + 1 ≤ Qof N := by
    simp only [Qof]; nlinarith [Nat.zero_le N, Nat.zero_le (N * N), Nat.zero_le (N * N * N), Nat.zero_le (N * N * N * N)]
  have hGG : (2 * N + 1) * (2 * N + 1) ≤ Qof N := by
    simp only [Qof]
    nlinarith [Nat.zero_le ((2 * N + 1) * (2 * N + 1)), Nat.mul_le_mul (show 1 ≤ 2 * N + 1 by omega)
      (show 1 ≤ 2 * N + 1 by omega)]
  have hGG4 : (2 * N + 1) * (2 * N + 1) * ((2 * N + 1) * (2 * N + 1)) + 1 = Qof N := rfl
  have a1 : Run W (.add (.mul (.lit 2) (.var 2)) (.lit 1)) (n :: x :: N :: T) (2 * N + 1) 5 :=
    (run_add (run_mul (run_lit h2) (run_var (by simp)) (by omega)) (run_one (by omega)) (by omega)).mono (by omega)
  set E := (2 * N + 1) :: n :: x :: N :: T
  have v0 : Run W (.var 0) E (2 * N + 1) 1 := run_var (by simp [E])
  have a2 := run_mul v0 v0 (by omega)
  have a3 := run_mul a2 a2 (by omega)
  have a4 := run_add a3 (run_one (by omega)) hQ
  exact (run_let a1 a4).mono (by omega)

/-- The loop of the parser computes the state word. -/
theorem run_foldP {W n x N : ℕ} {T : List ℕ} (hC : Ctx W n) (hn : n ≤ N) (hW : 3 * Qof N + N + 3 ≤ W)
    (hW2 : N + n + 1 < W) :
    Run W (.fold (.var 3) (.lit 0) bodyE) (Qof N :: n :: x :: N :: T)
      (pack (Qof N) (stateAt (2 * n + 1) x n N)) (3 + N * 201) := by
  have hQ := bound_lt_Qof hn
  have hNQ := N_lt_Qof N
  have hQpos : 1 ≤ Qof N := by omega
  have := run_fold (W := W) (env := Qof N :: n :: x :: N :: T) (b := bodyE) (n := .var 3) (s := .lit 0)
    (B := 200) (g := fun k => pack (Qof N) (stateAt (2 * n + 1) x n k)) (N := N) (Bn := 1) (Bs := 1)
    (run_var (by simp)) (by simpa [stateAt, pack] using run_zero (W := W) (env := Qof N :: n :: x :: N :: T) hC.one_le)
    (fun k hk => by
      have f0 := fit_stateAt (G := 2 * n + 1) (x := x) (n := n) (t := k) hk.le hQ
      have f1 := fit_stateAt (G := 2 * n + 1) (x := x) (n := n) (t := k + 1) hk hQ
      have p0 := pack_lt f0 hk.le hNQ hQ hW
      have p1 := pack_lt f1 hk hNQ hQ hW
      rw [stateAt_succ] at p1 ⊢
      have hkQ : (stateAt (2 * n + 1) x n k).k < Qof N :=
        lt_of_le_of_lt (f0.k.trans (Nat.mul_le_mul_right _ hk.le)) hQ
      exact run_bodyE hC hQpos f0.m (by have := f0.r; omega) hkQ (by omega) (by omega) p0 p1)
  exact this.mono (by omega)

/-! ### The encoding -/

/-- The bits that the loop reads, for the input `encodeNat n ++ body`. -/
theorem read_bits (n : ℕ) (body : List Bool) :
    (List.range ((encodeNat n ++ body).length)).map
        (fun p => (BinaryArithmetic.toNat (encodeNat n ++ body)).testBit (p + n + 1)) =
      body ++ List.replicate (n + 1) false := by
  have hg : ∀ p, (encodeNat n ++ body).getD (p + n + 1) false = body.getD p false := by
    intro p
    have hlen : (encodeNat n).length = n + 1 := length_encodeNat n
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega)]
    congr 2
    omega
  simp only [testBit_toNat, hg]
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    by_cases hi : i < body.length
    · rw [List.getElem_append_left hi, List.getD_eq_getElem _ _ hi]
    · rw [List.getElem_append_right (by omega), List.getElem_replicate,
        List.getD_eq_default _ _ (by omega)]

/-- **The parser.** With `x` the value of the input bits and `N` their number, `nE` and `encE` compute `n` and the
word of the formula, when the word size is large enough. -/
theorem parse_main {n : ℕ} (F : SAT.CNF (Fin n)) (hw : SAT.WidthAtMost 3 F) {W : ℕ}
    (hW : 3 * Qof (encodeCNF F).length + (encodeCNF F).length + 3 ≤ W)
    (hC2 : (2 * (encodeCNF F).length + 2) ^ 3 ≤ W) :
    Run W nE [BinaryArithmetic.toNat (encodeCNF F), (encodeCNF F).length] n (3 + (encodeCNF F).length * 12) ∧
    Run W encE [n, BinaryArithmetic.toNat (encodeCNF F), (encodeCNF F).length] (encF n (toCNF F))
      (50 + (encodeCNF F).length * 201) := by
  set N := (encodeCNF F).length with hN
  set x := BinaryArithmetic.toNat (encodeCNF F) with hx
  have hNn : n ≤ N := numVariables_le_formulaBitLength F
  have hNQ := N_lt_Qof N
  have hlen : N = (encodeNat n ++ encodeCNFBody F).length := rfl
  have hCtx : Ctx W n := ⟨(Nat.pow_le_pow_left (by omega) 3).trans hC2⟩
  have hW8 := hCtx.eight_le
  constructor
  · refine run_nE hCtx.two_le (fun i hi => ?_) ?_ hNn (by omega)
    · rw [hx, testBit_toNat, encodeCNF, encodeNat, List.append_assoc,
        List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hi)]
      simp [hi]
    · rw [hx, testBit_toNat, encodeCNF, encodeNat, List.append_assoc,
        List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
      simp
  · have hQlt : Qof N < 2 ^ W := by
      refine lt_trans ?_ Nat.lt_two_pow_self
      omega
    have h4 : (4 : ℕ) < 2 ^ W := by
      calc 4 < 2 ^ 8 := by norm_num
        _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW8
    have a0 := run_qE (x := x) (n := n) (N := N) (T := []) hW8 hQlt
    have a1 := run_foldP (x := x) (T := []) hCtx hNn hW (by omega)
    have hst : stateAt (2 * n + 1) x n N = ⟨0, 0, 0, encF n (toCNF F)⟩ := by
      have e1 : (List.range N).foldl (fun s p => stepP (2 * n + 1) s (x.testBit (p + n + 1))) ⟨0, 0, 0, 0⟩ =
          ((List.range N).map fun p => x.testBit (p + n + 1)).foldl (stepP (2 * n + 1)) ⟨0, 0, 0, 0⟩ := by
        rw [List.foldl_map]
      rw [stateAt, e1, hx, hN, encodeCNF, read_bits, parse_spec hw]
    rw [hst] at a1
    set f := encF n (toCNF F) with hf
    have hQpos : 0 < Qof N := by omega
    have a2 := run_div a1 (run_lit (m := 4) h4)
    have v : ∀ {w : ℕ}, Run W (.var 0) (Qof N :: n :: x :: N :: []) (Qof N) 1 := fun {_} => run_var (by simp)
    have a3 := run_div a2 (v (w := 0))
    have a4 := run_div a3 (v (w := 0))
    have e : pack (Qof N) ⟨0, 0, 0, f⟩ / 4 / Qof N / Qof N = f := by
      simp only [pack]
      rw [zero_add, Nat.mul_div_cancel_left _ (by norm_num), zero_add, Nat.mul_div_cancel_left _ hQpos,
        zero_add, Nat.mul_div_cancel_left _ hQpos]
    rw [e] at a4
    exact (run_let a0 a4).mono (by omega)

end TransposeBase.Machine.Parse
