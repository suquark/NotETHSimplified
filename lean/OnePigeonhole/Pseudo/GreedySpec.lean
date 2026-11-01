import OnePigeonhole.Greedy
import TransposeBase.Pseudo.LeafRun

/-!
# The placement as a program

* `greedy_spec`: the value of `greedyE` is `Greedy.table`, and its cost is at most `greedyK Q K * (m + v + 1) ^ 3`, for `K = L ^ Q`.
* `run_layTE`: the value of `layTE` is the table of the layers `Greedy.layN`, and its cost is at most `layCost m`.
* `run_hE`: the value of `hE` is the number of layers.

The sizes come from `Place.Bd`, and the tables of the wires from `Place.NetT`.
-/

namespace OnePigeonhole.Pseudo

open Finset TransposeBase.Pseudo TransposeBase.Pseudo.Leaf TransposeBase.Pseudo.Code
open TransposeBase.Pseudo.Place (fld Bd NetT fieldE setE eval_fieldE ops_fieldE eval_setE ops_setE)

/-! ### The programs -/

/-- `Greedy.load`: the number of wires with head below `α`, tail word `x` and head word `y`. -/
def loadE (im it ih ifw iR iα ix iy : ℕ) : Expr :=
  .sum (.var im) <|
    .letE (fieldE (it + 1) 0 (ifw + 1)) <|
    .letE (fieldE (ih + 2) 1 (ifw + 2)) <|
      .ite (.var (iα + 3)) (.var 0) (.lit 0) <|
        eqX (fieldE (iR + 3) 1 (ifw + 3)) (.var (ix + 3))
          (eqX (fieldE (iR + 3) 0 (ifw + 3)) (.var (iy + 3)) (.lit 1) (.lit 0))
          (.lit 0)

/-- `Greedy.score`: the sum of the loads from the words of the tails of `α` towards the word `y`. -/
def scoreE (im it ih ifw iR iα iy : ℕ) : Expr :=
  .sum (.var im) <|
    eqX (fieldE (ih + 1) 0 (ifw + 1)) (.var (iα + 1))
      (.letE (fieldE (it + 1) 0 (ifw + 1)) <|
       .letE (fieldE (iR + 2) 0 (ifw + 2)) <|
         loadE (im + 3) (it + 3) (ih + 3) (ifw + 3) (iR + 3) (iα + 3) 0 (iy + 3))
      (.lit 0)

/-- `Greedy.clash`. The variables hold `Q`, `L`, `m`, the tables of the tails and the heads, `fw`, the table `R`, the node and the word. -/
def clashE (iQ iL im it ih ifw iR iα iy : ℕ) : Expr :=
  .sum (.var im) <|
    eqX (fieldE (ih + 1) 0 (ifw + 1)) (.var (iα + 1))
      (.letE (fieldE (it + 1) 0 (ifw + 1)) <|
       .letE (fieldE (iR + 2) 0 (ifw + 2)) <|
         .sum (.var (iQ + 3)) <|
           eqX (digE 1 (iL + 4) 0) (digE (iy + 4) (iL + 4) 0) (.lit 1) (.lit 0))
      (.lit 0)

/-- `Greedy.adj`. -/
def adjE (iQ iL im it ih ifw iR iα iy : ℕ) : Expr :=
  .ite (clashE iQ iL im it ih ifw iR iα iy) (.lit 0)
    (scoreE im it ih ifw iR iα iy)
    (.add (.mul (.var im) (.var im)) (.lit 1))

/-- `Greedy.best`: the first word below `L ^ Q` with the minimal `adj`. The state of the loop is the best word so far. -/
def pickE (Q L iQ iL im it ih ifw iR iα : ℕ) : Expr :=
  .fold (.lit (L ^ Q)) (.lit 0) <|
    .ite (adjE (iQ + 2) (iL + 2) (im + 2) (it + 2) (ih + 2) (ifw + 2) (iR + 2) (iα + 2) 0)
      (adjE (iQ + 2) (iL + 2) (im + 2) (it + 2) (ih + 2) (ifw + 2) (iR + 2) (iα + 2) 1)
      (.var 0) (.var 1)

/-- `Greedy.table`: the words of all nodes. A node below `n` gets `α % L ^ Q`, and the other nodes get the word of `pickE`. The state of
the loop is the table of the nodes below `α`. -/
def greedyE (Q L inn im iv ifw it ih : ℕ) : Expr :=
  .letE (.lit Q) <| .letE (.lit L) <|
  .fold (.var (iv + 2)) (.lit 0) <|
    .letE
      (.ite (.var (inn + 4)) (.var 1)
        (pickE Q L 3 2 (im + 4) (it + 4) (ih + 4) (ifw + 4) 0 1)
        (.mod (.var 1) (.lit (L ^ Q)))) <|
      setE 1 0 2 (ifw + 5)

/-- The word of an end of the wire in the variable `i`: field `i` of the table `iT` is a node, and its field of the table `iR` is the word. -/
def wireWordE (iT ifw iR i : ℕ) : Expr := .letE (fieldE iT i ifw) (fieldE (iR + 1) 0 (ifw + 1))

/-- `Greedy.layN`, for the wire in the variable `ie`. -/
def layE (im it ih ifw iR ie : ℕ) : Expr :=
  .letE (wireWordE it ifw iR ie) <|
  .letE (wireWordE (ih + 1) (ifw + 1) (iR + 1) (ie + 1)) <|
  .sum (.var (im + 2)) <|
    .ite (.add (.var 0) (.lit 1)) (.var (ie + 3))
      (eqX (wireWordE (it + 3) (ifw + 3) (iR + 3) 0) (.var 2)
        (eqX (wireWordE (ih + 3) (ifw + 3) (iR + 3) 0) (.var 1) (.lit 1) (.lit 0))
        (.lit 0))
      (.lit 0)

/-- The table of the layers. -/
def layTE (im it ih ifw iR : ℕ) : Expr :=
  .sum (.var im) <|
    .mul (layE (im + 1) (it + 1) (ih + 1) (ifw + 1) (iR + 1) 0) (.pow2 (.mul (.var 0) (.var (ifw + 1))))

/-- The number of layers `Greedy.capB n K D`, for `n` in the variable `inn`. -/
def hE (K D inn : ℕ) : Expr :=
  .add (.div (.mul (.lit 6) (.mul (.add (.div (.var inn) (.lit K)) (.lit 1)) (.lit D))) (.lit K)) (.lit 3)

/-! ### The costs -/

/-- The bound on the operations of `loadE`. -/
def loadCost (m : ℕ) : ℕ := 1 + 1 + m * (100 + 1)

/-- The bound on the operations of `scoreE`. -/
def scoreCost (m : ℕ) : ℕ := 1 + 1 + m * (64 + 2 * loadCost m + 1)

/-- The bound on the operations of the sum over the digits in `clashE`. -/
def clashIn (Q : ℕ) : ℕ := 1 + 1 + Q * ((2 + 2 * ((6 + Q * 2) + (6 + Q * 2)) + 2 * (1 + 1)) + 1)

/-- The bound on the operations of the body of `clashE`. -/
def clashBody (Q : ℕ) : ℕ := 2 + 2 * (9 + 1) + 2 * ((1 + 9 + (1 + 9 + clashIn Q)) + 1)

/-- The bound on the operations of `clashE`. -/
def clashCost (Q m : ℕ) : ℕ := 1 + 1 + m * (clashBody Q + 1)

/-- The bound on the operations of `adjE`. -/
def adjCost (Q m : ℕ) : ℕ := 1 + clashCost Q m + 1 + (scoreCost m + (1 + (1 + 1 + 1) + 1))

/-- The bound on the operations of `pickE`. -/
def pickCost (Q K m : ℕ) : ℕ := 1 + 1 + 1 + K * ((1 + adjCost Q m + adjCost Q m + (1 + 1)) + 1)

/-- The bound on the operations of `greedyE`. -/
def greedyCost (Q K m v : ℕ) : ℕ :=
  1 + 1 + (1 + 1 + (1 + 1 + 1 + v * ((1 + (1 + 1 + 1 + (pickCost Q K m + (1 + 1 + 1))) + 8) + 1)))

/-- The constant of `greedyE`. -/
def greedyK (Q K : ℕ) : ℕ := (K + 1) * (2 * (69 + 2 * clashIn Q) + 590)

/-- The bound on the operations of `wireWordE`. -/
def wireWordCost : ℕ := 1 + 9 + 9

/-- The bound on the operations of the body of the sum in `layE`. -/
def layBody : ℕ :=
  1 + (1 + 1 + 1) + 1 +
    ((2 + 2 * (wireWordCost + 1) + 2 * ((2 + 2 * (wireWordCost + 1) + 2 * (1 + 1)) + 1)) + 1)

/-- The bound on the operations of `layE`. -/
def layOne (m : ℕ) : ℕ := 1 + wireWordCost + (1 + wireWordCost + (1 + 1 + m * (layBody + 1)))

/-- The bound on the operations of `layTE`. -/
def layCost (m : ℕ) : ℕ := 1 + 1 + m * ((1 + layOne m + (1 + (1 + 1 + 1))) + 1)

namespace GreedySpec

variable {W m v fw Q L tT hT : ℕ} {tail head : Fin m → Fin v}

/-- A loop with a state. The states are the values of `T`. -/
theorem run_fold {a s b : Expr} {env : List ℕ} {k ca cs B : ℕ} {T : ℕ → ℕ} (ha : Run W a env k ca)
    (hs : Run W s env (T 0) cs) (h : ∀ i < k, Run W b (T i :: i :: env) (T (i + 1)) B) :
    Run W (.fold a s b) env (T k) (1 + ca + cs + k * (B + 1)) := by
  have key : ∀ j ≤ k, (List.range j).foldl (fun st i => eval W b (st :: i :: env)) (T 0) = T j := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih (by omega)]
      exact (h j (by omega)).1
  refine ⟨by rw [eval_fold, ha.1, hs.1]; exact key k le_rfl, ?_⟩
  have h1 := ops_fold_le W a s b env (fun i st => st = T i) (B := B) hs.1
    (fun i st hi hst => by
      subst hst
      rw [ha.1] at hi
      exact (h i hi).1)
    (fun i st hi hst => by
      subst hst
      rw [ha.1] at hi
      exact (h i hi).2)
  rw [ha.1] at h1
  have := ha.2
  have := hs.2
  omega

theorem run_field {K : ℕ} (B : Bd W m v fw K) {t i f tv iv : ℕ} {env : List ℕ} (ht : env.getD t 0 = tv)
    (hi : env.getD i 0 = iv) (hf : env.getD f 0 = fw) (hiv : iv < v) :
    Run W (fieldE t i f) env (fld fw tv iv) 9 :=
  ⟨eval_fieldE ht hi hf (B.idx_lt (by omega)) B.fw_lt, (ops_fieldE W t i f env).le⟩

/-! ### Reading the tables of the wires -/

theorem load_eq_range (N : NetT fw tT hT tail head) (R α x y : ℕ) :
    Greedy.load fw tail head R α x y =
      ∑ i ∈ range m, if fld fw hT i < α ∧ fld fw R (fld fw tT i) = x ∧ fld fw R (fld fw hT i) = y then 1 else 0 := by
  rw [Finset.sum_range]
  refine sum_congr rfl fun e _ => ?_
  rw [N.tail_eq, N.head_eq]

theorem score_eq_range (N : NetT fw tT hT tail head) (R α y : ℕ) :
    Greedy.score fw tail head R α y =
      ∑ i ∈ range m, if fld fw hT i = α then Greedy.load fw tail head R α (fld fw R (fld fw tT i)) y else 0 := by
  rw [Finset.sum_range]
  refine sum_congr rfl fun e _ => ?_
  rw [N.tail_eq, N.head_eq]

theorem load_le (R α x y : ℕ) : Greedy.load fw tail head R α x y ≤ m := by
  calc Greedy.load fw tail head R α x y ≤ ∑ _e : Fin m, 1 := sum_le_sum fun e _ => by split_ifs <;> omega
    _ = m := by simp

/-! ### The values -/

theorem clash_eq_range (N : NetT fw tT hT tail head) (R α y : ℕ) :
    Greedy.clash fw Q L tail head R α y =
      ∑ i ∈ range m, if fld fw hT i = α then
        ∑ j ∈ range Q, (if dig L (fld fw R (fld fw tT i)) j = dig L y j then 1 else 0) else 0 := by
  rw [Finset.sum_range]
  refine sum_congr rfl fun e _ => ?_
  rw [N.tail_eq, N.head_eq]

/-- `clash` is at most the number of wires times the number of digits. -/
theorem clash_le (R α y : ℕ) : Greedy.clash fw Q L tail head R α y ≤ m * Q := by
  have h1 : ∀ x, ∑ j ∈ range Q, (if dig L x j = dig L y j then 1 else 0) ≤ Q := fun x => by
    calc _ ≤ ∑ _j ∈ range Q, 1 := sum_le_sum fun j _ => by split_ifs <;> omega
      _ = Q := by simp
  calc Greedy.clash fw Q L tail head R α y ≤ ∑ _e : Fin m, Q := sum_le_sum fun e _ => by
        split_ifs
        · exact h1 _
        · omega
    _ = m * Q := by simp

section Run

variable {iQ iL im it ih ifw iR iα : ℕ} {env : List ℕ} {R α : ℕ}

theorem run_loadE {K : ℕ} (B : Bd W m v fw K) (N : NetT fw tT hT tail head) {ix iy x y : ℕ}
    (hm : env.getD im 0 = m) (ht : env.getD it 0 = tT) (hh : env.getD ih 0 = hT) (hf : env.getD ifw 0 = fw)
    (hR : env.getD iR 0 = R) (hα : env.getD iα 0 = α) (hx : env.getD ix 0 = x) (hy : env.getD iy 0 = y) :
    Run W (loadE im it ih ifw iR iα ix iy) env (Greedy.load fw tail head R α x y) (loadCost m) := by
  rw [load_eq_range N]
  refine Run.sum (Run.var hm) le_rfl (B := 100) (fun i hi => ?_) ?_
  · have htv : fld fw tT i < v := by
      have := N.tail_eq ⟨i, hi⟩
      simp only at this
      rw [this]
      exact (tail _).2
    have hhv : fld fw hT i < v := by
      have := N.head_eq ⟨i, hi⟩
      simp only at this
      rw [this]
      exact (head _).2
    have him : i < v + m := by omega
    have hl1 : (1 : ℕ) < 2 ^ W := B.one_lt
    have h0 : (0 : ℕ) < 2 ^ W := by positivity
    have r1 : Run W (fieldE (it + 1) 0 (ifw + 1)) (i :: env) (fld fw tT i) 9 :=
      ⟨eval_fieldE (by simpa using ht) (by simp) (by simpa using hf) (B.idx_lt (by omega)) B.fw_lt,
        (ops_fieldE W _ _ _ _).le⟩
    have r2 : Run W (fieldE (ih + 2) 1 (ifw + 2)) (fld fw tT i :: i :: env) (fld fw hT i) 9 :=
      ⟨eval_fieldE (by simpa using hh) (by simp) (by simpa using hf) (B.idx_lt (by omega)) B.fw_lt,
        (ops_fieldE W _ _ _ _).le⟩
    generalize hE : fld fw hT i :: fld fw tT i :: i :: env = E
    have r3 : Run W (fieldE (iR + 3) 1 (ifw + 3)) E (fld fw R (fld fw tT i)) 9 :=
      run_field B (by rw [← hE]; simpa using hR) (by rw [← hE]; rfl) (by rw [← hE]; simpa using hf) htv
    have r4 : Run W (fieldE (iR + 3) 0 (ifw + 3)) E (fld fw R (fld fw hT i)) 9 :=
      run_field B (by rw [← hE]; simpa using hR) (by rw [← hE]; rfl) (by rw [← hE]; simpa using hf) hhv
    have vx : Run W (.var (ix + 3)) E x 1 := Run.var (by rw [← hE]; simpa using hx)
    have vy : Run W (.var (iy + 3)) E y 1 := Run.var (by rw [← hE]; simpa using hy)
    have l0 : Run W (.lit 0) E 0 1 := Run.lit h0
    have l1 : Run W (.lit 1) E 1 1 := Run.lit hl1
    have c1 : Run W (eqX (fieldE (iR + 3) 0 (ifw + 3)) (.var (iy + 3)) (.lit 1) (.lit 0)) E
        (if fld fw R (fld fw hT i) = y then 1 else 0) (2 + 2 * (9 + 1) + 2 * (1 + 1)) :=
      Run.eqX r4 vy (fun h => l1.eq (if_pos h).symm) (fun h => l0.eq (if_neg h).symm)
    have c2 : Run W (eqX (fieldE (iR + 3) 1 (ifw + 3)) (.var (ix + 3))
          (eqX (fieldE (iR + 3) 0 (ifw + 3)) (.var (iy + 3)) (.lit 1) (.lit 0)) (.lit 0)) E
        (if fld fw R (fld fw tT i) = x ∧ fld fw R (fld fw hT i) = y then 1 else 0)
        (2 + 2 * (9 + 1) + 2 * ((2 + 2 * (9 + 1) + 2 * (1 + 1)) + 1)) :=
      Run.eqX r3 vx (fun h => c1.eq (by simp [h])) (fun h => l0.eq (by simp [h]))
    have c3 : Run W (.ite (.var (iα + 3)) (.var 0) (.lit 0)
          (eqX (fieldE (iR + 3) 1 (ifw + 3)) (.var (ix + 3))
            (eqX (fieldE (iR + 3) 0 (ifw + 3)) (.var (iy + 3)) (.lit 1) (.lit 0)) (.lit 0))) E
        (if fld fw hT i < α ∧ fld fw R (fld fw tT i) = x ∧ fld fw R (fld fw hT i) = y then 1 else 0)
        (1 + 1 + 1 + (1 + (2 + 2 * (9 + 1) + 2 * ((2 + 2 * (9 + 1) + 2 * (1 + 1)) + 1)))) :=
      Run.ite (x := α) (y := fld fw hT i) (Run.var (by rw [← hE]; simpa using hα)) (Run.var (by rw [← hE]; rfl))
        (fun h => l0.eq (if_neg fun hh => by have := hh.1; omega).symm)
        (fun h => c2.eq (by
          have h' : fld fw hT i < α := not_le.mp h
          simp [h']))
    subst hE
    exact (Run.letE r1 (Run.letE r2 c3)).mono (by norm_num)
  · refine lt_of_le_of_lt ?_ (B.m_lt.trans B.pow_lt)
    rw [← load_eq_range N]
    exact load_le _ _ _ _

theorem run_scoreE {K : ℕ} (B : Bd W m v fw K) (N : NetT fw tT hT tail head) {iy y : ℕ}
    (hm : env.getD im 0 = m) (ht : env.getD it 0 = tT) (hh : env.getD ih 0 = hT) (hf : env.getD ifw 0 = fw)
    (hR : env.getD iR 0 = R) (hα : env.getD iα 0 = α) (hy : env.getD iy 0 = y) :
    Run W (scoreE im it ih ifw iR iα iy) env (Greedy.score fw tail head R α y) (scoreCost m) := by
  rw [score_eq_range N]
  refine Run.sum (Run.var hm) le_rfl (B := 64 + 2 * loadCost m) (fun i hi => ?_) ?_
  · have htv : fld fw tT i < v := by
      have := N.tail_eq ⟨i, hi⟩
      simp only at this
      rw [this]
      exact (tail _).2
    have r1 : Run W (fieldE (ih + 1) 0 (ifw + 1)) (i :: env) (fld fw hT i) 9 :=
      ⟨eval_fieldE (by simpa using hh) (by simp) (by simpa using hf) (B.idx_lt (by omega)) B.fw_lt,
        (ops_fieldE W _ _ _ _).le⟩
    have r2 : Run W (fieldE (it + 1) 0 (ifw + 1)) (i :: env) (fld fw tT i) 9 :=
      ⟨eval_fieldE (by simpa using ht) (by simp) (by simpa using hf) (B.idx_lt (by omega)) B.fw_lt,
        (ops_fieldE W _ _ _ _).le⟩
    have r3 : Run W (fieldE (iR + 2) 0 (ifw + 2)) (fld fw tT i :: i :: env) (fld fw R (fld fw tT i)) 9 :=
      run_field B (by simpa using hR) (by simp) (by simpa using hf) htv
    generalize hE : fld fw R (fld fw tT i) :: fld fw tT i :: i :: env = E
    have r4 : Run W (loadE (im + 3) (it + 3) (ih + 3) (ifw + 3) (iR + 3) (iα + 3) 0 (iy + 3)) E
        (Greedy.load fw tail head R α (fld fw R (fld fw tT i)) y) (loadCost m) :=
      run_loadE B N (by rw [← hE]; simpa using hm) (by rw [← hE]; simpa using ht) (by rw [← hE]; simpa using hh)
        (by rw [← hE]; simpa using hf) (by rw [← hE]; simpa using hR) (by rw [← hE]; simpa using hα)
        (by rw [← hE]; rfl) (by rw [← hE]; simpa using hy)
    subst hE
    have r5 := Run.letE r2 (Run.letE r3 r4)
    have l0 : Run W (.lit 0) (i :: env) 0 1 := Run.lit (by positivity)
    have vα : Run W (.var (iα + 1)) (i :: env) α 1 := Run.var (by simpa using hα)
    have r6 := Run.eqX (r := if fld fw hT i = α then Greedy.load fw tail head R α (fld fw R (fld fw tT i)) y else 0)
      r1 vα (fun h => r5.eq (if_pos h).symm) (fun h => l0.eq (if_neg h).symm)
    exact r6.mono (by omega)
  · rw [← score_eq_range N]
    exact lt_of_le_of_lt (Greedy.score_le _ _ _) (B.mul_lt B.m_lt B.m_lt)

theorem pow_small (B : Bd W m v fw (L ^ Q)) (hL : 0 < L) {j : ℕ} (hj : j ≤ Q) : L ^ j < 2 ^ W :=
  lt_of_le_of_lt (Nat.pow_le_pow_right hL hj) B.lit_K

/-- `Q` is below the number of words, for `2 ≤ L`. -/
theorem Q_lt_pow (hL : 2 ≤ L) : Q < L ^ Q :=
  Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_left hL Q)

theorem run_clashE (B : Bd W m v fw (L ^ Q)) (hL : 2 ≤ L) (N : NetT fw tT hT tail head) {iy y : ℕ}
    (hQv : env.getD iQ 0 = Q) (hLv : env.getD iL 0 = L) (hm : env.getD im 0 = m) (ht : env.getD it 0 = tT)
    (hh : env.getD ih 0 = hT) (hf : env.getD ifw 0 = fw) (hR : env.getD iR 0 = R) (hα : env.getD iα 0 = α)
    (hy : env.getD iy 0 = y) :
    Run W (clashE iQ iL im it ih ifw iR iα iy) env (Greedy.clash fw Q L tail head R α y) (clashCost Q m) := by
  have hl1 : (1 : ℕ) < 2 ^ W := B.one_lt
  have h0 : (0 : ℕ) < 2 ^ W := by positivity
  have hQK : Q < 2 ^ fw := (Q_lt_pow hL).trans B.K_lt
  have hmQ : m * Q < 2 ^ W := B.mul_lt B.m_lt hQK
  have hbig : Greedy.clash fw Q L tail head R α y < 2 ^ W := lt_of_le_of_lt (clash_le R α y) hmQ
  rw [clash_eq_range N] at hbig ⊢
  refine Run.sum (B := clashBody Q) (Run.var hm) le_rfl (fun i hi => ?_) hbig
  have htv : fld fw tT i < v := by
    have := N.tail_eq ⟨i, hi⟩
    simp only at this
    rw [this]
    exact (tail _).2
  have him : i < v + m := by omega
  have r1 : Run W (fieldE (ih + 1) 0 (ifw + 1)) (i :: env) (fld fw hT i) 9 :=
    ⟨eval_fieldE (by simpa using hh) (by simp) (by simpa using hf) (B.idx_lt (by omega)) B.fw_lt,
      (ops_fieldE W _ _ _ _).le⟩
  have r2 : Run W (fieldE (it + 1) 0 (ifw + 1)) (i :: env) (fld fw tT i) 9 :=
    ⟨eval_fieldE (by simpa using ht) (by simp) (by simpa using hf) (B.idx_lt (by omega)) B.fw_lt,
      (ops_fieldE W _ _ _ _).le⟩
  have r3 : Run W (fieldE (iR + 2) 0 (ifw + 2)) (fld fw tT i :: i :: env) (fld fw R (fld fw tT i)) 9 :=
    run_field B (by simpa using hR) (by simp) (by simpa using hf) htv
  generalize hx : fld fw R (fld fw tT i) = x at r3 ⊢
  have hle : ∑ j ∈ range Q, (if dig L x j = dig L y j then 1 else 0) ≤ Q := by
    calc _ ≤ ∑ _j ∈ range Q, 1 := sum_le_sum fun j _ => by split_ifs <;> omega
      _ = Q := by simp
  have hLp : 0 < L := by omega
  have r4 : Run W (.sum (.var (iQ + 3)) (eqX (digE 1 (iL + 4) 0) (digE (iy + 4) (iL + 4) 0) (.lit 1) (.lit 0)))
      (x :: fld fw tT i :: i :: env) (∑ j ∈ range Q, if dig L x j = dig L y j then 1 else 0) (clashIn Q) := by
    refine Run.sum (Run.var (by simpa using hQv)) le_rfl (fun j hj => ?_)
      (lt_of_le_of_lt hle (hQK.trans B.pow_lt))
    have hjQ : j ≤ Q := hj.le
    have d1 : Run W (digE 1 (iL + 4) 0) (j :: x :: fld fw tT i :: i :: env) (dig L x j) (6 + Q * 2) :=
      Run.digE rfl (by simpa using hLv) rfl hjQ (pow_small B hLp hjQ)
    have d2 : Run W (digE (iy + 4) (iL + 4) 0) (j :: x :: fld fw tT i :: i :: env) (dig L y j) (6 + Q * 2) :=
      Run.digE (by simpa using hy) (by simpa using hLv) rfl hjQ (pow_small B hLp hjQ)
    exact Run.eqX d1 d2 (fun e => (Run.lit hl1).eq (if_pos e).symm) (fun e => (Run.lit h0).eq (if_neg e).symm)
  have r5 := Run.letE r2 (Run.letE r3 r4)
  have vα : Run W (.var (iα + 1)) (i :: env) α 1 := Run.var (by simpa using hα)
  have r6 := Run.eqX (r := if fld fw hT i = α then
      ∑ j ∈ range Q, (if dig L x j = dig L y j then 1 else 0) else 0) r1 vα
    (fun h => r5.eq (if_pos h).symm) (fun h => (Run.lit h0).eq (if_neg h).symm)
  exact r6.mono (by simp only [clashBody]; omega)

theorem run_adjE (B : Bd W m v fw (L ^ Q)) (hL : 2 ≤ L) (N : NetT fw tT hT tail head) {iy y : ℕ}
    (hQv : env.getD iQ 0 = Q) (hLv : env.getD iL 0 = L) (hm : env.getD im 0 = m) (ht : env.getD it 0 = tT)
    (hh : env.getD ih 0 = hT) (hf : env.getD ifw 0 = fw) (hR : env.getD iR 0 = R) (hα : env.getD iα 0 = α)
    (hy : env.getD iy 0 = y) :
    Run W (adjE iQ iL im it ih ifw iR iα iy) env (Greedy.adj fw Q L tail head R α y) (adjCost Q m) := by
  have hl1 : (1 : ℕ) < 2 ^ W := B.one_lt
  have h0 : (0 : ℕ) < 2 ^ W := by positivity
  have hm1 : m + 1 < 2 ^ fw := by
    have h1 := B.hfw
    have h2 := B.hK
    omega
  have hmm : (m + 1) * (m + 1) < 2 ^ W := B.mul_lt hm1 hm1
  have hb : m * m + 1 ≤ (m + 1) * (m + 1) := by nlinarith
  have r1 := run_clashE (iy := iy) (y := y) B hL N hQv hLv hm ht hh hf hR hα hy
  have r2 := run_scoreE (iy := iy) (y := y) B N hm ht hh hf hR hα hy
  have r3 : Run W (.add (.mul (.var im) (.var im)) (.lit 1)) env (m * m + 1) (1 + (1 + 1 + 1) + 1) :=
    Run.add (Run.mul (Run.var hm) (Run.var hm) (by omega)) (Run.lit hl1) (by omega)
  exact Run.ite r1 (Run.lit h0) (fun h => r2.eq (if_pos h).symm) (fun h => r3.eq (if_neg h).symm)

theorem run_pickE (B : Bd W m v fw (L ^ Q)) (hL : 2 ≤ L) (N : NetT fw tT hT tail head)
    (hQv : env.getD iQ 0 = Q) (hLv : env.getD iL 0 = L) (hm : env.getD im 0 = m) (ht : env.getD it 0 = tT)
    (hh : env.getD ih 0 = hT) (hf : env.getD ifw 0 = fw) (hR : env.getD iR 0 = R) (hα : env.getD iα 0 = α) :
    Run W (pickE Q L iQ iL im it ih ifw iR iα) env (Greedy.best fw Q L tail head R α (L ^ Q)) (pickCost Q (L ^ Q) m) := by
  have hbody : ∀ y < L ^ Q, Run W (.ite (adjE (iQ + 2) (iL + 2) (im + 2) (it + 2) (ih + 2) (ifw + 2) (iR + 2) (iα + 2) 0)
      (adjE (iQ + 2) (iL + 2) (im + 2) (it + 2) (ih + 2) (ifw + 2) (iR + 2) (iα + 2) 1) (.var 0) (.var 1))
      (Greedy.best fw Q L tail head R α y :: y :: env) (Greedy.best fw Q L tail head R α (y + 1))
      (1 + adjCost Q m + adjCost Q m + (1 + 1)) := by
    intro y _
    generalize hb : Greedy.best fw Q L tail head R α y = b
    generalize hE : b :: y :: env = E
    have s0 : Run W (adjE (iQ + 2) (iL + 2) (im + 2) (it + 2) (ih + 2) (ifw + 2) (iR + 2) (iα + 2) 0) E
        (Greedy.adj fw Q L tail head R α b) (adjCost Q m) :=
      run_adjE B hL N (by rw [← hE]; simpa using hQv) (by rw [← hE]; simpa using hLv) (by rw [← hE]; simpa using hm)
        (by rw [← hE]; simpa using ht) (by rw [← hE]; simpa using hh) (by rw [← hE]; simpa using hf)
        (by rw [← hE]; simpa using hR) (by rw [← hE]; simpa using hα) (by rw [← hE]; rfl)
    have s1 : Run W (adjE (iQ + 2) (iL + 2) (im + 2) (it + 2) (ih + 2) (ifw + 2) (iR + 2) (iα + 2) 1) E
        (Greedy.adj fw Q L tail head R α y) (adjCost Q m) :=
      run_adjE B hL N (by rw [← hE]; simpa using hQv) (by rw [← hE]; simpa using hLv) (by rw [← hE]; simpa using hm)
        (by rw [← hE]; simpa using ht) (by rw [← hE]; simpa using hh) (by rw [← hE]; simpa using hf)
        (by rw [← hE]; simpa using hR) (by rw [← hE]; simpa using hα) (by rw [← hE]; rfl)
    have e : Greedy.best fw Q L tail head R α (y + 1) =
        if Greedy.adj fw Q L tail head R α b ≤ Greedy.adj fw Q L tail head R α y then b else y := by
      rw [Greedy.best, hb]
    rw [e]
    exact Run.ite s0 s1
      (fun h => (Run.var (by rw [← hE]; rfl)).eq (if_pos h).symm)
      (fun h => (Run.var (by rw [← hE]; rfl)).eq (if_neg h).symm)
  exact run_fold (T := Greedy.best fw Q L tail head R α) (Run.lit B.lit_K) (Run.lit (by positivity)) hbody

/-- **The placement as a program.** -/
theorem run_greedyE {n : ℕ} (B : Bd W m v fw (L ^ Q)) (hL : 2 ≤ L) (N : NetT fw tT hT tail head) {inn iv : ℕ}
    (hQW : Q < 2 ^ W) (hLW : L < 2 ^ W)
    (hn : env.getD inn 0 = n) (hm : env.getD im 0 = m) (hv : env.getD iv 0 = v) (hf : env.getD ifw 0 = fw)
    (ht : env.getD it 0 = tT) (hh : env.getD ih 0 = hT) :
    Run W (greedyE Q L inn im iv ifw it ih) env (Greedy.table fw n Q L tail head v) (greedyCost Q (L ^ Q) m v) := by
  have hK := B.hK
  have hK2 : L ^ Q ≤ 2 ^ fw := B.K_lt.le
  refine Run.letE (Run.lit hQW) (Run.letE (Run.lit hLW) ?_)
  refine run_fold (T := Greedy.table fw n Q L tail head) (Run.var (by simpa using hv)) (Run.lit (by positivity)) ?_
  intro a ha
  generalize hRd : Greedy.table fw n Q L tail head a = Ra
  have hRa : Ra < 2 ^ (a * fw) := by
    rw [← hRd]
    exact Greedy.table_lt hK hK2 a
  have hwlt : Greedy.word fw n Q L tail head Ra a < L ^ Q := Greedy.word_lt hK _ _
  generalize hE : Ra :: a :: L :: Q :: env = E
  have hpick : Run W (pickE Q L 3 2 (im + 4) (it + 4) (ih + 4) (ifw + 4) 0 1) E
      (Greedy.best fw Q L tail head Ra a (L ^ Q)) (pickCost Q (L ^ Q) m) :=
    run_pickE B hL N (by rw [← hE]; rfl) (by rw [← hE]; rfl) (by rw [← hE]; simpa using hm) (by rw [← hE]; simpa using ht)
      (by rw [← hE]; simpa using hh) (by rw [← hE]; simpa using hf) (by rw [← hE]; rfl) (by rw [← hE]; rfl)
  have hmod : Run W (.mod (.var 1) (.lit (L ^ Q))) E (a % L ^ Q) (1 + 1 + 1) :=
    Run.mod (Run.var (by rw [← hE]; rfl)) (Run.lit B.lit_K)
  have hword : Run W (.ite (.var (inn + 4)) (.var 1) (pickE Q L 3 2 (im + 4) (it + 4) (ih + 4) (ifw + 4) 0 1)
      (.mod (.var 1) (.lit (L ^ Q)))) E (Greedy.word fw n Q L tail head Ra a)
      (1 + 1 + 1 + (pickCost Q (L ^ Q) m + (1 + 1 + 1))) :=
    Run.ite (x := n) (y := a) (Run.var (by rw [← hE]; simpa using hn)) (Run.var (by rw [← hE]; rfl))
      (fun h => hpick.eq (if_pos h).symm) (fun h => hmod.eq (if_neg h).symm)
  generalize hw : Greedy.word fw n Q L tail head Ra a = w at hwlt hword
  have hw2 : w < 2 ^ fw := hwlt.trans_le hK2
  have hidx : a * fw < W := B.idx_lt (by omega)
  have hsum : Ra + w * 2 ^ (a * fw) < 2 ^ W :=
    (TransposeBase.Pseudo.Place.add_mul_lt hRa hw2).trans_le (Nat.pow_le_pow_right (by norm_num) (B.idx_lt (by omega)).le)
  have hset : Run W (setE 1 0 2 (ifw + 5)) (w :: E) (Ra + w * 2 ^ (a * fw)) 8 := by
    subst hE
    have g : (w :: Ra :: a :: L :: Q :: env).getD (ifw + 5) 0 = fw := by simpa using hf
    refine ⟨?_, (ops_setE W _ _ _ _ _).le⟩
    rw [eval_setE (by rw [g]; exact hidx) (by rw [g]; exact hsum), g]
    rfl
  have e : Greedy.table fw n Q L tail head (a + 1) = Ra + w * 2 ^ (a * fw) := by
    rw [Greedy.table, hRd, hw]
  rw [e]
  subst hE
  exact Run.letE hword hset

/-! ### The table of the layers -/

/-- The table of the layers, on numbers. -/
def layTable (fw R : ℕ) (tail head : Fin m → Fin v) : ℕ :=
  TransposeBase.Pseudo.Place.pk fw (fun i => if h : i < m then Greedy.layN fw R tail head ⟨i, h⟩ else 0) m

theorem layN_le (R : ℕ) (e : Fin m) : Greedy.layN fw R tail head e ≤ m := by
  calc Greedy.layN fw R tail head e ≤ ∑ _e : Fin m, 1 := sum_le_sum fun e _ => by split_ifs <;> omega
    _ = m := by simp

/-- The fields of the table of the layers. -/
theorem fld_layTable {K : ℕ} (B : Bd W m v fw K) (R : ℕ) (e : Fin m) :
    fld fw (layTable fw R tail head) e = Greedy.layN fw R tail head e := by
  unfold layTable
  rw [TransposeBase.Pseudo.Place.fld_pk (fun i hi => ?_) e.2]
  · simp
  · rw [dif_pos hi]
    exact lt_of_le_of_lt (layN_le R _) B.m_lt

theorem layN_eq_range (N : NetT fw tT hT tail head) (R : ℕ) (e : Fin m) :
    Greedy.layN fw R tail head e =
      ∑ i ∈ range m, if i + 1 ≤ (e : ℕ) then
        (if fld fw R (fld fw tT i) = fld fw R (fld fw tT e) then
          (if fld fw R (fld fw hT i) = fld fw R (fld fw hT e) then 1 else 0) else 0) else 0 := by
  rw [Finset.sum_range]
  refine sum_congr rfl fun i _ => ?_
  rw [N.tail_eq, N.head_eq, N.tail_eq, N.head_eq]
  have e1 : (i < e) ↔ ((i : ℕ) + 1 ≤ (e : ℕ)) := Fin.lt_def
  by_cases h1 : (i : ℕ) + 1 ≤ (e : ℕ)
  · rw [if_pos h1]
    by_cases h2 : fld fw R (tail i) = fld fw R (tail e)
    · by_cases h3 : fld fw R (head i) = fld fw R (head e)
      · rw [if_pos ⟨e1.mpr h1, h2, h3⟩, if_pos h2, if_pos h3]
      · rw [if_neg (fun h => h3 h.2.2), if_pos h2, if_neg h3]
    · rw [if_neg (fun h => h2 h.2.1), if_neg h2]
  · rw [if_neg h1, if_neg (fun h => h1 (e1.mp h.1))]

theorem run_wireWordE {K : ℕ} (B : Bd W m v fw K) {iT i Tv I : ℕ} (hT' : env.getD iT 0 = Tv) (hi : env.getD i 0 = I)
    (hI : I < m) (hf : env.getD ifw 0 = fw) (hR : env.getD iR 0 = R) (hnode : fld fw Tv I < v) :
    Run W (wireWordE iT ifw iR i) env (fld fw R (fld fw Tv I)) wireWordCost :=
  Run.letE ⟨eval_fieldE hT' hi hf (B.idx_lt (by omega)) B.fw_lt, (ops_fieldE W _ _ _ _).le⟩
    (run_field B (by simpa using hR) (by simp) (by simpa using hf) hnode)

theorem tail_lt (N : NetT fw tT hT tail head) {i : ℕ} (hi : i < m) : fld fw tT i < v := by
  have := N.tail_eq ⟨i, hi⟩
  simp only at this
  rw [this]
  exact (tail _).2

theorem head_lt (N : NetT fw tT hT tail head) {i : ℕ} (hi : i < m) : fld fw hT i < v := by
  have := N.head_eq ⟨i, hi⟩
  simp only at this
  rw [this]
  exact (head _).2

/-- The layer of a wire as a program. -/
theorem run_layE {K : ℕ} (B : Bd W m v fw K) (N : NetT fw tT hT tail head) {ie : ℕ} (e : Fin m)
    (hm : env.getD im 0 = m) (ht : env.getD it 0 = tT) (hh : env.getD ih 0 = hT) (hf : env.getD ifw 0 = fw)
    (hR : env.getD iR 0 = R) (hie : env.getD ie 0 = e) :
    Run W (layE im it ih ifw iR ie) env (Greedy.layN fw R tail head e) (layOne m) := by
  have hl1 : (1 : ℕ) < 2 ^ W := B.one_lt
  have h0 : (0 : ℕ) < 2 ^ W := by positivity
  have r1 : Run W (wireWordE it ifw iR ie) env (fld fw R (fld fw tT e)) wireWordCost :=
    run_wireWordE B ht hie e.2 hf hR (tail_lt N e.2)
  generalize hx : fld fw R (fld fw tT e) = x at r1
  have r2 : Run W (wireWordE (ih + 1) (ifw + 1) (iR + 1) (ie + 1)) (x :: env) (fld fw R (fld fw hT e)) wireWordCost :=
    run_wireWordE B (by simpa using hh) (by simpa using hie) e.2 (by simpa using hf) (by simpa using hR) (head_lt N e.2)
  generalize hy : fld fw R (fld fw hT e) = y at r2
  have hlt : Greedy.layN fw R tail head e < 2 ^ W := lt_of_le_of_lt (layN_le R e) (B.m_lt.trans B.pow_lt)
  rw [layN_eq_range N, hx, hy] at hlt ⊢
  refine Run.letE r1 (Run.letE r2 ?_)
  refine Run.sum (B := layBody) (Run.var (by simpa using hm)) le_rfl (fun i hi => ?_) hlt
  generalize hE : i :: y :: x :: env = E
  have him : i < m := hi
  have a1 : Run W (.add (.var 0) (.lit 1)) E (i + 1) (1 + 1 + 1) :=
    Run.add (Run.var (by rw [← hE]; rfl)) (Run.lit hl1) (by
      have := B.m_lt.trans B.pow_lt
      omega)
  have a2 : Run W (.var (ie + 3)) E (e : ℕ) 1 := Run.var (by rw [← hE]; simpa using hie)
  have w1 : Run W (wireWordE (it + 3) (ifw + 3) (iR + 3) 0) E (fld fw R (fld fw tT i)) wireWordCost :=
    run_wireWordE B (by rw [← hE]; simpa using ht) (by rw [← hE]; rfl) him (by rw [← hE]; simpa using hf)
      (by rw [← hE]; simpa using hR) (tail_lt N him)
  have w2 : Run W (wireWordE (ih + 3) (ifw + 3) (iR + 3) 0) E (fld fw R (fld fw hT i)) wireWordCost :=
    run_wireWordE B (by rw [← hE]; simpa using hh) (by rw [← hE]; rfl) him (by rw [← hE]; simpa using hf)
      (by rw [← hE]; simpa using hR) (head_lt N him)
  have vx : Run W (.var 2) E x 1 := Run.var (by rw [← hE]; rfl)
  have vy : Run W (.var 1) E y 1 := Run.var (by rw [← hE]; rfl)
  have l0 : Run W (.lit 0) E 0 1 := Run.lit h0
  have l1 : Run W (.lit 1) E 1 1 := Run.lit hl1
  have c1 := Run.eqX (r := if fld fw R (fld fw hT i) = y then 1 else 0) w2 vy
    (fun h => l1.eq (if_pos h).symm) (fun h => l0.eq (if_neg h).symm)
  have c2 := Run.eqX (r := if fld fw R (fld fw tT i) = x then
      (if fld fw R (fld fw hT i) = y then 1 else 0) else 0) w1 vx
    (fun h => c1.eq (if_pos h).symm) (fun h => l0.eq (if_neg h).symm)
  have c3 := Run.ite (r := if i + 1 ≤ (e : ℕ) then
      (if fld fw R (fld fw tT i) = x then (if fld fw R (fld fw hT i) = y then 1 else 0) else 0) else 0) a1 a2
    (fun h => c2.eq (if_pos h).symm) (fun h => l0.eq (if_neg h).symm)
  exact c3

/-- **The table of the layers as a program.** -/
theorem run_layTE {K : ℕ} (B : Bd W m v fw K) (N : NetT fw tT hT tail head)
    (hm : env.getD im 0 = m) (ht : env.getD it 0 = tT) (hh : env.getD ih 0 = hT) (hf : env.getD ifw 0 = fw)
    (hR : env.getD iR 0 = R) :
    Run W (layTE im it ih ifw iR) env (layTable fw R tail head) (layCost m) := by
  have hp := TransposeBase.Pseudo.Place.pk_lt (fw := fw) (M := m)
    (f := fun i => if h : i < m then Greedy.layN fw R tail head ⟨i, h⟩ else 0) (fun i hi => by
      rw [dif_pos hi]
      exact lt_of_le_of_lt (layN_le R _) B.m_lt)
  have hlt : layTable fw R tail head < 2 ^ W :=
    hp.trans_le (Nat.pow_le_pow_right (by norm_num) (by
      have h1 := B.hW
      have : m * fw ≤ (m + v + 8) * fw := Nat.mul_le_mul_right _ (by omega)
      omega))
  refine Run.sum (B := 1 + layOne m + (1 + (1 + 1 + 1))) (Run.var hm) le_rfl (fun i hi => ?_) hlt
  have hif : i * fw < W := B.idx_lt (by omega)
  have r1 : Run W (layE (im + 1) (it + 1) (ih + 1) (ifw + 1) (iR + 1) 0) (i :: env)
      (if h : i < m then Greedy.layN fw R tail head ⟨i, h⟩ else 0) (layOne m) := by
    rw [dif_pos hi]
    exact run_layE B N ⟨i, hi⟩ (by simpa using hm) (by simpa using ht) (by simpa using hh) (by simpa using hf)
      (by simpa using hR) rfl
  have r2 : Run W (.mul (.var 0) (.var (ifw + 1))) (i :: env) (i * fw) (1 + 1 + 1) :=
    Run.mul (Run.var rfl) (Run.var (by simpa using hf)) (hif.trans Nat.lt_two_pow_self)
  have h3 := Finset.single_le_sum (f := fun i => (if h : i < m then Greedy.layN fw R tail head ⟨i, h⟩ else 0) * 2 ^ (i * fw))
    (s := range m) (fun _ _ => Nat.zero_le _) (mem_range.mpr hi)
  have hlt' : (∑ e ∈ range m, (if h : e < m then Greedy.layN fw R tail head ⟨e, h⟩ else 0) * 2 ^ (e * fw)) < 2 ^ W := hlt
  exact Run.mul r1 (Run.pow2 r2 hif) (lt_of_le_of_lt h3 hlt')

end Run

/-! ### The number of layers -/

/-- The program `hE`. -/
theorem run_hE {K D inn n : ℕ} {env : List ℕ} (hn : env.getD inn 0 = n) (hD : 1 ≤ D)
    (hK : K < 2 ^ W) (hs : 6 * ((n + 1) * D) + 3 < 2 ^ W) :
    Run W (hE K D inn) env (Greedy.capB n K D) 15 := by
  have hdiv : n / K ≤ n := Nat.div_le_self _ _
  have h1 : (n / K + 1) * D ≤ (n + 1) * D := Nat.mul_le_mul_right _ (by omega)
  have h2 : (n + 1) * 1 ≤ (n + 1) * D := Nat.mul_le_mul_left _ hD
  have h3 : 1 * D ≤ (n + 1) * D := Nat.mul_le_mul_right _ (by omega)
  have a1 : Run W (.add (.div (.var inn) (.lit K)) (.lit 1)) env (n / K + 1) (1 + (1 + 1 + 1) + 1) :=
    Run.add (Run.div (Run.var hn) (Run.lit hK)) (Run.lit (by omega)) (by omega)
  have a2 := Run.mul a1 (Run.lit (x := D) (by omega)) (show (n / K + 1) * D < 2 ^ W by omega)
  have a3 := Run.mul (Run.lit (env := env) (x := 6) (by omega)) a2 (show 6 * ((n / K + 1) * D) < 2 ^ W by omega)
  have a4 := Run.div a3 (Run.lit (env := env) hK)
  have hle : 6 * ((n / K + 1) * D) / K ≤ 6 * ((n / K + 1) * D) := Nat.div_le_self _ _
  have a5 := Run.add a4 (Run.lit (env := env) (x := 3) (by omega)) (by omega)
  exact a5.mono (by omega)

/-! ### The cost -/

theorem greedyCost_le (Q K m v : ℕ) : greedyCost Q K m v ≤ greedyK Q K * (m + v + 1) ^ 3 := by
  generalize hA : m + v + 1 = A
  generalize hI : clashIn Q = I
  have hA1 : 1 ≤ A := by omega
  have hmA : m ≤ A := by omega
  have hvA : v ≤ A := by omega
  have hAA : A ≤ A ^ 2 := Nat.le_self_pow (by norm_num) A
  have hA2 : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ hA1
  have hA3 : 1 ≤ A ^ 3 := Nat.one_le_pow _ _ hA1
  have h1 : loadCost m ≤ 103 * A := by
    unfold loadCost
    omega
  have h2 : scoreCost m ≤ 273 * A ^ 2 := by
    have e : A * (271 * A) = 271 * A ^ 2 := by ring
    have h3 : m * (64 + 2 * loadCost m + 1) ≤ A * (271 * A) := Nat.mul_le_mul hmA (by omega)
    unfold scoreCost
    omega
  set c := 69 + 2 * I with hc
  have h3 : clashCost Q m ≤ c * A := by
    have e : clashBody Q + 1 ≤ c - 2 := by
      simp only [clashBody, hI, hc]
      omega
    have h4 : m * (clashBody Q + 1) ≤ A * (c - 2) := Nat.mul_le_mul hmA e
    have h5 : A * (c - 2) + 2 * A = c * A := by
      have : c = (c - 2) + 2 := by omega
      calc A * (c - 2) + 2 * A = (c - 2 + 2) * A := by ring
        _ = c * A := by rw [← this]
    unfold clashCost
    omega
  have h4 : c * A ≤ c * A ^ 2 := Nat.mul_le_mul_left _ hAA
  have h5 : adjCost Q m ≤ (c + 280) * A ^ 2 := by
    have e : (c + 280) * A ^ 2 = c * A ^ 2 + 280 * A ^ 2 := by ring
    unfold adjCost
    omega
  have h6 : pickCost Q K m ≤ (K + 1) * ((2 * c + 567) * A ^ 2) := by
    have h7 : (1 + adjCost Q m + adjCost Q m + (1 + 1)) + 1 ≤ (2 * c + 564) * A ^ 2 := by
      have e : (2 * c + 564) * A ^ 2 = 2 * ((c + 280) * A ^ 2) + 4 * A ^ 2 := by ring
      omega
    have h8 : K * ((1 + adjCost Q m + adjCost Q m + (1 + 1)) + 1) ≤ K * ((2 * c + 564) * A ^ 2) :=
      Nat.mul_le_mul_left _ h7
    have e : (K + 1) * ((2 * c + 567) * A ^ 2) = K * ((2 * c + 564) * A ^ 2) + (2 * c + 564) * A ^ 2 + 3 * (K * A ^ 2) + 3 * A ^ 2 := by
      ring
    have h9 : 0 ≤ K * A ^ 2 := Nat.zero_le _
    have h10 : 0 ≤ (2 * c + 564) * A ^ 2 := Nat.zero_le _
    unfold pickCost
    omega
  set P := (K + 1) * ((2 * c + 567) * A ^ 2) with hP
  have hP1 : 1 ≤ P := by
    have : 1 ≤ (2 * c + 567) * A ^ 2 := Nat.mul_pos (by omega) (by omega)
    exact Nat.mul_pos (by omega) (by omega)
  have h7 : v * ((1 + (1 + 1 + 1 + (pickCost Q K m + (1 + 1 + 1))) + 8) + 1) ≤ A * (P + 16) :=
    Nat.mul_le_mul hvA (by omega)
  have e1 : A * P = (K + 1) * ((2 * c + 567) * A ^ 3) := by
    rw [hP]
    ring
  have e2 : greedyK Q K * A ^ 3 = (K + 1) * ((2 * c + 567) * A ^ 3) + 23 * ((K + 1) * A ^ 3) := by
    simp only [greedyK, hI, hc]
    ring
  have h8 : A ≤ A ^ 3 := Nat.le_self_pow (by norm_num) A
  have h9 : A ^ 3 ≤ (K + 1) * A ^ 3 := Nat.le_mul_of_pos_left _ (by omega)
  have e3 : A * (P + 16) = A * P + 16 * A := by ring
  unfold greedyCost
  rw [e2]
  omega

end GreedySpec

/-- **The placement as a program**: value and cost. -/
theorem greedy_spec {W m v fw Q L n tT hT : ℕ} {tail head : Fin m → Fin v} (B : Bd W m v fw (L ^ Q)) (hL : 2 ≤ L)
    (N : NetT fw tT hT tail head) {inn im iv ifw it ih : ℕ} {env : List ℕ} (hQW : Q < 2 ^ W) (hLW : L < 2 ^ W)
    (hn : env.getD inn 0 = n) (hm : env.getD im 0 = m) (hv : env.getD iv 0 = v) (hf : env.getD ifw 0 = fw)
    (ht : env.getD it 0 = tT) (hh : env.getD ih 0 = hT) :
    Run W (greedyE Q L inn im iv ifw it ih) env (Greedy.table fw n Q L tail head v) (greedyK Q (L ^ Q) * (m + v + 1) ^ 3) :=
  (GreedySpec.run_greedyE B hL N hQW hLW hn hm hv hf ht hh).mono (GreedySpec.greedyCost_le Q (L ^ Q) m v)

end OnePigeonhole.Pseudo
