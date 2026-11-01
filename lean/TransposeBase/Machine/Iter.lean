import TransposeBase.Machine.Loops

/-!
# `sumIter`

The loop keeps the bound in the slot `t`, the iterate in `t + 1`, the sum in `t + 2`, the counter in `t + 3`.
The body evaluates `b` on the current iterate and adds it, and only then evaluates `f` for the next iterate.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace TransposeBase.Machine

open OAI.Algorithms.SubexponentialSAT
open StructuredCalls
open TransposeBase.Pseudo

variable {S : ℕ} [NeZero S]

local notation "u" => Function.update

/-- The memory at the guard of `sumIter`. -/
def L3 (W : ℕ) (m : Mem) (t N p a k : ℕ) : Mem :=
  u (u (u (u m (11 + t) (wordOf W N)) (11 + (t + 1)) (wordOf W p)) (11 + (t + 1 + 1)) (wordOf W a))
    (11 + (t + 1 + 1 + 1)) (wordOf W k)

def iterBody (S : ℕ) [NeZero S] (Cb Cf : List ℕ → ℕ → Cmd 10 S) (map : List ℕ) (t : ℕ) : Cmd 10 S :=
  .seq (Cb ((t + 1) :: map) (t + 1 + 1 + 1 + 1))
    (.seq (binC S (addCore S) (11 + (t + 1 + 1)) (11 + (t + 1 + 1 + 1 + 1)))
      (.seq (Cf ((t + 1) :: map) (t + 1 + 1 + 1 + 1))
        (.seq (replaceC S (11 + (t + 1)) (11 + (t + 1 + 1 + 1 + 1)))
          (incCmpC S (11 + (t + 1 + 1 + 1)) (11 + t)))))

def iterSetup (S : ℕ) [NeZero S] (t : ℕ) : Cmd 10 S :=
  .seq (copyC S 10 (11 + (t + 1 + 1))) (.seq (copyC S 10 (11 + (t + 1 + 1 + 1)))
    (cmpC S (11 + (t + 1 + 1 + 1)) (11 + t)))

def iterFinish (S : ℕ) [NeZero S] (t : ℕ) : Cmd 10 S :=
  .seq (clearC S (11 + t)) (.seq (clearC S (11 + (t + 1))) (.seq (clearC S (11 + (t + 1 + 1 + 1)))
    (mvC S (11 + (t + 1 + 1)) (11 + t))))

def iterE (S : ℕ) [NeZero S] (Cn Cs Cb Cf : List ℕ → ℕ → Cmd 10 S) (map : List ℕ) (t : ℕ) : Cmd 10 S :=
  .seq (Cn map t) (.seq (Cs map (t + 1))
    (.seq (.seq (iterSetup S t) (.while 0 (iterBody S Cb Cf map t))) (iterFinish S t)))

/-- The sum of `sumIter` after `k` iterations. -/
private def iterSum (W : ℕ) (s f b : Expr) (env : List ℕ) (k : ℕ) : ℕ :=
  ((List.range k).foldl (fun p _ => (eval W f (p.1 :: env), (p.2 + eval W b (p.1 :: env)) % 2 ^ W))
    (eval W s env, 0)).2

private theorem iterSum_succ (W : ℕ) (s f b : Expr) (env : List ℕ) (k : ℕ) :
    iterSum W s f b env (k + 1) =
      (iterSum W s f b env k + eval W b (iterate W f (eval W s env) env k :: env)) % 2 ^ W := by
  simp only [iterSum, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [foldl_iter_fst]

/-- The pair (iterate, operation count) after `k` iterations. -/
private def iterPair (W : ℕ) (n s f b : Expr) (env : List ℕ) (k : ℕ) : ℕ × ℕ :=
  (List.range k).foldl (fun p _ => (eval W f (p.1 :: env), p.2 + 1 + ops W b (p.1 :: env) + ops W f (p.1 :: env)))
    (eval W s env, 1 + ops W n env + ops W s env)

private theorem iterPair_succ (W : ℕ) (n s f b : Expr) (env : List ℕ) (k : ℕ) :
    iterPair W n s f b env (k + 1) =
      (eval W f ((iterPair W n s f b env k).1 :: env),
        (iterPair W n s f b env k).2 + 1 + ops W b ((iterPair W n s f b env k).1 :: env) +
          ops W f ((iterPair W n s f b env k).1 :: env)) := by
  simp [iterPair, List.range_succ, List.foldl_append]

private theorem iterPair_fst (W : ℕ) (n s f b : Expr) (env : List ℕ) (k : ℕ) :
    (iterPair W n s f b env k).1 = iterate W f (eval W s env) env k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterPair_succ]
    simp only [ih]
    rfl

private theorem L3_N {W t N p a k : ℕ} {m : Mem} : L3 W m t N p a k (11 + t) = wordOf W N := by
  simp only [L3]
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_self]

private theorem L3_p {W t N p a k : ℕ} {m : Mem} : L3 W m t N p a k (11 + (t + 1)) = wordOf W p := by
  simp only [L3]
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]

private theorem L3_a {W t N p a k : ℕ} {m : Mem} : L3 W m t N p a k (11 + (t + 1 + 1)) = wordOf W a := by
  simp only [L3]
  rw [Function.update_of_ne (by omega), Function.update_self]

private theorem L3_k {W t N p a k : ℕ} {m : Mem} : L3 W m t N p a k (11 + (t + 1 + 1 + 1)) = wordOf W k := by
  simp only [L3, Function.update_self]

private theorem L3_good {W t N p a k : ℕ} {map env : List ℕ} {m : Mem} (hg : Good W map env t m) :
    Good W map env (t + 1 + 1 + 1 + 1) (L3 W m t N p a k) := hg.step.step.step.step

theorem correct_sumIter {W : ℕ} {n s f b : Expr} {Cn Cs Cb Cf : List ℕ → ℕ → Cmd 10 S} (hS : 11 ≤ S)
    (hn : Correct W n Cn) (hs : Correct W s Cs) (hf : Correct W f Cf) (hb : Correct W b Cb) :
    Correct W (.sumIter n s f b) (iterE S Cn Cs Cb Cf) := by
  intro map env t m hg ht
  simp only [stack] at ht
  have hsn := stack_pos n
  have hss := stack_pos s
  have hsf := stack_pos f
  have hsb := stack_pos b
  have henv := hg.env_lt
  set N := eval W n env with hNdef
  have hN : N < 2 ^ W := eval_lt_word W n env henv
  have hpw : 0 < 2 ^ W := by positivity
  set P := fun k => iterate W f (eval W s env) env k with hP
  have hPlt : ∀ k, P k < 2 ^ W := by
    intro k
    induction k with
    | zero => exact eval_lt_word W s env henv
    | succ k ih =>
      refine eval_lt_word W f _ fun x hx => ?_
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ih
      · exact henv x hx
  have hPs : ∀ k, P (k + 1) = eval W f (P k :: env) := fun k => rfl
  set A := iterSum W s f b env with hA
  have hAlt : ∀ k, A k < 2 ^ W := by
    intro k
    cases k with
    | zero => exact hpw
    | succ k =>
      rw [hA, iterSum_succ]
      exact Nat.mod_lt _ hpw
  have hAs : ∀ k, A (k + 1) = (A k + eval W b (P k :: env)) % 2 ^ W := fun k => iterSum_succ W s f b env k
  have hsq := square_ge W
  have hTbig : 200 * W + 200 ≤ T W := by simp only [T]; omega
  have binT : 6000 * (W + 1) ^ 2 + 9 * (W + 1) + 8 + 3 * (9 * W + 8) + (11 * W + 11) + (54 * W + 71) + 1 ≤ T W := by
    simp only [T]
    omega
  have g₁ := hn map env t m hg (by omega)
  have g₂ := hs map env (t + 1) _ (hg.step (x := N)) (by omega)
  -- the setup
  have hg₂ : Good W map env (t + 1 + 1) (u (u m (11 + t) (wordOf W N)) (11 + (t + 1)) (wordOf W (P 0))) :=
    hg.step.step
  have gsetup : GoQ (B W) (iterSetup S t) (u (u m (11 + t) (wordOf W N)) (11 + (t + 1)) (wordOf W (P 0)))
      (L3 W m t N (P 0) (A 0) 0) (60 * W + 73) fun r => r 0 = decide (0 < N) := by
    have e₁ := ev_copy' (S := S) (src := 10) (dst := 11 + (t + 1 + 1)) (L := W)
      (m := u (u m (11 + t) (wordOf W N)) (11 + (t + 1)) (wordOf W (P 0))) (x := wordOf W (A 0))
      (by omega) (by omega) (by omega) (by omega) (by norm_num) (by omega) hg₂.clean.w8
      (by rw [hg₂.clean.ruler]; exact (wordOf_zero W).symm) (hg₂.empty _ le_rfl) (by simp)
    have hg₃ := hg₂.step (x := A 0)
    have e₂ : Ev (copyC S 10 (11 + (t + 1 + 1 + 1)))
        (u (u (u m (11 + t) (wordOf W N)) (11 + (t + 1)) (wordOf W (P 0))) (11 + (t + 1 + 1)) (wordOf W (A 0)))
        (L3 W m t N (P 0) (A 0) 0) (7 * W + 5) :=
      ev_copy' (S := S) (src := 10) (dst := 11 + (t + 1 + 1 + 1)) (L := W) (x := wordOf W 0)
      (by omega) (by omega) (by omega) (by omega) (by norm_num) (by omega) hg₃.clean.w8
      (by rw [hg₃.clean.ruler, wordOf_zero]) (hg₃.empty _ le_rfl) (by simp)
    have e₃ := ev_cmp (S := S) (W := W) (x := 11 + (t + 1 + 1 + 1)) (y := 11 + t) (a := 0) (b := N)
      (m := L3 W m t N (P 0) (A 0) 0) (by omega) (by omega) (by omega) (by omega) (by omega)
      (L3_good hg).clean L3_k L3_N hpw hN
    exact go_routine ((EvQ.seq e₁ (EvQ.seq e₂ e₃)).mono (by omega)) hg₂.small (by omega)
  -- the body
  have gb : ∀ k < N, GoQ (B W) (iterBody S Cb Cf map t) (L3 W m t N (P k) (A k) k)
      (L3 W m t N (P (k + 1)) (A (k + 1)) (k + 1))
      (ops W b (P k :: env) * T W + (ops W f (P k :: env) * T W + (T W - 1)))
      fun r => r 0 = decide (k + 1 < N) := by
    intro k hk
    have h₄ := hg.empty (t + 1 + 1 + 1 + 1) (by omega)
    have hgg : ∀ a, Good W ((t + 1) :: map) (P k :: env) (t + 1 + 1 + 1 + 1) (L3 W m t N (P k) a k) := fun a =>
      (L3_good hg).cons (by omega) L3_p (hPlt k)
    have g_b := hb _ _ _ _ (hgg (A k)) (by omega)
    set Y := eval W b (P k :: env) with hY
    have hYlt : Y < 2 ^ W := eval_lt_word W b _ (hgg (A k)).env_lt
    set M₁ := u (L3 W m t N (P k) (A k) k) (11 + (t + 1 + 1 + 1 + 1)) (wordOf W Y) with hM₁
    have hgM₁ : Good W map env (t + 1 + 1 + 1 + 1 + 1) M₁ := (L3_good hg).step
    have hclean : Clean W (u (u M₁ (11 + (t + 1 + 1))  []) (11 + (t + 1 + 1 + 1 + 1)) []) :=
      (hgM₁.clean.high (by omega) _).high (by omega) _
    have ebin := ev_bin (S := S) (W := W) (x := 11 + (t + 1 + 1)) (y := 11 + (t + 1 + 1 + 1 + 1))
      (wa := wordOf W (A k)) (wb := wordOf W Y) (wr := wordOf W ((A k + Y) % 2 ^ W)) (m := M₁) (core := addCore S)
      (tc := 6000 * (W + 1) ^ 2 + 9 * (W + 1) + 8) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      hgM₁.clean (by rw [hM₁, Function.update_of_ne (by omega), L3_a]) (by simp [hM₁]) (by simp) (by simp) (by simp)
      (ev_add hS hclean (hAlt k) hYlt)
    have hmem₁ : u (u M₁ (11 + (t + 1 + 1)) (wordOf W ((A k + Y) % 2 ^ W))) (11 + (t + 1 + 1 + 1 + 1)) [] =
        L3 W m t N (P k) (A (k + 1)) k := by
      rw [hAs]
      simp only [hM₁, L3]
      mem_eq'
    rw [hmem₁] at ebin
    have g_bin := go_routine ebin hgM₁.small (by omega)
    have g_f := hf _ _ _ _ (hgg (A (k + 1))) (by omega)
    rw [← hPs] at g_f
    set M₂ := u (L3 W m t N (P k) (A (k + 1)) k) (11 + (t + 1 + 1 + 1 + 1)) (wordOf W (P (k + 1))) with hM₂
    have hgM₂ : Good W map env (t + 1 + 1 + 1 + 1 + 1) M₂ := (L3_good hg).step
    have erep := ev_replace (S := S) (W := W) (x := 11 + (t + 1)) (y := 11 + (t + 1 + 1 + 1 + 1))
      (wv := wordOf W (P (k + 1))) (m := M₂) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      hgM₂.clean (by simp [hM₂]) (by simp) (by rw [hM₂, Function.update_of_ne (by omega), L3_p]; simp)
    have hmem₂ : u (u M₂ (11 + (t + 1)) (wordOf W (P (k + 1)))) (11 + (t + 1 + 1 + 1 + 1)) [] =
        L3 W m t N (P (k + 1)) (A (k + 1)) k := by
      simp only [hM₂, L3]
      mem_eq'
    rw [hmem₂] at erep
    have g_rep := go_routine erep hgM₂.small (by omega)
    have hg₃ : Good W map env (t + 1 + 1 + 1 + 1) (L3 W m t N (P (k + 1)) (A (k + 1)) k) := L3_good hg
    have eic := ev_incCmp (S := S) (W := W) (k := k) (N := N) (kS := 11 + (t + 1 + 1 + 1)) (nS := 11 + t)
      (m := L3 W m t N (P (k + 1)) (A (k + 1)) k) hS (by omega) (by omega) (by omega) (by omega) (by omega)
      hg₃.clean L3_k L3_N hk hN
    have hmem₃ : u (L3 W m t N (P (k + 1)) (A (k + 1)) k) (11 + (t + 1 + 1 + 1)) (wordOf W (k + 1)) =
        L3 W m t N (P (k + 1)) (A (k + 1)) (k + 1) := by
      simp only [L3, Function.update_idem]
    rw [hmem₃] at eic
    have g_ic := go_routine eic hg₃.small (by omega)
    exact (GoQ.seq g_b (GoQ.seq g_bin (GoQ.seq g_f (GoQ.seq g_rep g_ic)))).mono (by omega)
  -- the potential
  set c := iterPair W n s f b env with hc
  have hc₁ : ∀ k, (c k).1 = P k := iterPair_fst W n s f b env
  have hφ : ∀ k < N, (c k).2 * T W + (ops W b (P k :: env) * T W + (ops W f (P k :: env) * T W + (T W - 1))) + 1 ≤
      (c (k + 1)).2 * T W := by
    intro k _
    have hstep : (c (k + 1)).2 = (c k).2 + 1 + ops W b (P k :: env) + ops W f (P k :: env) := by
      rw [hc, iterPair_succ]
      simp only [iterPair_fst]
      rfl
    rw [hstep, add_mul, add_mul, add_mul]
    omega
  have hmono : (c 0).2 * T W ≤ (c N).2 * T W := phi_mono (Φ := fun k => (c k).2 * T W) hφ
  have h0' : (c 0).2 * T W = T W + ops W n env * T W + ops W s env * T W := by
    have : (c 0).2 = 1 + ops W n env + ops W s env := rfl
    rw [this]
    ring
  have hsN := (L3_good (N := N) (p := P N) (a := A N) (k := N) hg).small
  have hsB : ∀ i, (L3 W m t N (P N) (A N) N i).length ≤ B W := fun i =>
    (hsN i).trans (by simp only [B]; omega)
  have gloop := go_for (t := 60 * W + 73 + (c N).2 * T W + 1 - (c 0).2 * T W)
    (fun k => L3 W m t N (P k) (A k) k) N (fun k => (c k).2 * T W)
    (fun k => ops W b (P k :: env) * T W + (ops W f (P k :: env) * T W + (T W - 1))) gsetup gb hφ hsB (by omega)
  -- the clean-up
  have gfin : Go (B W) (iterFinish S t) (L3 W m t N (P N) (A N) N)
      (u m (11 + t) (wordOf W (A N))) (15 * W + 17) := by
    set M := L3 W m t N (P N) (A N) N with hM
    have e₁ := ev_clear' (S := S) (i := 11 + t) (L := W) (by omega) M (by rw [hM, L3_N]; simp)
    have e₂ := ev_clear' (S := S) (i := 11 + (t + 1)) (L := W) (by omega) (u M (11 + t) [])
      (by rw [Function.update_of_ne (by omega), hM, L3_p]; simp)
    have e₃ := ev_clear' (S := S) (i := 11 + (t + 1 + 1 + 1)) (L := W) (by omega)
      (u (u M (11 + t) []) (11 + (t + 1)) [])
      (by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hM, L3_k]; simp)
    set M₃ := u (u (u M (11 + t) []) (11 + (t + 1)) []) (11 + (t + 1 + 1 + 1)) [] with hM₃
    have hc₃ : Clean W M₃ :=
      (((L3_good hg).clean.high (by omega) _).high (by omega) _).high (by omega) _
    have e₄ := ev_mv (S := S) (src := 11 + (t + 1 + 1)) (dst := 11 + t) (L := W) (m := M₃) (x := wordOf W (A N))
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hc₃.w8
      (by rw [hM₃, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), hM, L3_a])
      (by rw [hM₃, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; simp) (by simp)
    have hmem : u (u M₃ (11 + t) (wordOf W (A N))) (11 + (t + 1 + 1)) [] = u m (11 + t) (wordOf W (A N)) := by
      have h₁ := hg.empty (t + 1) (by omega)
      have h₂ := hg.empty (t + 1 + 1) (by omega)
      have h₃ := hg.empty (t + 1 + 1 + 1) (by omega)
      simp only [hM₃, hM, L3]
      mem_eq'
    rw [hmem] at e₄
    exact (go_routine (EvQ.seq e₁ (EvQ.seq e₂ (EvQ.seq e₃ e₄))) hsN (by omega)).mono (by omega)
  have hval : eval W (.sumIter n s f b) env = A N := rfl
  have hops : ops W (.sumIter n s f b) env = (c N).2 := rfl
  rw [hval, hops]
  refine (GoQ.seq g₁ (GoQ.seq g₂ (GoQ.seq gloop gfin))).mono ?_
  omega

end TransposeBase.Machine
