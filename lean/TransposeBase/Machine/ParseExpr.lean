import TransposeBase.Machine.ParseSpec
import TransposeBase.Pseudo.CnfRun

/-!
# Reading the encoding in the word language: one step

The state of the automaton of `ParseSpec` is one word: `pack Q s = m + 4 * (r + Q * (k + Q * f))`. `bodyE` is the loop
body. It runs on `st :: pos :: Q :: n :: x :: T`, it reads the bit `pos + n + 1` of `x`, and its value is the word of
the next state (`run_bodyE`).
-/

namespace TransposeBase.Machine.Parse

open TransposeBase.Pseudo TransposeBase.Pseudo.CnfTree

/-- The word of a state. -/
def pack (Q : ℕ) (s : PS) : ℕ := s.m + 4 * (s.r + Q * (s.k + Q * s.f))

private theorem add_mul_mod' {a B c : ℕ} (h : a < B) : (a + B * c) % B = a := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]

private theorem add_mul_div' {a B c : ℕ} (h : a < B) : (a + B * c) / B = c := by
  rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt h, zero_add]

/-- The word of a state with the fields given by the expressions. The variable `9` is `Q`. -/
def packE (a b c d : Expr) : Expr :=
  .add a (.mul (.lit 4) (.add b (.mul (.var 9) (.add c (.mul (.var 9) d)))))

section Run

variable {W Q : ℕ} {env : List ℕ}

theorem run_packE {a b c d : Expr} {va vb vc vd Ba Bb Bc Bd : ℕ} (h4 : 4 < 2 ^ W) (hQ : 1 ≤ Q)
    (hq : env.getD 9 0 = Q) (ha : Run W a env va Ba) (hb : Run W b env vb Bb) (hc : Run W c env vc Bc)
    (hd : Run W d env vd Bd) (h : va + 4 * (vb + Q * (vc + Q * vd)) < 2 ^ W) :
    Run W (packE a b c d) env (va + 4 * (vb + Q * (vc + Q * vd))) (Ba + Bb + Bc + Bd + 9) := by
  have hv : Run W (.var 9) env Q 1 := run_var hq
  have e1 : Q * vd ≤ vc + Q * vd := by omega
  have e2 : vc + Q * vd ≤ Q * (vc + Q * vd) := Nat.le_mul_of_pos_left _ hQ
  have e3 : Q * (vc + Q * vd) ≤ vb + Q * (vc + Q * vd) := by omega
  have r1 := run_mul hv hd (by omega)
  have r2 := run_add hc r1 (by omega)
  have r3 := run_mul hv r2 (by omega)
  have r4 := run_add hb r3 (by omega)
  have r5 := run_mul (run_lit h4) r4 (by omega)
  have r6 := run_add ha r5 h
  exact r6.mono (by omega)

end Run

/-- The next clause code, in the environment of `branchE`. -/
def nextKE : Expr :=
  .add (.div (.var 1) (gE 10)) (.mul (.mul (gE 10) (gE 10)) (.div (.var 3) (.lit 2)))

/-- The step, on `f :: k :: v :: r :: u :: m :: b :: st :: pos :: Q :: n :: _`. -/
def branchE : Expr :=
  .ite (.var 5) (.lit 0)
    (.ite (.var 6) (.lit 0) (.var 7) (.add (.var 7) (.lit 1)))
    (.ite (.var 5) (.lit 1)
      (.ite (.var 6) (.lit 0)
        (packE (.lit 0) (.var 3) (.lit 0) (.add (.var 0) (.pow2 (.var 1))))
        (.add (.var 7) (.lit 1)))
      (.ite (.var 6) (.lit 0)
        (.ite (.var 3) (.lit 0)
          (packE (.lit 1) (.lit 0) (.var 1) (.var 0))
          (packE (.lit 1) (.lit 0) nextKE (.var 0)))
        (packE (.lit 1) (.add (.var 3) (.lit 1)) (.var 1) (.var 0))))

/-- The loop body, on `st :: pos :: Q :: n :: x :: _`. -/
def bodyE : Expr :=
  .letE (.letE (.add (.add (.var 1) (.var 3)) (.lit 1)) (bitE 5 0))
    (.letE (.mod (.var 1) (.lit 4))
      (.letE (.div (.var 2) (.lit 4))
        (.letE (.mod (.var 0) (.var 5))
          (.letE (.div (.var 1) (.var 6))
            (.letE (.mod (.var 0) (.var 7))
              (.letE (.div (.var 1) (.var 8)) branchE))))))

section Step

variable {W Q n : ℕ}

theorem run_bit {env : List ℕ} {f i fv iv : ℕ} (hW : 2 ≤ W) (hf : env.getD f 0 = fv) (hi : env.getD i 0 = iv)
    (hlt : iv < W) : Run W (bitE f i) env (fv.testBit iv).toNat 6 := by
  refine ⟨?_, (ops_bitE W f i env).le⟩
  rw [eval_bitE W f i env hW (by rwa [hi]), hf, hi]

theorem run_branchE (hC : Ctx W n) (hQ : 1 ≤ Q) {s : PS} {bit : Bool} {pos x v u : ℕ} {T : List ℕ}
    (hm : s.m ≤ 2) (hkW : s.k < W) (hst : pack Q s + 1 < 2 ^ W + 1)
    (hfit : pack Q (stepP (2 * n + 1) s bit) < 2 ^ W) :
    Run W branchE (s.f :: s.k :: v :: s.r :: u :: s.m :: bit.toNat :: pack Q s :: pos :: Q :: n :: x :: T)
      (pack Q (stepP (2 * n + 1) s bit)) 120 := by
  have w := hC.one_le
  have hW8 := hC.eight_le
  have h4 : (4 : ℕ) < 2 ^ W := by
    calc 4 < 2 ^ 8 := by norm_num
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW8
  have h2 : (2 : ℕ) < 2 ^ W := by omega
  have h1 : (1 : ℕ) < 2 ^ W := by omega
  set E := s.f :: s.k :: v :: s.r :: u :: s.m :: bit.toNat :: pack Q s :: pos :: Q :: n :: x :: T with hE
  have vb : Run W (.var 6) E bit.toNat 1 := run_var (by simp [hE])
  have vm : Run W (.var 5) E s.m 1 := run_var (by simp [hE])
  have vst : Run W (.var 7) E (pack Q s) 1 := run_var (by simp [hE])
  have vr : Run W (.var 3) E s.r 1 := run_var (by simp [hE])
  have vk : Run W (.var 1) E s.k 1 := run_var (by simp [hE])
  have vf : Run W (.var 0) E s.f 1 := run_var (by simp [hE])
  have hq : E.getD 9 0 = Q := by simp [hE]
  have hnv : E.getD 10 0 = n := by simp [hE]
  have z : Run W (.lit 0) E 0 1 := run_zero w
  have o : Run W (.lit 1) E 1 1 := run_one w
  have hstep1 : s.m = 0 → bit = true → pack Q (stepP (2 * n + 1) s bit) = pack Q s + 1 := fun h hb => by
    simp [stepP, h, hb, pack]; omega
  have m0 : s.m = 0 → Run W (.ite (.var 6) (.lit 0) (.var 7) (.add (.var 7) (.lit 1))) E
      (pack Q (stepP (2 * n + 1) s bit)) 100 := fun h => by
    refine (run_ite (Bc := 3) vb z (fun hb => ?_) (fun hb => ?_)).mono (by omega)
    · have hb' : bit = false := by cases bit <;> simp_all
      have : stepP (2 * n + 1) s bit = s := by simp [stepP, h, hb']
      rw [this]
      exact vst.mono (by omega)
    · have hb' : bit = true := by cases bit <;> simp_all
      rw [hstep1 h hb']
      have hf := hfit
      rw [hstep1 h hb'] at hf
      exact run_add vst o hf
  have hstep2 : s.m = 1 → bit = true → pack Q (stepP (2 * n + 1) s bit) = pack Q s + 1 := fun h hb => by
    simp [stepP, h, hb, pack]; omega
  have m1 : s.m = 1 → Run W (.ite (.var 6) (.lit 0)
        (packE (.lit 0) (.var 3) (.lit 0) (.add (.var 0) (.pow2 (.var 1))))
        (.add (.var 7) (.lit 1))) E (pack Q (stepP (2 * n + 1) s bit)) 100 := fun h => by
    refine (run_ite (Bc := 20) vb z (fun hb => ?_) (fun hb => ?_)).mono (by omega)
    · have hb' : bit = false := by cases bit <;> simp_all
      have he : stepP (2 * n + 1) s bit = ⟨0, s.r, 0, s.f + 2 ^ s.k⟩ := by simp [stepP, h, hb']
      rw [he] at hfit ⊢
      simp only [pack] at hfit ⊢
      have hle : s.f + 2 ^ s.k ≤ 0 + Q * (s.f + 2 ^ s.k) := by
        rw [zero_add]; exact Nat.le_mul_of_pos_left _ hQ
      have hle2 : 0 + Q * (s.f + 2 ^ s.k) ≤ Q * (0 + Q * (s.f + 2 ^ s.k)) :=
        Nat.le_mul_of_pos_left _ hQ
      have hsum : s.f + 2 ^ s.k < 2 ^ W := by omega
      have pk := run_pow2 vk hkW
      have add1 := run_add vf pk hsum
      exact (run_packE h4 hQ hq z vr z add1 hfit).mono (by omega)
    · have hb' : bit = true := by cases bit <;> simp_all
      rw [hstep2 h hb']
      have hf := hfit
      rw [hstep2 h hb'] at hf
      exact (run_add vst o hf).mono (by omega)
  have m2 : s.m = 2 → Run W (.ite (.var 6) (.lit 0)
        (.ite (.var 3) (.lit 0)
          (packE (.lit 1) (.lit 0) (.var 1) (.var 0))
          (packE (.lit 1) (.lit 0) nextKE (.var 0)))
        (packE (.lit 1) (.add (.var 3) (.lit 1)) (.var 1) (.var 0))) E
      (pack Q (stepP (2 * n + 1) s bit)) 100 := fun h => by
    refine (run_ite (Bc := 80) vb z (fun hb => ?_) (fun hb => ?_)).mono (by omega)
    · have hb' : bit = false := by cases bit <;> simp_all
      refine (run_ite (Bc := 70) vr z (fun hr => ?_) (fun hr => ?_)).mono (by omega)
      · have hr' : s.r = 0 := by omega
        have he : stepP (2 * n + 1) s bit = ⟨1, 0, s.k, s.f⟩ := by simp [stepP, h, hb', dstep, hr']
        rw [he] at hfit ⊢
        exact (run_packE h4 hQ hq o z vk vf hfit).mono (by omega)
      · have hr' : s.r ≠ 0 := by omega
        have he : stepP (2 * n + 1) s bit =
            ⟨1, 0, s.k / (2 * n + 1) + (2 * n + 1) ^ 2 * (s.r / 2), s.f⟩ := by
          simp [stepP, h, hb', dstep, hr']
        rw [he] at hfit ⊢
        simp only [pack] at hfit ⊢
        have g := run_g hC hnv
        have hsq : (2 * n + 1) * (2 * n + 1) < 2 ^ W := hC.cap_pow_lt (by
          show (2 * n + 1) * (2 * n + 1) ≤ (2 * n + 1) ^ 3
          nlinarith [Nat.le_self_pow (n := 3) (by norm_num) (2 * n + 1), Nat.pos_of_ne_zero
            (show (2 * n + 1) * (2 * n + 1) ≠ 0 by positivity)])
        have gg := run_mul g g hsq
        have hk' := run_div vk g
        have hr2 := run_div vr (run_lit (m := 2) h2)
        set K := s.k / (2 * n + 1) + (2 * n + 1) ^ 2 * (s.r / 2) with hK
        have hle0 : K ≤ K + Q * s.f := by omega
        have hle1 : K + Q * s.f ≤ Q * (K + Q * s.f) := Nat.le_mul_of_pos_left _ hQ
        have hKlt : K < 2 ^ W := by omega
        have eK : s.k / (2 * n + 1) + (2 * n + 1) * (2 * n + 1) * (s.r / 2) = K := by rw [hK, pow_two]
        have hsq2 : (2 * n + 1) * (2 * n + 1) * (s.r / 2) ≤ K := by
          rw [← eK]; exact Nat.le_add_left _ _
        have m12 := run_mul gg hr2 (by omega)
        have hadd := run_add hk' m12 (by rw [eK]; exact hKlt)
        have hadd' : Run W nextKE E K 40 := (hadd.val eK).mono (by omega)
        exact (run_packE h4 hQ hq o z hadd' vf hfit).mono (by omega)
    · have hb' : bit = true := by cases bit <;> simp_all
      have he : stepP (2 * n + 1) s bit = ⟨1, s.r + 1, s.k, s.f⟩ := by simp [stepP, h, hb', dstep]
      rw [he] at hfit ⊢
      simp only [pack] at hfit ⊢
      have hle1 : s.r + 1 ≤ (s.r + 1 + Q * (s.k + Q * s.f)) := by omega
      have hadd := run_add vr o (by omega)
      exact (run_packE h4 hQ hq o hadd vk vf hfit).mono (by omega)
  have hm3 : s.m = 0 ∨ s.m = 1 ∨ s.m = 2 := by omega
  refine (run_ite (Bc := 110) vm z (fun h => (m0 (by omega)).mono (by omega)) (fun h => ?_)).mono (by omega)
  refine (run_ite (Bc := 100) vm o (fun h' => (m1 (by omega))) (fun h' => m2 (by omega))).mono (by omega)

/-- **One step.** -/
theorem run_bodyE (hC : Ctx W n) (hQ : 1 ≤ Q) {s : PS} {pos x : ℕ} {T : List ℕ} (hm : s.m ≤ 2) (hr : s.r < Q)
    (hk : s.k < Q) (hkW : s.k < W) (hpos : pos + n + 1 < W) (hst : pack Q s < 2 ^ W)
    (hfit : pack Q (stepP (2 * n + 1) s (x.testBit (pos + n + 1))) < 2 ^ W) :
    Run W bodyE (pack Q s :: pos :: Q :: n :: x :: T)
      (pack Q (stepP (2 * n + 1) s (x.testBit (pos + n + 1)))) 200 := by
  have w := hC.one_le
  have hW8 := hC.eight_le
  have h4 : (4 : ℕ) < 2 ^ W := by
    calc 4 < 2 ^ 8 := by norm_num
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW8
  set st := pack Q s with hstdef
  set bit := x.testBit (pos + n + 1) with hbit
  have hposlt : pos + n + 1 < 2 ^ W := hpos.trans Nat.lt_two_pow_self
  -- the bit
  have r1 : Run W (.add (.add (.var 1) (.var 3)) (.lit 1)) (st :: pos :: Q :: n :: x :: T) (pos + n + 1) 5 :=
    (run_add (run_add (run_var (by simp)) (run_var (by simp)) (by omega)) (run_one w) hposlt).mono (by omega)
  have r2 : Run W (bitE 5 0) ((pos + n + 1) :: st :: pos :: Q :: n :: x :: T) bit.toNat 6 :=
    run_bit hC.two_le (by simp) (by simp) hpos
  have a0 := run_let r1 r2
  have emod : st % 4 = s.m := by
    rw [hstdef, pack]; exact add_mul_mod' (by omega)
  have ediv : st / 4 = s.r + Q * (s.k + Q * s.f) := by
    rw [hstdef, pack]; exact add_mul_div' (by omega)
  have a1 : Run W (.mod (.var 1) (.lit 4)) (bit.toNat :: st :: pos :: Q :: n :: x :: T) s.m 3 :=
    (run_mod (run_var (by simp)) (run_lit h4)).val emod
  have a2 : Run W (.div (.var 2) (.lit 4)) (s.m :: bit.toNat :: st :: pos :: Q :: n :: x :: T)
      (s.r + Q * (s.k + Q * s.f)) 3 :=
    (run_div (run_var (by simp)) (run_lit h4)).val ediv
  set u := s.r + Q * (s.k + Q * s.f) with hu
  have a3 : Run W (.mod (.var 0) (.var 5)) (u :: s.m :: bit.toNat :: st :: pos :: Q :: n :: x :: T) s.r 3 :=
    (run_mod (run_var (v := u) (by simp)) (run_var (v := Q) (by simp))).val (by rw [hu]; exact add_mul_mod' hr)
  have a4 : Run W (.div (.var 1) (.var 6)) (s.r :: u :: s.m :: bit.toNat :: st :: pos :: Q :: n :: x :: T)
      (s.k + Q * s.f) 3 :=
    (run_div (run_var (v := u) (by simp)) (run_var (v := Q) (by simp))).val (by rw [hu]; exact add_mul_div' hr)
  set v := s.k + Q * s.f with hv
  have a5 : Run W (.mod (.var 0) (.var 7))
      (v :: s.r :: u :: s.m :: bit.toNat :: st :: pos :: Q :: n :: x :: T) s.k 3 :=
    (run_mod (run_var (v := v) (by simp)) (run_var (v := Q) (by simp))).val (by rw [hv]; exact add_mul_mod' hk)
  have a6 : Run W (.div (.var 1) (.var 8))
      (s.k :: v :: s.r :: u :: s.m :: bit.toNat :: st :: pos :: Q :: n :: x :: T) s.f 3 :=
    (run_div (run_var (v := v) (by simp)) (run_var (v := Q) (by simp))).val (by rw [hv]; exact add_mul_div' hk)
  have b := run_branchE (x := x) (T := T) (pos := pos) (v := v) (u := u) hC hQ hm hkW (by omega) hfit
  have := run_let a0 (run_let a1 (run_let a2 (run_let a3 (run_let a4 (run_let a5 (run_let a6 b))))))
  exact this.mono (by omega)

end Step

end TransposeBase.Machine.Parse
