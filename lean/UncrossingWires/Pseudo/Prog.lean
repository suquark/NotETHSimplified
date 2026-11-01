import UncrossingWires.Chain
import UncrossingWires.Base
import TransposeBase.Pseudo.LeafRun
import TransposeBase.Pseudo.Lag
import TransposeBase.Pseudo.Place
import TransposeBase.Pseudo.CnfNet

/-!
# The program of the uncrossing proof

Programs are expressions over words (`TransposeBase.Pseudo.Lang`). Helpers take variable indices as arguments, so an
argument never has to be shifted under a binder. `g` is the index of the frame: the variables `g, g + 1, ...` hold

`c, bk, sc, partT, headT, tailT, fw, v, m, encG, p, root, enc, n, rest`,

where `c` is the code of the chain, `sc = 2 * m` is the scale, and `bk` is the width of the fields of binomials.

A step takes a program for the weights of a level, `wt g ix iy`, and a program for its word functions, `word g ix iZ`,
and it gives the same programs for the next level. They recompute everything from the code `c`: the sizes of the words
of a level are constants, so the recomputation costs a constant factor.
-/

namespace UncrossingWires.Pseudo

open TransposeBase.Pseudo TransposeBase.Pseudo.Leaf

/-! ### Reading strings of letters -/

/-- The number of set bits below `j`, for variables `M`, `j`. -/
def popBE (iM ij : ℕ) : Expr := .sum (.var ij) (bitX (iM + 1) (.var 0))

/-- `3 ^ e`. -/
def pow3E (e : Expr) : Expr := .prod e (.lit 3)

/-- The letter `j` of the index `ξ`, for the variables `cheap`, `dir`, `m`, `ξ`, `j`. A Boolean is `0` or `1`. -/
def letterE (ic id im ixi ij : ℕ) : Expr :=
  .ite (.var im) (.var ij) (.lit 0) <|
    .ite (.var ic) (.lit 0)
      (.mod (.div (.var ixi) (.pow2 (.mul (.lit 2) (.var ij)))) (.lit 4))
      (.letE (.mod (.var ixi) (.pow2 (.var im))) <|
        .ite (bitX 0 (.var (ij + 1))) (.lit 0)
          (.add
            (.mod (.div (.div (.var (ixi + 1)) (.pow2 (.var (im + 1))))
              (pow3E (.sub (.var (ij + 1)) (popBE 0 (ij + 1))))) (.lit 3))
            (.ite (.var (id + 1)) (.lit 0) (.lit 1) (.lit 0)))
          (.ite (.var (id + 1)) (.lit 0) (.lit 0) (.lit 3)))

/-- `chi`, for a variable letter and two bits given by expressions. -/
def chiE (il : ℕ) (a b : Expr) : Expr :=
  let sg : Expr := .ite a (.lit 0) (.lit 1) (.sub (.lit 0) (.lit 1))
  .ite (.var il) (.lit 0) (eqX a b (.lit 1) (.lit 0)) <|
    .ite (.var il) (.lit 1) (eqX a b (.lit 0) (.lit 1)) <|
      .ite (.var il) (.lit 2) (eqX a b sg (.lit 0)) (eqX a b (.lit 0) sg)

/-- `fpat` of the string of letters of an index. -/
def fpatE (ic id im ixi ip iq : ℕ) : Expr :=
  .prod (.var im) <|
    .letE (letterE (ic + 1) (id + 1) (im + 1) (ixi + 1) 0) <|
      chiE 0 (bitX (ip + 2) (.var 1)) (bitX (iq + 2) (.var 1))

/-- `cnt` of the string of letters of an index. -/
def cntE (ic id im ixi l : ℕ) : Expr :=
  .sum (.var im) <|
    .letE (letterE (ic + 1) (id + 1) (im + 1) (ixi + 1) 0) <|
      eqX (.var 0) (.lit l) (.lit 1) (.lit 0)

/-- `if condP pol m r then c else d`. -/
def condE (ipol im ir : ℕ) (c d : Expr) : Expr :=
  let t : Expr := .div (.add (.var im) (.lit 1)) (.lit 2)
  .ite (.var ipol) (.lit 0) (.ite t (.var ir) d c) (.ite t (.var ir) c d)

/-- `(-1) ^ r`, for a variable `r`. -/
def signE (ir : ℕ) : Expr :=
  .ite (.mod (.var ir) (.lit 2)) (.lit 0) (.lit 1) (.sub (.lit 0) (.lit 1))

/-- `coefR`. -/
def coefRE (ipol im in3 ibk : ℕ) : Expr :=
  .sum (.add (.var in3) (.lit 1)) <|
    condE (ipol + 1) (im + 1) 0
      (.mul (.mul (Lag.chooseE (in3 + 1) (ibk + 1) 0) (signE 0)) (.pow2 (.var 0))) (.lit 0)

/-- `coefC`. -/
def coefCE (ipol im in0 in3 ibk : ℕ) : Expr :=
  .mul (signE in3) <|
    .sum (.add (.var in0) (.lit 1)) <|
      .letE (.add (.sub (.var (im + 1)) (.var (in0 + 1))) (.var 0)) <|
        condE (ipol + 2) (im + 2) 0
          (.mul (.mul (Lag.chooseE (in0 + 2) (ibk + 2) 1) (.pow2 (.sub (.var (in0 + 2)) (.var 1))))
            (signE 1)) (.lit 0)

/-- `rectCoef`. -/
def rectCoefE (ic id ipol im ixi ibk : ℕ) : Expr :=
  .letE (cntE ic id im ixi 3) <|
  .letE (cntE (ic + 1) (id + 1) (im + 1) (ixi + 1) 0) <|
    .ite (.var (id + 2)) (.lit 0)
      (coefCE (ipol + 2) (im + 2) 0 1 (ibk + 2))
      (coefRE (ipol + 2) (im + 2) 1 (ibk + 2))

/-- `1` if the index is valid, and `0` if not. -/
def validE (ic im ixi : ℕ) : Expr :=
  .ite (.var ic) (.lit 0) (.lit 1) <|
    .letE (.mod (.var ixi) (.pow2 (.var im))) <|
      .ite (.add (.div (.var (ixi + 1)) (.pow2 (.var (im + 1)))) (.lit 1))
        (pow3E (.sub (.var (im + 1)) (popBE 0 (im + 1)))) (.lit 1) (.lit 0)

/-- `rectA`. Variables: `dir`, `pol`, `scale`, `m`, `ξ`, `p`, `q`, `bk`. -/
def rectAE (id ipol isc im ixi ip iq ibk : ℕ) : Expr :=
  .letE (eqX (.var ipol) (.var id) (.lit 1) (.lit 0)) <|
    .ite (validE 0 (im + 1) (ixi + 1)) (.lit 0) (.lit 0) <|
      .mul
        (.mul (.pow2 (.sub (.var (isc + 1)) (.var (im + 1))))
          (rectCoefE 0 (id + 1) (ipol + 1) (im + 1) (ixi + 1) (ibk + 1)))
        (fpatE 0 (id + 1) (im + 1) (ixi + 1) (ip + 1) (iq + 1))

/-- `rectB`. -/
def rectBE (id ipol im ixi ir is : ℕ) : Expr :=
  .letE (eqX (.var ipol) (.var id) (.lit 1) (.lit 0)) <|
    .ite (validE 0 (im + 1) (ixi + 1)) (.lit 0) (.lit 0) <|
      fpatE 0 (id + 1) (im + 1) (ixi + 1) (ir + 1) (is + 1)

/-! ### One step: the weights -/

section Step

variable (K' base : ℕ) (wt : ℕ → ℕ → ℕ → Expr)

/-- `Lev.wd`, for a variable direction. -/
def wdE (id iu iv : ℕ) : Expr :=
  .ite (.var id) (.lit 0)
    (.add (.mul (.var iv) (.lit K')) (.var iu))
    (.add (.mul (.var iu) (.lit K')) (.var iv))

/-- `oddMin`. -/
def oddMinE (ia ib : ℕ) : Expr :=
  .letE (.ite (.var ia) (.var ib) (.var ia) (.var ib)) <|
    .ite (.var 0) (.lit 0) (.lit 0) <|
      .ite (.mod (.var 0) (.lit 2)) (.lit 0) (.sub (.var 0) (.lit 1)) (.var 0)

/-- `Lev.pm`. -/
def pmE (g id iu iu' iv iv' : ℕ) : Expr :=
  eqX (.var iu) (.var iu') (.lit 0) <|
  eqX (.var iv) (.var iv') (.lit 0) <|
    .letE (wdE K' id iu iv) <|
    .letE (wdE K' (id + 1) (iu' + 1) (iv' + 1)) <|
    .letE (wdE K' (id + 2) (iu + 2) (iv' + 2)) <|
    .letE (wdE K' (id + 3) (iu' + 3) (iv + 3)) <|
    .letE (wt (g + 4) 3 2) <|
    .letE (wt (g + 5) 2 1) <|
      oddMinE 1 0

/-- `Lev.idx`. -/
def idxE (id iu iu' iv iv' : ℕ) : Expr :=
  let d4 (a b c e : ℕ) : Expr :=
    .add (.mul (.add (.mul (.add (.mul (.var a) (.lit K')) (.var b)) (.lit K')) (.var c)) (.lit K')) (.var e)
  .ite (.var id) (.lit 0) (d4 iv iv' iu iu') (d4 iu iu' iv iv')

/-- `Lev.pol`, as `0` or `1`. The bits of this step start at `base`. -/
def polE (g id iu iu' iv iv' : ℕ) : Expr :=
  .ite (bitX g (.add (.lit base) (idxE K' id iu iu' iv iv'))) (.lit 0) (.lit 1) (.lit 0)

/-- `dLen`, for the variables `cheap`, `m`. -/
def dLenE (ic im : ℕ) : Expr :=
  .ite (.var ic) (.lit 0)
    (.mul (.lit 2) (.var im))
    (.add (.var im) (.div (.add (.mul (.lit 8) (.div (.var im) (.lit 2))) (.lit 4)) (.lit 5)))

/-- `Lev.dd`. -/
def ddE (g id iu iu' iv iv' : ℕ) : Expr :=
  .ite (.var iv') (.var iv) (.lit 0) <|
    .letE (polE K' base g id iu iu' iv iv') <|
    .letE (pmE K' wt (g + 1) (id + 1) (iu + 1) (iu' + 1) (iv + 1) (iv' + 1)) <|
    .letE (eqX (.var 1) (.var (id + 2)) (.lit 1) (.lit 0)) <|
      dLenE 0 1

/-- `Lev.carry`. -/
def carryE (g id iu iu' iv iv' : ℕ) : Expr :=
  .letE (wdE K' id iu iv) <|
  .letE (wdE K' (id + 1) (iu' + 1) (iv' + 1)) <|
    .sub (wt (g + 2) 1 0) (pmE K' wt (g + 2) (id + 2) (iu + 2) (iu' + 2) (iv + 2) (iv' + 2))

/-- `Lev.seg`. -/
def segE (g id iu iu' iv iv' : ℕ) : Expr :=
  .add (carryE K' wt g id iu iu' iv iv') (ddE K' base wt g id iu iu' iv iv')

/-- `Lev.segS`. -/
def segSE (g id iu iu' is : ℕ) : Expr :=
  .letE (.div (.var is) (.lit K')) <|
  .letE (.mod (.var (is + 1)) (.lit K')) <|
    segE K' base wt (g + 2) (id + 2) (iu + 2) (iu' + 2) 1 0

/-- `Lev.newW`, for a variable direction. -/
def newWE (g id iu iu' : ℕ) : Expr :=
  eqX (.var iu) (.var iu') (.lit 0) <|
    .letE (.ite (.var iu) (.var iu') (.var iu) (.var iu')) <|
    .letE (.ite (.var (iu + 1)) (.var (iu' + 1)) (.var (iu' + 1)) (.var (iu + 1))) <|
      .sum (.lit (K' * K')) (segSE K' base wt (g + 3) (id + 3) 2 1 0)

/-- `psi` of the new weights, for a variable direction. -/
def psiE (g id : ℕ) : Expr :=
  .sum (.lit K') <| .sum (.lit K') <|
    .letE (newWE K' base wt (g + 2) (id + 2) 1 0) (.mul (.var 0) (.var 0))

/-- `dirOf`, as `0` or `1`. -/
def dirE (g : ℕ) : Expr :=
  .ite (.letE (.lit 1) (psiE K' base wt (g + 1) 0)) (.letE (.lit 0) (psiE K' base wt (g + 1) 0))
    (.lit 1) (.lit 0)

/-- The program of the weights of the next level. -/
def wtNext (g ix iy : ℕ) : Expr :=
  .letE (dirE K' base wt g) (newWE K' base wt (g + 1) 0 (ix + 1) (iy + 1))

/-! ### One step: the word functions -/

/-- The number of ends on a word. -/
def endsE (K g ix : ℕ) : Expr := .sum (.lit K) (wt (g + 1) (ix + 1) 0)

/-- The position of the number towards `y`, on the word `x`. -/
def offE (g ix iy : ℕ) : Expr := .sum (.var iy) (wt (g + 1) (ix + 1) 0)

/-- The position of the word `wd u v`, in the number of the words of `u`. -/
def rowOffE (g id iu iv : ℕ) : Expr :=
  .sum (.var iv) <| .letE (wdE K' (id + 1) (iu + 1) 0) (endsE wt (K' * K') (g + 2) 0)

/-- The number of the word `wd u v`, from the number `Z` of the words of `u`. -/
def zvE (g id iu iZ iv : ℕ) : Expr :=
  .letE (wdE K' id iu iv) <|
    .mod (.div (.var (iZ + 1)) (.pow2 (rowOffE K' wt (g + 1) (id + 1) (iu + 1) (iv + 1))))
      (.pow2 (endsE wt (K' * K') (g + 1) 0))

/-- `B v y`: the number of the word `wd u v` towards `y`. -/
def bvE (g id iu iZ iv iy : ℕ) : Expr :=
  .letE (wdE K' id iu iv) <|
  .letE (zvE K' wt (g + 1) (id + 1) (iu + 1) (iZ + 1) (iv + 1)) <|
    .mod (.div (.var 0) (.pow2 (offE wt (g + 2) 1 (iy + 2)))) (.pow2 (wt (g + 2) 1 (iy + 2)))

/-- `B' u'`: the new number at `u` towards `u'`. -/
def bpE (g id iu iZ iu' : ℕ) : Expr :=
  .mod (.div (.var iZ) (.pow2 (.sum (.var iu') (newWE K' base wt (g + 1) (id + 1) (iu + 1) 0))))
    (.pow2 (newWE K' base wt g id iu iu'))

/-- Field `s` of the number `b`, whose fields are the segments of the pair `u1 < u2`. -/
def segPartE (g id iu1 iu2 ib is : ℕ) : Expr :=
  .mod (.div (.var ib) (.pow2 (.sum (.var is) (segSE K' base wt (g + 1) (id + 1) (iu1 + 1) (iu2 + 1) 0))))
    (.pow2 (segSE K' base wt g id iu1 iu2 is))

/-- `Lev.segT`. -/
def segTE (g id iu iu' iv iv' ib iZ : ℕ) : Expr :=
  .ite (.var iu') (.var iu)
    -- the word `u'` is below the word `u`
    (.letE (pmE K' wt g id iu' iu iv iv') <|
     .letE (carryE K' wt (g + 1) (id + 1) (iu' + 1) (iu + 1) (iv + 1) (iv' + 1)) <|
     .letE (wdE K' (id + 2) (iu' + 2) (iv' + 2)) <|
     .letE (bvE K' wt (g + 3) (id + 3) (iu + 3) (iZ + 3) (iv + 3) 0) <|
     .letE (wdE K' (id + 4) (iu' + 4) (iv + 4)) <|
     .letE (bvE K' wt (g + 5) (id + 5) (iu + 5) (iZ + 5) (iv' + 5) 0) <|
      .mul
        (eqX (.mod (.var (ib + 6)) (.pow2 (.var 4)))
          (.div (.var 0) (.pow2 (.var 5))) (.lit 1) (.lit 0))
        (.ite (.var (iv' + 6)) (.var (iv + 6)) (.lit 1) <|
          .letE (polE K' base (g + 6) (id + 6) (iu' + 6) (iu + 6) (iv + 6) (iv' + 6)) <|
          .letE (.div (.var (ib + 7)) (.pow2 (.var 5))) <|
          .letE (.mod (.var 4) (.pow2 (.var 7))) <|
          .letE (.mod (.var 3) (.pow2 (.var 8))) <|
            rectBE (id + 10) 3 9 2 1 0))
    -- the word `u` is below the word `u'`
    (.letE (pmE K' wt g id iu iu' iv iv') <|
     .letE (carryE K' wt (g + 1) (id + 1) (iu + 1) (iu' + 1) (iv + 1) (iv' + 1)) <|
     .letE (wdE K' (id + 2) (iu' + 2) (iv' + 2)) <|
     .letE (bvE K' wt (g + 3) (id + 3) (iu + 3) (iZ + 3) (iv + 3) 0) <|
     .letE (wdE K' (id + 4) (iu' + 4) (iv + 4)) <|
     .letE (bvE K' wt (g + 5) (id + 5) (iu + 5) (iZ + 5) (iv' + 5) 0) <|
      .mul
        (eqX (.mod (.var (ib + 6)) (.pow2 (.var 4)))
          (.div (.var 2) (.pow2 (.var 5))) (.lit 1) (.lit 0))
        (.ite (.var (iv' + 6)) (.var (iv + 6)) (.lit 1) <|
          .letE (polE K' base (g + 6) (id + 6) (iu + 6) (iu' + 6) (iv + 6) (iv' + 6)) <|
          .letE (.div (.var (ib + 7)) (.pow2 (.var 5))) <|
          .letE (.mod (.var 4) (.pow2 (.var 7))) <|
          .letE (.mod (.var 3) (.pow2 (.var 8))) <|
            rectAE (id + 10) 3 (g + 10 + 2) 9 2 1 0 (g + 10 + 1)))

/-- `Lev.trans`. `Z` is the number of the words of `u`, and `Z'` is the new number at `u`. -/
def transE (g id iu iZ iZ' : ℕ) : Expr :=
  .mul
    (.prod (.lit K') <| .prod (.lit K') <|
      .ite (.var 0) (.var 1) (.lit 1) <|
        .letE (wdE K' (id + 2) (iu + 2) 0) <|
        .letE (wdE K' (id + 3) (iu + 3) 2) <|
        .letE (bvE K' wt (g + 4) (id + 4) (iu + 4) (iZ + 4) 3 1) <|
        .letE (bvE K' wt (g + 5) (id + 5) (iu + 5) (iZ + 5) 3 1) <|
          eqX (.var 1) (.var 0) (.lit 1) (.lit 0))
    (.prod (.lit K') <|
      eqX (.var 0) (.var (iu + 1)) (.lit 1) <|
        .letE (bpE K' base wt (g + 1) (id + 1) (iu + 1) (iZ' + 1) 0) <|
        .letE (.ite (.var (iu + 2)) (.var 1) (.var (iu + 2)) (.var 1)) <|
        .letE (.ite (.var (iu + 3)) (.var 2) (.var 2) (.var (iu + 3))) <|
        .prod (.lit (K' * K')) <|
          .letE (segPartE K' base wt (g + 5) (id + 5) 2 1 3 0) <|
          .letE (.div (.var 1) (.lit K')) <|
          .letE (.mod (.var 2) (.lit K')) <|
            segTE K' base wt (g + 8) (id + 8) (iu + 8) 7 1 0 2 (iZ + 8))

/-- The program of the word functions of the next level. -/
def wordNext (word : ℕ → ℕ → ℕ → Expr) (g iu iZ' : ℕ) : Expr :=
  .letE (dirE K' base wt g) <|
    .sum (.pow2 (.sum (.lit K') <|
      .letE (wdE K' 1 (iu + 2) 0) (endsE wt (K' * K') (g + 3) 0))) <|
      .mul (transE K' base wt (g + 2) 1 (iu + 2) 0 (iZ' + 2)) <|
        .prod (.lit K') <|
          .letE (wdE K' 2 (iu + 3) 0) <|
          .letE (zvE K' wt (g + 4) 3 (iu + 4) 2 1) <|
            word (g + 5) 1 0

end Step

/-! ### The value of the last level, and the codes -/

/-- `val` of the last level, with the numbers read from one number. -/
def finalE (L : ℕ) (wt word : ℕ → ℕ → ℕ → Expr) (g : ℕ) : Expr :=
  .sum (.pow2 (.sum (.lit L) (endsE wt L (g + 1) 0))) <|
    let zx (iZ ix ig : ℕ) : Expr :=
      .mod (.div (.var iZ) (.pow2 (.sum (.var ix) (endsE wt L (ig + 1) 0))))
        (.pow2 (endsE wt L ig ix))
    .mul
      (.prod (.lit L) <| .prod (.lit L) <|
        .letE (zx 2 1 (g + 3)) <|
        .letE (zx 3 1 (g + 4)) <|
        eqX
          (.mod (.div (.var 1) (.pow2 (offE wt (g + 5) 3 2))) (.pow2 (wt (g + 5) 3 2)))
          (.mod (.div (.var 0) (.pow2 (offE wt (g + 5) 2 3))) (.pow2 (wt (g + 5) 2 3)))
          (.lit 1) (.lit 0))
      (.prod (.lit L) <|
        .letE (zx 1 0 (g + 2)) <|
          word (g + 3) 1 0)

/-- `1` if the bits of one step form a valid code, and `0` if not. -/
def validStepE (K' base g : ℕ) : Expr :=
  .prod (.lit K') <| .prod (.lit K') <| .prod (.lit K') <| .prod (.lit K') <|
    .ite (.ite (.var 2) (.var 3) (.lit 0) (.ite (.var 0) (.var 1) (.lit 0) (.lit 1))) (.lit 0)
      (.ite (bitX (g + 4) (.add (.lit base)
        (.add (.mul (.add (.mul (.add (.mul (.var 3) (.lit K')) (.var 2)) (.lit K')) (.var 1)) (.lit K')) (.var 0))))
        (.lit 0) (.lit 1) (.lit 0))
      (.lit 1)

/-! ### The first level -/

/-- The word of the tail of the wire `ie`. -/
def twE (g ie : ℕ) : Expr := Place.endPartE (g + 5) (g + 3) ie (g + 6)

/-- The word of the head of the wire `ie`. -/
def hwE (g ie : ℕ) : Expr := Place.endPartE (g + 4) (g + 3) ie (g + 6)

/-- `1` if the words in the variables `itw`, `ihw` are the words `x`, `y` in either order, and `0` if not. -/
def joinsE (itw ihw ix iy : ℕ) : Expr :=
  eqX (.var itw) (.var ix)
    (eqX (.var ihw) (.var iy) (.lit 1)
      (eqX (.var itw) (.var iy) (eqX (.var ihw) (.var ix) (.lit 1) (.lit 0)) (.lit 0)))
    (eqX (.var itw) (.var iy) (eqX (.var ihw) (.var ix) (.lit 1) (.lit 0)) (.lit 0))

/-- `BaseNet.w0`. -/
def wt0E (g ix iy : ℕ) : Expr :=
  .sum (.var (g + 8)) <|
    .letE (twE (g + 1) 0) <|
    .letE (hwE (g + 2) 1) <|
      joinsE 1 0 (ix + 3) (iy + 3)

/-- `BaseNet.rk` of the wire `ie`. -/
def rkE (g ie : ℕ) : Expr :=
  .letE (twE g ie) <|
  .letE (hwE (g + 1) (ie + 1)) <|
    .sum (.var (ie + 2)) <|
      .letE (twE (g + 3) 0) <|
      .letE (hwE (g + 4) 1) <|
        joinsE 1 0 4 3

/-- The bit of the wire `e` at the word `x`, for the numbers in the variable `Z` of the word `x`. The other end of the wire
is on the word in the variable `iy`. -/
def endBitE (g ix iZ iy ie : ℕ) : Expr :=
  .letE (.mod (.div (.var iZ) (.pow2 (offE wt0E g ix iy))) (.pow2 (wt0E g ix iy))) <|
    bitX 0 (rkE (g + 1) (ie + 1))

/-- `BaseNet.aWord`. -/
def aWordE (g ix iZ : ℕ) : Expr :=
  .sum (.var (g + 8)) <|
    .letE (twE (g + 1) 0) <|
    .letE (hwE (g + 2) 1) <|
      .add
        (eqX (.var 1) (.var (ix + 3))
          (.mul (endBitE (g + 3) (ix + 3) (iZ + 3) 0 2) (.pow2 (.var 2)))
          (.lit 0))
        (eqX (.var 0) (.var (ix + 3))
          (.mul (endBitE (g + 3) (ix + 3) (iZ + 3) 1 2) (.pow2 (.add (.var (g + 3 + 8)) (.var 2))))
          (.lit 0))

/-- The word function of the first level. `nodeG g'` is the program of the node, where the frame has index `g'` in the
environment `α :: A :: m :: v :: 0 :: fw :: tailT :: headT :: α :: A :: ...` of the node, counting from `α`. -/
def word0E (nodeG : ℕ → Expr) (g ix iZ : ℕ) : Expr :=
  .letE (aWordE g ix iZ) <|
    .prod (.var (g + 1 + 7)) <|
      eqX (Place.fieldE (g + 2 + 3) 0 (g + 2 + 6)) (.var (ix + 2))
        (.letE (.var (g + 2 + 4)) <|
         .letE (.var (g + 3 + 5)) <|
         .letE (.var (g + 4 + 6)) <|
         .letE (.lit 0) <|
         .letE (.var (g + 6 + 7)) <|
         .letE (.var (g + 7 + 8)) <|
         .letE (.var 7) <|
         .letE (.var 7) <|
           nodeG (g + 10))
        (.lit 1)

/-! ### The chain -/

/-- The number of words at depth `d`, from height `H`. -/
def Kd (L H d : ℕ) : ℕ := Ktow L (H - d)

/-- The first bit of the step from depth `d`. -/
def baseD (L H : ℕ) : ℕ → ℕ
  | 0 => 0
  | d + 1 => baseD L H d + Kd L H (d + 1) ^ 4

/-- The program of the weights at depth `d`. -/
def wtD (L H : ℕ) : ℕ → ℕ → ℕ → ℕ → Expr
  | 0 => wt0E
  | d + 1 => wtNext (Kd L H (d + 1)) (baseD L H d) (wtD L H d)

/-- The program of the word functions at depth `d`. -/
def wordD (L H : ℕ) (nodeG : ℕ → Expr) : ℕ → ℕ → ℕ → ℕ → Expr
  | 0 => word0E nodeG
  | d + 1 => wordNext (Kd L H (d + 1)) (baseD L H d) (wtD L H d) (wordD L H nodeG d)

/-- `1` if the bits of the first `d` steps form valid codes, and `0` if not. -/
def validD (L H g : ℕ) : ℕ → Expr
  | 0 => .lit 1
  | d + 1 => .mul (validD L H g d) (validStepE (Kd L H (d + 1)) (baseD L H d) g)

/-- The core of the program: the sum over the codes of a chain of `H` steps. The variable `0` is the code in the body. -/
def coreE (L H : ℕ) (nodeG : ℕ → Expr) : Expr :=
  .sum (.pow2 (.lit (chainBits L H))) <|
    .mul (validD L H 0 H) (finalE L (wtD L H H) (wordD L H nodeG H) 0)

/-! ### The placement

The table `R` holds the words of the nodes below `α`, one field for each node. The tables `tailT`, `headT` hold the ends of
the wires. `UncrossingWires/Greedy.lean` has the mathematics. -/

/-- `Greedy.load`: the number of wires with head below `α`, tail word `x` and head word `y`. -/
def loadE (im it ih ifw iR iα ix iy : ℕ) : Expr :=
  .sum (.var im) <|
    .letE (Place.fieldE (it + 1) 0 (ifw + 1)) <|
    .letE (Place.fieldE (ih + 2) 1 (ifw + 2)) <|
      .ite (.var (iα + 3)) (.var 0) (.lit 0) <|
        eqX (Place.fieldE (iR + 3) 1 (ifw + 3)) (.var (ix + 3))
          (eqX (Place.fieldE (iR + 3) 0 (ifw + 3)) (.var (iy + 3)) (.lit 1) (.lit 0))
          (.lit 0)

/-- `Greedy.score`: the sum of the loads from the words of the tails of `α` towards the word `y`. -/
def scoreE (im it ih ifw iR iα iy : ℕ) : Expr :=
  .sum (.var im) <|
    eqX (Place.fieldE (ih + 1) 0 (ifw + 1)) (.var (iα + 1))
      (.letE (Place.fieldE (it + 1) 0 (ifw + 1)) <|
       .letE (Place.fieldE (iR + 2) 0 (ifw + 2)) <|
         loadE (im + 3) (it + 3) (ih + 3) (ifw + 3) (iR + 3) (iα + 3) 0 (iy + 3))
      (.lit 0)

/-- `Greedy.best`: the first word below `K` with the minimal score. The state of the loop is the best word so far. -/
def pickE (K im it ih ifw iR iα : ℕ) : Expr :=
  .fold (.lit K) (.lit 0) <|
    .ite (scoreE (im + 2) (it + 2) (ih + 2) (ifw + 2) (iR + 2) (iα + 2) 0)
      (scoreE (im + 2) (it + 2) (ih + 2) (ifw + 2) (iR + 2) (iα + 2) 1)
      (.var 0) (.var 1)

/-- `Greedy.table`: the words of all nodes. A node below `n` gets `α % K`, and the other nodes get the word of `pickE`. The state
of the loop is the table of the nodes below `α`. -/
def greedyE (K inn im iv ifw it ih : ℕ) : Expr :=
  .fold (.var iv) (.lit 0) <|
    .letE
      (.ite (.var (inn + 2)) (.var 1)
        (pickE K (im + 2) (it + 2) (ih + 2) (ifw + 2) 0 1)
        (.mod (.var 1) (.lit K))) <|
      Place.setE 1 0 2 (ifw + 3)

/-- The program of a leaf of the branching tree. It runs on `encF n G :: p :: root :: enc :: n :: rest`. -/
def leafE (L H : ℕ) : Expr :=
  .letE (CnfNet.mE 4 0) <|
  .letE (CnfNet.vE 5 1) <|
  .letE (CnfNet.fwE (Ktow L H) 1 0) <|
  .letE (CnfNet.tailTE 7 3 0) <|
  .letE (CnfNet.headTE 8 4 1) <|
  .letE (greedyE (Ktow L H) 9 4 3 2 1 0) <|
  .letE (.mul (.lit 2) (.var 5)) <|
  .letE (.mul (.add (.var 0) (.lit 2)) (.add (.var 0) (.lit 2))) <|
    coreE L H (fun g => CnfNet.nodeE (g + 13) (g + 9))

end UncrossingWires.Pseudo
