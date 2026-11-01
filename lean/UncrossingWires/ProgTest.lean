import UncrossingWires.Pseudo.Prog
/-!
Runs the program of `Prog.lean` on tiny networks and compares with brute force. It is not part of the proof, and nothing imports it.
Run it with `lake env lean UncrossingWires/ProgTest.lean`. Each line prints `(true, count, value)`, where `value` is `count` times the power of two.
A node function here reads only the bits of its wires, as the node functions of a formula do.
-/

open TransposeBase.Pseudo TransposeBase.Pseudo.Leaf UncrossingWires UncrossingWires.Pseudo

def W : ℕ := 500
def pack (fw : ℕ) (l : List ℕ) : ℕ := (l.zipIdx.map fun (a, i) => a * 2 ^ (fw * i)).sum

/-- The mock node function, in the environment `α :: A :: m :: v :: c :: fw :: tT :: hT :: ...`. -/
def nodeM (_ : ℕ) : Expr :=
  .add (.add (.lit 1) (.var 0)) <|
    .sum (.var 2) <|   -- e at 0, α at 1, A at 2, m at 3, v at 4, c at 5, fw at 6, tT at 7, hT at 8
      .mul (.add (.var 0) (.lit 1)) <|
        eqX (Place.fieldE 7 0 6) (.var 1)
          (bitX 2 (.var 0))
          (eqX (Place.fieldE 8 0 6) (.var 1) (bitX 2 (.add (.var 3) (.var 0))) (.lit 0))

def frame (c bk sc pT hT tT fw v m : ℕ) : List ℕ := [c, bk, sc, pT, hT, tT, fw, v, m, 0, 0, 0, 0, 0]

def brute (m v fw tT hT : ℕ) : ℕ :=
  ((List.range (2 ^ m)).map fun z =>
    ((List.range v).map fun α =>
      eval W (nodeM 0) [α, z + 2 ^ m * z, m, v, 0, fw, tT, hT]).prod).sum

/-- wires: pairs of nodes; words of the nodes. -/
def test (L H : ℕ) (codes : List ℕ) (wires : List (ℕ × ℕ)) (words : List ℕ) : Bool × ℕ × ℕ :=
  let fw := 8
  let m := wires.length
  let v := words.length
  let tT := pack fw (wires.map (·.1))
  let hT := pack fw (wires.map (·.2))
  let pT := pack fw words
  let sc := 2 * m
  let bk := (sc + 2) * (sc + 2)
  let b := brute m v fw tT hT
  let body := Expr.mul (validD L H 0 H) (finalE L (wtD L H H) (wordD L H nodeM H) 0)
  let r := (codes.map fun c => eval W body (frame c bk sc pT hT tT fw v m)).sum % 2 ^ W
  let s := sc * nRect (Ktow L (H - 1)) + 0
  (r == (b * 2 ^ s) % 2 ^ W, b, r)

#eval test 2 1 [0] [(0, 1)] [0, 1]
#eval test 2 1 [0, 32] [(0, 1), (2, 3)] [0, 3, 1, 2]
#eval test 2 1 [0, 32] [(0, 1), (2, 3), (0, 2)] [0, 3, 1, 2]
#eval test 2 1 [0, 32] [(0, 1), (2, 3), (1, 2)] [0, 3, 2, 1]
#eval test 2 1 [0, 32] [(0, 1), (1, 2)] [0, 0, 1]
