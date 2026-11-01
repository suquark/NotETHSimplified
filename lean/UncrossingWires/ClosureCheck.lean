import UncrossingWires.Machine.FinalMain

/-! Run with `lake env lean UncrossingWires/ClosureCheck.lean`. It shows that `UncrossingWires.Machine.not_ETH` does not depend on the
window, on determinants, on the search of the placement, or on the library `OnePigeonhole`. -/

open Lean Elab Command in
elab "#closure_check " n:ident : command => do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut stack := [n.getId]
  while !stack.isEmpty do
    let c := stack.head!
    stack := stack.tail!
    if seen.contains c then continue
    seen := seen.insert c
    if let some ci := env.find? c then
      let body : Array Name := match ci with
        | .thmInfo v => v.value.getUsedConstants
        | .defnInfo v => v.value.getUsedConstants
        | .opaqueInfo v => v.value.getUsedConstants
        | _ => #[]
      for d in ci.type.getUsedConstants ++ body do
        unless seen.contains d do stack := d :: stack
  logInfo m!"closure size {seen.size}"
  let names := seen.toList.map (·.toString)
  for s in ["OnePigeonhole", "Search.", "Chebyshev", "Fourier", "Matrix.det", "indow", ".det", "det_", "fourier", "Hermite", "partK", "fineC", "load_wordsOf"] do
    logInfo m!"{s}: {(names.filter fun x => (x.splitOn s).length > 1).length}"

#closure_check UncrossingWires.Machine.not_ETH
