import OnePigeonhole.Machine.FinalMain

/-! Run with `lake env lean OnePigeonhole/ClosureCheck.lean`. It shows that `OnePigeonhole.Machine.not_ETH` has no constant of the namespace below, and that it does use the decomposition of this library. -/

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
  let names := seen.toList
  let mut failed : List Name := []
  -- constants of these namespaces must not occur: every count must be 0
  for p in [`UncrossingWires] do
    let count := (names.filter fun x => p.isPrefixOf x).length
    logInfo m!"constants under {p}: {count}"
    if count != 0 then failed := p :: failed
  -- these theorems must occur: every answer must be true
  for f in [`OnePigeonhole.net_decomp_masks, `OnePigeonhole.prod_eqv_eq_sum_rowMix] do
    logInfo m!"{f}: {seen.contains f}"
    unless seen.contains f do failed := f :: failed
  logInfo m!"constants of OnePigeonhole: {(names.filter fun x => (`OnePigeonhole).isPrefixOf x).length}"
  unless failed.isEmpty do throwError m!"the closure check failed at {failed}"

#closure_check OnePigeonhole.Machine.not_ETH
