import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CompileSpace

/-! The output and both resource bounds are about a single primitive run.
The source program and its complete execution must be provided by the user. -/
namespace FormalizationKit.ResourceTransfer
open OAI.Algorithms.SubexponentialSAT
open BitProgram SqrtLogSpace SqrtLogSpace.GuardedCompiler

theorem primitive_of_source {r s l : ℕ} (program : Program r s l)
    (input : List Bool) (answer : Bool) (timeBound stackBound inputBound : ℕ)
    (inputSize : input.length ≤ inputBound)
    (source : ∃ steps ≤ timeBound,∃ final,
      Trace program steps (initial program input) final ∧
      final.pc=none ∧ final.stacks program.outputStack=[answer] ∧
      ∀ n c,n ≤ steps → Trace program n (initial program input) c →
        ∀ j,(c.stacks j).length ≤ stackBound) :
    ∃ time ≤ 7*timeBound,∃ d : LocatedCfg (primitive program),
      Computation.Trace (locatedStep (primitive program)) time (locatedInit (primitive program) input) d ∧
      d.config.state=.inl answer ∧
      d.config.tapes program.outputStack=Turing.Tape.mk₁ [some answer] ∧
      ∀ n c,n ≤ time →
        Computation.Trace (locatedStep (primitive program)) n (locatedInit (primitive program) input) c →
        visitedSpace c ≤ s*(stackBound+inputBound+15) := by
  obtain ⟨steps,hsteps,final,ht,hhalt,hanswer,hspace⟩ := source
  obtain ⟨time,htime,d,hrun,hout,htape,hcap⟩ :=
    CompileSpace.compile_word_space program ht hhalt hanswer hspace
  refine ⟨time,htime.trans (Nat.mul_le_mul_left 7 hsteps),d,hrun,?_,?_,?_⟩
  · simpa only [List.head?_cons,Option.getD_some] using hout
  · simpa only [List.map_cons,List.map_nil] using htape
  · intro n c hn hc
    exact (hcap n c hn hc).trans (Nat.mul_le_mul_left s (by omega))

end FormalizationKit.ResourceTransfer
