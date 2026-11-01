import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.StackRoutines
namespace FormalizationKit.StackCalls
open OAI.Algorithms.SubexponentialSAT
open BitProgram ProgramLinking StructuredCalls
abbrev copyCall {S : ℕ} (src dst tmp : Fin S) : Cmd 10 S :=
  .call (StackRoutines.copyProgram src dst tmp (0 : Fin 10) 1)
abbrev transferCall {S : ℕ} (src dst : Fin S) : Cmd 10 S :=
  .call (StackRoutines.transferProgram src dst (0 : Fin 10) 1)
abbrev clearCall {S : ℕ} (src : Fin S) : Cmd 10 S :=
  .call (StackRoutines.clearProgram src (0 : Fin 10) 1)

theorem copy_eval {S : ℕ} (src dst tmp : Fin S) (hsd : src≠dst) (hst : src≠tmp) (htd : tmp≠dst)
    (regs : Fin 10 → Bool) (stk : Fin S → List Bool) (ht : stk tmp=[]) :
    Eval (copyCall src dst tmp) (7*(stk src).length+5) ⟨regs,stk⟩
      ⟨readRegs regs 0 1 none,StackRoutines.copyStacks src dst stk⟩ := by
  apply Eval.call
  have h := StackRoutines.halt_after_trace _
    (StackRoutines.copyProgram_trace src dst tmp (0 : Fin 10) 1 hsd hst htd (by decide) regs stk ht) 7 rfl rfl
  simpa [StackRoutines.copyResult,StructuredProgram.State.withPC,Nat.add_assoc] using h

theorem transfer_eval {S : ℕ} (src dst : Fin S) (hsd : src≠dst)
    (regs : Fin 10 → Bool) (stk : Fin S → List Bool) :
    Eval (transferCall src dst) (3*(stk src).length+3) ⟨regs,stk⟩
      ⟨readRegs regs 0 1 none,StackRoutines.transferStacks src dst stk⟩ := by
  apply Eval.call
  have h := StackRoutines.halt_after_trace _
    (StackRoutines.transferProgram_trace src dst (0 : Fin 10) 1 hsd (by decide) regs stk) 3 rfl rfl
  simpa [StackRoutines.transferResult,StructuredProgram.State.withPC,Nat.add_assoc] using h

theorem clear_eval {S : ℕ} (src : Fin S) (regs : Fin 10 → Bool) (stk : Fin S → List Bool) :
    Eval (clearCall src) (2*(stk src).length+3) ⟨regs,stk⟩
      ⟨readRegs regs 0 1 none,StackRoutines.clearStacks src stk⟩ := by
  apply Eval.call
  have h := StackRoutines.halt_after_trace _
    (StackRoutines.clearProgram_trace src (0 : Fin 10) 1 regs stk) 2 rfl rfl
  simpa [StackRoutines.clearResult,StructuredProgram.State.withPC,Nat.add_assoc] using h

end FormalizationKit.StackCalls
