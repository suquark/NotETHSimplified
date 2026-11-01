import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

/-! A call uses fixed injective register/stack ports. Agreement on those
ports and preservation outside them identify its complete caller states.
The imported trace and linker retain every source instruction, including
the callee halt that becomes the return jump. -/
namespace FormalizationKit.MachineCallFrames
open OAI.Algorithms.SubexponentialSAT
open BitProgram ProgramLinking StructuredCalls

theorem embed_state_agree {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (hinjr : Function.Injective register) (hinjs : Function.Injective stack)
    (localState : State r s) (frame target : State R S)
    (hr : ∀ i,target.regs (register i)=localState.regs i)
    (hrf : ∀ i,(¬∃ j,register j=i) → target.regs i=frame.regs i)
    (hs : ∀ i,target.stacks (stack i)=localState.stacks i)
    (hsf : ∀ i,(¬∃ j,stack j=i) → target.stacks i=frame.stacks i) :
    embedState register stack frame localState=target := by
  exact embedState_eq_of_ports register stack frame target localState
    hinjr hinjs hr hrf hs hsf

theorem eval_lifted_frame {r s l R S : ℕ} (p : Program r s l)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (hinjr : Function.Injective register) (hinjs : Function.Injective stack)
    {steps : ℕ} {localStart localFinish : State r s}
    (trace : Trace p steps (localStart.withPC (some p.entry)) (localFinish.withPC none))
    (callerStart callerFinish : State R S)
    (hr : ∀ i,callerStart.regs (register i)=localStart.regs i)
    (hs : ∀ i,callerStart.stacks (stack i)=localStart.stacks i)
    (hr' : ∀ i,callerFinish.regs (register i)=localFinish.regs i)
    (hs' : ∀ i,callerFinish.stacks (stack i)=localFinish.stacks i)
    (hrf : ∀ i,(¬∃ j,register j=i) → callerFinish.regs i=callerStart.regs i)
    (hsf : ∀ i,(¬∃ j,stack j=i) → callerFinish.stacks i=callerStart.stacks i) :
    Eval (.call (liftProgram p register stack)) steps callerStart callerFinish := by
  have h := eval_call_lifted p register stack callerStart hinjr hinjs trace
  have hstart := embed_state_agree register stack hinjr hinjs localStart callerStart callerStart
    hr (fun _ _ => rfl) hs (fun _ _ => rfl)
  have hfinish := embed_state_agree register stack hinjr hinjs localFinish callerStart callerFinish
    hr' hrf hs' hsf
  simpa only [hstart,hfinish] using h

end FormalizationKit.MachineCallFrames
