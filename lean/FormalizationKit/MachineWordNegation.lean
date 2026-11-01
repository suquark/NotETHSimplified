import FormalizationKit.MachineSignedDivision

/-! Compute 0-x modulo the input word width. Specializing the existing
subtractor identity proves the value; the loop uses only one operand. -/
namespace FormalizationKit.MachineWordNegation
open OAI.Algorithms.SubexponentialSAT
open BitProgram ProgramLinking

def loopProgram : Program 8 3 6 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code := ![.pop 0 1 2 1,.branch 2 2 5,.bxor 3 1 0 3,
    .bor 0 0 1 4,.push 1 3 0,.halt]

def wordNegate (borrow : Bool) (word : List Bool) : List Bool × Bool :=
  ModularArithmetic.subCarry borrow (List.replicate word.length false) word

theorem wordNegate_nil (borrow : Bool) : wordNegate borrow []=([],borrow) := rfl

theorem wordNegate_cons (borrow bit : Bool) (word : List Bool) :
    wordNegate borrow (bit::word)=
      ((bit^^borrow)::(wordNegate (borrow||bit) word).1,(wordNegate (borrow||bit) word).2) := by
  cases borrow <;> cases bit <;> simp [wordNegate,ModularArithmetic.subCarry,
    ModularArithmetic.borrowBit,ModularArithmetic.differenceBit,List.replicate_succ]

theorem wordNegate_length (borrow : Bool) (word : List Bool) :
    (wordNegate borrow word).1.length=word.length := by
  simpa only [wordNegate,List.length_replicate] using
    ModularArithmetic.subCarry_length borrow (List.replicate word.length false) word (List.length_replicate ..)

theorem zero_word_value (n : ℕ) : BinaryArithmetic.toNat (List.replicate n false)=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,ih]

theorem wordNegate_value (word : List Bool) :
    BinaryArithmetic.toNat word+BinaryArithmetic.toNat (wordNegate false word).1=
      2^word.length*BinaryArithmetic.bitVal (wordNegate false word).2 := by
  have h := ModularArithmetic.subCarry_correct false (List.replicate word.length false) word (by simp)
  simpa [wordNegate,zero_word_value] using h.symm

def loopRegs (regs : Fin 8 → Bool) (bit : Bool) : Fin 8 → Bool :=
  Function.update (Function.update (readRegs regs 1 2 (some bit)) 3 (bit^^regs 0)) 0 (regs 0||bit)

theorem loop_round (regs : Fin 8 → Bool) (bit : Bool) (word output : List Bool) :
    Trace loopProgram 5
      ⟨some 0,regs,BinaryPrograms.Add.stackState (bit::word) output []⟩
      ⟨some 0,loopRegs regs bit,BinaryPrograms.Add.stackState word ((bit^^regs 0)::output) []⟩ := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply,step,loopProgram,execInstr,loopRegs,BinaryPrograms.Add.stackState,
    readRegs,Function.update_apply]

theorem loop_exit (regs : Fin 8 → Bool) (output : List Bool) :
    Trace loopProgram 3 ⟨some 0,regs,BinaryPrograms.Add.stackState [] output []⟩
      ⟨none,readRegs regs 1 2 none,BinaryPrograms.Add.stackState [] output []⟩ := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply,step,loopProgram,execInstr,BinaryPrograms.Add.stackState,
    readRegs,Function.update_apply]

theorem loop_trace (regs : Fin 8 → Bool) (word output : List Bool) :
    ∃ finalRegs,Trace loopProgram (5*word.length+3)
      ⟨some 0,regs,BinaryPrograms.Add.stackState word output []⟩
      ⟨none,finalRegs,BinaryPrograms.Add.stackState [] ((wordNegate (regs 0) word).1.reverse++output) []⟩ ∧
      finalRegs 0=(wordNegate (regs 0) word).2 := by
  induction word generalizing regs output with
  | nil =>
    refine ⟨readRegs regs 1 2 none,?_,?_⟩
    · simpa [wordNegate_nil] using loop_exit regs output
    · simp [readRegs,wordNegate_nil]
  | cons bit word ih =>
    obtain ⟨rf,ht,hb⟩ := ih (loopRegs regs bit) ((bit^^regs 0)::output)
    refine ⟨rf,?_,?_⟩
    · have h := (loop_round regs bit word output).trans ht
      convert h using 1 <;>
        simp [wordNegate_cons,loopRegs,List.reverse_cons,List.append_assoc]
      omega
    · simpa [wordNegate_cons,loopRegs] using hb

abbrev negateProgram : Program 8 3 10 :=
  link loopProgram (StackRoutines.transferProgram (1 : Fin 3) 0 (1 : Fin 8) 2)

theorem negate_trace (regs : Fin 8 → Bool) (word : List Bool) :
    ∃ finalRegs,Trace negateProgram (8*word.length+6)
      ⟨some 0,regs,BinaryPrograms.Add.stackState word [] []⟩
      ⟨none,finalRegs,BinaryPrograms.Add.stackState (wordNegate (regs 0) word).1 [] []⟩ := by
  obtain ⟨rf,ht,hb⟩ := loop_trace regs word []
  have hx := StackRoutines.transferProgram_trace (1 : Fin 3) 0 (1 : Fin 8) 2
    (by decide) (by decide) rf (BinaryPrograms.Add.stackState [] (wordNegate (regs 0) word).1.reverse [])
  have hh := StackRoutines.halt_after_trace _ hx 3 rfl rfl
  have hh' : Trace (StackRoutines.transferProgram (1 : Fin 3) 0 (1 : Fin 8) 2)
      (3*word.length+3)
      ⟨some 0,rf,BinaryPrograms.Add.stackState [] (wordNegate (regs 0) word).1.reverse []⟩
      ⟨none,readRegs rf 1 2 none,BinaryPrograms.Add.stackState (wordNegate (regs 0) word).1 [] []⟩ := by
    simpa [StackRoutines.transferResult,StackRoutines.transferStacks,BinaryPrograms.Add.stackState,
      wordNegate_length] using hh
  simp only [List.append_nil] at ht
  have h := link_trace loopProgram _ ht rfl hh'
  refine ⟨readRegs rf 1 2 none,?_⟩
  have hz : (Fin.castAdd 4 (0 : Fin 6) : Fin 10)=0 := Fin.ext rfl
  convert h using 1 <;> try simp only [relabelCfg,relocatePc,hz]
  all_goals first | rfl | omega

end FormalizationKit.MachineWordNegation
