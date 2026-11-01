import FormalizationKit.MachineSignedDivision

/-! Canonicalize a signed-magnitude word without changing its magnitude.
The imported zero test restores the word and clears its own scratch.
Clearing the sign of zero gives one sign convention for later comparisons,
including words with leading zero bits. -/
namespace FormalizationKit.MachineSignedNormalization
open OAI.Algorithms.SubexponentialSAT
open BitProgram ProgramLinking MachineSignedDivision

def canonicalSign (sign : Bool) (word : List Bool) : Bool :=
  sign && !CounterPrograms.isZero word

theorem canonicalSign_negative (sign : Bool) (word : List Bool) :
    canonicalSign sign word=negative (signedValue sign (BinaryArithmetic.toNat word)) := by
  by_cases hz : CounterPrograms.isZero word=true
  · have hv : BinaryArithmetic.toNat word=0 := by
      rw [←CounterPrograms.value_eq_toNat]
      exact (CounterPrograms.isZero_eq_true_iff word).mp hz
    cases sign <;> simp [canonicalSign,hz,hv,signedValue,negative]
  · have he : CounterPrograms.isZero word=false := Bool.eq_false_iff.mpr hz
    have hv : 0<BinaryArithmetic.toNat word := by
      rw [←CounterPrograms.value_eq_toNat]
      exact (CounterPrograms.isZero_eq_false_iff word).mp he
    cases sign <;> simp [canonicalSign,he,signedValue,negative]
    omega

def registerPorts : Fin 3 → Fin 8 := fun i => ⟨i.val,by omega⟩
def stackPorts : Fin 2 → Fin 3 := fun i => ⟨i.val,by omega⟩

theorem registerPorts_injective : Function.Injective registerPorts := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 8 => i.val) h)

theorem stackPorts_injective : Function.Injective stackPorts := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 3 => i.val) h)

def zeroRegs (base : Fin 8 → Bool) (b p z : Bool) : Fin 8 → Bool :=
  ![b,p,z,base 3,base 4,base 5,base 6,base 7]

theorem zeroRegs_self (base : Fin 8 → Bool) : zeroRegs base (base 0) (base 1) (base 2)=base := by
  funext i
  fin_cases i <;> rfl

private theorem cfg_ext {r s l : ℕ} {a b : Cfg r s l}
    (hp : a.pc=b.pc) (hr : a.regs=b.regs) (hs : a.stacks=b.stacks) : a=b := by
  cases a
  cases b
  simp_all

private theorem embed_zero (pc : Option (Fin 10)) (base : Fin 8 → Bool)
    (b p z : Bool) (word scratch : List Bool) :
    embedCfg registerPorts stackPorts id none
      (⟨none,base,![word,[],[]]⟩ : Cfg 8 3 10)
      (⟨pc,CounterPrograms.counterRegs b p z,CounterPrograms.counterStacks word scratch⟩ : Cfg 3 2 10)=
      ⟨pc,zeroRegs base b p z,![word,scratch,[]]⟩ := by
  apply cfg_ext
  · cases pc <;> rfl
  · funext i
    by_cases hi : ∃ j,registerPorts j=i
    · obtain ⟨j,rfl⟩ := hi
      rw [embedCfg_register registerPorts stackPorts id none _ _ registerPorts_injective]
      fin_cases j <;> rfl
    · rw [embedCfg_register_frame registerPorts stackPorts id none _ _ i hi]
      have hn : ¬i.val<3 := by
        intro hv
        exact hi ⟨⟨i.val,hv⟩,Fin.ext rfl⟩
      fin_cases i <;> simp_all [zeroRegs]
  · funext i
    by_cases hi : ∃ j,stackPorts j=i
    · obtain ⟨j,rfl⟩ := hi
      rw [embedCfg_stack registerPorts stackPorts id none _ _ stackPorts_injective]
      fin_cases j <;> rfl
    · rw [embedCfg_stack_frame registerPorts stackPorts id none _ _ i hi]
      have hn : ¬i.val<2 := by
        intro hv
        exact hi ⟨⟨i.val,hv⟩,Fin.ext rfl⟩
      fin_cases i <;> simp_all

theorem zero_arbitrary_trace (b p z : Bool) (word : List Bool) :
    Trace CounterPrograms.zeroProgram (8*word.length+6)
      (CounterPrograms.counterCfg 0 b p z word [])
      (⟨none,CounterPrograms.counterRegs false false (CounterPrograms.isZero word),
        CounterPrograms.counterStacks word []⟩ : Cfg 3 2 10) := by
  have h := OAI.Algorithms.SubexponentialSAT.Computation.Trace.cons
    (CounterPrograms.zero_step0 b p z word []) (CounterPrograms.zero_scan_trace b p true word [])
  have ht := StackRoutines.halt_after_trace CounterPrograms.zeroProgram h 9 rfl rfl
  simpa only [List.length_nil,List.reverse_nil,List.nil_append,Bool.true_and,Nat.mul_zero,
    Nat.add_zero,CounterPrograms.counterCfg] using ht

def prefixProgram : Program 8 3 2 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code := ![.pop 2 3 4 1,.halt]

abbrev zeroCore : Program 8 3 10 :=
  liftProgram CounterPrograms.zeroProgram registerPorts stackPorts

def suffixProgram : Program 8 3 4 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code := ![.bnot 2 2 1,.band 3 3 2 2,.push 2 3 3,.halt]

abbrev normalizationProgram : Program 8 3 16 := link (link prefixProgram zeroCore) suffixProgram

theorem prefix_trace (regs : Fin 8 → Bool) (word : List Bool) (sign : Bool) :
    Trace prefixProgram 2 ⟨some 0,regs,![word,[],[sign]]⟩
      ⟨none,readRegs regs 3 4 (some sign),![word,[],[]]⟩ := by
  apply OAI.Algorithms.SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply,step,prefixProgram,execInstr,readRegs,Function.update_apply]
  funext i
  fin_cases i <;> simp

theorem suffix_trace (regs : Fin 8 → Bool) (word : List Bool) (sign : Bool)
    (hz : regs 2=CounterPrograms.isZero word) (hs : regs 3=sign) :
    ∃ finalRegs,Trace suffixProgram 4 ⟨some 0,regs,![word,[],[]]⟩
      ⟨none,finalRegs,![word,[],[canonicalSign sign word]]⟩ := by
  refine ⟨Function.update (Function.update regs 2 (!CounterPrograms.isZero word)) 3
    (canonicalSign sign word),?_⟩
  apply OAI.Algorithms.SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply,step,suffixProgram,execInstr,hz,hs,canonicalSign,Function.update_apply]
  funext i
  fin_cases i <;> simp

def start (regs : Fin 8 → Bool) (word : List Bool) (sign : Bool) : Cfg 8 3 16 :=
  ⟨some 0,regs,![word,[],[sign]]⟩

def finish (regs : Fin 8 → Bool) (word : List Bool) (sign : Bool) : Cfg 8 3 16 :=
  ⟨none,regs,![word,[],[canonicalSign sign word]]⟩

theorem normalization_trace (regs : Fin 8 → Bool) (word : List Bool) (sign : Bool) :
    ∃ finalRegs,Trace normalizationProgram (8*word.length+12)
      (start regs word sign) (finish finalRegs word sign) := by
  let pre := readRegs regs 3 4 (some sign)
  have hp := prefix_trace regs word sign
  have hz := zero_arbitrary_trace (pre 0) (pre 1) (pre 2) word
  have hc := liftProgram_trace CounterPrograms.zeroProgram registerPorts stackPorts
    (⟨none,pre,![word,[],[]]⟩ : Cfg 8 3 10)
    registerPorts_injective stackPorts_injective hz
  change Trace zeroCore (8*word.length+6)
    (embedCfg registerPorts stackPorts id none _
      (⟨some 0,CounterPrograms.counterRegs (pre 0) (pre 1) (pre 2),CounterPrograms.counterStacks word []⟩ : Cfg 3 2 10))
    (embedCfg registerPorts stackPorts id none _
      (⟨none,CounterPrograms.counterRegs false false (CounterPrograms.isZero word),CounterPrograms.counterStacks word []⟩ : Cfg 3 2 10)) at hc
  rw [embed_zero,embed_zero,zeroRegs_self] at hc
  have hfirst := link_trace prefixProgram zeroCore hp rfl hc
  have hzero : (Fin.castAdd 10 (0 : Fin 2) : Fin 12)=0 := Fin.ext rfl
  have hfirst' : Trace (link prefixProgram zeroCore) (2+(8*word.length+6))
      (⟨some 0,regs,![word,[],[sign]]⟩ : Cfg 8 3 12)
      ⟨none,zeroRegs pre false false (CounterPrograms.isZero word),![word,[],[]]⟩ := by
    simpa only [relabelCfg,relocatePc,hzero,pre] using hfirst
  have hreg : zeroRegs pre false false (CounterPrograms.isZero word) 3=sign := by
    simp [zeroRegs,pre,readRegs]
  obtain ⟨rf,hs⟩ := suffix_trace (zeroRegs pre false false (CounterPrograms.isZero word))
    word sign rfl hreg
  have hfull := link_trace (link prefixProgram zeroCore) suffixProgram hfirst' rfl hs
  refine ⟨rf,?_⟩
  have hzero' : (Fin.castAdd 4 (0 : Fin 12) : Fin 16)=0 := Fin.ext rfl
  convert hfull using 1
  all_goals try simp only [start,finish,relabelCfg,relocatePc,hzero']
  all_goals first | rfl | omega

end FormalizationKit.MachineSignedNormalization
