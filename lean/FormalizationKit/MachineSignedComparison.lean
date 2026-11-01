import FormalizationKit.MachineSignedNormalization

/-! Signed comparison uses one unsigned subtraction. Its borrow gives the
strict forward comparison; testing the difference for zero also gives the
strict reverse comparison. The two input words have the same width, may
contain padding, and are consumed. Only the Boolean answer remains. -/
namespace FormalizationKit.MachineSignedComparison
open OAI.Algorithms.SubexponentialSAT
open BitProgram ProgramLinking MachineSignedDivision

def orderBit (sx sy borrow equal : Bool) : Bool :=
  if sx != sy then sx else if sx then !borrow && !equal else borrow

theorem orderBit_correct (a b : ℤ) :
    orderBit (negative a) (negative b) (decide (a.natAbs<b.natAbs))
      (decide (a.natAbs=b.natAbs))=decide (a<b) := by
  have ha := signedValue_natAbs a
  have hb := signedValue_natAbs b
  cases hsa : negative a <;> cases hsb : negative b <;>
    simp [hsa,hsb,signedValue] at ha hb
  all_goals
    apply Bool.eq_iff_iff.mpr
    simp [orderBit]
    simp [negative] at hsa hsb
    omega

theorem isZero_append (xs ys : List Bool) :
    CounterPrograms.isZero (xs++ys)=
      (CounterPrograms.isZero xs && CounterPrograms.isZero ys) := by
  induction xs with
  | nil => simp [CounterPrograms.isZero]
  | cons b xs ih => simp [CounterPrograms.isZero,ih,Bool.and_assoc]

theorem isZero_reverse (xs : List Bool) :
    CounterPrograms.isZero xs.reverse=CounterPrograms.isZero xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [List.reverse_cons,isZero_append,ih,CounterPrograms.isZero,Bool.and_comm]

theorem subtraction_zero (xs ys : List Bool) (hlen : xs.length=ys.length) :
    CounterPrograms.isZero (ModularArithmetic.subCarry false xs ys).1.reverse=
      decide (BinaryArithmetic.toNat xs=BinaryArithmetic.toNat ys) := by
  rw [isZero_reverse]
  apply Bool.eq_iff_iff.mpr
  rw [CounterPrograms.isZero_eq_true_iff,CounterPrograms.value_eq_toNat,decide_eq_true_eq]
  have h := ModularArithmetic.subCarry_correct false xs ys hlen
  have hx := ModularArithmetic.toNat_lt_pow_length xs
  have hy := ModularArithmetic.toNat_lt_pow_length ys
  have hd := ModularArithmetic.toNat_lt_pow_length (ModularArithmetic.subCarry false xs ys).1
  rw [ModularArithmetic.subCarry_length false xs ys hlen] at hd
  rw [←hlen] at hy
  cases hc : (ModularArithmetic.subCarry false xs ys).2 <;>
    simp only [hc,BinaryArithmetic.bitVal,Bool.false_eq_true,if_false,if_true,
      Nat.mul_zero,Nat.mul_one] at h <;> omega

def registerPorts : Fin 8 → Fin 10 := fun i => ⟨i.val,by omega⟩
def stackPorts : Fin 3 → Fin 5 := fun i => ⟨i.val,by omega⟩

theorem registerPorts_injective : Function.Injective registerPorts := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 10 => i.val) h)

theorem stackPorts_injective : Function.Injective stackPorts := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 5 => i.val) h)

def comparisonStacks (xs ys difference leftSign rightSign : List Bool) : Fin 5 → List Bool :=
  ![xs,ys,difference,leftSign,rightSign]

def extendRegs (base : Fin 10 → Bool) (regs : Fin 8 → Bool) : Fin 10 → Bool :=
  ![regs 0,regs 1,regs 2,regs 3,regs 4,regs 5,regs 6,regs 7,base 8,base 9]

theorem extendRegs_self (base : Fin 10 → Bool) :
    extendRegs base (fun i => base (registerPorts i))=base := by
  funext i
  fin_cases i <;> rfl

private theorem cfg_ext {r s l : ℕ} {a b : Cfg r s l}
    (hp : a.pc=b.pc) (hr : a.regs=b.regs) (hs : a.stacks=b.stacks) : a=b := by
  cases a
  cases b
  simp_all

private theorem embed_subtract (pc : Option (Fin 13)) (base : Fin 10 → Bool)
    (regs : Fin 8 → Bool) (xs ys difference : List Bool) :
    embedCfg registerPorts stackPorts id none
      (⟨none,base,comparisonStacks [] [] [] [] []⟩ : Cfg 10 5 13)
      (ModularPrograms.subtractCfg pc regs xs ys difference)=
      ⟨pc,extendRegs base regs,comparisonStacks xs ys difference [] []⟩ := by
  apply cfg_ext
  · cases pc <;> rfl
  · funext i
    by_cases hi : ∃ j,registerPorts j=i
    · obtain ⟨j,rfl⟩ := hi
      rw [embedCfg_register registerPorts stackPorts id none _ _ registerPorts_injective]
      fin_cases j <;> rfl
    · rw [embedCfg_register_frame registerPorts stackPorts id none _ _ i hi]
      have hn : ¬i.val<8 := by
        intro hv
        exact hi ⟨⟨i.val,hv⟩,Fin.ext rfl⟩
      fin_cases i <;> simp_all [extendRegs]
  · funext i
    by_cases hi : ∃ j,stackPorts j=i
    · obtain ⟨j,rfl⟩ := hi
      rw [embedCfg_stack registerPorts stackPorts id none _ _ stackPorts_injective]
      fin_cases j <;> rfl
    · rw [embedCfg_stack_frame registerPorts stackPorts id none _ _ i hi]
      have hn : ¬i.val<3 := by
        intro hv
        exact hi ⟨⟨i.val,hv⟩,Fin.ext rfl⟩
      fin_cases i <;> simp_all [comparisonStacks]

def prefixProgram : Program 10 5 4 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code := ![.pop 3 8 3 1,.pop 4 9 4 2,.set 0 false 3,.halt]

def prefixRegs (regs : Fin 10 → Bool) (sx sy : Bool) : Fin 10 → Bool :=
  Function.update (readRegs (readRegs regs 8 3 (some sx)) 9 4 (some sy)) 0 false

theorem prefix_trace (regs : Fin 10 → Bool) (xs ys : List Bool) (sx sy : Bool) :
    Trace prefixProgram 4 ⟨some 0,regs,comparisonStacks xs ys [] [sx] [sy]⟩
      ⟨none,prefixRegs regs sx sy,comparisonStacks xs ys [] [] []⟩ := by
  apply OAI.Algorithms.SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply,step,prefixProgram,execInstr,comparisonStacks,prefixRegs,readRegs,
    Function.update_apply]
  funext i
  fin_cases i <;> simp

abbrev subtractionCore : Program 10 5 13 :=
  liftProgram ModularPrograms.subtractProgram registerPorts stackPorts

def suffixProgram : Program 10 5 19 where
  inputStack := 2
  outputStack := 0
  entry := 0
  code := ![.set 1 true 1,.pop 2 2 3 2,.branch 3 3 5,
    .bnot 2 2 4,.band 1 1 2 1,.bnot 2 0 6,.bnot 3 1 7,
    .band 2 2 3 8,.band 2 2 8 9,.bnot 3 8 10,.band 3 3 0 11,
    .bor 2 2 3 12,.bxor 3 8 9 13,.bnot 4 3 14,.band 2 2 4 15,
    .band 3 3 8 16,.bor 2 2 3 17,.push 0 2 18,.halt]

def scanRegs (regs : Fin 10 → Bool) (bit : Bool) : Fin 10 → Bool :=
  Function.update (Function.update (readRegs regs 2 3 (some bit)) 2 (!bit)) 1
    (regs 1 && !bit)

theorem scan_round (regs : Fin 10 → Bool) (bit : Bool) (xs : List Bool) :
    Trace suffixProgram 4 ⟨some 1,regs,comparisonStacks [] [] (bit::xs) [] []⟩
      ⟨some 1,scanRegs regs bit,comparisonStacks [] [] xs [] []⟩ := by
  apply OAI.Algorithms.SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply,step,suffixProgram,execInstr,comparisonStacks,scanRegs,readRegs,
    Function.update_apply]
  funext i
  fin_cases i <;> simp

theorem scan_trace (regs : Fin 10 → Bool) (xs : List Bool) :
    ∃ finalRegs,Trace suffixProgram (4*xs.length+2)
      ⟨some 1,regs,comparisonStacks [] [] xs [] []⟩
      ⟨some 5,finalRegs,comparisonStacks [] [] [] [] []⟩ ∧
      finalRegs 0=regs 0 ∧ finalRegs 8=regs 8 ∧ finalRegs 9=regs 9 ∧
      finalRegs 1=(regs 1 && CounterPrograms.isZero xs) := by
  induction xs generalizing regs with
  | nil =>
    refine ⟨readRegs regs 2 3 none,?_,by simp [readRegs],by simp [readRegs],
      by simp [readRegs],by simp [readRegs,CounterPrograms.isZero]⟩
    apply OAI.Algorithms.SubexponentialSAT.Computation.Trace.of_iterate
    simp [Function.iterate_succ_apply,step,suffixProgram,execInstr,comparisonStacks,readRegs,Function.update_apply]
  | cons bit xs ih =>
    obtain ⟨rf,ht,h0,h8,h9,h1⟩ := ih (scanRegs regs bit)
    refine ⟨rf,?_,?_,?_,?_,?_⟩
    · convert (scan_round regs bit xs).trans ht using 1
      simp only [List.length_cons]
      omega
    · simpa [scanRegs,readRegs] using h0
    · simpa [scanRegs,readRegs] using h8
    · simpa [scanRegs,readRegs] using h9
    · simpa [scanRegs,CounterPrograms.isZero,Bool.and_assoc] using h1

theorem suffix_tail (regs : Fin 10 → Bool) :
    ∃ finalRegs,Trace suffixProgram 14 ⟨some 5,regs,comparisonStacks [] [] [] [] []⟩
      ⟨none,finalRegs,comparisonStacks [orderBit (regs 8) (regs 9) (regs 0) (regs 1)] [] [] [] []⟩ := by
  let r2 := ((!regs 0 && !regs 1) && regs 8) || ((!regs 8) && regs 0)
  let signDiff := regs 8 ^^ regs 9
  let result := (r2 && !signDiff) || (signDiff && regs 8)
  refine ⟨Function.update (Function.update (Function.update regs 2 result) 3 (signDiff && regs 8)) 4 (!signDiff),?_⟩
  have hresult : result=orderBit (regs 8) (regs 9) (regs 0) (regs 1) := by
    cases h8 : regs 8 <;> cases h9 : regs 9 <;> cases h0 : regs 0 <;> cases h1 : regs 1 <;>
      simp [result,r2,signDiff,orderBit,h8,h9,h0,h1]
  apply OAI.Algorithms.SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply,step,suffixProgram,execInstr,comparisonStacks,readRegs,
    Function.update_apply,r2,signDiff,result,hresult]
  constructor <;> funext i <;> fin_cases i <;> simp

theorem suffix_trace (regs : Fin 10 → Bool) (difference : List Bool) :
    ∃ finalRegs,Trace suffixProgram (4*difference.length+17)
      ⟨some 0,regs,comparisonStacks [] [] difference [] []⟩
      ⟨none,finalRegs,comparisonStacks [orderBit (regs 8) (regs 9) (regs 0)
        (CounterPrograms.isZero difference)] [] [] [] []⟩ := by
  have hset : step suffixProgram ⟨some 0,regs,comparisonStacks [] [] difference [] []⟩=
      some ⟨some 1,Function.update regs 1 true,comparisonStacks [] [] difference [] []⟩ := rfl
  obtain ⟨rm,hs,h0,h8,h9,h1⟩ := scan_trace (Function.update regs 1 true) difference
  obtain ⟨rf,ht⟩ := suffix_tail rm
  refine ⟨rf,?_⟩
  have hfull := (OAI.Algorithms.SubexponentialSAT.Computation.Trace.cons hset hs).trans ht
  simpa only [h0,h8,h9,h1,Function.update_of_ne (by decide : (0 : Fin 10)≠1),
    Function.update_of_ne (by decide : (8 : Fin 10)≠1),
    Function.update_of_ne (by decide : (9 : Fin 10)≠1),Function.update_same,
    Bool.true_and,Nat.add_assoc] using hfull

abbrev canonicalComparisonProgram : Program 10 5 36 :=
  link (link prefixProgram subtractionCore) suffixProgram

def start (regs : Fin 10 → Bool) (xs ys : List Bool) (sx sy : Bool) : Cfg 10 5 36 :=
  ⟨some 0,regs,comparisonStacks xs ys [] [sx] [sy]⟩

def finish (regs : Fin 10 → Bool) (answer : Bool) : Cfg 10 5 36 :=
  ⟨none,regs,comparisonStacks [answer] [] [] [] []⟩

theorem comparison_trace (regs : Fin 10 → Bool) (xs ys : List Bool)
    (a b : ℤ) (hlen : xs.length=ys.length)
    (hx : BinaryArithmetic.toNat xs=a.natAbs) (hy : BinaryArithmetic.toNat ys=b.natAbs) :
    ∃ finalRegs,Trace canonicalComparisonProgram (16*xs.length+24)
      (start regs xs ys (negative a) (negative b)) (finish finalRegs (decide (a<b))) := by
  let pre := prefixRegs regs (negative a) (negative b)
  have hp := prefix_trace regs xs ys (negative a) (negative b)
  obtain ⟨rm,ht,hborrow⟩ := ModularPrograms.subtract_comparison
    (fun i => pre (registerPorts i)) xs ys (by simp [pre,prefixRegs,registerPorts]) hlen
  have hc := liftProgram_trace ModularPrograms.subtractProgram registerPorts stackPorts
    (⟨none,pre,comparisonStacks [] [] [] [] []⟩ : Cfg 10 5 13)
    registerPorts_injective stackPorts_injective ht
  change Trace subtractionCore (12*xs.length+3)
    (embedCfg registerPorts stackPorts id none _ (ModularPrograms.subtractCfg (some 0) _ xs ys [])) _ at hc
  rw [embed_subtract,embed_subtract,extendRegs_self] at hc
  have hfirst := link_trace prefixProgram subtractionCore hp rfl hc
  have hz : (Fin.castAdd 13 (0 : Fin 4) : Fin 17)=0 := Fin.ext rfl
  have hfirst' : Trace (link prefixProgram subtractionCore) (4+(12*xs.length+3))
      (⟨some 0,regs,comparisonStacks xs ys [] [negative a] [negative b]⟩ : Cfg 10 5 17)
      ⟨none,extendRegs pre rm,comparisonStacks [] [] (ModularArithmetic.subCarry false xs ys).1.reverse [] []⟩ := by
    simpa only [relabelCfg,relocatePc,hz,pre] using hfirst
  obtain ⟨rf,hs⟩ := suffix_trace (extendRegs pre rm) (ModularArithmetic.subCarry false xs ys).1.reverse
  have h0 : rm 0=decide (a.natAbs<b.natAbs) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [hx,hy,decide_eq_true_eq] using hborrow
  have heq := subtraction_zero xs ys hlen
  rw [hx,hy] at heq
  have hanswer : orderBit (extendRegs pre rm 8) (extendRegs pre rm 9)
      (extendRegs pre rm 0) (CounterPrograms.isZero (ModularArithmetic.subCarry false xs ys).1.reverse)=
      decide (a<b) := by
    simpa [extendRegs,pre,prefixRegs,readRegs,h0,heq] using orderBit_correct a b
  rw [hanswer] at hs
  have hfull := link_trace (link prefixProgram subtractionCore) suffixProgram hfirst' rfl hs
  refine ⟨rf,?_⟩
  have hz' : (Fin.castAdd 19 (0 : Fin 17) : Fin 36)=0 := Fin.ext rfl
  convert hfull using 1
  all_goals try simp only [start,finish,relabelCfg,relocatePc,hz',List.length_reverse,
    ModularArithmetic.subCarry_length false xs ys hlen]
  all_goals first | rfl | omega

def normalizationPorts (right : Bool) : Fin 3 → Fin 5 :=
  if right then ![1,2,4] else ![0,2,3]

theorem normalizationPorts_injective (right : Bool) : Function.Injective (normalizationPorts right) := by
  intro a b h
  cases right <;> fin_cases a <;> fin_cases b <;> simp_all [normalizationPorts]

def normalizationStacks (right : Bool) (word scratch sign otherWord otherSign : List Bool) :
    Fin 5 → List Bool :=
  if right then comparisonStacks otherWord word scratch otherSign sign
  else comparisonStacks word otherWord scratch sign otherSign

private theorem embed_normalization (right : Bool) (pc : Option (Fin 16))
    (base : Fin 10 → Bool) (localRegs : Fin 8 → Bool)
    (word scratch sign otherWord otherSign : List Bool) :
    embedCfg registerPorts (normalizationPorts right) id none
      (⟨none,base,normalizationStacks right word [] [] otherWord otherSign⟩ : Cfg 10 5 16)
      (⟨pc,localRegs,![word,scratch,sign]⟩ : Cfg 8 3 16)=
      ⟨pc,extendRegs base localRegs,normalizationStacks right word scratch sign otherWord otherSign⟩ := by
  apply cfg_ext
  · cases pc <;> rfl
  · funext i
    by_cases hi : ∃ j,registerPorts j=i
    · obtain ⟨j,rfl⟩ := hi
      rw [embedCfg_register registerPorts (normalizationPorts right) id none _ _ registerPorts_injective]
      fin_cases j <;> rfl
    · rw [embedCfg_register_frame registerPorts (normalizationPorts right) id none _ _ i hi]
      have hn : ¬i.val<8 := by
        intro hv
        exact hi ⟨⟨i.val,hv⟩,Fin.ext rfl⟩
      fin_cases i <;> simp_all [extendRegs]
  · funext i
    by_cases hi : ∃ j,normalizationPorts right j=i
    · obtain ⟨j,rfl⟩ := hi
      rw [embedCfg_stack registerPorts (normalizationPorts right) id none _ _
        (normalizationPorts_injective right)]
      cases right <;> fin_cases j <;> rfl
    · rw [embedCfg_stack_frame registerPorts (normalizationPorts right) id none _ _ i hi]
      have h0 := fun h => hi ⟨0,h⟩
      have h1 := fun h => hi ⟨1,h⟩
      have h2 := fun h => hi ⟨2,h⟩
      cases right <;> fin_cases i <;> simp_all [normalizationPorts,normalizationStacks,comparisonStacks]

abbrev normalizationCore (right : Bool) : Program 10 5 16 :=
  liftProgram MachineSignedNormalization.normalizationProgram registerPorts (normalizationPorts right)

theorem normalization_core_trace_frame (right : Bool) (regs : Fin 10 → Bool)
    (word otherWord : List Bool) (sign : Bool) (otherSign : List Bool) :
    ∃ finalRegs,Trace (normalizationCore right) (8*word.length+12)
      ⟨some 0,regs,normalizationStacks right word [] [sign] otherWord otherSign⟩
      ⟨none,finalRegs,normalizationStacks right word []
        [MachineSignedNormalization.canonicalSign sign word] otherWord otherSign⟩ := by
  obtain ⟨rf,ht⟩ := MachineSignedNormalization.normalization_trace
    (fun i => regs (registerPorts i)) word sign
  have hl := liftProgram_trace MachineSignedNormalization.normalizationProgram
    registerPorts (normalizationPorts right)
    (⟨none,regs,normalizationStacks right word [] [] otherWord otherSign⟩ : Cfg 10 5 16)
    registerPorts_injective (normalizationPorts_injective right) ht
  change Trace (normalizationCore right) _
    (embedCfg registerPorts (normalizationPorts right) id none _
      (⟨some 0,_,![word,[],[sign]]⟩ : Cfg 8 3 16))
    (embedCfg registerPorts (normalizationPorts right) id none _
      (⟨none,rf,![word,[],[MachineSignedNormalization.canonicalSign sign word]]⟩ : Cfg 8 3 16)) at hl
  rw [embed_normalization,embed_normalization,extendRegs_self] at hl
  exact ⟨_,hl⟩

theorem normalization_core_trace (right : Bool) (regs : Fin 10 → Bool)
    (word otherWord : List Bool) (sign otherSign : Bool) :
    ∃ finalRegs,Trace (normalizationCore right) (8*word.length+12)
      ⟨some 0,regs,normalizationStacks right word [] [sign] otherWord [otherSign]⟩
      ⟨none,finalRegs,normalizationStacks right word []
        [MachineSignedNormalization.canonicalSign sign word] otherWord [otherSign]⟩ :=
  normalization_core_trace_frame right regs word otherWord sign [otherSign]

abbrev comparisonProgram : Program 10 5 68 :=
  link (link (normalizationCore false) (normalizationCore true)) canonicalComparisonProgram

def wordStart (regs : Fin 10 → Bool) (xs ys : List Bool) (sx sy : Bool) : Cfg 10 5 68 :=
  ⟨some 0,regs,comparisonStacks xs ys [] [sx] [sy]⟩

def wordFinish (regs : Fin 10 → Bool) (answer : Bool) : Cfg 10 5 68 :=
  ⟨none,regs,comparisonStacks [answer] [] [] [] []⟩

/-- Full signed comparison, including sign normalization, accepts arbitrary
equal-width words. No canonical-bit or nonzero-sign premise is required. -/
theorem word_comparison_resources (regs : Fin 10 → Bool) (xs ys : List Bool) (sx sy : Bool)
    (hlen : xs.length=ys.length) :
    ∃ finalRegs,Trace comparisonProgram (32*xs.length+48)
      (wordStart regs xs ys sx sy)
      (wordFinish finalRegs (decide (signedValue sx (BinaryArithmetic.toNat xs)<
        signedValue sy (BinaryArithmetic.toNat ys)))) ∧
      dataBits (wordFinish finalRegs (decide (signedValue sx (BinaryArithmetic.toNat xs)<
        signedValue sy (BinaryArithmetic.toNat ys))))=1 ∧
      ∀ prefixSteps intermediate,prefixSteps≤32*xs.length+48 →
        Trace comparisonProgram prefixSteps (wordStart regs xs ys sx sy) intermediate →
        dataBits intermediate≤34*xs.length+50 := by
  let a := signedValue sx (BinaryArithmetic.toNat xs)
  let b := signedValue sy (BinaryArithmetic.toNat ys)
  let ca := MachineSignedNormalization.canonicalSign sx xs
  let cb := MachineSignedNormalization.canonicalSign sy ys
  obtain ⟨ra,ha⟩ := normalization_core_trace false regs xs ys sx sy
  obtain ⟨rb,hb⟩ := normalization_core_trace true ra ys xs sy ca
  have hn := link_trace (normalizationCore false) (normalizationCore true) ha rfl hb
  have hz : (Fin.castAdd 16 (0 : Fin 16) : Fin 32)=0 := Fin.ext rfl
  have hn' : Trace (link (normalizationCore false) (normalizationCore true))
      ((8*xs.length+12)+(8*ys.length+12))
      (⟨some 0,regs,comparisonStacks xs ys [] [sx] [sy]⟩ : Cfg 10 5 32)
      ⟨none,rb,comparisonStacks xs ys [] [ca] [cb]⟩ := by
    simpa only [relabelCfg,relocatePc,hz,normalizationStacks,Bool.false_eq_true,
      if_false,if_true,ca,cb] using hn
  have hca : ca=negative a := MachineSignedNormalization.canonicalSign_negative sx xs
  have hcb : cb=negative b := MachineSignedNormalization.canonicalSign_negative sy ys
  have hxa : BinaryArithmetic.toNat xs=a.natAbs := by cases sx <;> simp [a,signedValue]
  have hyb : BinaryArithmetic.toNat ys=b.natAbs := by cases sy <;> simp [b,signedValue]
  obtain ⟨rf,hc⟩ := comparison_trace rb xs ys a b hlen hxa hyb
  rw [hca,hcb] at hn'
  change Trace canonicalComparisonProgram _ ⟨some 0,rb,_⟩ ⟨none,rf,_⟩ at hc
  have hall := link_trace (link (normalizationCore false) (normalizationCore true))
    canonicalComparisonProgram hn' rfl hc
  have hz' : (Fin.castAdd 36 (0 : Fin 32) : Fin 68)=0 := Fin.ext rfl
  have ht : Trace comparisonProgram (32*xs.length+48)
      (wordStart regs xs ys sx sy) (wordFinish rf (decide (a<b))) := by
    convert hall using 1
    all_goals try simp only [wordStart,wordFinish,relabelCfg,relocatePc,hz',←hlen]
    all_goals first | rfl | omega
  refine ⟨rf,ht,?_,?_⟩
  · simp [wordFinish,comparisonStacks,dataBits,stackBits,Fin.sum_univ_succ]
  · intro prefixSteps intermediate hp htr
    have hs := trace_dataBits comparisonProgram htr
    have hi : dataBits (wordStart regs xs ys sx sy)=2*xs.length+2 := by
      simp [wordStart,comparisonStacks,dataBits,stackBits,Fin.sum_univ_succ,←hlen]
      omega
    rw [hi] at hs
    omega

end FormalizationKit.MachineSignedComparison
