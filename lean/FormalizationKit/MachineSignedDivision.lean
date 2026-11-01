import FormalizationKit.MachineArithmetic

/-! Exact signed division reuses the existing unsigned long-division
program. Two input sign bits determine the output sign by xor. Exactness
eliminates the rounding correction needed for general signed division.
The primitive's input magnitudes, signs and all scratch are explicit. -/
namespace FormalizationKit.MachineSignedDivision
open OAI.Algorithms.SubexponentialSAT
open BitProgram ProgramLinking

def negative (a : ℤ) : Bool := decide (a<0)

def signedValue (sign : Bool) (magnitude : ℕ) : ℤ :=
  if sign then -(magnitude:ℤ) else (magnitude:ℤ)

theorem signedValue_natAbs (a : ℤ) : signedValue (negative a) a.natAbs=a := by
  by_cases h : a<0
  · simp [signedValue,negative,h,abs_of_neg h]
  · simp [signedValue,negative,h,abs_of_nonneg (by omega : 0≤a)]

/-- The last three stacks carry the two input signs and the output sign. -/
def extend (core : Fin 8 → List Bool) (leftSign rightSign outputSign : List Bool) :
    Fin 11 → List Bool :=
  ![core 0,core 1,core 2,core 3,core 4,core 5,core 6,core 7,leftSign,rightSign,outputSign]

def start (regs : Fin 8 → Bool) (a d : ℤ) : Cfg 8 11 97 :=
  ⟨some 0,regs,extend (ModularQuotientPrograms.quotientStacks [] d.natAbs.bits a.natAbs.bits [])
    [negative a] [negative d] []⟩

def finish (regs : Fin 8 → Bool) (a d : ℤ) (quotient remainder : List Bool) : Cfg 8 11 97 :=
  ⟨none,regs,extend (ModularQuotientPrograms.quotientStacks remainder d.natAbs.bits [] quotient)
    [] [] [negative a^^negative d]⟩

end FormalizationKit.MachineSignedDivision
