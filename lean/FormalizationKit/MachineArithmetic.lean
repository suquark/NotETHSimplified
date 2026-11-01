import OAI.Algorithms.SubexponentialSAT.ModularRingPrograms
import OAI.Algorithms.SubexponentialSAT.ModularQuotientPrograms
import OAI.Algorithms.SubexponentialSAT.BitProgramSelectedSpace
import OAI.Algorithms.SubexponentialSAT.CounterForPrograms
import Mathlib.Data.Nat.Size

namespace FormalizationKit.MachineArithmetic
open OAI.Algorithms.SubexponentialSAT
/-- Mathlib's canonical little-endian expansion has the value expected by
OpenAI's bit-list routines. -/
theorem bits_value (a : ℕ) : BinaryArithmetic.toNat a.bits=a := by
  induction a using Nat.binaryRec' with
  | zero => simp
  | bit b a ha ih =>
    rw [Nat.bits_append_bit a b ha]
    simp only [BinaryArithmetic.toNat_cons, ih]
    cases b <;> simp [BinaryArithmetic.bitVal, Nat.bit, Nat.add_comm]

end FormalizationKit.MachineArithmetic
