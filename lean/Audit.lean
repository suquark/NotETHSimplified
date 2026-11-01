import TransposeBase
import SatBase

/-! Axiom audit of the results of the shared libraries that the papers cite directly. Run with `lake env lean Audit.lean`. -/

open TransposeBase

#print axioms SatBase.sparseTree_leaves
#print axioms SatBase.sparseTree_height
#print axioms Sat.net_count
#print axioms Sector.skein
#print axioms Moments.digit_cost
#print axioms Exact.exact_degree
#print axioms Exact.cut_prop
#print axioms TransposeBase.Machine.compile_correct
