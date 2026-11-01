import TransposeBase.Statements
import UncrossingWires.Machine.FinalMain

/-! Axiom audit of the uncrossing proof at the pseudocode layer and on the machine. Run with `lake env lean UncrossingWires/Audit.lean`. -/

#print axioms UncrossingWires.sum_cube_prod
#print axioms UncrossingWires.prod_sum_viewL
#print axioms UncrossingWires.sum_symm_prod
#print axioms UncrossingWires.Ppol_add
#print axioms UncrossingWires.dLen_le
#print axioms UncrossingWires.seed_sum
#print axioms UncrossingWires.dLen_cheap_le
#print axioms UncrossingWires.step_val
#print axioms UncrossingWires.potential_two
#print axioms UncrossingWires.potential_min
#print axioms UncrossingWires.newW_total_le
#print axioms UncrossingWires.chain_val
#print axioms UncrossingWires.BaseNet.val_base
#print axioms UncrossingWires.BaseNet.w0_total

#print axioms UncrossingWires.Pseudo.runZ_rectAE
#print axioms UncrossingWires.Pseudo.runZ_rectBE
#print axioms UncrossingWires.Pseudo.wtNext_spec
#print axioms UncrossingWires.Pseudo.wordNext_spec
#print axioms UncrossingWires.Pseudo.wt0_spec
#print axioms UncrossingWires.Pseudo.word0_spec
#print axioms UncrossingWires.Pseudo.chainVal_eq
#print axioms UncrossingWires.Pseudo.core_spec

#print axioms UncrossingWires.Greedy.best_le
#print axioms UncrossingWires.Greedy.best_first
#print axioms UncrossingWires.Greedy.load_table_le
#print axioms UncrossingWires.Greedy.psi_table_le
#print axioms UncrossingWires.Greedy.psi_table_le_all
#print axioms UncrossingWires.Pseudo.greedy_spec
#print axioms UncrossingWires.Pseudo.Final.shape_net
#print axioms UncrossingWires.Pseudo.Final.psi_part
#print axioms UncrossingWires.Pseudo.Final.leaf_main
#print axioms UncrossingWires.Pseudo.Final.exponent_le
#print axioms UncrossingWires.Pseudo.Final.exists_rate
#print axioms UncrossingWires.Pseudo.Final.large_case
#print axioms UncrossingWires.Pseudo.Final.pseudo_main
#print axioms UncrossingWires.Pseudo.Final.encF_lt_word
#print axioms UncrossingWires.Pseudo.Final.pseudo_wide

#print axioms SatBase.sparseTree_leaves
#print axioms SatBase.noSparseRule_variable_bound
#print axioms TransposeBase.Machine.compile_correct

#print axioms UncrossingWires.Machine.main_value
#print axioms UncrossingWires.Machine.machine_runs
#print axioms UncrossingWires.Machine.machine_main
#print axioms UncrossingWires.Machine.eth_false
#print axioms UncrossingWires.Machine.not_ETH

/-! The end statements are those of `TransposeBase/Statements.lean`. -/

example : type_of% @UncrossingWires.Pseudo.Final.pseudo_main = ∀ ε : ℝ, 0 < ε → TransposeBase.PseudoMain ε := rfl
example : type_of% @UncrossingWires.Pseudo.Final.pseudo_wide = ∀ ε : ℝ, 0 < ε → TransposeBase.PseudoWide ε := rfl
example : type_of% @UncrossingWires.Machine.machine_main = ∀ ε : ℝ, 0 < ε → TransposeBase.Machine.MachineMain ε := rfl
example : type_of% @UncrossingWires.Machine.eth_false = TransposeBase.Machine.EthFalse := rfl
example : type_of% @UncrossingWires.Machine.not_ETH = ¬ TransposeBase.Machine.ETH := rfl
