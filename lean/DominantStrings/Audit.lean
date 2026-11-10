import TransposeBase.Statements
import DominantStrings.Machine.FinalMain
import DominantStrings.Machine.Bounded

/-! Axiom audit of the proof with dominant strings at the pseudocode layer and on the machine. Run with `lake env lean DominantStrings/Audit.lean`. -/

#print axioms DominantStrings.sum_cube_prod
#print axioms DominantStrings.prod_sum_viewL
#print axioms DominantStrings.sum_symm_prod
#print axioms DominantStrings.Ppol_add
#print axioms DominantStrings.dLen_le
#print axioms DominantStrings.seed_sum
#print axioms DominantStrings.dLen_cheap_le
#print axioms DominantStrings.step_val
#print axioms DominantStrings.potential_two
#print axioms DominantStrings.potential_min
#print axioms DominantStrings.newW_total_le
#print axioms DominantStrings.chain_val
#print axioms DominantStrings.BaseNet.val_base
#print axioms DominantStrings.val_flip
#print axioms DominantStrings.sum_mk_index
#print axioms DominantStrings.sum_pair_prod
#print axioms DominantStrings.BaseNet.w0_total

#print axioms DominantStrings.Pseudo.runZ_rectAE
#print axioms DominantStrings.Pseudo.runZ_rectBE
#print axioms DominantStrings.Pseudo.wtNext_spec
#print axioms DominantStrings.Pseudo.wordNext_spec
#print axioms DominantStrings.Pseudo.wt0_spec
#print axioms DominantStrings.Pseudo.word0_spec
#print axioms DominantStrings.Pseudo.chainVal_eq
#print axioms DominantStrings.Pseudo.core_spec

#print axioms DominantStrings.Greedy.best_le
#print axioms DominantStrings.Greedy.best_first
#print axioms DominantStrings.Greedy.load_table_le
#print axioms DominantStrings.Greedy.psi_table_le
#print axioms DominantStrings.Greedy.psi_table_le_all
#print axioms DominantStrings.Pseudo.greedy_spec
#print axioms DominantStrings.Pseudo.Final.shape_net
#print axioms DominantStrings.Pseudo.Final.psi_part
#print axioms DominantStrings.Pseudo.Final.leaf_main
#print axioms DominantStrings.Pseudo.Final.exponent_le
#print axioms DominantStrings.Pseudo.Final.exists_rate
#print axioms DominantStrings.Pseudo.Final.large_case
#print axioms DominantStrings.Pseudo.Final.pseudo_main
#print axioms DominantStrings.Pseudo.Final.encF_lt_word
#print axioms DominantStrings.Pseudo.Final.pseudo_wide
#print axioms DominantStrings.Pseudo.Final.pseudo_bounded

#print axioms SatBase.sparseTree_leaves
#print axioms SatBase.noSparseRule_variable_bound
#print axioms TransposeBase.Machine.compile_correct

#print axioms DominantStrings.Machine.main_value
#print axioms DominantStrings.Machine.machine_runs
#print axioms DominantStrings.Machine.machine_main
#print axioms DominantStrings.Machine.eth_false
#print axioms DominantStrings.Machine.not_ETH
#print axioms DominantStrings.Machine.occ_toCNF
#print axioms DominantStrings.Machine.machine_bounded

/-! The end statements are those of `TransposeBase/Statements.lean` and `DominantStrings/Statements.lean`. -/

example : type_of% @DominantStrings.Pseudo.Final.pseudo_bounded = ∀ (D : ℕ) (ε : ℝ), 0 < ε → DominantStrings.PseudoBounded D ε := rfl
example : type_of% @DominantStrings.Machine.machine_bounded = ∀ (D : ℕ) (ε : ℝ), 0 < ε → DominantStrings.Machine.MachineBounded D ε := rfl

example : type_of% @DominantStrings.Pseudo.Final.pseudo_main = ∀ ε : ℝ, 0 < ε → TransposeBase.PseudoMain ε := rfl
example : type_of% @DominantStrings.Pseudo.Final.pseudo_wide = ∀ ε : ℝ, 0 < ε → TransposeBase.PseudoWide ε := rfl
example : type_of% @DominantStrings.Machine.machine_main = ∀ ε : ℝ, 0 < ε → TransposeBase.Machine.MachineMain ε := rfl
example : type_of% @DominantStrings.Machine.eth_false = TransposeBase.Machine.EthFalse := rfl
example : type_of% @DominantStrings.Machine.not_ETH = ¬ TransposeBase.Machine.ETH := rfl
