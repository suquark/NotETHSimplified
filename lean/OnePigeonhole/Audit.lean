import TransposeBase.Statements
import OnePigeonhole.Machine.FinalMain

/-! Axiom audit of the proof of `papers/one-pigeonhole/proof.tex`, at the pseudocode layer and on the machine. Run with `lake env lean OnePigeonhole/Audit.lean`. -/

#print axioms OnePigeonhole.sum_chi
#print axioms OnePigeonhole.card_exc_mul_sq_le
#print axioms OnePigeonhole.kappa
#print axioms OnePigeonhole.sum_kappa_chi_of_notMem_exc
#print axioms OnePigeonhole.tau_corner
#print axioms OnePigeonhole.Wires.tau_c_eq_d_iff
#print axioms OnePigeonhole.Bmat_sub_one_eq
#print axioms OnePigeonhole.rank_Bmat_sub_one_le
#print axioms OnePigeonhole.row_mem_span
#print axioms OnePigeonhole.hypotheses_of_numbers
#print axioms OnePigeonhole.det_eq_sum_rowMix
#print axioms OnePigeonhole.prod_eqv_eq_sum_rowMix
#print axioms OnePigeonhole.sum_exp_le
#print axioms OnePigeonhole.det_Hz_exp_le
#print axioms OnePigeonhole.prod_eqv_eq_sum_sumT
#print axioms OnePigeonhole.prod_eqv_eq_grid
#print axioms OnePigeonhole.det_cubeMat
#print axioms OnePigeonhole.sidePoly_congr
#print axioms OnePigeonhole.sideS_congr
#print axioms OnePigeonhole.sideS_exp_le
#print axioms OnePigeonhole.letter_of_coefH_ne_zero
#print axioms OnePigeonhole.det_Hz_eq_prod
#print axioms OnePigeonhole.det_Hz_eq_sum_U
#print axioms OnePigeonhole.blockF_reads
#print axioms OnePigeonhole.blockS_reads
#print axioms OnePigeonhole.det_decomp_sumT
#print axioms OnePigeonhole.det_decomp_cubes
#print axioms OnePigeonhole.det_decomp
#print axioms OnePigeonhole.det_decomp_masks
#print axioms OnePigeonhole.glue_eqv
#print axioms OnePigeonhole.sum_letterProduct
#print axioms OnePigeonhole.net_decomp_sumT
#print axioms OnePigeonhole.net_decomp
#print axioms OnePigeonhole.net_decomp_masks
#print axioms OnePigeonhole.card_blockBits_mul_le

#print axioms OnePigeonhole.Greedy.card_allowed
#print axioms OnePigeonhole.Greedy.score_best_le
#print axioms OnePigeonhole.Greedy.load_table_le
#print axioms OnePigeonhole.Greedy.sq_mul_capB_le
#print axioms OnePigeonhole.Greedy.wiresOf
#print axioms OnePigeonhole.Greedy.onNodes_wiresOf
#print axioms OnePigeonhole.Pseudo.greedy_spec
#print axioms OnePigeonhole.Pseudo.GreedySpec.run_layTE

#print axioms OnePigeonhole.Pseudo.sideT_fullWord
#print axioms OnePigeonhole.Pseudo.blockZ_cast
#print axioms OnePigeonhole.Pseudo.net_int

#print axioms OnePigeonhole.Pseudo.Leaf.exists_lits
#print axioms OnePigeonhole.Pseudo.Leaf.big_of_le
#print axioms OnePigeonhole.Pseudo.Leaf.run_wordE
#print axioms OnePigeonhole.Pseudo.Leaf.runZ_sideE
#print axioms OnePigeonhole.Pseudo.Leaf.runZ_blockE
#print axioms OnePigeonhole.Pseudo.Leaf.runZ_cTestE
#print axioms OnePigeonhole.Pseudo.Leaf.runZ_coreE
#print axioms OnePigeonhole.Pseudo.Leaf.coreE_eval
#print axioms OnePigeonhole.Pseudo.Leaf.coreE_ops_poly

#print axioms OnePigeonhole.Pseudo.Final.exp_part
#print axioms OnePigeonhole.Pseudo.Final.core_real
#print axioms OnePigeonhole.Pseudo.Final.shape_net
#print axioms OnePigeonhole.Pseudo.Final.leaf_main
#print axioms OnePigeonhole.Pseudo.Final.exists_m
#print axioms OnePigeonhole.Pseudo.Final.large_case
#print axioms OnePigeonhole.Pseudo.Final.pseudo_main
#print axioms OnePigeonhole.Pseudo.Final.pseudo_wide

#print axioms OnePigeonhole.Machine.machine_runs
#print axioms OnePigeonhole.Machine.machine_main
#print axioms OnePigeonhole.Machine.eth_false
#print axioms OnePigeonhole.Machine.not_ETH

/-! The end statements are those of `TransposeBase/Statements.lean`. -/

example : type_of% @OnePigeonhole.Pseudo.Final.pseudo_main = ∀ ε : ℝ, 0 < ε → TransposeBase.PseudoMain ε := rfl
example : type_of% @OnePigeonhole.Pseudo.Final.pseudo_wide = ∀ ε : ℝ, 0 < ε → TransposeBase.PseudoWide ε := rfl
example : type_of% @OnePigeonhole.Machine.machine_main = ∀ ε : ℝ, 0 < ε → TransposeBase.Machine.MachineMain ε := rfl
example : type_of% @OnePigeonhole.Machine.eth_false = TransposeBase.Machine.EthFalse := rfl
example : type_of% @OnePigeonhole.Machine.not_ETH = ¬ TransposeBase.Machine.ETH := rfl
