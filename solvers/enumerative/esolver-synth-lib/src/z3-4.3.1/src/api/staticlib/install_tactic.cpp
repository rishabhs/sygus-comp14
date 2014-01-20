// Automatically generated file.
#include"tactic.h"
#include"tactic_cmds.h"
#include"cmd_context.h"
#include"qe_sat_tactic.h"
#include"qe_tactic.h"
#include"vsubst_tactic.h"
#include"unit_subsumption_tactic.h"
#include"aig_tactic.h"
#include"fpa2bv_tactic.h"
#include"qffpa_tactic.h"
#include"ufbv_tactic.h"
#include"sat_tactic.h"
#include"probe.h"
#include"tactic.h"
#include"subpaving_tactic.h"
#include"sls_tactic.h"
#include"qflra_tactic.h"
#include"qfnra_tactic.h"
#include"qfbv_tactic.h"
#include"qflia_tactic.h"
#include"qfnia_tactic.h"
#include"ctx_solver_simplify_tactic.h"
#include"smt_tactic.h"
#include"bv1_blaster_tactic.h"
#include"max_bv_sharing_tactic.h"
#include"bit_blaster_tactic.h"
#include"bv_size_reduction_tactic.h"
#include"qfnra_nlsat_tactic.h"
#include"nlsat_tactic.h"
#include"diff_neq_tactic.h"
#include"recover_01_tactic.h"
#include"lia2pb_tactic.h"
#include"degree_shift_tactic.h"
#include"probe_arith.h"
#include"propagate_ineqs_tactic.h"
#include"purify_arith_tactic.h"
#include"nla2bv_tactic.h"
#include"factor_tactic.h"
#include"fm_tactic.h"
#include"pb2bv_tactic.h"
#include"add_bounds_tactic.h"
#include"normalize_bounds_tactic.h"
#include"fix_dl_var_tactic.h"
#include"ctx_simplify_tactic.h"
#include"simplify_tactic.h"
#include"der_tactic.h"
#include"solve_eqs_tactic.h"
#include"propagate_values_tactic.h"
#include"tseitin_cnf_tactic.h"
#include"elim_uncnstr_tactic.h"
#include"cofactor_term_ite_tactic.h"
#include"reduce_args_tactic.h"
#include"nnf_tactic.h"
#include"symmetry_reduce_tactic.h"
#include"split_clause_tactic.h"
#include"elim_term_ite_tactic.h"
#include"distribute_forall_tactic.h"
#include"occf_tactic.h"
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_0, qe::mk_sat_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_1, mk_qe_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_2, mk_vsubst_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_3, mk_unit_subsumption_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_4, mk_aig_tactic());
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_5, mk_fpa2bv_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_6, mk_qffpa_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_7, mk_ufbv_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_8, mk_ufbv_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_9, mk_sat_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_10, mk_sat_preprocessor_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_11, mk_skip_tactic());
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_12, mk_fail_tactic());
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_13, mk_fail_if_undecided_tactic());
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_14, mk_subpaving_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_15, mk_qfbv_sls_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_16, mk_qflra_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_17, mk_qfnra_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_18, mk_qfbv_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_19, mk_qflia_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_20, mk_qfnia_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_21, mk_ctx_solver_simplify_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_22, mk_smt_tactic(p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_23, mk_bv1_blaster_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_24, mk_max_bv_sharing_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_25, mk_bit_blaster_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_26, mk_bv_size_reduction_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_27, mk_qfnra_nlsat_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_28, mk_nlsat_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_29, mk_diff_neq_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_30, mk_recover_01_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_31, mk_lia2pb_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_32, mk_degree_shift_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_33, mk_propagate_ineqs_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_34, mk_purify_arith_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_35, mk_nla2bv_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_36, mk_factor_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_37, mk_fm_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_38, mk_pb2bv_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_39, mk_add_bounds_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_40, mk_normalize_bounds_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_41, mk_fix_dl_var_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_42, mk_ctx_simplify_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_43, mk_simplify_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_44, mk_elim_and_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_45, mk_der_tactic(m));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_46, mk_solve_eqs_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_47, mk_propagate_values_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_48, mk_tseitin_cnf_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_49, mk_tseitin_cnf_core_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_50, mk_elim_uncnstr_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_51, mk_cofactor_term_ite_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_52, mk_reduce_args_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_53, mk_snf_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_54, mk_nnf_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_55, mk_symmetry_reduce_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_56, mk_split_clause_tactic(p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_57, mk_elim_term_ite_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_58, mk_distribute_forall_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_59, mk_occf_tactic(m, p));
#define ADD_TACTIC_CMD(NAME, DESCR, FACTORY) ctx.insert(alloc(tactic_cmd, symbol(NAME), DESCR, alloc(FACTORY)))
#define ADD_PROBE(NAME, DESCR, PROBE) ctx.insert(alloc(probe_info, symbol(NAME), DESCR, PROBE))
void install_tactics(tactic_manager & ctx) {
  ADD_TACTIC_CMD("qe-sat", "check satisfiability of quantified formulas using quantifier elimination.", __Z3_local_factory_0);
  ADD_TACTIC_CMD("qe", "apply quantifier elimination.", __Z3_local_factory_1);
  ADD_TACTIC_CMD("vsubst", "checks satsifiability of quantifier-free non-linear constraints using virtual substitution.", __Z3_local_factory_2);
  ADD_TACTIC_CMD("unit-subsume-simplify", "unit subsumption simplification.", __Z3_local_factory_3);
  ADD_TACTIC_CMD("aig", "simplify Boolean structure using AIGs.", __Z3_local_factory_4);
  ADD_TACTIC_CMD("fpa2bv", "convert floating point numbers to bit-vectors.", __Z3_local_factory_5);
  ADD_TACTIC_CMD("qffpa", "(try to) solve goal using the tactic for QF_FPA.", __Z3_local_factory_6);
  ADD_TACTIC_CMD("bv", "builtin strategy for solving BV problems (with quantifiers).", __Z3_local_factory_7);
  ADD_TACTIC_CMD("ufbv", "builtin strategy for solving UFBV problems (with quantifiers).", __Z3_local_factory_8);
  ADD_TACTIC_CMD("sat", "(try to) solve goal using a SAT solver.", __Z3_local_factory_9);
  ADD_TACTIC_CMD("sat-preprocess", "Apply SAT solver preprocessing procedures (bounded resolution, Boolean constant propagation, 2-SAT, subsumption, subsumption resolution).", __Z3_local_factory_10);
  ADD_TACTIC_CMD("skip", "do nothing tactic.", __Z3_local_factory_11);
  ADD_TACTIC_CMD("fail", "always fail tactic.", __Z3_local_factory_12);
  ADD_TACTIC_CMD("fail-if-undecided", "fail if goal is undecided.", __Z3_local_factory_13);
  ADD_TACTIC_CMD("subpaving", "tactic for testing subpaving module.", __Z3_local_factory_14);
  ADD_TACTIC_CMD("qfbv-sls", "(try to) solve using stochastic local search for QF_BV.", __Z3_local_factory_15);
  ADD_TACTIC_CMD("qflra", "builtin strategy for solving QF_LRA problems.", __Z3_local_factory_16);
  ADD_TACTIC_CMD("qfnra", "builtin strategy for solving QF_NRA problems.", __Z3_local_factory_17);
  ADD_TACTIC_CMD("qfbv", "builtin strategy for solving QF_BV problems.", __Z3_local_factory_18);
  ADD_TACTIC_CMD("qflia", "builtin strategy for solving QF_LIA problems.", __Z3_local_factory_19);
  ADD_TACTIC_CMD("qfnia", "builtin strategy for solving QF_NIA problems.", __Z3_local_factory_20);
  ADD_TACTIC_CMD("ctx-solver-simplify", "apply solver-based contextual simplification rules.", __Z3_local_factory_21);
  ADD_TACTIC_CMD("smt", "apply a SAT based SMT solver.", __Z3_local_factory_22);
  ADD_TACTIC_CMD("bv1-blast", "reduce bit-vector expressions into bit-vectors of size 1 (notes: only equality, extract and concat are supported).", __Z3_local_factory_23);
  ADD_TACTIC_CMD("max-bv-sharing", "use heuristics to maximize the sharing of bit-vector expressions such as adders and multipliers.", __Z3_local_factory_24);
  ADD_TACTIC_CMD("bit-blast", "reduce bit-vector expressions into SAT.", __Z3_local_factory_25);
  ADD_TACTIC_CMD("reduce-bv-size", "try to reduce bit-vector sizes using inequalities.", __Z3_local_factory_26);
  ADD_TACTIC_CMD("qfnra-nlsat", "builtin strategy for solving QF_NRA problems using only nlsat.", __Z3_local_factory_27);
  ADD_TACTIC_CMD("nlsat", "(try to) solve goal using a nonlinear arithmetic solver.", __Z3_local_factory_28);
  ADD_TACTIC_CMD("diff-neq", "specialized solver for integer arithmetic problems that contain only atoms of the form (<= k x) (<= x k) and (not (= (- x y) k)), where x and y are constants and k is a numberal, and all constants are bounded.", __Z3_local_factory_29);
  ADD_TACTIC_CMD("recover-01", "recover 0-1 variables hidden as Boolean variables.", __Z3_local_factory_30);
  ADD_TACTIC_CMD("lia2pb", "convert bounded integer variables into a sequence of 0-1 variables.", __Z3_local_factory_31);
  ADD_TACTIC_CMD("degree-shift", "try to reduce degree of polynomials (remark: :mul2power simplification is automatically applied).", __Z3_local_factory_32);
  ADD_TACTIC_CMD("propagate-ineqs", "propagate ineqs/bounds, remove subsumed inequalities.", __Z3_local_factory_33);
  ADD_TACTIC_CMD("purify-arith", "eliminate unnecessary operators: -, /, div, mod, rem, is-int, to-int, ^, root-objects.", __Z3_local_factory_34);
  ADD_TACTIC_CMD("nla2bv", "convert a nonlinear arithmetic problem into a bit-vector problem, in most cases the resultant goal is an under approximation and is useul for finding models.", __Z3_local_factory_35);
  ADD_TACTIC_CMD("factor", "polynomial factorization.", __Z3_local_factory_36);
  ADD_TACTIC_CMD("fm", "eliminate variables using fourier-motzkin elimination.", __Z3_local_factory_37);
  ADD_TACTIC_CMD("pb2bv", "convert pseudo-boolean constraints to bit-vectors.", __Z3_local_factory_38);
  ADD_TACTIC_CMD("add-bounds", "add bounds to unbounded variables (under approximation).", __Z3_local_factory_39);
  ADD_TACTIC_CMD("normalize-bounds", "replace a variable x with lower bound k <= x with x' = x - k.", __Z3_local_factory_40);
  ADD_TACTIC_CMD("fix-dl-var", "if goal is in the difference logic fragment, then fix the variable with the most number of occurrences at 0.", __Z3_local_factory_41);
  ADD_TACTIC_CMD("ctx-simplify", "apply contextual simplification rules.", __Z3_local_factory_42);
  ADD_TACTIC_CMD("simplify", "apply simplification rules.", __Z3_local_factory_43);
  ADD_TACTIC_CMD("elim-and", "convert (and a b) into (not (or (not a) (not b))).", __Z3_local_factory_44);
  ADD_TACTIC_CMD("der", "destructive equality resolution.", __Z3_local_factory_45);
  ADD_TACTIC_CMD("solve-eqs", "eliminate variables by solving equations.", __Z3_local_factory_46);
  ADD_TACTIC_CMD("propagate-values", "propagate constants.", __Z3_local_factory_47);
  ADD_TACTIC_CMD("tseitin-cnf", "convert goal into CNF using tseitin-like encoding (note: quantifiers are ignored).", __Z3_local_factory_48);
  ADD_TACTIC_CMD("tseitin-cnf-core", "convert goal into CNF using tseitin-like encoding (note: quantifiers are ignored). This tactic does not apply required simplifications to the input goal like the tseitin-cnf tactic.", __Z3_local_factory_49);
  ADD_TACTIC_CMD("elim-uncnstr", "eliminate application containing unconstrained variables.", __Z3_local_factory_50);
  ADD_TACTIC_CMD("cofactor-term-ite", "eliminate term if-the-else using cofactors.", __Z3_local_factory_51);
  ADD_TACTIC_CMD("reduce-args", "reduce the number of arguments of function applications, when for all occurrences of a function f the i-th is a value.", __Z3_local_factory_52);
  ADD_TACTIC_CMD("snf", "put goal in skolem normal form.", __Z3_local_factory_53);
  ADD_TACTIC_CMD("nnf", "put goal in negation normal form.", __Z3_local_factory_54);
  ADD_TACTIC_CMD("symmetry-reduce", "apply symmetry reduction.", __Z3_local_factory_55);
  ADD_TACTIC_CMD("split-clause", "split a clause in many subgoals.", __Z3_local_factory_56);
  ADD_TACTIC_CMD("elim-term-ite", "eliminate term if-then-else by adding fresh auxiliary declarations.", __Z3_local_factory_57);
  ADD_TACTIC_CMD("distribute-forall", "distribute forall over conjunctions.", __Z3_local_factory_58);
  ADD_TACTIC_CMD("occf", "put goal in one constraint per clause normal form (notes: fails if proof generation is enabled; only clauses are considered).", __Z3_local_factory_59);
  ADD_PROBE("memory", "ammount of used memory in megabytes.", mk_memory_probe());
  ADD_PROBE("depth", "depth of the input goal.", mk_depth_probe());
  ADD_PROBE("size", "number of assertions in the given goal.", mk_size_probe());
  ADD_PROBE("num-exprs", "number of expressions/terms in the given goal.", mk_num_exprs_probe());
  ADD_PROBE("num-consts", "number of non Boolean constants in the given goal.", mk_num_consts_probe());
  ADD_PROBE("num-bool-consts", "number of Boolean constants in the given goal.", mk_num_bool_consts_probe());
  ADD_PROBE("num-arith-consts", "number of arithmetic constants in the given goal.", mk_num_arith_consts_probe());
  ADD_PROBE("num-bv-consts", "number of bit-vector constants in the given goal.", mk_num_bv_consts_probe());
  ADD_PROBE("produce-proofs", "true if proof generation is enabled for the given goal.", mk_produce_proofs_probe());
  ADD_PROBE("produce-model", "true if model generation is enabled for the given goal.", mk_produce_models_probe());
  ADD_PROBE("produce-unsat-cores", "true if unsat-core generation is enabled for the given goal.", mk_produce_unsat_cores_probe());
  ADD_PROBE("has-patterns", "true if the goal contains quantifiers with patterns.", mk_has_pattern_probe());
  ADD_PROBE("is-propositional", "true if the goal is in propositional logic.", mk_is_propositional_probe());
  ADD_PROBE("is-qfbv", "true if the goal is in QF_BV.", mk_is_qfbv_probe());
  ADD_PROBE("is-qfbv-eq", "true if the goal is in a fragment of QF_BV which uses only =, extract, concat.", mk_is_qfbv_eq_probe());
  ADD_PROBE("arith-max-deg", "max polynomial total degree of an arithmetic atom.", mk_arith_max_degree_probe());
  ADD_PROBE("arith-avg-deg", "avg polynomial total degree of an arithmetic atom.", mk_arith_avg_degree_probe());
  ADD_PROBE("arith-max-bw", "max coefficient bit width.", mk_arith_max_bw_probe());
  ADD_PROBE("arith-avg-bw", "avg coefficient bit width.", mk_arith_avg_bw_probe());
  ADD_PROBE("is-qflia", "true if the goal is in QF_LIA.", mk_is_qflia_probe());
  ADD_PROBE("is-qflra", "true if the goal is in QF_LRA.", mk_is_qflra_probe());
  ADD_PROBE("is-qflira", "true if the goal is in QF_LIRA.", mk_is_qflira_probe());
  ADD_PROBE("is-ilp", "true if the goal is ILP.", mk_is_ilp_probe());
  ADD_PROBE("is-qfnia", "true if the goal is in QF_NIA (quantifier-free nonlinear integer arithmetic).", mk_is_qfnia_probe());
  ADD_PROBE("is-qfnra", "true if the goal is in QF_NRA (quantifier-free nonlinear real arithmetic).", mk_is_qfnra_probe());
  ADD_PROBE("is-nia", "true if the goal is in NIA (nonlinear integer arithmetic, formula may have quantifiers).", mk_is_nia_probe());
  ADD_PROBE("is-nra", "true if the goal is in NRA (nonlinear real arithmetic, formula may have quantifiers).", mk_is_nra_probe());
  ADD_PROBE("is-pb", "true if the goal is a pseudo-boolean problem.", mk_is_pb_probe());
  ADD_PROBE("is-unbounded", "true if the goal contains integer/real constants that do not have lower/upper bounds.", mk_is_unbounded_probe());
}
