/***************************************************************************
FileName : helper.cpp

SystemName: ParSyn : Parallel Boolean Funciton Synthesis Tool/ Parallel Skolem Function Generation Tool.

Authors: Shetal Shah, Dinesh Chattani, Ajith John
 
Affliation: IIT Bombay

Description: The file contains a number of functions that are used by the functions in AIGBasedSkolem.cc
************************************************************/

#include <iostream>
#include <sstream>
#include <map>
#include <fstream>
#include <algorithm>
#include "helper.hpp"


using namespace std;


//############CONFIG OPTIONS ###########
string pathValue; // path where the circuit is present, should end with '/'
string circuitValue; //circuit name or benchmark name for e.g., 6s1.aig
int numOfComponents = 4; // Number of components to generated , defalut 4
int badStateDepth = 3; // bad state  update depth (backward unrolling steps), default 3

// The following line is changed by Ajith John on 22 Nov 2013
// It is found that resyn, resyn2, resyn2rs, compress, and compress2
// calls balance initially. Calling balance on the result of 
// x & y with x replaced by y results in assertion failure inside balance,
// caused by y & y. Hence always call fraig initially which reduces y & y to y
// without balancing.

//string nodeCommand = "ps;resyn;resyn2;resyn2rs;compress;compress2;fraig;ps;"; Original command by Dinesh
string nodeCommand = "fraig;balance; rewrite; rewrite -z; balance; rewrite -z; balance;balance; rewrite; refactor; balance; rewrite; rewrite -z; balance; refactor -z; rewrite -z; balance;balance; resub -K 6; rewrite; resub -K 6 -N 2; refactor; resub -K 8; balance; resub -K 8 -N 2; rewrite; resub -K 10; rewrite -z; resub -K 10 -N 2; balance; resub -K 12; refactor -z; resub -K 12 -N 2; rewrite -z; balance;balance -l; rewrite -l; rewrite -z -l; balance -l; rewrite -z -l; balance -l;balance -l; rewrite -l; refactor -l; balance -l; rewrite -l; rewrite -z -l; balance -l; refactor -z -l; rewrite -z -l; balance -l;"; //"fraig;resyn;resyn2;resyn2rs;compress;compress2;"; 
//####################################################################

//############CONFIG OPTIONS FOR SKOLEM FUNCTION GENERATION###########
set<string> factor_file_names; //set of file names which contain the original factors
string variables_to_eliminate_file_name; //file name which contains the variables to be eliminated

// string initCommand = "resyn;resyn2;fraig;"; Original command by Dinesh
string initCommand = "fraig; balance; rewrite; rewrite -z; balance; rewrite -z; balance; balance; rewrite; refactor; balance; rewrite; rewrite -z; balance; refactor -z; rewrite -z; balance;"; 	//"fraig; resyn; resyn2;" 
string benchmark_type = "benchmark_type";
string benchmark_name = "";
string machine = "machine";
string problem_kind = "variable_elimination";

int minimum_size_to_apply_nodeCommand = 1;

string benchmark_name_without_extension;
string extension_of_benchmark;
int maximum_index_to_eliminate = -1; // this helps in stopping computation after skolem function
				     // of some variables are found
bool apply_cone_before_simplifications = true; // option to turn on coi reduction after simplifications

int order_of_elimination_of_variables = 1; // orders possible are
// 0: alphabetical order
// 1: least occurring variable first
// 2: external order
// 3: factor graph based ordering
// 4: reverse of factor graph based ordering
// 5: reverse of least occurring variable first
// 6: smallest cofactor-1 first ordering
// 7: biggest cofactor-1 first ordering
int number_of_variables_eliminated = 0; 
bool perform_reverse_substitution = true; // option to enable reverse-substitution of skolem functions after their generation to make them order-independent
string variable_order_file_name = "";
bool print_factor_graph = false; // option to print the factor graph

int uniformity_condition_counter = 1; // count of the uniformity condition

// Declarations for timeout
time_t time_out = 1800;
time_t time_out_start = 0;
bool time_out_enabled = false; // timeout will happen only if this variable is true
bool timed_out = false;

bool exit_after_order_finding = false;
bool exit_after_factor_graph_generation = false;
bool exit_after_finding_abstract_skolem_functions = false;
// Declarations for timeout ends here
//####################################################################

// options for analysing compose
 unsigned long long int first_level_cache_hits = 0;  
 unsigned long long int first_level_cache_misses = 0;
 unsigned long long int second_level_cache_hits = 0;  
 unsigned long long int second_level_cache_misses = 0;
 unsigned long long int leaf_cases = 0;  
 unsigned long long int node_cases = 0;
 unsigned long long int no_recreation_cases = 0;  
 unsigned long long int recreation_cases = 0;

//####################################################################
//####################################################################

 // data to plot
 unsigned long long int sum_of_number_of_factors_containing_variable = 0;  
 unsigned long long int sum_of_skolem_function_sizes = 0;
 unsigned long long int total_number_of_compose_operations = 0;  
 unsigned long long int total_time_in_compose_operations = 0;
 unsigned long long int total_time_in_alpha_combined = 0;
 unsigned long long int total_time_in_delta_part = 0;
 unsigned long long int total_time_in_correction_part = 0;
 unsigned long long int total_time_in_delta_combined = 0;
 unsigned long long int total_time_in_next_factor = 0;
 unsigned long long int sum_of_skolem_function_sizes_after_reverse_substitution = 0;
 list<int> skolem_function_sizes_after_reverse_substitution;
 unsigned long long int total_time_in_ordering = 0;
 unsigned long long int total_of_skyline_sizes_in_least_cost_ordering = 0;
 unsigned long long int total_time_in_compute_size = 0;
 unsigned long long int total_time_in_compute_support = 0;
 unsigned long long int total_time_in_generator_initialization = 0;
 int sum_of_numbers_of_affecting_factors = 0;

 int max_factor_size = -1;
 int min_factor_size = -1;
 int max_factor_varstoelim_size = -1;
 int min_factor_varstoelim_size = -1;

 int number_of_boolean_operations_for_variable = 0;
 unsigned long long int BooleanOpTime = 0;
 int number_of_support_operations_for_variable = 0;

 int total_number_of_compose_operations_in_initial_skolem_function_generation = 0;
 unsigned long long int total_ComposeTime_in_initial_skolem_function_generation = 0;
 int total_number_of_boolean_operations_in_initial_skolem_function_generation = 0;
 unsigned long long int total_BooleanOpTime_in_initial_skolem_function_generation = 0;
 int total_number_of_support_operations_in_initial_skolem_function_generation = 0;
 unsigned long long int total_FactorFindingTime_in_initial_skolem_function_generation = 0;
 int size_of_quantified_result_in_bdd_like_scheme = 0;
//####################################################################

//########################################################################

// declarations for least cost first ordering
 map<int, set<string> > factor_graph_factors_to_vars_map;
 map<string, set<int> > factor_graph_vars_to_factors_map;
 map<int, string > factor_graph_factors_to_topvars_map;
 set<string > topvars;

 map<string, int > factor_graph_vars_to_sccnos_map;
 map<int, set<string> > factor_graph_sccnos_to_sccs_map;

 map<string, int > vars_to_eqclassnos_map;
 map<int, set<string> > eqclassnos_to_eqclasses_map;

 list<string> ordered_vars_to_elim;
 set<string> unordered_vars_to_elim;

 map<int, int> factor_to_costs_map;
 map<int, int> skolemfunctions_to_costs_map;
 map<int, int> deltas_to_costs_map;

//#########################################################################
//########################################################################

// declarations for proving correctness

 bool prove_correctness_of_skolem_functions_using_qbf_solving = false; 
 bool prove_correctness_of_skolem_functions_of_conjunctions = false;
 string qbf_solver_to_use = "";
 
//#########################################################################
//########################################################################

// declarations for scope reduction inside factorized approach

 set<int> top_factors_considered;
//#########################################################################
//#########################################################################

// declarations to interface with AIG Manager

 Aig_Obj_t* aig_bad_set = NULL;
 map<int, string> Ci_id_to_Ci_name_map;
 map<string, int> Ci_name_to_Ci_number_map;
 map<string, Aig_Obj_t*> Ci_to_eliminate_name_to_Ci_to_eliminate_object_map; 
 map<int, Aig_Obj_t*> B_i_index_to_B_i_object_map; 
 map<string, Aig_Obj_t*> connection_string_to_connection_object_map; 

 map<string, Aig_Obj_t*> Ci_name_to_Ci_object_map; 
 map<int, Aig_Obj_t*> Ci_to_eliminate_renamed_to_Ci_to_eliminate_renamed_object_map; 
 map<string, Aig_Obj_t*> Ci_to_eliminate_renamed_name_to_Ci_to_eliminate_renamed_object_map; 

//#########################################################################


 // declarations to perform CEGAR style skolem function generation

 bool enable_cegar = false; // To turn/off CEGAR based skolem function computation (by default disabled)
 int cegar_iteration_number = 0; 
 Aig_Obj_t* disjunction_of_bad_symbols;
 Aig_Obj_t* conjunction_of_factors = NULL;
 Aig_Obj_t* renamed_conjunction_of_factors;
 Aig_Obj_t* B_equivalence_part = NULL;
 int number_of_Cis = 0;
 t_HashTable<string, int> LabelTable;
 int LabelCount = 1;
 map<string, int> Ci_name_to_Ci_label_mapForGetCNF;
 map<int, string> Ci_label_to_Ci_name_mapForGetCNF;
 int number_of_variables_in_renamed_conjunction_of_factors = 0;
 unsigned long long int total_time_in_smt_solver = 0;
 string solver = "abc"; // abc, glucose and lingeling are supported; abc is default
 bool apply_global_simplifications_before_each_iteration = false;
 t_HashTable<string, bool> EvaluationTable;
 int refinement_strategy = 0;
 map<int, set<int> > sensitivity_list; 
 map<int, set<int> > dependency_list; 
 string kind_of_global_simplifications = "default";
 bool use_interpolant_as_skolem_function = false;
 int size_of_alpha_in_interpolant_computation_for_variable = -1;
 int size_of_beta_in_interpolant_computation_for_variable = -1;
 unsigned long long int time_in_interpolant_computation_for_variable = 0;
 unsigned long long int total_time_in_interpolant_computation = 0;

 map<int, set<string> > connections_starting_at_skolem_function; 
 map<int, set<string> > connections_ending_at_skolem_function; 
 int maximum_length_of_connection_in_connection_based_scheme = 0;
 int number_of_connections_in_connection_based_scheme = 0;
 int number_of_connections_updated_in_iteration_in_connection_based_scheme = 0;
 bool apply_optimization_on_connection_finding = true;
 map<int, map<int, int> > values_of_variables_from_bad_to_var;
 map<int, map<int, int> > values_of_variables_from_var;
 map<string, int> values_of_Y_variables;

// declarations to perform incremental solving
 map<int, int> Z_variable_counter; 
 map<string, int> I_variable_counter;
 map<string, Aig_Obj_t*> temporary_variable_for_incremental_solving_to_object_map;
 bool apply_solver_simplify_in_incremental_sat = true;// switching off solver_simplify

 sat_solver* pSat_for_exactness_check; 
 t_HashTable<int, int> IncrementalLabelTableForExactnessCheck;
 int IncrementalLabelCountForExactnessCheck = 1;
 map<string, int> Ci_name_to_Ci_label_mapForExactnessCheck; 
 map<int, string> Ci_label_to_Ci_name_mapForExactnessCheck; 

 sat_solver* pSat_for_mismatch_check; 
 t_HashTable<int, int> IncrementalLabelTableForMismatchCheck;
 int IncrementalLabelCountForMismatchCheck = 1;
 map<string, int> Ci_name_to_Ci_label_mapForMismatchCheck; 
 map<int, string> Ci_label_to_Ci_name_mapForMismatchCheck; 

 bool incremental_solver_for_mismatch_check_initialized = false;
 bool apply_incremental_solving_for_mismatch_check = true; // to apply incremental solving on mismatch checks also
 // in incremental sat increases the solving time

 
 // the following are for debugging 
 map<int, Aig_Obj_t*> BetaCombineds;
 map<int, Aig_Obj_t*> AlphaOrGammaCombineds;
 map<int, Aig_Obj_t*> GammaDisjunctions;
 map<int, Aig_Obj_t*> DeltaDisjunctions;
 vector<Aig_Obj_t*> DeltasForSpecificVariable;
 // for debugging ends here

 // data collected
 unsigned long long int total_time_in_initial_abstraction_generation_in_cegar = 0;
 unsigned long long int total_time_in_cegar_loops_in_cegar = 0;
 unsigned long long int total_time_in_connection_substitution_in_cegar = 0;
 unsigned long long int total_time_in_reverse_substitution_in_cegar = 0;

 unsigned long long int total_time_in_exactness_checking_in_cegar = 0;
 unsigned long long int total_time_in_x_new_recompution_in_cegar = 0;
 unsigned long long int total_time_in_reevaluation_in_cegar = 0;
 int number_of_exactness_checking_in_cegar = 0;
 int number_of_x_new_recompution_in_cegar = 0;
 int number_of_reevaluation_in_cegar = 0;

 unsigned long long int size_computation_time_in_initialization = 0;
 unsigned long long int size_computation_time_in_initial_abstraction_generation_in_cegar = 0;
 unsigned long long int size_computation_time_in_reverse_substitution_in_cegar = 0;
 unsigned long long int size_computation_time_in_cegar_loops_in_cegar = 0;
 unsigned long long int size_computation_time_in_connection_substitution_in_cegar = 0;
 // sum of the above four should give the total time
 list<int> sizes_of_exactness_formulae_in_cegar;
 list<unsigned long long int> times_in_cnf_generation_in_cegar;
 list<unsigned long long int> times_in_sat_solving_in_cegar;
 unsigned long long int total_time_in_true_sat_solving_in_cegar = 0;
 unsigned long long int total_time_in_false_sat_solving_in_cegar = 0;
 unsigned long long int total_time_in_sat_solving_in_cegar = 0;
 list<unsigned long long int> times_in_aig_simplification_in_cegar;

 // for additional assertion checking inside cegar
 int maximum_bad_location_from_counterexample_in_this_iteration;
 int cannot_be_one_count = 0;
 int cannot_be_zero_count = 0;
 map<string, Aig_Obj_t*> cannot_be_string_to_cannot_be_object_map;
 map<Aig_Obj_t*, Aig_Obj_t*> cannot_be_object_to_cannot_be_dag_map;
 map<int, set<Aig_Obj_t*> > cannot_be_one_set;
 map<int, set<Aig_Obj_t*> > cannot_be_zero_set;
 map<int, Aig_Obj_t*> initial_cannot_be_zero_dags;
 map<int, Aig_Obj_t*> initial_cannot_be_zero_objects;
 int size_of_conjunction_of_factors = 0;
 list<int> sizes_of_cannot_be_one_elements_of_variable;
 list<int> sizes_of_cannot_be_zero_elements_of_variable;

 int number_of_components_generated = 0;
 int cegar_iteration_for_correction_index = 0;
 set<string> variables_not_quantified;
 set<string> original_variables;
 set<string> variables_quantified;
 unsigned long long int total_time_in_mu_evaluation_in_cegar = 0;
 bool select_cannot_be_elements_based_on_supports = true;
 bool avoid_y_variables_in_select_cannot_be_elements_based_on_supports = true;
 bool refine_all_locations_in_cegar = true;
 bool use_interpolants_in_cegar = false;

 unsigned long long int total_time_in_interpolant_computation_in_cegar = 0;
 bool use_dontcare_optimization_in_cegar = false;
 unsigned long long int total_time_in_dontcare_optimization_in_cegar = 0;
 map<int, int> D_variable_counter; // for incremental solving
 map<int, int> S_variable_counter; // for incremental solving
 int InitialSkolemFunctionSizeBeforeOptimization; // size of initial skolem function before don't care optimization
 bool use_refinement_from_bottom_in_mu_based_scheme_with_optimizations_in_cegar = false;
 bool use_incremental_solving_for_generalization_in_mu_based_scheme_with_optimizations_in_cegar = false;
 unsigned long long int total_time_in_generalization_in_mu_based_scheme_with_optimizations_in_cegar = 0;

 sat_solver* pSat_for_generalization_check; 
 t_HashTable<int, int> IncrementalLabelTableForGeneralizationCheck;
 int IncrementalLabelCountForGeneralizationCheck = 1;
 map<string, int> Ci_name_to_Ci_label_mapForGeneralizationCheck; 
 map<int, string> Ci_label_to_Ci_name_mapForGeneralizationCheck; 
 bool incremental_solver_for_generalization_check_initialized = false;

 bool drop_free_factors = true;

 map<int, int> Y_variable_counter; // for incremental solving
 map<int, Aig_Obj_t*> N_i_index_to_N_i_object_map; 
 map<int, set<int> > bads_to_exclude; 

 // declarations for component generation
 unsigned long long int cumulative_time_in_compute_size = 0;

 // declarations for benchmark generation
 bool generate_graph_decomposition_benchmarks = false;

 // declarations for LOGGING
 string logfile_prefix;

 // Declarations for memoryout
 int memory_out;

 // Declarations for bloqqer
 bool use_bloqqer = false;
 bool skip_satisfiability_check_before_bloqqer = true; // assume that qbf is sat
 bool exit_after_generating_qdimacs = true;

 // To limit variables to eliminate
 int limit_on_variables_to_eliminate = -1;


 // To select skolem function in Jiang's method
 string skolem_function_type_in_jiang = "cofactorone";

 bool accumulate_formulae_in_cbzero_in_cegar = true; // by default, we accumulate
 // formulae in Cb0 in CEGAR


 // options for unifying CEGAR methods
 bool use_assumptions_in_unified_cegar = false;
 bool use_bads_in_unified_cegar = false;
 bool use_cbzero_in_unified_cegar = false;
 int assumptions_flag = 1;
 Aig_Obj_t* use_bads_in_unified_cegar_aig;
 Aig_Obj_t* use_cbzero_in_unified_cegar_aig;
 bool allow_intermediate_generic_sat_calls = true;
 bool compute_initial_bads_from_cbs = true;

 // declarations for performing graph decomposition
 bool write_component_as_sequential_circuit = true;
 bool write_component_in_file = false;
 string component_generation_strategy = "uncovered_edge";
 bool use_uncovered_edge_with_preferred_edge = false;
 int failure_condition_location = 0;
 Aig_Obj_t* failure_condition_aig = NULL;
 set<string> input_names_in_circuit;
 int component_number_to_be_generated = -1;
 bool generate_specific_component = false;
 bool purify_failure_condition = true;
 bool apply_tsietin_encoding_before_calling_cegarskolem_inside_graph_decomposition = false;
 bool apply_global_time_outs_in_component_generation = false;
 bool apply_fraiging_in_graph_decomposition = false;
 bool conjoin_negfail_with_failfxi_to_get_preferred_edges = true;

 // declarations for performing tsietin encoding on benchmarks
 bool apply_tsietin_encoding_on_benchmarks = false;
 int number_of_tsietin_variables = 0;
 map<string, Aig_Obj_t*> tsietin_variable_to_exact_skolem_function_map; 
 bool obtain_tsietin_variables_in_bfs_order = true;
 int threshold_for_tsietin_encoding = -1;


 // declarations supporting game benchmarks 
 string original_logfile_prefix;
 string original_benchmark_name;
 map<int, string> initial_Ci_id_to_Ci_name_map; 
 map<string, int> initial_Ci_name_to_Ci_number_map; 
 map<string, Aig_Obj_t*> initial_Ci_name_to_Ci_object_map; 
 int initial_number_of_Cis = 0;


 // declarations for generation of satisfiable benchmarks
 bool generate_satisfiable_benchmarks = false;
 int limit_on_number_of_extra_conjuncts = -1;
 bool make_variable_to_skolem_function_map_complex = true;
 string function_to_make_variable_to_skolem_function_map_complex = "fi";
 bool make_alternate_entries_toggle_in_initial_variable_to_skolem_function_map = true;
 bool extend_tsietin_encoding_to_extra_part = true;
 bool make_initial_variable_to_skolem_function_map_a_formula = false;


 // declarations to existentially quantified Tseitin variables during benchmark generation
 // Note that this is applicable when GENERATE-SATISFIABLE-BENCHMARKS=false. 
 // If GENERATE-SATISFIABLE-BENCHMARKS=true, then  Tseitin variables are existentially quantified
 // always
 bool existentially_quantify_tseitin_variables_in_benchmark_generation = false; 

 
 // to fix the number of clauses/factor in qdimacs benchmark
 int number_of_clauses_per_factor_in_qdimacs_benchmark = 1;


 // for skolem function generation from arbitrary Boolean formulas using CegarSkolem
 bool perform_cegar_on_arbitrary_boolean_formulas = true;
 map<string, vector<Aig_Obj_t*> > R0_map; // maps NNF node of given polarity to r0's of variables to eliminate
 map<string, vector<Aig_Obj_t*> > R1_map; // maps NNF node of given polarity to r1's of variables to eliminate
 list<string> Global_VariablesToEliminate; // Global copy of list of variables to eliminate
 set<string> Global_VariablesToEliminate_Set; // Global copy of set of variables to eliminate
 set<string> Global_VariablesToRemain_Set; // Global copy of set of variables to remain
 Aig_Obj_t* input_arbitrary_boolean_formula; // copy of arbitrary_boolean_formula given as input
 bool prove_correctness_of_skolem_functions_of_arbitrary_boolean_formula = false; // for proving correctness
 bool prove_correctness_of_skolem_functions_of_arbitrary_boolean_formula_detailed_check = false; // for detailed check at all levels of computation
 int number_of_cegarskolem_calls_on_arbitrary_boolean_formulas = 0;
 int number_of_monoskolem_calls_on_arbitrary_boolean_formulas = 0;
 int number_of_disjunctions_on_arbitrary_boolean_formulas = 0; 
 int number_of_conjunctions_on_arbitrary_boolean_formulas = 0;
 list<int> skolem_function_sizes_before_reverse_substitution;
 unsigned long long int total_time_in_reverse_substitution_on_arbitrary_boolean_formulas = 0;
 unsigned long long int total_time_in_callconjunction = 0;
 unsigned long long int total_time_in_calldisjunction = 0;
 unsigned long long int total_time_in_callmonolithic = 0;
 unsigned long long int total_time_in_cegarskolem = 0;
 int min_skolem_function_size_after_reverse_substitution = -1;
 int max_skolem_function_size_after_reverse_substitution = -1;
 int min_skolem_function_size_before_reverse_substitution = -1;
 int max_skolem_function_size_before_reverse_substitution = -1;
 int total_number_of_cegar_iterations_in_cegarskolem = 0;
 int max_number_of_cegar_iterations_in_cegarskolem = -1;
 int min_number_of_cegar_iterations_in_cegarskolem = -1;
 bool mask_printing_cegar_details = true;
 int depth_from_root_in_cegarskolem_call_on_arbitrary_boolean_formulas = -1;
 bool generate_benchmarks_for_arbitrary_boolean_combinations = false;
 unsigned long long int total_time_in_ordering_for_arbitrary_boolean_combinations = 0;

 sat_solver* pSat_for_proving_correctness; 
 t_HashTable<int, int> IncrementalLabelTableForProvingCorrectness;
 int IncrementalLabelCountForProvingCorrectness = 1;
 map<string, int> Ci_name_to_Ci_label_mapForProvingCorrectness; 
 map<int, string> Ci_label_to_Ci_name_mapForProvingCorrectness; 
 bool incremental_solver_for_proving_correctness_initialized;

 bool use_for_qbf_satisfiability = false;

 bool choose_to_apply_monoskolem_on_smaller_problem_instances = false;
 t_HashTable<int, int> TreeSizesOfNodes;
 t_HashTable<int, set<string> > VarsToElimOfNodes;
 unsigned long long int total_time_in_dfs_during_preprocessing;
 int threshold_size_mult_two_pow_varstoelim_to_apply_monoskolem = 8000;

 bool mask_printing_details_file = true; 

 bool generate_all_counterexamples_from_sat_call = false; // from a solution of ~F(X, Y), 
 // generate all counterexamples before calling sat solver again
 unsigned long long int cumulative_time_in_true_sat_solving_in_cegar = 0;
 unsigned long long int cumulative_time_in_false_sat_solving_in_cegar = 0;
 unsigned long long int cumulative_time_in_sat_solving_in_cegar = 0;
 unsigned long long int total_time_in_simulation_to_replace_sat_in_cegar = 0;
 unsigned long long int cumulative_time_in_simulation_to_replace_sat_in_cegar = 0;
 bool avoid_sat_call_in_functional_forms = false;
 bool internal_flag_to_avoid_sat_call_in_functional_forms = false;
 int number_of_simulations_before_sat_call_in_functional_forms = 1;
 unsigned long long int total_time_in_function_evaluation_to_replace_sat_in_cegar_in_functional_forms = 0;
 bool cleanup_after_each_step_in_arbitrary_boolean_combinations = true;
 set<Aig_Obj_t*> intermediate_cos_created;
 set<Aig_Obj_t*> intermediate_cis_created;
 set<Aig_Obj_t*> r1r0_cos_created;
 bool set_most_significant_word_to_zero_in_factorization_benchmarks = false;
 // Declarations for global time-out inside the parallel version
 time_t cluster_global_time_out = 900;
 time_t cluster_global_time_out_start = 0;
 bool cluster_global_time_out_enabled = false; // global timeout will happen only if this variable is true
 bool cluster_global_timed_out = false; 
 bool avoid_cluster_global_time_out_at_top_node = true; // this will cause computing exact result at the top node
 bool factorizedskolem_applied_on_disjunction = false; // should be true if we are applying FactorizedSkolemFunctionGenerator on disjunctions
 // Declarations for RSynth
 bool use_rsynth = false;
 bool perform_interractive_solving_on_arbitrary_boolean_formulas = false;
 string skf_gen_algorithm = "MonoSkolem";// to simplify the options and to allow user 
 // to directly select the skf.gen. algorithm
 bool include_tsietin_variables_in_rsynth_qdimacs_generation = true;

 // Declarations to make interface with SAT solver clean
 bool use_generic_sat_solver_interface = false;
 string sat_solver_used_in_cegar = "abc";

 // Options for simplifying the command-line options
 bool prove_correctness_of_skolem_functions = false; 
//#########################################################################


/**
 * converts string to integer
 * @param str
 * @return 
 */
int StringToInteger(string str)
{
    stringstream streamObj;
    int stInt;
    streamObj << str;
    streamObj >> stInt;
    return stInt;
}

string IntegerToString(int i)
{
    string temp;
    stringstream istr;
    istr << i;
    temp = istr.str();
    return temp;
}

/*
 * TODO: can be made more efficient
 */
void changeNamesbyAddingSuffix(Abc_Ntk_t* &Ntk)
{
    Abc_Obj_t* tempObj;
    int i = 0;
    map<int, string> origNames;
    int j = 0;
    string name;

    Abc_NtkForEachPi(Ntk, tempObj, i)
    {
        // cout << "name is " << Abc_ObjName(tempObj) << endl;
        name = Abc_ObjName(tempObj);

        origNames[tempObj->Id] = name;

    }

    Abc_NtkForEachPo(Ntk, tempObj, i)
    {
        //cout << "name is " << Abc_ObjName(tempObj) << endl;
        name = Abc_ObjName(tempObj);
        if (name.find('_') != string::npos)
        {
            name = name.substr(0, name.find('_'));
        }
        origNames[tempObj->Id] = name;
    }
    Nm_ManFree(Ntk->pManName);
    Ntk->pManName = Nm_ManCreate(Abc_NtkCiNum(Ntk) + Abc_NtkCoNum(Ntk) + Abc_NtkBoxNum(Ntk));
    j = 0;

    Abc_NtkForEachPi(Ntk, tempObj, i)
    {
        string name = origNames[tempObj->Id];

        //         if (name.find('_') != string::npos)
        //            {
        //                name = name.substr(0, name.find('_'));
        //            }
        //  string suffix = "_" + IntegerToString(ABC::nameSuffixCount++);

        //Abc_ObjAssignName(tempObj, (char*) origNames[j++].c_str(), (char*) suffix.c_str());
        Abc_ObjAssignName(tempObj, (char*) name.c_str(), NULL);
    }

    Abc_NtkForEachPo(Ntk, tempObj, i)
    {
        string suffix = "_" + IntegerToString(ABC::nameSuffixCount++);
        Abc_ObjAssignName(tempObj, (char*) origNames[tempObj->Id].c_str(), (char*) suffix.c_str());
    }
    origNames.clear();

}

int getLastPinumByprefix(Abc_Ntk_t* c1, string name)
{
    int i;
    Abc_Obj_t* tempObj;
    name = name.substr(0, name.find("_"));
    string temp;
    for (i = Abc_NtkPiNum(c1) - 1; i >= 0; --i)
    {
        tempObj = Abc_NtkPi(c1, i);
        temp = Abc_ObjName(tempObj);
        temp = temp.substr(0, temp.find("_"));
        if (temp == name)
            return i;

    }

    return -1;

}

Abc_Obj_t* getPIObjByName(Abc_Ntk_t*& pNtk, const string &name)
{
    Abc_Obj_t* tempObj;
    int i;

    Abc_NtkForEachPi(pNtk, tempObj, i)
    {
        if (Abc_ObjName(tempObj) == name)
        {
            return tempObj;
        }
    }
}

Abc_Obj_t* getPOObjByPrefix(Abc_Ntk_t* pNtk, const string &prefix)
{
    Abc_Obj_t* tempObj = NULL;
    int i;

    Abc_NtkForEachPo(pNtk, tempObj, i)
    {
        string objName = Abc_ObjName(tempObj);
        objName = objName.substr(0, objName.find('_'));
        if (prefix == objName)
        {
            return tempObj;
        }
    }
}

Abc_Obj_t* getPiObjWithHighestSuffix(Abc_Ntk_t* &c1)
{
    int i;
    Abc_Obj_t* tempObj;
    map<int,Abc_Obj_t*> mapOfObj ;
    Abc_NtkForEachPi(c1,tempObj,i)
    {
        string name = Abc_ObjName(tempObj);
        int suffix = StringToInteger(name.substr(name.find("_")+1));
        mapOfObj[suffix] = tempObj;
    }
    return mapOfObj.rbegin()->second;
}
/**
 * removepos will remove the outputs for benchmarks as our outputs latch's next state.
 */
void changeNamesAndRemovePos(Abc_Ntk_t*& c1, string namePrefix, int removepos)
{
    //string command = "ps;write inputF.v";
    //ABC::getSingleton()->comExecute(ABC::getSingleton()->getAbcFrame(), command);
    //getchar();
    #ifdef DEBUG_SKOLEM
    cout << "changing names " << endl;
    #endif

    assert(c1 != NULL);
    if (removepos)
    {
	int number_of_pos = Abc_NtkPoNum(c1);		
	while(number_of_pos >= 1)
	{
		#ifdef DEBUG_SKOLEM
		cout << "number of POs = " << number_of_pos << endl;
		#endif

		int po_to_be_deleted = number_of_pos-1;

		#ifdef DEBUG_SKOLEM
		Abc_Obj_t* tempPo = Abc_NtkPo(c1, po_to_be_deleted);
		assert(tempPo != NULL);
		string tempPoname = Abc_ObjName(tempPo);
		cout << "deleting PO number " << po_to_be_deleted << " with name " << tempPoname << " with address " << tempPo << endl;
		#endif

		Abc_NtkDeleteObj(Abc_NtkPo(c1, po_to_be_deleted));
		number_of_pos = Abc_NtkPoNum(c1);			
	}
	#ifdef DEBUG_SKOLEM
        cout << "deleted POS" << endl;
	#endif
    }
    Abc_Obj_t* tempObj;
    int i = 0;
    
#ifdef HWMCC_BENCHMARK
    int extraLatchId;
    Abc_Obj_t* extraLatchObj;
    Abc_NtkForEachLatchOutput(c1, extraLatchObj, i)
    {
        if (Abc_ObjName(extraLatchObj) == EXTRA_LATCH)
        {
            extraLatchId = extraLatchObj->Id;
           // getchar();
        }
        cout << Abc_ObjName(extraLatchObj) << extraLatchObj->Id << endl;
    }

#endif
     
//    Nm_ManFree(c1->pManName);
//    cout << "here " << endl << Abc_NtkPiNum(c1) << endl;
//    c1->pManName = Nm_ManCreate(Abc_NtkCiNum(c1) + Abc_NtkCoNum(c1) + Abc_NtkBoxNum(c1));
//    int j = 0;
//
//    ;
//
//    Abc_NtkForEachPi(c1, tempObj, i)
//    {
//        string suffix = "_" + IntegerToString(++j);
//        Abc_ObjAssignName(tempObj, (char*) namePrefix.c_str(), (char*) suffix.c_str());
//    }
    changeNamesToTempForPIs(c1,namePrefix+"_");
   

#ifdef HWMCC_BENCHMARK
     Nm_Man_t* t = c1->pManName;

    

        Nm_ManTableDelete(t, extraLatchObj->Id);
      
        Abc_ObjAssignName(extraLatchObj, (char*) EXTRA_LATCH.c_str(), NULL);
    
#endif
    
    #ifdef DEBUG_SKOLEM
    cout << "changed the names of primary inputs" << endl;
    #endif

}

void DeleteNetworksInMap(map<string, Abc_Ntk_t*> &mapOfNetworks)
{
    cout << "Deleting from Vector " << endl;
    map<string, Abc_Ntk_t*>::iterator it = mapOfNetworks.begin(), end = mapOfNetworks.end();
    while (it != end)
    {
        //  cout<<"deleting "<<it->first<<endl;
        Abc_NtkDelete(it->second);
        ++it;
    }
    mapOfNetworks.clear();
}

bool DeleteNetworkByNameFromMap(const string &name, map<string, Abc_Ntk_t*> & mapOfNetworks)
{
    map<string, Abc_Ntk_t*>::iterator it = mapOfNetworks.find(name);
    if (it != mapOfNetworks.end())
    {
        Abc_NtkDelete(it->second);
        return true;
    }
    return false;
}

void printPIs(Abc_Ntk_t*pNtk)
{
    int i;
    Abc_Obj_t* tempObj;

    Abc_NtkForEachPi(pNtk, tempObj, i)
    {
        cout << Abc_ObjName(tempObj) << endl;
    }
}

void readFileAndInitializeConfigVars()
{
    ifstream configFile(MYCONFIGFILENAME.c_str());

    if (!configFile)
    {
#ifndef benchmark
        return;
#endif
        assert(false && "cannot open config file");
    }
    string line;

    while (getline(configFile, line, '\n'))
    {

        if (line.empty() || line[0] == '#')
        {
            continue;
        }
        trimString(line);
        int idx = line.find("=");
        string name = line.substr(0, idx);
        string value = line.substr(idx + 1, line.length());
        setOption(name, value);
    }
}

void trimString(string & s)
{
    s.erase(remove(s.begin(), s.end(), ' '), s.end());
}

void setOption(const string & name, const string &value)
{
    cout << "name is " << name << " value is " << value << endl;
    if (name == "PATHNAME")
    {
        pathValue = value;
    }
    else if (name == "CIRCUITNAME")
    {
        circuitValue = value;
    }
    else if (name == "NUM-OF-COMPONENTS")
    {
        numOfComponents = StringToInteger(value);
    }
    else if (name == "BAD-STATE-DEPTH")
    {
        badStateDepth = StringToInteger(value);
    }
    else if(name == "NODE-COMMAND")
    {
        nodeCommand = value;
    }
    else
    {
        cout << "Option name is " << name << "::" << value << endl;
        assert(false && "Invalid Option");
    }
}

string renameLatches(Abc_Ntk_t*& c1)
{
    map<int, string> origNames;

    int j = 0;
    int i = 0;
    Abc_Obj_t* tempObj;
#ifdef HWMCC_BENCHMARK
    assert(Abc_NtkFindCo(c1,(char*)"extra_latch_in") != NULL);
#endif
    Abc_NtkForEachPi(c1, tempObj, i)
    {
        origNames[tempObj->Id] = Abc_ObjName(tempObj);
    }
//    Nm_ManFree(c1->pManName);
//    cout << "here " << endl << Abc_NtkPiNum(c1) << endl;
//    c1->pManName = Nm_ManCreate(Abc_NtkCiNum(c1) + Abc_NtkCoNum(c1) + Abc_NtkBoxNum(c1));

    string name;
    Nm_Man_t* t = c1->pManName;
    Abc_NtkForEachPi(c1, tempObj, i)
    {
        name = origNames[tempObj->Id];
        if (name.find(PREFPREFIX) != string::npos)
        {
            Abc_ObjAssignName(tempObj, (char*) name.c_str(), NULL);
        }
        else
        {
            //cout<<"reassigning name "<<endl;
            Nm_ManTableDelete(t,tempObj->Id);
            name = LATCHPREFIX + IntegerToString(++j);

            Abc_ObjAssignName(tempObj, (char*) name.c_str(), NULL);
            //getchar();
        }
    }
    j = 0;

    Abc_NtkForEachPo(c1, tempObj, i)
    {
//        if(Abc_ObjName(tempObj) == EXTRA_LATCH+"_in")
//        {
//            cout<<"continuing"<<endl;
//           
//            continue;
//        }

        #ifdef DEBUG_SKOLEM 
        cout<<"renaming "<<Abc_ObjName(tempObj)<<" to suffix "<<j+1<<endl;;
	#endif

         Nm_ManTableDelete(t,tempObj->Id);
        name = LATCHOUTPREFIX + IntegerToString(++j);

	#ifdef DEBUG_SKOLEM 
        cout << "latchout:" << Abc_ObjName(tempObj) << tempObj->Id << endl;
	#endif

        Abc_ObjAssignName(tempObj, (char*) name.c_str(), NULL);
    }
    return name;
   // getchar();
}

void renameBadStateInputs(Abc_Ntk_t*& not_of_bad)
{
    int i;
    Abc_Obj_t* tempObj;
    Nm_Man_t* t = not_of_bad->pManName;

    Abc_NtkForEachPi(not_of_bad, tempObj, i)
    {

        Nm_ManTableDelete(t, tempObj->Id);
        Abc_ObjAssignName(tempObj, (char*) (LATCHPREFIX + IntegerToString(i + 1)).c_str(), NULL);
    }
}

void changeNamesToTempForPIs(Abc_Ntk_t*& copyOfC1, const string& newName)
{
    int i;
    Abc_Obj_t* tempObj;
    string name;
    if (newName == "")
    {
        name = TEMPPREFIX;
    }
    else
    {
        name = newName;
    }
    Nm_Man_t* t = copyOfC1->pManName;

    Abc_NtkForEachPi(copyOfC1, tempObj, i)
    {
        Nm_ManTableDelete(t, tempObj->Id);
        Abc_ObjAssignName(tempObj, (char*) (name + IntegerToString(i + 1)).c_str(), NULL);
    }
}
//skip Latch inputs which are converted to PIs using comb

void changeNamesToTempForOnlyPIs(Abc_Ntk_t*& copyOfC1, const string & newName)
{
    int i;
    int j = 1;
    Abc_Obj_t* tempObj;
    string name;
    if (newName == "")
    {
        name = TEMPPREFIX;
    }
    else
    {
        name = newName;
    }
    Nm_Man_t* t = copyOfC1->pManName;

    Abc_NtkForEachPi(copyOfC1, tempObj, i)
    {
        string origName = Abc_ObjName(tempObj);
        if (origName.find(LATCHPREFIX) != string::npos)
        {
            continue;
        }
        Nm_ManTableDelete(t, tempObj->Id);
        Abc_ObjAssignName(tempObj, (char*) (name + IntegerToString(j)).c_str(), NULL);
        ++j;
    }

}

string changeNameToTempOfObj(Abc_Obj_t*& prefObj, string name, int suffixCount)
{
    assert(prefObj != NULL);
    if (name == "")
    {
        name = TEMPPREFIX;
    }
    string newName = name + IntegerToString(suffixCount);
    Nm_Man_t* t = prefObj->pNtk->pManName;
    Nm_ManTableDelete(t, prefObj->Id);
    Abc_ObjAssignName(prefObj, (char*) newName.c_str(), NULL);
    return newName;
}

//finds the number  of PI object in the given network

int getNumberOfObject(Abc_Obj_t*& obj, Abc_Ntk_t* pNtk)
{
    Abc_Obj_t* tempObj;
    int i;
    int num = 0;
    if (Abc_ObjIsPi(obj))
    {

        Abc_NtkForEachPi(pNtk, tempObj, i)
        {
            if (tempObj->Id == obj->Id)
            {
                return num;
            }
            ++num;
        }
    }
    else if (Abc_ObjIsPo(obj))
    {

        Abc_NtkForEachPo(pNtk, tempObj, i)
        {
            if (tempObj->Id == obj->Id)
            {
                return num;
            }
            ++num;
        }
    }

    return -1;
}

int deleteAllPiNamesWithBad(Abc_Ntk_t*& c1)
{
    Abc_Obj_t* tempObj;
    int i;
    int count = 0;
    vector<Abc_Obj_t*> bads;
    Abc_NtkForEachPi(c1,tempObj,i)
    {
        string name = Abc_ObjName(tempObj);
        if(name.find("bad") != string::npos)
        {
            ++count;
            bads.push_back(tempObj);
        }
    }
    int j;
    for(int i = 0;i<bads.size();++i)
    {
        Abc_Obj_t* fout;
        Abc_ObjForEachFanout(bads[i],fout,j)
        {
            bads.push_back(fout);
        }
        Abc_NtkDeleteObj(bads[i]);
    }
    return count;
}



// New functions added by Ajith John starts here

void readConfigFile()
{
    ifstream configFile(MYCONFIGFILENAME.c_str());

    if (!configFile)
    {
	assert(false && "cannot open config file");
    }
    string line;

    while (getline(configFile, line, '\n'))
    {
        if (line.empty() || line[0] == '#')
        {
            continue;
        }

        trimString(line);
        int idx = line.find("=");
	assert(idx != string::npos);

        string name = line.substr(0, idx);
        string value = line.substr(idx + 1, line.length());
        setArgument(name, value);
    }

    setInternalOptions();
}


void readCommandLineArguments(int argc, char** argv)
{
	bool show_only_basic_usage = true;

	#ifdef LIMITED_USAGE
		if(argc < 3) // we need at least the benchmark name and variables to eliminate
	    	{
			if(show_only_basic_usage)
				basic_usage();
			else
				limited_usage();

			exit(1);
	    	}
	#else
		if(argc < 2) // we need at least the benchmark name
	    	{
			usage();
			exit(1);
	    	}
	#endif

	#ifdef LIMITED_USAGE
		int i;
		for(i = 1; i <= argc-3; i++)
	    	{
	      		char* argument = argv[i];
	      		string argument_str(argument);
			int idx = argument_str.find("=");
			assert(idx != string::npos);

			string name = argument_str.substr(0, idx);
			string value = argument_str.substr(idx + 1, argument_str.length());
			setArgument(name, value);
		}

		char* argument;
		string argument_str;
		argument = argv[i];
		argument_str = argument;
		
		benchmark_name = argument_str;
		int index_of_dot = benchmark_name.find_last_of(".");
		assert(index_of_dot != string::npos);
		string extension = benchmark_name.substr(index_of_dot+1);	
		assert(extension == "aig" || extension == "v" || extension == "qdimacs");
		extension_of_benchmark = extension;
		benchmark_name_without_extension = benchmark_name.substr(0, index_of_dot); 

		i++;
		argument = argv[i];
		argument_str = argument;
		
		variables_to_eliminate_file_name = argument_str;	
	#else
		for(int i = 1; i <= argc-1; i++)
	    	{
	      		char* argument = argv[i];
	      		string argument_str(argument);
			int idx = argument_str.find("=");
			assert(idx != string::npos);

			string name = argument_str.substr(0, idx);
			string value = argument_str.substr(idx + 1, argument_str.length());
			setArgument(name, value);
		}
	#endif

	setInternalOptions();
} 


void setInternalOptions()
{
	if(prove_correctness_of_skolem_functions)
	{
		if(perform_cegar_on_arbitrary_boolean_formulas)
		{
			prove_correctness_of_skolem_functions_of_arbitrary_boolean_formula = true;	
		}
		else
		{
			prove_correctness_of_skolem_functions_of_conjunctions = true;
		}
	}
}


void printTabs(int count)
{
	for(int i = 1; i <= count; i++)
	{
		cout << "\t";
	}
}


void limited_usage()
{
	cout<<"\nUsage: SkolemFunctionGenerator [options] <specification-file> <outputs-file>\n";
	
	cout<<"\nwhere specification-file is boolean specification in .aig or .v file,";
	cout<<"\nand outputs-file is the list of outputs to be synthesized.\n";
	
	cout<<"\nMain options are:\n";

	//cout<<"\nBENCHMARK-NAME=<name of benchmark>"; 
	//cout<<"\t\t\tgive the name of benchmark", 

	//cout<<"\nBENCHMARK-TYPE=<type of benchmark>";
	//cout<<"\t\t\tcrafted, hwmcc-2010, hwmcc-2012, generated, qdimacs,";
	//cout<<"\n\t\t\t\t\t\t\tfactorization or external_skolem\n";

	//cout<<"\nPROBLEM-KIND=<kind of problem>";
	//cout<<"\t\t\t\tvariable_elimination, benchmark_generation, graph_decomposition";
	//cout<<"\n\t\t\t\t\t\t\tor print_stats (default is variable_elimination)\n";

	//cout<<"\nMACHINE=<name of machine>\n";

	// options for variable elimination
	//cout<<"\nMain options for variable_elimination are:\n";

	cout<<"\nALGORITHM=<algorithm>";
	cout<<"\t\t\t\t\tCSeqCegar, CegarSkolem, or MonoSkolem (default is MonoSkolem)";
	//cout<<"\n\t\t\t\t\t\t\tSelecting Bloqqer converts the problem to equivalent QDIMACS file and exits";
	//cout<<"\n\t\t\t\t\t\t\tSelecting Rsynth converts the problem to equivalent Rsynth input and exits\n";

	//cout<<"\nVARIABLES-TO-ELIMINATE=<file name>";
	//cout<<"\t\t\tName of file with variables whose Skolem functions are to be generated\n";

	cout<<"\nORDER=<number>";
	cout<<"\t\t\t\t\t\t0: lexicographical order, 1: least occurring variable first, ";
	cout<<"\n\t\t\t\t\t\t\t2: order from external file ";
	//cout<<"\n\t\t\t\t\t\t\t4: reverse factor graph based ordering ";
	//cout<<"\n\t\t\t\t\t\t\t4: reverse factor graph based ordering, 5: most occurring variable first, ";
	//cout<<"\n\t\t\t\t\t\t\t6: smallest cofactor-1 first ordering, 7: biggest cofactor-1 first ordering ";
	cout<<"\n\t\t\t\t\t\t\t(default is 1)\n";

        cout<<"\nORDER-FILE=<file name>";
	cout<<"\t\t\t\t\tFor ORDER=2";

	cout<<"\nPERFORM-REVERSE-SUBSTITUTION=<true/false>";
	cout<<"\t\tto enable reverse-substitution (default is true)";

	cout<<"\nTIMEOUT=<time-out in seconds>";
	cout<<"\t\t\t\tto set the time-out (by default time-out is disabled)";

	cout<<"\nMEMORYOUT=<memory-out in GiBs>";
	cout<<"\t\t\t\tto set the memory-out (by default memory-out is disabled)";

	//cout<<"\nPROVE-CORRECTNESS-FOR-CONJUNCTIONS=<true/false>";
	//cout<<"\t\tto prove correctness of CegarSkolem / MonoSkolem (default is false)";

	//cout<<"\nPROVE-CORRECTNESS-FOR-ARBITRARY-FORMULAE=<true/false>";
	//cout<<"\tto prove correctness of CSeqCegar (by default false)";
	
	cout<<"\nPROVE-CORRECTNESS=<true/false>";
	cout<<"\t\t\t\tto prove correctness of Skolem functions generated (by default false)";


	// options for CEGAR based algorithms
	cout<<"\n\nOptions for CegarSkolem are:\n";
	cout<<"\nSELECT-CANNOT-BE-ELEMENTS-BASED-ON-SUPPORTS=<true/false>";
	cout<<"  to turn on/off selection of true cannot-be elements based on supports";
	cout<<"\n\t\t\t\t\t\t\tinside refinement (by default true; if false then all ";
	cout<<"\n\t\t\t\t\t\t\tthe cannot-be elements that are true are selected)\n";

	
	cout<<"\nREFINE-ALL-LOCATIONS-IN-CEGAR=<true/false>";
	cout<<"\t\tto turn on/off refining all locations from source of conflict to destination";
	cout<<"\n\t\t\t\t\t\t\tinside refinement (by default true; if false then only the destination";
	cout<<"\n\t\t\t\t\t\t\tlocation is refined)\n";

	cout<<"\nUSE-INTERPOLANTS-IN-CEGAR=<true/false>";
	cout<<"\t\t\tto turn on/off use of Craig interpolants in CEGAR (default is false)";
	cout<<"\nUSE-DONTCARE-OPTIMIZATION-IN-CEGAR=<true/false>";
	cout<<"\t\tto turn on/off use of don't-care optimization in CEGAR (default is false)";
	cout<<"\nACCUMULATE-FORMULAE-IN-CB0-IN-CEGAR=<true/false>";
	cout<<"\tto turn on/off accumulation of formulae in Cb0 in CEGAR (default is true)";
	cout<<"\nUSE-ASSUMPTIONS-IN-CEGAR=<true/false>";
	cout<<"\t\t\tto turn on/off fixing of Skolem functions one by one in CEGAR (default is false)";
	cout<<"\nUSE-BADS-IN-CEGAR=<true/false>";
	cout<<"\t\t\t\tto turn on/off use of disjunction of bads in epsilon in CEGAR (default is false)";
	cout<<"\nUSE-CBZERO-IN-CEGAR=<true/false>";
	cout<<"\t\t\tto turn on/off use of r0[i] in psi_i in CEGAR (default is false)";
	
	// options for MonoSkolem
	cout<<"\n\nOptions for MonoSkolem are:\n";

	// --> --> options for MonoSkolem
	cout<<"\nUSE-INTERPOLANT-AS-SKOLEM-FUNCTION=<true/false>";
	cout<<"\t\tuse Craig interpolant as Skolem function in MonoSkolem (default is  false)"; 
	cout<<"\nSKOLEM-FUNCTION-TYPE-IN-MONOSKOLEM=<function type>";
	cout<<"\twhen USE-INTERPOLANT-AS-SKOLEM-FUNCTION=false, set function_type to";
	cout<<"\n\t\t\t\t\t\t\tcofactorone or cofactorone_or_negcofactorzero (default is cofactorone)\n";
		
		        
        // options for CSeqCeagr
	cout<<"\n\nOptions for CSeqCegar are:\n";

	cout<<"\nAPPLY-MONOSKOLEM-ON-SMALL-INSTANCES=<true/false>";
	cout<<"\tapply MonoSkolem on small problem instances inside CSeqCegar (default is false)"; 

	cout<<"\nTHRESHOLD-SIZE-MULT-TWO-POW-VARSTOELIM=<value>";
	cout<<"\t\tthreshold value of Tree-size of formula * 2^(number of varstoelim) beyond";
	cout<<"\n\t\t\t\t\t\t\twhich apply MonoSkolem on AND nodes (by default 8000)\n";

	cout << "\nGENERATE-ALL-COUNTEREXAMPLES-FROM-SAT-CALL=<true/false>";
	cout<<" generate all counterexamples from each sat call (default is false)";

	//cout << "\nAVOID-SAT-CALL-IN-FUNCTIONAL-FORMS=<true/false>";
	//cout<<"\t\treplace satisfiable sat call by simulation when the formula F(X,Y) is in a";
	//cout<<"\n\t\t\t\t\t\t\tfunctional form (by default false)";

	//cout << "\nNUMBER-OF-SIMULATIONS-BEFORE-SAT-CALL=<value>";
	//cout<<"\t\tnumber of unsat simulations before calling sat solver when";
	//cout<<"\n\t\t\t\t\t\t\tAVOID-SAT-CALL-IN-FUNCTIONAL-FORMS is true (by default 1)\n";

	cout<<"\nGRACEFUL-TIMEOUT=<time-out in seconds>";
	cout<<"\t\t\tafter graceful-timeout, CSeqCegar skips refinement loop and";
	cout<<"\n\t\t\t\t\t\t\treturns the initial r1/r0's (disabled by default)\n\n";

	//cout<<"\nAVOID-GRACEFUL-TIMEOUT-AT-TOPNODE=<true/false>";
	//cout<<"\t\tavoid graceful-timeout at top-node giving exact result (default is true)\n";
	
}



void basic_usage()
{
	cout<<"\nUsage: SkolemFunctionGenerator [options] <specification-file> <outputs-file>\n";
	
	cout<<"\nwhere specification-file is boolean specification in .aig or .v file,";
	cout<<"\nand outputs-file is the list of outputs to be synthesized.\n";
	
	cout<<"\noptions are:\n";

	cout<<"\nALGORITHM=<algorithm>";
	cout<<"\t\t\t\t\tCSeqCegar, CegarSkolem, or MonoSkolem (default is CSeqCegar)";
	
	cout<<"\nORDER=<number>";
	cout<<"\t\t\t\t\t\t0: lexicographical order, 1: least occurring variable first, ";
	cout<<"\n\t\t\t\t\t\t\t2: order from external file ";
	
	cout<<"\n\t\t\t\t\t\t\t(default is 1)\n";

        cout<<"\nORDER-FILE=<file name>";
	cout<<"\t\t\t\t\tFor ORDER=2";

	cout<<"\nPERFORM-REVERSE-SUBSTITUTION=<true/false>";
	cout<<"\t\tto enable reverse-substitution (default is true)";

	cout<<"\nTIMEOUT=<time-out in seconds>";
	cout<<"\t\t\t\tto set the time-out (by default time-out is disabled)";

	cout<<"\nMEMORYOUT=<memory-out in GiBs>";
	cout<<"\t\t\t\tto set the memory-out (by default memory-out is disabled)";

	cout<<"\nPROVE-CORRECTNESS=<true/false>";
	cout<<"\t\t\t\tto prove correctness of Skolem functions generated (by default false)";

	cout<<"\nGRACEFUL-TIMEOUT=<time-out in seconds>";
	cout<<"\t\t\tafter graceful-timeout, CSeqCegar skips refinement loop and";
	cout<<"\n\t\t\t\t\t\t\treturns the initial r1/r0's (disabled by default)\n\n";
	
}




void usage()
{
	cout<<"\nUsage: SkolemFunctionGenerator [options]\n";
	cout<<"\nMain options are:\n";

	cout<<"\nBENCHMARK-NAME=<name of benchmark>"; 
	cout<<"\t\t\tgive the name of benchmark", 

	//cout<<"\nBENCHMARK-TYPE=<type of benchmark>";
	//cout<<"\t\t\tcrafted, hwmcc-2010, hwmcc-2012, generated, qdimacs,";
	//cout<<"\n\t\t\t\t\t\t\tfactorization or external_skolem\n";

	cout<<"\nPROBLEM-KIND=<kind of problem>";
	cout<<"\t\t\t\tvariable_elimination, benchmark_generation, graph_decomposition";
	cout<<"\n\t\t\t\t\t\t\tor print_stats (default is variable_elimination)\n";

	//cout<<"\nMACHINE=<name of machine>\n";

	// options for variable elimination
	cout<<"\nMain options for variable_elimination are:\n";

	cout<<"\nSKF-GEN-ALGORITHM=<algorithm>";
	cout<<"\t\t\t\tCSeqCegar, CegarSkolem, MonoSkolem, Bloqqer, or Rsynth (default is MonoSkolem)";
	cout<<"\n\t\t\t\t\t\t\tSelecting Bloqqer converts the problem to equivalent QDIMACS file and exits";
	cout<<"\n\t\t\t\t\t\t\tSelecting Rsynth converts the problem to equivalent Rsynth input and exits\n";

	cout<<"\nVARIABLES-TO-ELIMINATE=<file name>";
	cout<<"\t\t\tName of file with variables whose Skolem functions are to be generated\n";

	cout<<"\nORDER-OF-VARIABLE-ELIMINATION=<number>";
	cout<<"\t\t\t0: alphabetical order, 1: least occurring variable first, ";
	cout<<"\n\t\t\t\t\t\t\t2: order from external file ";
	//cout<<"\n\t\t\t\t\t\t\t4: reverse factor graph based ordering, 5: most occurring variable first, ";
	//cout<<"\n\t\t\t\t\t\t\t6: smallest cofactor-1 first ordering, 7: biggest cofactor-1 first ordering ";
	cout<<"\n\t\t\t\t\t\t\t(default is 1)\n";

        cout<<"\nVARIABLE-ORDER-FILE=<file name>";
	cout<<"\t\t\t\tFor ORDER-OF-VARIABLE-ELIMINATION=2";

	cout<<"\nPERFORM-REVERSE-SUBSTITUTION=<true/false>";
	cout<<"\t\tto enable reverse-substitution (default is true)";

	cout<<"\nTIMEOUT=<time-out in seconds>";
	cout<<"\t\t\t\tto set the time-out (by default time-out is disabled)";

	cout<<"\nMEMORYOUT=<memory-out in GiBs>";
	cout<<"\t\t\t\tto set the memory-out (by default memory-out is disabled)";

	//cout<<"\nPROVE-CORRECTNESS-FOR-CONJUNCTIONS=<true/false>";
	//cout<<"\t\tto prove correctness of CegarSkolem / MonoSkolem (default is false)";

	//cout<<"\nPROVE-CORRECTNESS-FOR-ARBITRARY-FORMULAE=<true/false>";
	//cout<<"\tto prove correctness of CSeqCegar (by default false)";
	
	cout<<"\nPROVE-CORRECTNESS=<true/false>";
	cout<<"\t\t\t\tto prove correctness of Skolem functions generated (by default false)";


	// options for CEGAR based algorithms
	cout<<"\n\nOptions for CegarSkolem are:\n";
	cout<<"\nSELECT-CANNOT-BE-ELEMENTS-BASED-ON-SUPPORTS=<true/false>";
	cout<<"  to turn on/off selection of true cannot-be elements based on supports";
	cout<<"\n\t\t\t\t\t\t\tinside refinement (by default true; if false then all ";
	cout<<"\n\t\t\t\t\t\t\tthe cannot-be elements that are true are selected)\n";

	
	cout<<"\nREFINE-ALL-LOCATIONS-IN-CEGAR=<true/false>";
	cout<<"\t\tto turn on/off refining all locations from source of conflict to destination";
	cout<<"\n\t\t\t\t\t\t\tinside refinement (by default true; if false then only the destination";
	cout<<"\n\t\t\t\t\t\t\tlocation is refined)\n";

	cout<<"\nUSE-INTERPOLANTS-IN-CEGAR=<true/false>";
	cout<<"\t\t\tto turn on/off use of Craig interpolants in CEGAR (default is false)";
	cout<<"\nUSE-DONTCARE-OPTIMIZATION-IN-CEGAR=<true/false>";
	cout<<"\t\tto turn on/off use of don't-care optimization in CEGAR (default is false)";
	cout<<"\nACCUMULATE-FORMULAE-IN-CB0-IN-CEGAR=<true/false>";
	cout<<"\tto turn on/off accumulation of formulae in Cb0 in CEGAR (default is true)";
	cout<<"\nUSE-ASSUMPTIONS-IN-CEGAR=<true/false>";
	cout<<"\t\t\tto turn on/off fixing of Skolem functions one by one in CEGAR (default is false)";
	cout<<"\nUSE-BADS-IN-CEGAR=<true/false>";
	cout<<"\t\t\t\tto turn on/off use of disjunction of bads in epsilon in CEGAR (default is false)";
	cout<<"\nUSE-CBZERO-IN-CEGAR=<true/false>";
	cout<<"\t\t\tto turn on/off use of r0[i] in psi_i in CEGAR (default is false)";
	
	// options for MonoSkolem
	cout<<"\n\nOptions for MonoSkolem are:\n";

	// --> --> options for MonoSkolem
	cout<<"\nUSE-INTERPOLANT-AS-SKOLEM-FUNCTION=<true/false>";
	cout<<"\t\tuse Craig interpolant as Skolem function in MonoSkolem (default is  false)"; 
	cout<<"\nSKOLEM-FUNCTION-TYPE-IN-MONOSKOLEM=<function type>";
	cout<<"\twhen USE-INTERPOLANT-AS-SKOLEM-FUNCTION=false, set function_type to";
	cout<<"\n\t\t\t\t\t\t\tcofactorone or cofactorone_or_negcofactorzero (default is cofactorone)\n";
		
		        
        // options for CSeqCeagr
	cout<<"\n\nOptions for CSeqCegar are:\n";

	cout<<"\nAPPLY-MONOSKOLEM-ON-SMALL-INSTANCES=<true/false>";
	cout<<"\tapply MonoSkolem on small problem instances inside CSeqCegar (default is false)"; 

	cout<<"\nTHRESHOLD-SIZE-MULT-TWO-POW-VARSTOELIM=<value>";
	cout<<"\t\tthreshold value of Tree-size of formula * 2^(number of varstoelim) beyond";
	cout<<"\n\t\t\t\t\t\t\twhich apply MonoSkolem on AND nodes (by default 8000)\n";

	cout << "\nGENERATE-ALL-COUNTEREXAMPLES-FROM-SAT-CALL=<true/false>";
	cout<<" generate all counterexamples from each sat call (default is false)";

	//cout << "\nAVOID-SAT-CALL-IN-FUNCTIONAL-FORMS=<true/false>";
	//cout<<"\t\treplace satisfiable sat call by simulation when the formula F(X,Y) is in a";
	//cout<<"\n\t\t\t\t\t\t\tfunctional form (by default false)";

	//cout << "\nNUMBER-OF-SIMULATIONS-BEFORE-SAT-CALL=<value>";
	//cout<<"\t\tnumber of unsat simulations before calling sat solver when";
	//cout<<"\n\t\t\t\t\t\t\tAVOID-SAT-CALL-IN-FUNCTIONAL-FORMS is true (by default 1)\n";

	cout<<"\nGRACEFUL-TIMEOUT=<time-out in seconds>";
	cout<<"\t\t\tafter graceful-timeout, CegarSkolem skips refinement loop and";
	cout<<"\n\t\t\t\t\t\t\treturns the initial r1/r0's (disabled by default)\n";

	//cout<<"\nAVOID-GRACEFUL-TIMEOUT-AT-TOPNODE=<true/false>";
	//cout<<"\t\tavoid graceful-timeout at top-node giving exact result (default is true)\n";


	// options for benchmark generation
	cout<<"\n\nOptions for benchmark_generation are:\n";

	cout<<"\nGENERATE-ARBITRARY-BOOLEAN-COMBINATIONS=<true/false>";
	cout<<"\tif true then generate benchmark as arbitrary boolean combination; if false then";
	cout<<"\n\t\t\t\t\t\t\tperform one level Tsietin encoding to flatten the boolean combination (default is false)\n";

	cout<<"\nGENERATE-SATISFIABLE-BENCHMARKS=<true/false>";
	cout<<"\t\tif GENERATE-ARBITRARY-BOOLEAN-COMBINATIONS=false, then disjoin additional formula";
	cout<<"\n\t\t\t\t\t\t\tto guarantee that the benchmark is satisfiable (default is false)\n";

	cout<<"\nEXISTENTIALLY-QUANTIFY-TSEITIN-VARIABLES=<true/false>";
	cout<<"\tif GENERATE-ARBITRARY-BOOLEAN-COMBINATIONS=false and GENERATE-SATISFIABLE-BENCHMARKS=false";
	cout<<"\n\t\t\t\t\t\t\tthen existentially quantify the one level Tseitin variables (by default false";
	cout<<"\n\t\t\t\t\t\t\t, i.e., Tseitin variables are universally quantified)\n";
		
	
	// options for graph decomposition
	cout<<"\n\nOptions for graph_decomposition are:\n";
	cout<<"\nCOMPONENT-GENERATION-STRATEGY=<strategy>";
	cout<<"\t\tuncovered_edge or preferred_edge (default is uncovered_edge)";

	cout<<"\nSKF-GEN-ALGORITHM-IN-COMPONENT-GENERATION=<algorithm>";
	cout<<"\tSkolem function generation algorithm to be used in graph decomposition";
	cout<<"\n\t\t\t\t\t\t\tCSeqCegar, CegarSkolem, or MonoSkolem (default is MonoSkolem)";
	cout<<"\n\t\t\t\t\t\t\tPlease set ORDER-OF-VARIABLE-ELIMINATION. Default value is 1 if not set\n";

	cout<<"\nGENERATE-SPECIFIC-COMPONENT=<true/false>";
	cout<<"\t\tgenerate a specific component (default is false, i.e., all components are generated)";

	cout<<"\nCOMPONENT-NUMBER-TO-BE-GENERATED=<number>";
	cout<<"\t\tnumber of the component to be generated if GENERATE-SPECIFIC-COMPONENT is true";

	cout<<"\nFAILURE-CONDITION-LOCATION=<number>";
	cout<<"\t\t\tindex of the output corresponding to observer in the .aig file when";
	cout<<"\n\t\t\t\t\t\t\tCOMPONENT-GENERATION-STRATEGY=preferred_edge (default is 0)";
	
	cout<<"\n\nAPPLY-GRACEFUL-TIMEOUT-IN-GRAPH-DECOMPOSITION=<true/false>";
	cout<<" apply graceful-timeout inside CSeqCegar when used in graph decomposition (default is false)";
	cout<<"\n\t\t\t\t\t\t\tPlease set GRACEFUL-TIMEOUT if this is set. Default value is 900 secs if not set\n";

        cout<<"\nAPPLY-FRAIGING-IN-GRAPH-DECOMPOSITION=<true/false>";
	cout<<"\tapply fraiging during graph decomposition (default is false)";

	cout<<"\nCONJOIN-NEG-FAIL-TO-GET-PREFERRED-EDGES=<true/false>";
	cout<<"\tif true, then ~Fail(X) & Fail(F(X,I)) is the preferred_edge function";
	cout<<"\n\t\t\t\t\t\t\tif false, then Fail(F(X,I)) is the preferred_edge function (default is true)";

	// other options
	cout<<"\n\nOther Options are:\n";

	cout<<"\nMASK-PRINTING-CEGAR-DETAILS=<true/false>";
	cout<<"\t\tmask printing to screen, the details of CEGAR in Skolem function generation (by default true)";

	cout<<"\nMASK-PRINTING-DETAILS-FILE=<true/false>";
	cout<<"\t\t\tmask printing to file, the details of CEGAR in Skolem function generation (by default true)";


	cout<<"\nNUMBER-OF-CLAUSES-PER-FACTOR-IN-QDIMACS-BENCHMARK=<number> number of clauses per factor in a qdimacs benchmark (default is 1)";

	//cout<<"\nLIMIT-ON-VARIABLES-TO-ELIMINATE=<number>";
	//cout<<"\t\tto limit the variables to be eliminated; give limit as % (default is";
	//cout<<"\n\t\t\t\t\t\t\t -1,i.e, no limit)\n";

	//cout<<"\nMAX-INDEX-TO-ELIMINATE=<number>";
	//cout<<"\t\t\t\tmaximum index of the variable up to which skolem function is to be ";
	//cout<<"\n\t\t\t\t\t\t\tcomputed (default is -1, i.e. disabled)\n";

	cout<<"\nPRINT-FACTOR-GRAPH=<true/false>";
	cout<<"\t\t\t\tto print the factor graph (by default false)";

	// for order finding
	//cout << "\nSET-MOST-SIGNIFICANT-WORD-TO-ZERO-IN-FACTORIZATION-BENCHMARKS=true/false: When benchmark type is factorization, set the most significant word of x and y in z=x.y as zeros (by default true)";
	// This option is of not much use
	
	cout<<"\nEXIT-AFTER-ORDER-FINDING=<true/false>";
	cout<<"\t\t\tto exit/continue after order finding (default is false)";
	cout<<"\nEXIT-AFTER-FACTOR-GRAPH-GENERATION=<true/false>";
	cout<<"\t\tto exit/continue after factor graph generation (default is false)";
	//cout<<"\nEXIT-AFTER-FINDING-ABSTRACT-SKOLEM-FUNCTIONS=<true/false>";
	//cout<<" to exit/continue after finding abstract Skolem functions (default is false)\n";

	//cout<<"\nFUNCTION=input file containing factor (useful when the individual factors are available)";
	//cout<<"\nFUNCTION-LIST=list of input files containing factors (useful when the individual factors are available)";
	//cout<<"\nVARIABLES-TO-ELIMINATE=file containing the list of variables to be eliminated (useful when the individual factors are available)";
	// These options are of not much use

	// --> --> options for applying Tsietin encoding internally before calling algorithms
	//cout<<"\nAPPLY-TSIETIN-ENCODING-ON-BENCHMARKS=<true/false>";
	//cout<<"\tto turn on/off application of Tsietin's encoding on benchmarks and then push the Tsietin";
	//cout<<"\n\t\t\t\t\t\t\tvariables up in the order (default is false)\n";//after reading benchmark

	//cout<<"\nOBTAIN-TSIETIN-VARIABLES-IN-BFS-ORDER=<true/false>";
	//cout<<"\tto turn on/off labeling nodes by Tsietin variables in BFS order (applicable only when";
	//cout<<"\n\t\t\t\t\t\t\tAPPLY-TSIETIN-ENCODING-ON-BENCHMARKS is true) (default is true)\n";

	//cout<<"\nTHRESHOLD-FOR-TSIETIN-ENCODING=<number>";
	//cout<<"\t\t\tthreshold size of dag below which the dag is considered as Tsietin variable";
	//cout<<"\n\t\t\t\t\t\t\t(default is -1, i.e. complete Tsietin encdoing)\n";

	//cout<<"\nAPPLY-TSIETIN-ENCODING-IN-GRAPH-DECOMPOSITION=<true/false>";
	//cout<<" to perform factorization before calling CegarSkolem inside graph decomposition (default is false)";//inside graph decomposition
	
	cout<<endl<<endl;
}


void setArgument(const string & name, const string &value)
{
    #ifdef DEBUG_SKOLEM
    cout << "name is " << name << ", value is " << value << endl;
    #endif

    if (name == "FUNCTION")
    {
        string factor_file_name = value;
	factor_file_names.insert(factor_file_name);
    }
    else if (name == "FUNCTION-LIST")
    {
        string factor_file_name_list = value;
	updateFactorFileNames(factor_file_name_list); 
    }
    else if (name == "VARIABLES-TO-ELIMINATE")
    {
        variables_to_eliminate_file_name = value;
    }    
    else if(name == "NODE-COMMAND")
    {
        nodeCommand = value;
    }
    else if(name == "BENCHMARK-TYPE")
    {
        benchmark_type = value;
    }
    else if(name == "VARIABLE-ORDER-FILE" || name == "ORDER-FILE")
    {
        variable_order_file_name = value;
    }
    else if(name == "SOLVER")
    {
	solver = value;
    }
    else if(name == "USE-INTERPOLANT-AS-SKOLEM-FUNCTION")
    {
	if(value == "true")
	{
		use_interpolant_as_skolem_function = true;
	}
	else if(value == "false")
	{
		use_interpolant_as_skolem_function = false;
	}
	else
	{
		cout << "Value of USE-INTERPOLANT-AS-SKOLEM-FUNCTION is "<< value << endl;
		assert(false && "Invalid Value");
	}
    }
    else if(name == "BENCHMARK-NAME")
    {
        benchmark_name = value;
	int index_of_dot = benchmark_name.find_last_of(".");
	assert(index_of_dot != string::npos);
	string extension = benchmark_name.substr(index_of_dot+1);	
	assert(extension == "aig" || extension == "v" || extension == "qdimacs");
	extension_of_benchmark = extension;
	benchmark_name_without_extension = benchmark_name.substr(0, index_of_dot); 
    }
    else if(name == "SKOLEM-FUNCTION-TYPE-IN-MONOSKOLEM")
    {
	skolem_function_type_in_jiang = value;
	assert(skolem_function_type_in_jiang == "cofactorone" || skolem_function_type_in_jiang == "cofactorone_or_negcofactorzero" );
    }
    else if(name == "PROBLEM-KIND")
    {
        problem_kind = value;
    }
   else if(name == "ACCUMULATE-FORMULAE-IN-CB0-IN-CEGAR")
    {
	if(value == "true")
	{
		accumulate_formulae_in_cbzero_in_cegar = true;
	}
	else if(value == "false")
	{
		accumulate_formulae_in_cbzero_in_cegar = false;
	}
	else
	{
		cout << "Value of ACCUMULATE-FORMULAE-IN-CB0-IN-CEGAR is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }
   else if(name == "USE-ASSUMPTIONS-IN-CEGAR")
    {
	if(value == "true")
	{
		use_assumptions_in_unified_cegar = true;
	}
	else if(value == "false")
	{
		use_assumptions_in_unified_cegar = false;
	}
	else
	{
		cout << "Value of USE-ASSUMPTIONS-IN-CEGAR is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }
   else if(name == "WRITE-COMPONENT-IN-FILE")
    {
	if(value == "true")
	{
		write_component_in_file = true;
	}
	else if(value == "false")
	{
		write_component_in_file = false;
	}
	else
	{
		cout << "Value of WRITE-COMPONENT-IN-FILE is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }
   else if(name == "WRITE-COMPONENT-AS-SEQUENTIAL-CIRCUIT")
    {
	if(value == "true")
	{
		write_component_as_sequential_circuit = true;
	}
	else if(value == "false")
	{
		write_component_as_sequential_circuit = false;
	}
	else
	{
		cout << "Value of WRITE-COMPONENT-AS-SEQUENTIAL-CIRCUIT is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }
   else if(name == "APPLY-TSIETIN-ENCODING-ON-BENCHMARKS")
    {
	if(value == "true")
	{
		apply_tsietin_encoding_on_benchmarks = true;
	}
	else if(value == "false")
	{
		apply_tsietin_encoding_on_benchmarks = false;
	}
	else
	{
		cout << "Value of APPLY-TSIETIN-ENCODING-ON-BENCHMARKS is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }
   else if(name == "OBTAIN-TSIETIN-VARIABLES-IN-BFS-ORDER")
    {
	if(value == "true")
	{
		obtain_tsietin_variables_in_bfs_order = true;
	}
	else if(value == "false")
	{
		obtain_tsietin_variables_in_bfs_order = false;
	}
	else
	{
		cout << "Value of OBTAIN-TSIETIN-VARIABLES-IN-BFS-ORDER is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }
   else if(name == "GENERATE-SPECIFIC-COMPONENT")
    {
	if(value == "true")
	{
		generate_specific_component = true;
	}
	else if(value == "false")
	{
		generate_specific_component = false;
	}
	else
	{
		cout << "Value of GENERATE-SPECIFIC-COMPONENT is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    } 
   else if(name == "APPLY-GRACEFUL-TIMEOUT-IN-GRAPH-DECOMPOSITION")
    {
	if(value == "true")
	{
		apply_global_time_outs_in_component_generation = true;
	}
	else if(value == "false")
	{
		apply_global_time_outs_in_component_generation = false;
	}
	else
	{
		cout << "Value of APPLY-GRACEFUL-TIMEOUT-IN-GRAPH-DECOMPOSITION is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    } 
   else if(name == "APPLY-FRAIGING-IN-GRAPH-DECOMPOSITION")
    {
	if(value == "true")
	{
		apply_fraiging_in_graph_decomposition = true;
	}
	else if(value == "false")
	{
		apply_fraiging_in_graph_decomposition = false;
	}
	else
	{
		cout << "Value of APPLY-FRAIGING-IN-GRAPH-DECOMPOSITION is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    } 
   else if(name == "CONJOIN-NEG-FAIL-TO-GET-PREFERRED-EDGES")
    {
	if(value == "true")
	{
		conjoin_negfail_with_failfxi_to_get_preferred_edges = true;
	}
	else if(value == "false")
	{
		conjoin_negfail_with_failfxi_to_get_preferred_edges = false;
	}
	else
	{
		cout << "Value of CONJOIN-NEG-FAIL-TO-GET-PREFERRED-EDGES is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    } 		
   else if(name == "PURIFY-FAILURE-CONDITION")
    {
	if(value == "true")
	{
		purify_failure_condition = true;
	}
	else if(value == "false")
	{
		purify_failure_condition = false;
	}
	else
	{
		cout << "Value of PURIFY-FAILURE-CONDITION is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }
   else if(name == "USE-UNCOVERED-EDGE-WITH-PREFERRED-EDGE")
    {
	if(value == "true")
	{
		use_uncovered_edge_with_preferred_edge = true;
	}
	else if(value == "false")
	{
		use_uncovered_edge_with_preferred_edge = false;
	}
	else
	{
		cout << "Value of USE-UNCOVERED-EDGE-WITH-PREFERRED-EDGE is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }	
   else if(name == "APPLY-TSIETIN-ENCODING-IN-GRAPH-DECOMPOSITION")
    {
	if(value == "true")
	{
		apply_tsietin_encoding_before_calling_cegarskolem_inside_graph_decomposition = true;
	}
	else if(value == "false")
	{
		apply_tsietin_encoding_before_calling_cegarskolem_inside_graph_decomposition = false;
	}
	else
	{
		cout << "Value of APPLY-TSIETIN-ENCODING-IN-GRAPH-DECOMPOSITION is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }	
   else if(name == "GENERATE-SATISFIABLE-BENCHMARKS")
    {
	if(value == "true")
	{
		generate_satisfiable_benchmarks = true;
	}
	else if(value == "false")
	{
		generate_satisfiable_benchmarks = false;
	}
	else
	{
		cout << "Value of GENERATE-SATISFIABLE-BENCHMARKS is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }  
  else if(name == "GENERATE-ARBITRARY-BOOLEAN-COMBINATIONS")
    {
	if(value == "true")
	{
		generate_benchmarks_for_arbitrary_boolean_combinations = true;
	}
	else if(value == "false")
	{
		generate_benchmarks_for_arbitrary_boolean_combinations = false;
	}
	else
	{
		cout << "Value of GENERATE-ARBITRARY-BOOLEAN-COMBINATIONS is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }
  else if(name == "USE-FOR-QBF-SATISFIABILITY")
    {
	if(value == "true")
	{
		use_for_qbf_satisfiability = true;
	}
	else if(value == "false")
	{
		use_for_qbf_satisfiability = false;
	}
	else
	{
		cout << "Value of USE-FOR-QBF-SATISFIABILITY is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }
  else if(name == "PERFORM-CEGAR-ON-ARBITRARY-BOOLEAN-FORMULAS")
    {
	if(value == "true")
	{
		perform_cegar_on_arbitrary_boolean_formulas = true;
	}
	else if(value == "false")
	{
		perform_cegar_on_arbitrary_boolean_formulas = false;
	}
	else
	{
		cout << "Value of PERFORM-CEGAR-ON-ARBITRARY-BOOLEAN-FORMULAS is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }  
  else if(name == "APPLY-MONOSKOLEM-ON-SMALL-INSTANCES")
    {
	if(value == "true")
	{
		choose_to_apply_monoskolem_on_smaller_problem_instances = true;
	}
	else if(value == "false")
	{
		choose_to_apply_monoskolem_on_smaller_problem_instances = false;
	}
	else
	{
		cout << "Value of APPLY-MONOSKOLEM-ON-SMALL-INSTANCES is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }
  else if(name == "MASK-PRINTING-CEGAR-DETAILS")
    {
	if(value == "true")
	{
		mask_printing_cegar_details = true;
	}
	else if(value == "false")
	{
		mask_printing_cegar_details = false;
	}
	else
	{
		cout << "Value of MASK-PRINTING-CEGAR-DETAILS is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }
   else if(name == "MASK-PRINTING-DETAILS-FILE")
    {
	if(value == "true")
	{
		mask_printing_details_file = true;
	}
	else if(value == "false")
	{
		mask_printing_details_file = false;
	}
	else
	{
		cout << "Value of MASK-PRINTING-DETAILS-FILE is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }
  else if(name == "GENERATE-ALL-COUNTEREXAMPLES-FROM-SAT-CALL")
    {
	if(value == "true")
	{
		generate_all_counterexamples_from_sat_call = true;
	}
	else if(value == "false")
	{
		generate_all_counterexamples_from_sat_call = false;
	}
	else
	{
		cout << "Value of GENERATE-ALL-COUNTEREXAMPLES-FROM-SAT-CALL is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }
   else if(name == "SET-MOST-SIGNIFICANT-WORD-TO-ZERO-IN-FACTORIZATION-BENCHMARKS")
    {
	if(value == "true")
	{
		set_most_significant_word_to_zero_in_factorization_benchmarks = true;
	}
	else if(value == "false")
	{
		set_most_significant_word_to_zero_in_factorization_benchmarks = false;
	}
	else
	{
		cout << "Value of SET-MOST-SIGNIFICANT-WORD-TO-ZERO-IN-FACTORIZATION-BENCHMARKS is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }
   else if(name == "CLEANUP-AFTER-EACH-STEP-IN-ARBITRARY-BOOLEAN-COMBINATIONS")
    {
	if(value == "true")
	{
		cleanup_after_each_step_in_arbitrary_boolean_combinations = true;
	}
	else if(value == "false")
	{
		cleanup_after_each_step_in_arbitrary_boolean_combinations = false;
	}
	else
	{
		cout << "Value of CLEANUP-AFTER-EACH-STEP-IN-ARBITRARY-BOOLEAN-COMBINATIONS is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }
   else if(name == "AVOID-SAT-CALL-IN-FUNCTIONAL-FORMS")
    {
	if(value == "true")
	{
		avoid_sat_call_in_functional_forms = true;
	}
	else if(value == "false")
	{
		avoid_sat_call_in_functional_forms = false;
	}
	else
	{
		cout << "Value of AVOID-SAT-CALL-IN-FUNCTIONAL-FORMS is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }
   else if(name == "EXISTENTIALLY-QUANTIFY-TSEITIN-VARIABLES")
    {
	if(value == "true")
	{
		existentially_quantify_tseitin_variables_in_benchmark_generation = true;
	}
	else if(value == "false")
	{
		existentially_quantify_tseitin_variables_in_benchmark_generation = false;
	}
	else
	{
		cout << "Value of EXISTENTIALLY-QUANTIFY-TSEITIN-VARIABLES is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }
   else if(name == "EXTEND-TSEITIN-ENCODING-TO-EXTRA-PART")
    {
	if(value == "true")
	{
		extend_tsietin_encoding_to_extra_part = true;
	}
	else if(value == "false")
	{
		extend_tsietin_encoding_to_extra_part = false;
	}
	else
	{
		cout << "Value of EXTEND-TSEITIN-ENCODING-TO-EXTRA-PART is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }	
   else if(name == "MAKE-INITIAL-VARIABLE-TO-SKOLEM-FUNCTION-MAP-ENTRIES-FORMULAE")
    {
	if(value == "true")
	{
		make_initial_variable_to_skolem_function_map_a_formula = true;
	}
	else if(value == "false")
	{
		make_initial_variable_to_skolem_function_map_a_formula = false;
	}
	else
	{
		cout << "Value of MAKE-INITIAL-VARIABLE-TO-SKOLEM-FUNCTION-MAP-ENTRIES-FORMULAE is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }	
   else if(name == "USE-BADS-IN-CEGAR")
    {
	if(value == "true")
	{
		use_bads_in_unified_cegar = true;
	}
	else if(value == "false")
	{
		use_bads_in_unified_cegar = false;
	}
	else
	{
		cout << "Value of USE-BADS-IN-CEGAR is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }
   else if(name == "USE-CBZERO-IN-CEGAR")
    {
	if(value == "true")
	{
		use_cbzero_in_unified_cegar = true;
	}
	else if(value == "false")
	{
		use_cbzero_in_unified_cegar = false;
	}
	else
	{
		cout << "Value of USE-CBZERO-IN-CEGAR is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    } 
   else if(name == "PERFORM-REVERSE-SUBSTITUTION")
    {
	if(value == "true")
	{
		perform_reverse_substitution = true;
	}
	else if(value == "false")
	{
		perform_reverse_substitution = false;
	}
	else
	{
		cout << "Value of PERFORM-REVERSE-SUBSTITUTION is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }
    else if(name == "PROVE-CORRECTNESS-OF-SKOLEM-FUNCTIONS-USING-QBF-SOLVING")
    {
	if(value == "true")
	{
		prove_correctness_of_skolem_functions_using_qbf_solving = true;
	}
	else if(value == "false")
	{
		prove_correctness_of_skolem_functions_using_qbf_solving = false;
	}
	else
	{
		cout << "Value of PROVE-CORRECTNESS-OF-SKOLEM-FUNCTIONS-USING-QBF-SOLVING is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }  
    else if(name == "PROVE-CORRECTNESS")
    {
	if(value == "true")
	{
		prove_correctness_of_skolem_functions = true;
	}
	else if(value == "false")
	{
		prove_correctness_of_skolem_functions = false;
	}
	else
	{
		cout << "Value of PROVE-CORRECTNESS-OF-SKOLEM-FUNCTIONS is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }  
    else if(name == "PROVE-CORRECTNESS-FOR-ARBITRARY-FORMULAE")
    {
	if(value == "true")
	{
		prove_correctness_of_skolem_functions_of_arbitrary_boolean_formula = true;
	}
	else if(value == "false")
	{
		prove_correctness_of_skolem_functions_of_arbitrary_boolean_formula = false;
	}
	else
	{
		cout << "Value of PROVE-CORRECTNESS-FOR-ARBITRARY-FORMULAE is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }
    else if(name == "PROVE-CORRECTNESS-OF-SKOLEM-FUNCTIONS-OF-ARBITRARY-BOOLEAN-FORMULA-DETAILED-CHECK")
    {
	if(value == "true")
	{
		prove_correctness_of_skolem_functions_of_arbitrary_boolean_formula_detailed_check = true;
	}
	else if(value == "false")
	{
		prove_correctness_of_skolem_functions_of_arbitrary_boolean_formula_detailed_check = false;
	}
	else
	{
		cout << "Value of PROVE-CORRECTNESS-OF-SKOLEM-FUNCTIONS-OF-ARBITRARY-BOOLEAN-FORMULA-DETAILED-CHECK is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }      
    else if(name == "PROVE-CORRECTNESS-FOR-CONJUNCTIONS")
    {
	if(value == "true")
	{
		prove_correctness_of_skolem_functions_of_conjunctions = true;
	}
	else if(value == "false")
	{
		prove_correctness_of_skolem_functions_of_conjunctions = false;
	}
	else
	{
		cout << "Value of PROVE-CORRECTNESS-FOR-CONJUNCTIONS is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    } 
   else if(name == "PRINT-FACTOR-GRAPH")
    {
	if(value == "true")
	{
		print_factor_graph = true;
	}
	else if(value == "false")
	{
		print_factor_graph = false;
	}
	else
	{
		cout << "Value of PRINT-FACTOR-GRAPH is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }
    else if(name == "EXIT-AFTER-ORDER-FINDING")
    {
	if(value == "true")
	{
		exit_after_order_finding = true;
	}
	else if(value == "false")
	{
		exit_after_order_finding = false;
	}
	else
	{
		cout << "Value of EXIT-AFTER-ORDER-FINDING is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }  
    else if(name == "EXIT-AFTER-FINDING-ABSTRACT-SKOLEM-FUNCTIONS")
    {
	if(value == "true")
	{
		exit_after_finding_abstract_skolem_functions = true;
	}
	else if(value == "false")
	{
		exit_after_finding_abstract_skolem_functions = false;
	}
	else
	{
		cout << "Value of EXIT-AFTER-FINDING-ABSTRACT-SKOLEM-FUNCTIONS is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }  
    else if(name == "EXIT-AFTER-FACTOR-GRAPH-GENERATION")
    {
	if(value == "true")
	{
		exit_after_factor_graph_generation = true;
	}
	else if(value == "false")
	{
		exit_after_factor_graph_generation = false;
	}
	else
	{
		cout << "Value of EXIT-AFTER-FACTOR-GRAPH-GENERATION is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    } 
    else if(name == "ENABLE-CEGAR")
    {
	if(value == "true")
	{
		enable_cegar = true;
	}
	else if(value == "false")
	{
		enable_cegar = false;
	}
	else
	{
		cout << "Value of ENABLE-CEGAR is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }     
 else if(name == "SELECT-CANNOT-BE-ELEMENTS-BASED-ON-SUPPORTS")
    {
	if(value == "true")
	{
		select_cannot_be_elements_based_on_supports = true;
	}
	else if(value == "false")
	{
		select_cannot_be_elements_based_on_supports = false;
	}
	else
	{
		cout << "Value of SELECT-CANNOT-BE-ELEMENTS-BASED-ON-SUPPORTS is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    } 
 else if(name == "REFINE-ALL-LOCATIONS-IN-CEGAR")
    {
	if(value == "true")
	{
		refine_all_locations_in_cegar = true;
	}
	else if(value == "false")
	{
		refine_all_locations_in_cegar = false;
	}
	else
	{
		cout << "Value of REFINE-ALL-LOCATIONS-IN-CEGAR is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    } 
 else if(name == "USE-INTERPOLANTS-IN-CEGAR")
    {
	if(value == "true")
	{
		use_interpolants_in_cegar = true;
	}
	else if(value == "false")
	{
		use_interpolants_in_cegar = false;
	}
	else
	{
		cout << "Value of USE-INTERPOLANTS-IN-CEGAR is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    } 
  else if(name == "USE-DONTCARE-OPTIMIZATION-IN-CEGAR")
    {
	if(value == "true")
	{
		use_dontcare_optimization_in_cegar = true;
	}
	else if(value == "false")
	{
		use_dontcare_optimization_in_cegar = false;
	}
	else
	{
		cout << "Value of USE-DONTCARE-OPTIMIZATION-IN-CEGAR is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }  
 else if(name == "USE-REFINEMENT-FROM-BOTTOM-IN-MU-BASED-SCHEME-WITH-OPTIMIZATIONS-IN-CEGAR")
    {
	if(value == "true")
	{
		use_refinement_from_bottom_in_mu_based_scheme_with_optimizations_in_cegar = true;
	}
	else if(value == "false")
	{
		use_refinement_from_bottom_in_mu_based_scheme_with_optimizations_in_cegar = false;
	}
	else
	{
		cout << "Value of USE-REFINEMENT-FROM-BOTTOM-IN-MU-BASED-SCHEME-WITH-OPTIMIZATIONS-IN-CEGAR is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }  
 else if(name == "USE-INCREMENTAL-SOLVING-FOR-GENERALIZATION-IN-MU-BASED-SCHEME-WITH-OPTIMIZATIONS-IN-CEGAR")
    {
	if(value == "true")
	{
		use_incremental_solving_for_generalization_in_mu_based_scheme_with_optimizations_in_cegar = true;
	}
	else if(value == "false")
	{
		use_incremental_solving_for_generalization_in_mu_based_scheme_with_optimizations_in_cegar = false;
	}
	else
	{
		cout << "Value of USE-INCREMENTAL-SOLVING-FOR-GENERALIZATION-IN-MU-BASED-SCHEME-WITH-OPTIMIZATIONS-IN-CEGAR is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }
    else if(name == "USE-BLOQQER")
    {
	if(value == "true")
	{
		use_bloqqer = true;
	}
	else if(value == "false")
	{
		use_bloqqer = false;
	}
	else
	{
		cout << "Value of USE-BLOQQER is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }  
    else if(name == "USE-RSYNTH")
    {
	if(value == "true")
	{
		use_rsynth = true;
	}
	else if(value == "false")
	{
		use_rsynth = false;
	}
	else
	{
		cout << "Value of USE-RSYNTH is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }
    else if(name == "INCLUDE-TSEITIN-VARIABLES-IN-RSYNTH-QDIMACS-GENERATION")
    {
	if(value == "true")
	{
		include_tsietin_variables_in_rsynth_qdimacs_generation = true;
	}
	else if(value == "false")
	{
		include_tsietin_variables_in_rsynth_qdimacs_generation = false;
	}
	else
	{
		cout << "Value of INCLUDE-TSEITIN-VARIABLES-IN-RSYNTH-QDIMACS-GENERATION is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }
    else if(name == "PERFORM-INTERRACTIVE-SOLVING-ON-ARBITRARY-BOOLEAN-FORMULAS")
    {
	if(value == "true")
	{
		perform_interractive_solving_on_arbitrary_boolean_formulas = true;
	}
	else if(value == "false")
	{
		perform_interractive_solving_on_arbitrary_boolean_formulas = false;
	}
	else
	{
		cout << "Value of PERFORM-INTERRACTIVE-SOLVING-ON-ARBITRARY-BOOLEAN-FORMULAS is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    }	  
    else if(name == "SKIP-SAT-CHECK-BEFORE-BLOQQER")
    {
	if(value == "true")
	{
		skip_satisfiability_check_before_bloqqer = true;
	}
	else if(value == "false")
	{
		skip_satisfiability_check_before_bloqqer = false;
	}
	else
	{
		cout << "Value of SKIP-SAT-CHECK-BEFORE-BLOQQER is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
    } 
    else if(name == "MAKE-VARIABLE-TO-SKOLEM-FUNCTION-MAP-COMPLEX")
    {
	if(value == "true")
	{
		make_variable_to_skolem_function_map_complex = true;
	}
	else if(value == "false")
	{
		make_variable_to_skolem_function_map_complex = false;
	}
	else
	{
		cout << "Value of MAKE-VARIABLE-TO-SKOLEM-FUNCTION-MAP-COMPLEX is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
	
    } 
    else if(name == "MAKE-ALTERNATE-ENTRIES-TOGGLE-IN-VARIABLE-TO-SKOLEM-FUNCTION-MAP")
    {
	if(value == "true")
	{
		 make_alternate_entries_toggle_in_initial_variable_to_skolem_function_map = true;
	}
	else if(value == "false")
	{
		 make_alternate_entries_toggle_in_initial_variable_to_skolem_function_map = false;
	}
	else
	{
		cout << "Value of MAKE-ALTERNATE-ENTRIES-TOGGLE-IN-VARIABLE-TO-SKOLEM-FUNCTION-MAP is "<< value << endl;
		assert(false && "Invalid Value");
	}	        
	
    } 
    else if(name == "TIMEOUT")
    {
	time_out = atoi(value.c_str());
	time_out_enabled = true;
	time_out_start = 0;
	timed_out = false;
    }  
    else if(name == "GRACEFUL-TIMEOUT")
    {
	cluster_global_time_out = atoi(value.c_str());
	cluster_global_time_out_enabled = true;
	cluster_global_time_out_start = 0;
	cluster_global_timed_out = false;
    } 
    else if(name == "AVOID-GRACEFUL-TIMEOUT-AT-TOPNODE")
    {
	if(value == "true")
	{
		 avoid_cluster_global_time_out_at_top_node = true;
	}
	else if(value == "false")
	{
		 avoid_cluster_global_time_out_at_top_node = false;
	}
	else
	{
		cout << "Value of AVOID-GRACEFUL-TIMEOUT-AT-TOPNODE is "<< value << endl;
		assert(false && "Invalid Value");
	}
    }   
    else if(name == "MEMORYOUT")
    {
	memory_out = atoi(value.c_str());
	long long int memory_out_in_bytes = memory_out * 1024;
	memory_out_in_bytes = memory_out_in_bytes * 1024;
	memory_out_in_bytes = memory_out_in_bytes * 1024;

	//printf("\nmemory_out_in_bytes is: %lld\n", memory_out_in_bytes);

	struct rlimit rl;
	rl.rlim_cur = memory_out_in_bytes;
	setrlimit(RLIMIT_AS, &rl);

	getrlimit(RLIMIT_AS, &rl);
	//printf("\nMaximum memory is: %lld\n", (long long int)rl.rlim_cur);
    }   
    else if(name == "LIMIT-ON-NUMBER-OF-EXTRA-CONJUNCTS")
    {
	limit_on_number_of_extra_conjuncts = atoi(value.c_str());
    }  
    else if(name == "NUMBER-OF-CLAUSES-PER-FACTOR-IN-QDIMACS-BENCHMARK")
    {
	number_of_clauses_per_factor_in_qdimacs_benchmark = atoi(value.c_str());
    }  
    else if(name == "FAILURE-CONDITION-LOCATION")
    {
	failure_condition_location = atoi(value.c_str());
    }
    else if(name == "ORDER-OF-VARIABLE-ELIMINATION" || name == "ORDER")
    {
	order_of_elimination_of_variables = atoi(value.c_str());
	assert(order_of_elimination_of_variables >= 0 && order_of_elimination_of_variables <= 7);
    } 
    else if(name == "REFINEMENT-STRATEGY")
    {
	refinement_strategy = atoi(value.c_str());
	assert(refinement_strategy >= 0 && refinement_strategy <= 1);
    }   
    else if(name == "LIMIT-ON-VARIABLES-TO-ELIMINATE")
    {
	limit_on_variables_to_eliminate = atoi(value.c_str());
    } 	
    else if(name == "COMPONENT-NUMBER-TO-BE-GENERATED")
    {
	component_number_to_be_generated = atoi(value.c_str());
    } 
    else if(name == "THRESHOLD-FOR-TSIETIN-ENCODING")
    {
	threshold_for_tsietin_encoding = atof(value.c_str());
    }  	
    else if(name == "MACHINE")
    {
	machine = value;
	assert(machine != "");
    }
    else if(name == "QBF-SOLVER-TO-USE")
    {
	qbf_solver_to_use = value;
    }
    else if(name == "MAX-INDEX-TO-ELIMINATE")
    {
	maximum_index_to_eliminate = atoi(value.c_str());
    }
    else if(name == "COMPONENT-GENERATION-STRATEGY")
    {
	component_generation_strategy = value;
	assert( component_generation_strategy == "uncovered_edge" || component_generation_strategy == "preferred_edge" );
    }
    else if(name == "FUNCTION-TO-MAKE-VARIABLE-TO-SKOLEM-FUNCTION-MAP-COMPLEX")
    {
	function_to_make_variable_to_skolem_function_map_complex = value;
	assert( function_to_make_variable_to_skolem_function_map_complex == "fi" || function_to_make_variable_to_skolem_function_map_complex == "F" );	
    }
    else if(name == "THRESHOLD-SIZE-MULT-TWO-POW-VARSTOELIM")
    {
	threshold_size_mult_two_pow_varstoelim_to_apply_monoskolem = atoi(value.c_str());
    }
    else if(name == "NUMBER-OF-SIMULATIONS-BEFORE-SAT-CALL")
    {
	number_of_simulations_before_sat_call_in_functional_forms = atoi(value.c_str());
    }
    else if(name == "SKF-GEN-ALGORITHM" || name == "SKF-GEN-ALGORITHM-IN-COMPONENT-GENERATION" || name == "ALGORITHM")
    {
	skf_gen_algorithm = value;
	if(skf_gen_algorithm == "CSeqCegar")
	{
		perform_cegar_on_arbitrary_boolean_formulas = true;
	}
	else if(skf_gen_algorithm == "Solving")
	{
		perform_cegar_on_arbitrary_boolean_formulas = false;
		perform_interractive_solving_on_arbitrary_boolean_formulas = true;
	}
	else if(skf_gen_algorithm == "Bloqqer")
	{
		perform_cegar_on_arbitrary_boolean_formulas = false;
		perform_interractive_solving_on_arbitrary_boolean_formulas = false;
		use_bloqqer = true;
	}
	else if(skf_gen_algorithm == "Rsynth")
	{
		perform_cegar_on_arbitrary_boolean_formulas = false;
		perform_interractive_solving_on_arbitrary_boolean_formulas = false;
		use_bloqqer = false;
		use_rsynth = true;
	}
	else if(skf_gen_algorithm == "CegarSkolem")
	{
		perform_cegar_on_arbitrary_boolean_formulas = false;
		perform_interractive_solving_on_arbitrary_boolean_formulas = false;
		use_bloqqer = false;
		use_rsynth = false;
		enable_cegar = true;
	}
	else if(skf_gen_algorithm == "MonoSkolem")
	{
		perform_cegar_on_arbitrary_boolean_formulas = false;
		perform_interractive_solving_on_arbitrary_boolean_formulas = false;
		use_bloqqer = false;
		use_rsynth = false;
		enable_cegar = false;
	}
	else
	{
		cout << "Unknown Skolem function generation algorithm "<< skf_gen_algorithm << endl;
		assert(false);
	}
    }
    else
    {
        cout << "Option name is " << name << "::" << value << endl;
        assert(false && "Invalid Option");
    }
}


void obtainVariablesToEliminate(list<string> &VariablesToEliminate)
{
	ifstream *varstoelim_file = new ifstream();
	assert(varstoelim_file != NULL);

  	varstoelim_file->open(variables_to_eliminate_file_name.c_str()); 
	assert(varstoelim_file->is_open());

	// Let us read the varstoelim_file
	while(!varstoelim_file->eof()) //read until end of file
    	{
		string word;
      		*varstoelim_file >> word;
      		
      		if(word == "")
		{
			break;	
		}
		
		VariablesToEliminate.push_back(word);		
	}// while ends here
	varstoelim_file->close();
}



void updateFactorFileNames(string &factor_file_name_list)
{
	ifstream *factor_file_name_list_file = new ifstream();
	assert(factor_file_name_list_file != NULL);

  	factor_file_name_list_file->open(factor_file_name_list.c_str()); 
	assert(factor_file_name_list_file->is_open());

	// Let us read the factor_file_name_list_file
	while(!factor_file_name_list_file->eof()) //read until end of file
    	{
		string word;
      		*factor_file_name_list_file >> word;
      		
      		if(word == "")
		{
			break;	
		}
		
		factor_file_names.insert(word);	
	}// while ends here
	factor_file_name_list_file->close();	
}



void writeFormulaToFile(ABC* abcObj, Abc_Frame_t* abcFrame, Abc_Ntk_t* formula, string outfile)
{
	Abc_FrameSetCurrentNetwork(abcFrame, Abc_NtkDup(formula));
	string command = "write " + outfile;
	if (abcObj->comExecute(abcFrame, command))
    	{
        	cout << "cannot execute command " << command << endl;
        	assert(false);
	}
}




void insertIntoOneDimensionalMatrix(map<int, int> &Matrix, int rows, int location, int entry, bool delete_existing)
{
	// simple sanity checks
	assert(location >= 1 && location <= rows);
	
	// check if entry already exists at location
	map<int, int>::iterator matrix_it = Matrix.find(location);
	if(matrix_it != Matrix.end())
	{
		if(delete_existing) // existing entry is no more needed
		{
			Matrix[location] = entry;
		}
		else
		{
			cout << "Error in insertIntoOneDimensionalMatrix in helper.cpp! Entry already exists in matrix at " << location << endl;
			assert(false);
		}
	}
	else
	{
		Matrix.insert(make_pair(location, entry)); 
	}
}


int searchOneDimensionalMatrix(map<int, int> &Matrix, int rows, int location)
{
	// simple sanity checks
	assert(location >= 1 && location <= rows);
	
	// check if entry exists at location
	map<int, int>::iterator matrix_it = Matrix.find(location);
	if(matrix_it == Matrix.end())
	{
		return -1;
	}
	else
	{
		return matrix_it->second;
	}
}




void insertIntoVarNameToVarIndexMap(map<string, int> &var_name_to_var_index_map, string &var_name, int var_index)
{
	assert(var_index >= 1);

	// check if entry already exists
	map<string, int>::iterator map_it = var_name_to_var_index_map.find(var_name);
	if(map_it != var_name_to_var_index_map.end())
	{
		cout << "Error in insertIntoVarNameToVarIndexMap in helper.cpp! Entry already exists for " << var_name << endl;
		assert(false);
	}
	
	var_name_to_var_index_map.insert(make_pair(var_name, var_index)); 
}


int searchVarNameToVarIndexMap(map<string, int> &var_name_to_var_index_map, string &var_name)
{
	map<string, int>::iterator map_it = var_name_to_var_index_map.find(var_name);
	if(map_it == var_name_to_var_index_map.end()) // This happens if the variable is not to be eliminated
	{
		return -1;
	}
	else
	{
		int var_index = map_it->second;
		assert(var_index >= 1);
		return var_index; 
	}
}


void insertIntoVarIndexToVarNameMap(map<int, string> &var_index_to_var_name_map, int var_index, string &var_name)
{
	assert(var_index >= 1);

	// check if entry already exists
	map<int, string>::iterator map_it = var_index_to_var_name_map.find(var_index);
	if(map_it != var_index_to_var_name_map.end())
	{
		cout << "Error in insertIntoVarIndexToVarNameMap in helper.cpp! Entry already exists for " << var_index << endl;
		assert(false);
	}
	
	var_index_to_var_name_map.insert(make_pair(var_index, var_name)); 
}


string searchVarIndexToVarNameMap(map<int, string> &var_index_to_var_name_map, int var_index)
{
	assert(var_index >= 1);
	map<int, string>::iterator map_it = var_index_to_var_name_map.find(var_index);
	assert(map_it != var_index_to_var_name_map.end());
	string var_name = map_it->second;
	return var_name; 
}


void showSet(set<string> &string_set, string who_am_i)
{
	cout << endl << endl << who_am_i << endl << endl;

	for(set<string>::iterator string_it = string_set.begin(); string_it != string_set.end(); string_it++)
	{
		cout << *string_it << ", ";
	}

	cout << endl;
}


void showSet(set<int> &integer_set, string who_am_i)
{
	cout << endl << endl << who_am_i << endl << endl;

	for(set<int>::iterator integer_it = integer_set.begin(); integer_it != integer_set.end(); integer_it++)
	{
		cout << *integer_it << ", ";
	}

	cout << endl;
}



void printSet(set<string> &string_set, string who_am_i, FILE* fptr)
{
	fprintf(fptr, "\n%s\n", who_am_i.c_str()); 

	for(set<string>::iterator string_it = string_set.begin(); string_it != string_set.end(); string_it++)
	{
		fprintf(fptr, "%s, ", (*string_it).c_str());
	}	 	
}



bool checkTimeOut()
{
	if(!time_out_enabled) // time_out mode is disabled
	{
		return false;
	}

	if(timed_out) // already timed out. No need to check
	{
		return true;
	}

	assert(time_out_start != 0);

	time_t present_time, duration;
	time(&present_time);
	duration = present_time - time_out_start;
	if(duration >= time_out)
	{
		return true;
	}
	else
	{
		return false;
	}
}



void printList(list<string> &string_list, FILE* fptr)
{
	for(list<string>::iterator string_it = string_list.begin(); string_it != string_list.end(); string_it++)
	{
		fprintf(fptr, "%s\n", (*string_it).c_str());
	}	 	
}

void showSet(set<string> &string_set)
{
	for(set<string>::iterator string_it = string_set.begin(); string_it != string_set.end(); string_it++)
	{
		cout << *string_it << ", ";
	}
}


void showSet(set<int> &integer_set)
{
	for(set<int>::iterator integer_it = integer_set.begin(); integer_it != integer_set.end(); integer_it++)
	{
		cout << *integer_it << ", ";
	}
}

void showList(list<string> &string_list)
{
	for(list<string>::iterator string_it = string_list.begin(); string_it != string_list.end(); string_it++)
	{
		cout << *string_it << ", ";
	}	 	
}


void obtainOrderOfVariableEliminationFromFile(list<string> &OrderOfVariableEliminationFromFile)
{
	ifstream *variable_file = new ifstream();
	assert(variable_order_file_name != "");
  	variable_file->open(variable_order_file_name.c_str()); // open the variable_file
	assert(variable_file->is_open());

	// Let us read the variable_file
	while(!variable_file->eof()) //read until end of file
    	{
		string word;
      		*variable_file>>word;
      		
      		if(word == "")
		{
			break;	
		}
		//cout<<"Line read is "<<word<<endl;
		OrderOfVariableEliminationFromFile.push_back(word);
	}
	variable_file->close();
}



void obtainFactorsAndVariablesToEliminatFromHWMCCFile(ABC* abcObj, Abc_Frame_t* abcFrame, set<Aig_Obj_t*> &Factors, list<string> &VariablesToEliminate, Aig_Man_t* &aig_manager)
{
	assert(benchmark_name != "");

	string command = "read " + benchmark_name + ";" + initCommand;

	#ifdef DEBUG_SKOLEM
	cout << command << endl;
	#endif

	if (abcObj->comExecute(abcFrame, command))
    	{
	 	cout << "cannot execute " << command << endl;
		assert(false);
	}

	#ifdef DEBUG_SKOLEM //Printing original circuit
	command = "write ckt.v;";
	cout << command << endl;
		
	if (abcObj->comExecute(abcFrame, command))
	{
		cout << "cannot execute command " << command << endl;
		assert(false);
	}
	#endif	
	
	//ofstream cktInfo("cktInfo");
	//int pis = Abc_NtkPiNum(abcFrame->pNtkCur);
    	//cktInfo << "Inputs:" << pis << endl;
    	//int states = Abc_NtkLatchNum(abcFrame->pNtkCur);
    	//cktInfo << "Latches:" << states << endl;    

	#ifdef DEBUG_SKOLEM
	cout << "Changing names and removing POs" << endl;
	#endif

	changeNamesAndRemovePos(abcFrame->pNtkCur, PREFPREFIX, 1);


	#ifdef DEBUG_SKOLEM //Printing po-deleted and pi-renamed circuit
	command = "write ckt_after_po_deletion_pi_renaming.v;";
	cout << command << endl;
		
	if (abcObj->comExecute(abcFrame, command))
	{
		cout << "cannot execute command " << command << endl;
		assert(false);
	}
	#endif	

    	command = ";comb";

	#ifdef DEBUG_SKOLEM
	cout << command << endl;
	#endif
	if (abcObj->comExecute(abcFrame, command))
    	{
		cout << "cannot execute " << command << endl;
		assert(false);
	}   

	#ifdef DEBUG_SKOLEM //Printing circuit after comb
	command = "write comb_ckt.v;";
	cout << command << endl;
		
	if (abcObj->comExecute(abcFrame, command))
	{
		cout << "cannot execute command " << command << endl;
		assert(false);
	}
	#endif	 		

	#ifdef DEBUG_SKOLEM	
	cout << "Renaming latches" << endl;
	#endif

	string lastLatch = renameLatches(abcFrame->pNtkCur);

	#ifdef DEBUG_SKOLEM //Printing latch-renamed  circuit 
	command = "write comb_ckt_after_latch_renaming.v;";
	cout << command << endl;
		
	if (abcObj->comExecute(abcFrame, command))
	{
		cout << "cannot execute command " << command << endl;
		assert(false);
	}
	#endif	 

	command = "fraig;write F.aig;";		

	#ifdef DEBUG_SKOLEM
	cout << command << endl;
	#endif

	if (abcObj->comExecute(abcFrame, command))
	{
	 	cout << "cannot execute " << command << endl;
		assert(false);
	}

	#ifdef PRINT_SKOLEM_FUNCTIONS
	//Printing original transition function
	command = "write ";
	command += benchmark_name_without_extension;
	command += "_transition_function.v;";
	cout << command << endl;
		
	if (abcObj->comExecute(abcFrame, command))
	{
		cout << "cannot execute command " << command << endl;
		assert(false);
	}
	#endif	

	Abc_Ntk_t* transition_function = abcFrame->pNtkCur;
	transition_function = Abc_NtkDup(transition_function);


	// Let's find VariablesToEliminate now

	Abc_Obj_t* tempInputObj;
	int j = 0;
	set<string> input_names;
	Abc_NtkForEachPi(transition_function, tempInputObj, j)
	{
		string input_name = Abc_ObjName(tempInputObj);
		if(input_name[0] == 'z' && input_name[1] == 'z' && input_name[2] == 'p')
		{  
			input_names.insert(input_name);
		}			
	} 

	for(set<string>::iterator input_it = input_names.begin(); input_it != input_names.end(); input_it++)
	{
		VariablesToEliminate.push_back(*input_it);
	}

	// Let's get all the variable names and
	// Ci_name_to_Ci_number_map
	j = 0;
	vector<string> variable_names;
	Abc_NtkForEachCi(transition_function, tempInputObj, j)
	{
		string variable_name = Abc_ObjName(tempInputObj);
		variable_names.push_back(variable_name);

		Ci_name_to_Ci_number_map.insert(make_pair(variable_name, j));

		number_of_Cis++;				
	} 

	//if(to include POs in transition relation)
	//start here
	Abc_Obj_t* tempOutputObj;
	int k = 0;
	vector<string> output_names;
	Abc_NtkForEachPo(transition_function, tempOutputObj, k)
	{
		string variable_name = Abc_ObjName(tempOutputObj);
		variable_names.push_back(variable_name);
		output_names.push_back(variable_name);

		Ci_name_to_Ci_number_map.insert(make_pair(variable_name, j));	
					
		j++;

		number_of_Cis++;
	} 
	//end here

	// Let's split the transition_function into factors

	aig_manager = Abc_NtkToDar(transition_function, 0, 0);
	// transition function converted to aig_manager	

	// reading the factors
	Aig_Obj_t* factorObj;
    	int i = 0;

	Aig_ManForEachPoSeq(aig_manager, factorObj, i )
    	{
		assert(factorObj != NULL);

		Aig_Obj_t* Fanin0_factorObj = Aig_ObjChild0(factorObj);		 
		// Note that it is important to use Aig_ObjChild0 here
		// Earlier Aig_ObjFanin0 was used; but Aig_ObjFanin0 regularizes the dag,
		// Aig_ObjChild0 does not regularize the dag		

		assert(Fanin0_factorObj != NULL);

		//if(to include POs in transition relation)
		//start here
		Aig_Obj_t* output_obj = Aig_ObjCreateCi(aig_manager);
		Aig_Obj_t* Factor = createEquivalence(output_obj, Fanin0_factorObj, aig_manager);
		Factors.insert(Factor);
		// Let's add output_name as a new CI
		//otherwise
		//Factors.insert(Fanin0_factorObj);
    	}

	// Let's get the IDs of the variables

	vector<int> variable_ids;
	i = 0;
	Aig_ManForEachCi(aig_manager, factorObj, i )
	{
		int Id = Aig_ObjId(factorObj); // no need to apply Aig_Regular() as factorObj is CI
		variable_ids.push_back(Id);

		string variable_name = 	variable_names[i];	
		if(input_names.find(variable_name) != input_names.end())
		// variable_name is an input; it is a Ci to be eliminated
		{
			Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.insert(make_pair(variable_name, factorObj));
		}

		Ci_name_to_Ci_object_map.insert(make_pair(variable_name, factorObj));
		
	}

	// Let's create the variable_id ---> variable_name map

	assert(variable_ids.size() == variable_names.size());	
	for(int i = 0; i < variable_ids.size(); i++)
	{
		Ci_id_to_Ci_name_map.insert(make_pair(variable_ids[i], variable_names[i]));
	}

	command = "rm F.aig";
	system(command.c_str());
}



void insertIntoOneDimensionalMatrix(map<int, Aig_Obj_t*> &Matrix, int rows, int location, Aig_Obj_t* entry, bool delete_existing)
{
	// simple sanity checks
	assert(location >= 1 && location <= rows);
	assert(entry != NULL);
	
	// check if entry already exists at location
	map<int, Aig_Obj_t*>::iterator matrix_it = Matrix.find(location);
	if(matrix_it != Matrix.end())
	{
		if(delete_existing) // existing entry is no more needed
		{
			Matrix[location] = entry;
		}
		else
		{
			cout << "Error in insertIntoOneDimensionalMatrix in helper.cpp! Entry already exists in matrix at " << location << endl;
			assert(false);
		}
	}
	else
	{
		Matrix.insert(make_pair(location, entry)); 
	}
}



Aig_Obj_t* searchOneDimensionalMatrix(map<int, Aig_Obj_t*> &Matrix, int rows, int location)
{
	// simple sanity checks
	assert(location >= 1 && location <= rows);
	
	// check if entry exists at location
	map<int, Aig_Obj_t*>::iterator matrix_it = Matrix.find(location);
	if(matrix_it == Matrix.end())
	{
		return NULL;
	}
	else
	{
		Aig_Obj_t* entry = matrix_it->second;
		assert(entry != NULL);
		return entry; 
	}
}


void writeFormulaToFile(Aig_Man_t* aig_manager, Aig_Obj_t* formula, string outfile)
{
	assert(formula != NULL);
	
	FILE* fp = fopen(outfile.c_str(), "w+");
	assert(fp != NULL);

	// Unable to find a function which does dag printing in ABC
        // The function call Aig_ObjPrintVerilog seg. faults
	//Vec_Vec_t * vLevels = NULL;
	//int Level = 0;
	//Aig_ObjPrintVerilog( fp, formula, vLevels, Level);

	bool use_dag_based_printing = true;
	if(use_dag_based_printing)
	{
		writeFormulaToFile(aig_manager, formula, fp);
	}
	else
	{

		if(Aig_IsComplement(formula))
		{
			formula = Aig_Regular(formula);

			if(formula == createTrue(aig_manager))
			{
				fprintf(fp, "\n%s: false\n", outfile.c_str());
			}
			else
			{
				fprintf(fp, "\n%s: ~%d\n", outfile.c_str(), Aig_ObjId(formula));
			}
		}
		else
		{
			if(formula == createTrue(aig_manager))
			{
				fprintf(fp, "\n%s: true\n", outfile.c_str());
			}
			else
			{
				fprintf(fp, "\n%s: %d\n", outfile.c_str(), Aig_ObjId(formula));
			}
		
		}
	}

	fclose(fp);
}


void writeFormulaToFile(Aig_Man_t* aig_manager, Aig_Obj_t* formula, string type_of_formula, string file_type, int row_index, int column_index)
{
	assert(formula != NULL);

	string outfile = type_of_formula;

	char i_char[10];
	char j_char[10];	
	sprintf(i_char, "%d", row_index);
	sprintf(j_char, "%d", column_index);			

	string i_string(i_char);
	string j_string(j_char);

	outfile += "_";
	outfile += i_string;
	outfile += "_";
	outfile += j_string;
	outfile += file_type;

	FILE* fp = fopen(outfile.c_str(), "w+");
	assert(fp != NULL);

	bool use_dag_based_printing = true;
	if(use_dag_based_printing)
	{
		writeFormulaToFile(aig_manager, formula, fp);	
	}
	else
	{
	
		if(Aig_IsComplement(formula))
		{
			formula = Aig_Regular(formula);

			if(formula == createTrue(aig_manager))
			{
				fprintf(fp, "\n%s: false\n", outfile.c_str());
			}
			else
			{
				fprintf(fp, "\n%s: ~%d\n", outfile.c_str(), Aig_ObjId(formula));
			}
		}
		else
		{
			if(formula == createTrue(aig_manager))
			{
				fprintf(fp, "\n%s: true\n", outfile.c_str());
			}
			else
			{
				fprintf(fp, "\n%s: %d\n", outfile.c_str(), Aig_ObjId(formula));
			}
		
		}
	}
	
	fclose(fp);
}



Aig_Obj_t* createNot(Aig_Obj_t* child, Aig_Man_t* aig_manager)
{
	number_of_boolean_operations_for_variable++;	
	unsigned long long int step_ms;
	struct timeval step_start_ms, step_finish_ms;
	gettimeofday (&step_start_ms, NULL); 	

	assert(child != NULL);
	Aig_Obj_t* ret_expression = Aig_Not(child);
	assert(ret_expression != NULL);
	
	gettimeofday (&step_finish_ms, NULL);
   	step_ms = step_finish_ms.tv_sec * 1000 + step_finish_ms.tv_usec / 1000;
   	step_ms -= step_start_ms.tv_sec * 1000 + step_start_ms.tv_usec / 1000;
	BooleanOpTime += step_ms;

	return ret_expression;
}


Aig_Obj_t* createOr(set<Aig_Obj_t*> &Circuits, Aig_Man_t* aig_manager)
{
	int number_of_circuits = Circuits.size();
	assert(number_of_circuits > 0);
	
	number_of_boolean_operations_for_variable = number_of_boolean_operations_for_variable + number_of_circuits - 1;	
	unsigned long long int step_ms;
	struct timeval step_start_ms, step_finish_ms;
	gettimeofday (&step_start_ms, NULL); 	
	
	Aig_Obj_t* result;
	
	if(number_of_circuits == 1)
	{
		set<Aig_Obj_t*>::iterator circuit_it = Circuits.begin();

		result = *circuit_it;		
		assert(result != NULL);		
	}
	else if(number_of_circuits == 2)
	{
		set<Aig_Obj_t*>::iterator circuit_it = Circuits.begin();
		Aig_Obj_t* Circuit1 = *circuit_it;
		circuit_it++;
		Aig_Obj_t* Circuit2 = *circuit_it;
		assert(Circuit1 != NULL);
		assert(Circuit2 != NULL);		

		result = Aig_Or(aig_manager, Circuit1, Circuit2);
		assert(result != NULL);
	}
	else
	{
		set<Aig_Obj_t*>::iterator circuit_it = Circuits.begin();
		Aig_Obj_t* Circuit1 = *circuit_it;
		circuit_it++;
		Aig_Obj_t* Circuit2 = *circuit_it;		
		assert(Circuit1 != NULL);
		assert(Circuit2 != NULL);

		result = Aig_Or(aig_manager, Circuit1, Circuit2);

		circuit_it++;
		for(; circuit_it != Circuits.end(); circuit_it++)
		{
			Aig_Obj_t* Circuiti = *circuit_it;
			assert(Circuiti != NULL);
			assert(result != NULL);

			result = Aig_Or(aig_manager, result, Circuiti);	
		}
		assert(result != NULL);		
	}

	gettimeofday (&step_finish_ms, NULL);
   	step_ms = step_finish_ms.tv_sec * 1000 + step_finish_ms.tv_usec / 1000;
   	step_ms -= step_start_ms.tv_sec * 1000 + step_start_ms.tv_usec / 1000;
	BooleanOpTime += step_ms;

	return result;
}


Aig_Obj_t* createOr(Aig_Obj_t* child1, Aig_Obj_t* child2, Aig_Man_t* aig_manager)
{
	number_of_boolean_operations_for_variable++;
	unsigned long long int step_ms;
	struct timeval step_start_ms, step_finish_ms;
	gettimeofday (&step_start_ms, NULL); 	

	assert(child1 != NULL);
	assert(child2 != NULL);
	Aig_Obj_t* ret_expression = Aig_Or(aig_manager, child1, child2);
	assert(ret_expression != NULL);

	gettimeofday (&step_finish_ms, NULL);
   	step_ms = step_finish_ms.tv_sec * 1000 + step_finish_ms.tv_usec / 1000;
   	step_ms -= step_start_ms.tv_sec * 1000 + step_start_ms.tv_usec / 1000;
	BooleanOpTime += step_ms;

	return ret_expression;	
}



Aig_Obj_t* createAnd(set<Aig_Obj_t*> &Circuits, Aig_Man_t* aig_manager)
{
	int number_of_circuits = Circuits.size();
	assert(number_of_circuits > 0);

	number_of_boolean_operations_for_variable = number_of_boolean_operations_for_variable + number_of_circuits - 1;	
	unsigned long long int step_ms;
	struct timeval step_start_ms, step_finish_ms;
	gettimeofday (&step_start_ms, NULL); 	

	Aig_Obj_t* result;

	if(number_of_circuits == 1)
	{
		set<Aig_Obj_t*>::iterator circuit_it = Circuits.begin();

		result = *circuit_it;		
		assert(result != NULL);
	}
	else if(number_of_circuits == 2)
	{
		set<Aig_Obj_t*>::iterator circuit_it = Circuits.begin();
		Aig_Obj_t* Circuit1 = *circuit_it;
		circuit_it++;
		Aig_Obj_t* Circuit2 = *circuit_it;
		assert(Circuit1 != NULL);
		assert(Circuit2 != NULL);		

		result = Aig_And(aig_manager, Circuit1, Circuit2);
		assert(result != NULL);
	}
	else
	{
		set<Aig_Obj_t*>::iterator circuit_it = Circuits.begin();
		Aig_Obj_t* Circuit1 = *circuit_it;
		circuit_it++;
		Aig_Obj_t* Circuit2 = *circuit_it;		
		assert(Circuit1 != NULL);
		assert(Circuit2 != NULL);

		result = Aig_And(aig_manager, Circuit1, Circuit2);

		circuit_it++;
		for(; circuit_it != Circuits.end(); circuit_it++)
		{
			Aig_Obj_t* Circuiti = *circuit_it;
			assert(Circuiti != NULL);
			assert(result != NULL);

			result = Aig_And(aig_manager, result, Circuiti);	
		}
		assert(result != NULL);
	}

	gettimeofday (&step_finish_ms, NULL);
   	step_ms = step_finish_ms.tv_sec * 1000 + step_finish_ms.tv_usec / 1000;
   	step_ms -= step_start_ms.tv_sec * 1000 + step_start_ms.tv_usec / 1000;
	BooleanOpTime += step_ms;

	return result;
}


Aig_Obj_t* createAnd(Aig_Obj_t* child1, Aig_Obj_t* child2, Aig_Man_t* aig_manager)
{
	number_of_boolean_operations_for_variable++;	
	unsigned long long int step_ms;
	struct timeval step_start_ms, step_finish_ms;
	gettimeofday (&step_start_ms, NULL); 	

	assert(child1 != NULL);
	assert(child2 != NULL);
	Aig_Obj_t* ret_expression = Aig_And(aig_manager, child1, child2);
	assert(ret_expression != NULL);

	gettimeofday (&step_finish_ms, NULL);
   	step_ms = step_finish_ms.tv_sec * 1000 + step_finish_ms.tv_usec / 1000;
   	step_ms -= step_start_ms.tv_sec * 1000 + step_start_ms.tv_usec / 1000;
	BooleanOpTime += step_ms;

	return ret_expression;	
}


Aig_Obj_t* createFalse(Aig_Man_t* aig_manager)
{	
	Aig_Obj_t* ret_expression = Aig_ManConst0(aig_manager);	
	assert(ret_expression != NULL);
	return ret_expression;	
}


Aig_Obj_t* createTrue(Aig_Man_t* aig_manager)
{
	Aig_Obj_t* ret_expression = Aig_ManConst1(aig_manager);	
	assert(ret_expression != NULL);
	return ret_expression;	
}


Aig_Obj_t* createEquivalence(Aig_Obj_t* child1, Aig_Obj_t* child2, Aig_Man_t* aig_manager)
{
	assert(child1 != NULL);
	assert(child2 != NULL);

	Aig_Obj_t* child1_and_child2 = Aig_And(aig_manager, child1, child2);
	Aig_Obj_t* neg_child1_and_neg_child2 = Aig_And(aig_manager, Aig_Not(child1), Aig_Not(child2)); 
	Aig_Obj_t* ret_expression = Aig_Or(aig_manager, child1_and_child2, neg_child1_and_neg_child2);

	assert(ret_expression != NULL);
	return ret_expression;	
}



Aig_Obj_t* createExor(Aig_Obj_t* child1, Aig_Obj_t* child2, Aig_Man_t* aig_manager)
{
	assert(child1 != NULL);
	assert(child2 != NULL);

	Aig_Obj_t* child1_and_neg_child2 = Aig_And(aig_manager, child1, Aig_Not(child2));
	Aig_Obj_t* neg_child1_and_child2 = Aig_And(aig_manager, Aig_Not(child1), child2); 
	Aig_Obj_t* ret_expression = Aig_Or(aig_manager, child1_and_neg_child2, neg_child1_and_child2);

	assert(ret_expression != NULL);
	return ret_expression;	
}



Aig_Obj_t* createIte(Aig_Obj_t* condition, Aig_Obj_t* true_branch, Aig_Obj_t* false_branch, Aig_Man_t* aig_manager)
{
	assert(condition != NULL);
	assert(true_branch != NULL);
	assert(false_branch != NULL);

	Aig_Obj_t* disjunct_1 = Aig_And(aig_manager, condition, true_branch);
	Aig_Obj_t* disjunct_2 = Aig_And(aig_manager, Aig_Not(condition), false_branch); 
	Aig_Obj_t* ret_expression = Aig_Or(aig_manager, disjunct_1, disjunct_2);

	assert(ret_expression != NULL);
	return ret_expression;	
}



Aig_Obj_t* createImplication(Aig_Obj_t* antecedent, Aig_Obj_t* consequent, Aig_Man_t* aig_manager)
{
	assert(antecedent != NULL);
	assert(consequent != NULL);

	Aig_Obj_t* ret_expression = Aig_Or(aig_manager, Aig_Not(antecedent), consequent);
	assert(ret_expression != NULL);
	return ret_expression;	
}



void computeSupport(Aig_Obj_t* formula, set<string> &support, Aig_Man_t* aig_manager)
{
	#ifdef DETAILED_RECORD_KEEP
	unsigned long long int step_ms;
	struct timeval step_start_ms, step_finish_ms;
	gettimeofday (&step_start_ms, NULL); 	
	#endif 

	assert(formula != NULL);
	formula = Aig_Regular(formula);
	support.clear();

	bool use_hashing = false;

	if(use_hashing)
	{
		static t_HashTable<string, set<string> > cache;	
		string key;       

		key = toString(formula);
	
		t_HashTable<string, set<string> >::iterator cache_it = cache.find(key);
		if (cache_it != cache.end())
		{
			support = cache_it.getValue();	
		}
		else if(formula == createTrue(aig_manager))
		{
			// empty support
			cache[key] = support;
		}
		else
		{
			Vec_Ptr_t* aig_support = Aig_Support(aig_manager, formula);
		
			int j = 0;
			Aig_Obj_t* element;
			Vec_PtrForEachEntry(Aig_Obj_t*, aig_support, element, j )  
			{
				assert(element != NULL);
				int element_id = element->Id;
				map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(element_id);
				assert(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end());

				string element_name = Ci_id_to_Ci_name_map_it->second;
				support.insert(element_name);
			}	

			cache[key] = support;
		}
	}// if(use_hashing)
	else
	{
		if(formula != createTrue(aig_manager))
		{
			Vec_Ptr_t* aig_support = Aig_Support(aig_manager, formula);
		
			int j = 0;
			Aig_Obj_t* element;
			Vec_PtrForEachEntry(Aig_Obj_t*, aig_support, element, j )  
			{
				assert(element != NULL);
				int element_id = element->Id;
				map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(element_id);
				assert(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end());

				string element_name = Ci_id_to_Ci_name_map_it->second;
				support.insert(element_name);
			}

			Vec_PtrFree( aig_support ); // added to avoid memory leaks
		}
	}// else of if(use_hashing)

	#ifdef DETAILED_RECORD_KEEP
	gettimeofday (&step_finish_ms, NULL);
   	step_ms = step_finish_ms.tv_sec * 1000 + step_finish_ms.tv_usec / 1000;
   	step_ms -= step_start_ms.tv_sec * 1000 + step_start_ms.tv_usec / 1000;

	//cout << "\nTime to find support of dag with size " << computeSize(formula) << " is: " << step_ms << "milli seconds\n";
	total_time_in_compute_support = total_time_in_compute_support + step_ms;
	#endif
}





Aig_Obj_t* ReplaceLeafByExpression(Aig_Obj_t* OriginalFormula, string var_to_replace, Aig_Obj_t* FormulaToSubstitute, Aig_Man_t* aig_manager)
{
	// sanity checks
	assert(OriginalFormula != NULL);
	assert(FormulaToSubstitute != NULL);

	// First let's find the ci_index of var_to_replace
	map<string, int>::iterator Ci_name_to_Ci_number_map_it = Ci_name_to_Ci_number_map.find(var_to_replace);

	if(Ci_name_to_Ci_number_map_it == Ci_name_to_Ci_number_map.end())
	{
		cout <<"\nNo entry for " << var_to_replace << " in Ci_name_to_Ci_number_map\n";
		assert(Ci_name_to_Ci_number_map_it != Ci_name_to_Ci_number_map.end());
	}

	int aig_variable_index = Ci_name_to_Ci_number_map_it->second;
	
	// Let's compose
	Aig_Obj_t* ComposedFormula = Aig_Compose(aig_manager, OriginalFormula, FormulaToSubstitute, aig_variable_index);
	assert(ComposedFormula != NULL);
	
	return ComposedFormula;
}





int computeSize(Aig_Obj_t* formula, Aig_Man_t* aig_manager)
{
	unsigned long long int step_ms;
	struct timeval step_start_ms, step_finish_ms;
	gettimeofday (&step_start_ms, NULL); 

	assert(formula != NULL);
	formula = Aig_Regular(formula);
	int size;

        bool use_hashing = false;

	if(use_hashing)
	{
		static t_HashTable<string, int > cache;		

		string key = toString(formula);	
	
		t_HashTable<string, int >::iterator cache_it = cache.find(key);
		if(cache_it != cache.end())
	    	{
			size = cache_it.getValue();	
		}
		else if(formula ==  createTrue(aig_manager))
		{
			size = 1;
			cache[key] = 1;
		}
		else
		{		
			size = Aig_SupportSize(aig_manager, formula) + Aig_DagSize(formula);	
			cache[key] = size;		
		}
	}
	else
	{
		if(formula ==  createTrue(aig_manager))
		{
			size = 1;
		}
		else
		{		
			size = Aig_SupportSize(aig_manager, formula) + Aig_DagSize(formula);
		}
	}	

	gettimeofday (&step_finish_ms, NULL);
   	step_ms = step_finish_ms.tv_sec * 1000 + step_finish_ms.tv_usec / 1000;
   	step_ms -= step_start_ms.tv_sec * 1000 + step_start_ms.tv_usec / 1000;
	total_time_in_compute_size = total_time_in_compute_size + step_ms;

	return size;
}


void obtainFactors(ABC* abcObj, Abc_Frame_t* abcFrame, set<Aig_Obj_t*> &Factors, Aig_Man_t* &aig_manager, list<string> &VariablesToEliminate)
{
	assert(benchmark_name != "");

	string command = "read " + benchmark_name + ";" + initCommand;

	#ifdef DEBUG_SKOLEM
	cout << command << endl;
	#endif

	if (abcObj->comExecute(abcFrame, command))
    	{
	 	cout << "cannot execute " << command << endl;
		assert(false);
	}

	Abc_Ntk_t* transition_function = abcFrame->pNtkCur;
	transition_function = Abc_NtkDup(transition_function);

	set<string> VariablesToEliminate_Set(VariablesToEliminate.begin(), VariablesToEliminate.end());

	// Let's get all the variable names and
	// Ci_name_to_Ci_number_map
	Abc_Obj_t* tempInputObj;
	int j = 0;
	vector<string> variable_names;
	Abc_NtkForEachCi(transition_function, tempInputObj, j)
	{
		string variable_name = Abc_ObjName(tempInputObj);
		variable_names.push_back(variable_name);

		Ci_name_to_Ci_number_map.insert(make_pair(variable_name, j));

		number_of_Cis++;				
	} 

	// Let's split the transition_function into factors

	aig_manager = Abc_NtkToDar(transition_function, 0, 0);
	// transition function converted to aig_manager	

	// reading the factors
	Aig_Obj_t* factorObj;
    	int i = 0;

	Aig_ManForEachPoSeq(aig_manager, factorObj, i )
    	{
		assert(factorObj != NULL);

		Aig_Obj_t* Fanin0_factorObj = Aig_ObjChild0(factorObj);		 
		// Note that it is important to use Aig_ObjChild0 here
		// Earlier Aig_ObjFanin0 was used; but Aig_ObjFanin0 regularizes the dag,
		// Aig_ObjChild0 does not regularize the dag		

		assert(Fanin0_factorObj != NULL);

		Factors.insert(Fanin0_factorObj);
    	}

	// Let's get the IDs of the variables

	vector<int> variable_ids;
	i = 0;
	Aig_ManForEachCi(aig_manager, factorObj, i )
	{
		int Id = Aig_ObjId(factorObj); // no need to apply Aig_Regular() as factorObj is CI
		variable_ids.push_back(Id);

		string variable_name = 	variable_names[i];	
		if(VariablesToEliminate_Set.find(variable_name) != VariablesToEliminate_Set.end())
		// variable_name is an input; it is a Ci to be eliminated
		{
			Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.insert(make_pair(variable_name, factorObj));
		}

		Ci_name_to_Ci_object_map.insert(make_pair(variable_name, factorObj));
	}

	// Let's create the variable_id ---> variable_name map

	assert(variable_ids.size() == variable_names.size());	
	for(int i = 0; i < variable_ids.size(); i++)
	{
		Ci_id_to_Ci_name_map.insert(make_pair(variable_ids[i], variable_names[i]));
	}
}




bool isSat(Aig_Man_t* aig_manager, Aig_Obj_t* formula, map<string, int> &Model, unsigned long long int &cnf_time, int &formula_size, unsigned long long int &simplification_time)
{
	Model.clear(); 

	if(apply_global_simplifications_before_each_iteration)
	{

		unsigned long long int simplification_ms;
		struct timeval simplification_start_ms, simplification_finish_ms;
		gettimeofday (&simplification_start_ms, NULL); 	


		assert(formula != NULL);
		Aig_Obj_t* formula_CO;
		// formula is an internal node
		// connect formula to a CO, formula_CO
		formula_CO = Aig_ObjCreateCo( aig_manager, formula );
		assert(formula_CO != NULL);	

		int number_of_nodes_removed = Aig_ManSeqCleanupBasic(aig_manager);
		cout << "\nNumber of nodes removed by Aig_ManSeqCleanupBasic = " << number_of_nodes_removed << endl;
		
		cout << "\nformula size before simplifications = " << computeSize(formula, aig_manager) << endl;

		Aig_Man_t* temp_aig_manager_for_coi;
		// for cone of influence reduction starts here
		bool cone_of_influence_reduction = true;
		if(cone_of_influence_reduction)
		{
			cout << "\nCalling simplifyUsingConeOfInfluence\n";
			temp_aig_manager_for_coi = simplifyUsingConeOfInfluence( aig_manager, Aig_ManCoNum(aig_manager)-1, 1 );
			cout << "\nsimplifyUsingConeOfInfluence called\n";
		}
		else
		{
			temp_aig_manager_for_coi = aig_manager;	
		}
		// for cone of influence reduction ends here	


		Aig_Man_t* temp_aig_manager;
		// for simplification starts here	
		if(kind_of_global_simplifications == "rewrite")
		{
			cout << "\nCalling Dar_ManRewriteDefault\n";
			temp_aig_manager = Dar_ManRewriteDefault(temp_aig_manager_for_coi); 
			cout << "\nDar_ManRewriteDefault called\n";
		}
		else if(kind_of_global_simplifications == "compress")
		{
			cout << "\nCalling Dar_ManCompress\n";
			temp_aig_manager = Dar_ManCompress(temp_aig_manager_for_coi, 1, 1, 0, 1); 
			cout << "\nDar_ManCompress called\n";
		}
		else if(kind_of_global_simplifications == "compress2")
		{
			cout << "\nCalling Dar_ManCompress2\n";
			temp_aig_manager = Dar_ManCompress2(temp_aig_manager_for_coi, 1, 1, 1, 0, 1); 
			cout << "\nDar_ManCompress2 called\n";
		}
		else if(kind_of_global_simplifications == "rwsat")
		{
			cout << "\nCalling Dar_ManRwsat\n";
			temp_aig_manager = Dar_ManRwsat(temp_aig_manager_for_coi, 1, 1); 
			cout << "\nDar_ManRwsat called\n";
		}
		else if(kind_of_global_simplifications == "fraig")
		{
			cout << "\nCalling simplifyUsingFraiging\n";
			temp_aig_manager = simplifyUsingFraiging(temp_aig_manager_for_coi);
			cout << "\nsimplifyUsingFraiging called\n";
		}
		else if(kind_of_global_simplifications == "default")
		{
			cout << "\nNo simplification\n";
			temp_aig_manager = temp_aig_manager_for_coi;
		}
		else
		{
			cout << "\nError in isSat! Unknown simplification\n";
			assert(false);
		}

		gettimeofday (&simplification_finish_ms, NULL);
		simplification_ms = simplification_finish_ms.tv_sec * 1000 + simplification_finish_ms.tv_usec / 1000;
		simplification_ms -= simplification_start_ms.tv_sec * 1000 + simplification_start_ms.tv_usec / 1000;
		cout << "\nsimplification finished in " << simplification_ms << " milliseconds\n";

		simplification_time = simplification_ms;
		times_in_aig_simplification_in_cegar.push_back(simplification_ms);
	

		formula_CO = Aig_ManCo(temp_aig_manager, Aig_ManCoNum(temp_aig_manager)-1 );
		assert(formula_CO != NULL);
		
		formula_size = computeSize(Aig_ObjChild0(formula_CO), temp_aig_manager);
		cout << "\nformula size after simplifications = " << formula_size << endl;
		sizes_of_exactness_formulae_in_cegar.push_back(formula_size);


		unsigned long long int cnf_ms;
		struct timeval cnf_start_ms, cnf_finish_ms;
		gettimeofday (&cnf_start_ms, NULL); 	

	
		// derive CNF for all CO's of aig_manager
		Cnf_Dat_t* pCnf = Cnf_Derive( temp_aig_manager, Aig_ManCoNum(temp_aig_manager) ); 

		cout << "\nCNF created" << endl;

		// showing CNF
		bool show_cnf = false; // note that this CNF may not be final as we need to assert Lit to Lit+1 literals
		if(show_cnf)
		{
			char cnf_file[100];
			strcpy(cnf_file, "temp.cnf");
			//Cnf_DataWriteIntoFile(pCnf, cnf_file, 1);			
		}

		sat_solver * pSat = sat_solver_new();
	
	    	sat_solver_setnvars( pSat, pCnf->nVars );
		for (int i = 0; i < pCnf->nClauses; i++ )
	    	{
			if ( !sat_solver_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] ) )
			{
		    		assert( false );
			}
		}

		printf( "CNF: Variables = %6d. Clauses = %7d. Literals = %8d. ", pCnf->nVars, pCnf->nClauses, pCnf->nLiterals );

		gettimeofday (&cnf_finish_ms, NULL);
		cnf_ms = cnf_finish_ms.tv_sec * 1000 + cnf_finish_ms.tv_usec / 1000;
		cnf_ms -= cnf_start_ms.tv_sec * 1000 + cnf_start_ms.tv_usec / 1000;
		cout << "\ncnf generation finished in " << cnf_ms << " milliseconds\n";

		cnf_time = cnf_ms;
		times_in_cnf_generation_in_cegar.push_back(cnf_ms);


		unsigned long long int solver_ms;
		struct timeval solver_start_ms, solver_finish_ms;
		gettimeofday (&solver_start_ms, NULL); 

		bool return_value;
		bool apply_solver_simplify = true;// note that this CNF may not be final as we need to assert Lit to Lit+1 literals
		// But if this is already unsat, then even after adding the clauses, we will get unsat only

		int trivially_unsat = 1;

		if(apply_solver_simplify)
		{
			cout << "\nApplying simplification of CNF\n";
			trivially_unsat = sat_solver_simplify(pSat);
		}

		if(trivially_unsat == 0)
		{
			cout << "\nFormula is trivially unsat\n";
			Model.clear();
			return_value = false;
		}
		else
		{

			int Lit = toLitCond( pCnf->pVarNums[formula_CO->Id], 0 );

			#ifdef DEBUG_SKOLEM
				cout << "\nLiteral added is " << lit_print(Lit) << endl;
			#endif
	
			#ifdef DEBUG_SKOLEM
				pSat->verbosity = 2;
			#endif

			int status = sat_solver_solve( pSat, &Lit, &Lit + 1, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );

			if ( status == l_False )
			{
				cout << "\nFormula is unsat\n";
				Model.clear();
				return_value = false;
			}
			else if ( status == l_True )
			{
				cout << "\nFormula is sat; get the CEX\n";  

				Vec_Int_t * vCiIds = Cnf_DataCollectPiSatNums( pCnf, temp_aig_manager );
				int * pModel = Sat_SolverGetModel( pSat, vCiIds->pArray, vCiIds->nSize );
			
				// Note that ids of Ci's in the temp_aig_manager are different from
				//	     ids of Ci's in the aig_manager
				// But their order in the manager must be the same
				// Let's find the order of Ci's in aig_manager

				map<int, int> order_of_Cis_in_aig_manager;
				int j = 0;
				Aig_Obj_t* aig_manager_Ci_Obj;
				Aig_ManForEachCi( aig_manager, aig_manager_Ci_Obj, j )
				{
					int Ci_id = aig_manager_Ci_Obj->Id;
					order_of_Cis_in_aig_manager.insert(make_pair(j, Ci_id));
				}

				j = 0;
				Aig_Obj_t* temp_aig_manager_Ci_Obj;
				Aig_ManForEachCi( temp_aig_manager, temp_aig_manager_Ci_Obj, j )
				{
					map<int, int>::iterator order_of_Cis_in_aig_manager_it = order_of_Cis_in_aig_manager.find(j);
					assert(order_of_Cis_in_aig_manager_it != order_of_Cis_in_aig_manager.end());
					int Ci_id = order_of_Cis_in_aig_manager_it->second;

					map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(Ci_id);
					assert(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end());
					string Ci_name = Ci_id_to_Ci_name_map_it->second;

					int Ci_value = pModel[j];
					
					Model.insert(make_pair(Ci_name, Ci_value));
				}
				
				return_value = true;           
			}
			else
			{
				cout << "\nUnknown value " << status <<" returned from solver inside helper.cc::isSat()\n";
				assert(false);
			}
		}

		sat_solver_delete( pSat );
		Cnf_DataFree( pCnf );	

		gettimeofday (&solver_finish_ms, NULL);
		solver_ms = solver_finish_ms.tv_sec * 1000 + solver_finish_ms.tv_usec / 1000;
		solver_ms -= solver_start_ms.tv_sec * 1000 + solver_start_ms.tv_usec / 1000;
		cout << "\ninternal solver finished in " << solver_ms << " milliseconds\n";
		times_in_sat_solving_in_cegar.push_back(solver_ms);


		if(cone_of_influence_reduction)
		{
			if(kind_of_global_simplifications == "default") // only coi applied
			// temp_aig_manager same as temp_aig_manager_for_coi, but not the same as 
			// aig_manager
			{
				Aig_ManStop(temp_aig_manager);
				cout << "\ntemp_aig_manager deleted\n";	
			}
			else // both coi and simplification applied
			// temp_aig_manager same as temp_aig_manager_for_coi, but not the same as 
			// aig_manager
			{
				Aig_ManStop(temp_aig_manager_for_coi);	
				Aig_ManStop(temp_aig_manager);	
				cout << "\ntemp_aig_manager and temp_aig_manager_for_coi deleted\n";	
			}
		}
		else
		{
			cout << "\nno aig manager deletion\n";
			// no need to stop! temp_aig_manager is the
			// same as aig_manager as no simplification is applied
		}
			
		return return_value;		
	}
	else
	{
		
		assert(formula != NULL);

		Aig_Obj_t* formula_CO;

		bool use_simplifications = false;
		if(use_simplifications)
		{
			bool apply_rewrites = false;
			bool apply_cleanups = false; // this works!!
			bool apply_rewrites_on_networks = false;
			bool apply_rewrite_after_cleanup = false;

			if(apply_rewrites)
			{	

				// formula is an internal node
				// connect formula to a CO, formula_CO

				formula_CO = Aig_ObjCreateCo( aig_manager, formula );
				assert(formula_CO != NULL);
	
				cout << "\nformula size before rewrite = " << computeSize(formula, aig_manager) << endl;

				//int number_of_pos_added = Aig_ManAntiCleanup(aig_manager);
				//cout << "\nNumber of POs added by Aig_ManAntiCleanup = " << number_of_pos_added << endl;


				/* When one of these functions is used, the unsat formula 
				   for bj08amba2g1.aig becomes sat */

				//aig_manager = Dar_ManRewriteDefault(aig_manager);
				//aig_manager = Dar_ManCompress(aig_manager, 1, 1, 0, 1); 
				//aig_manager = Dar_ManCompress2(aig_manager, 1, 1, 1, 0, 1); 
				aig_manager = Dar_ManRwsat(aig_manager, 1, 1); 

				cout << "\nformula size after rewrite = " << computeSize(formula, aig_manager) << endl;

			}
			else if(apply_cleanups) // This Works! Only Clean-up after formula_CO = Aig_ObjCreateCo( aig_manager, formula )
			// Try this out
			{

				// formula is an internal node
				// connect formula to a CO, formula_CO

				formula_CO = Aig_ObjCreateCo( aig_manager, formula );
				assert(formula_CO != NULL);			

				cout << "\nformula size before cleanup = " << computeSize(formula, aig_manager) << endl;


				int number_of_nodes_removed = Aig_ManSeqCleanupBasic(aig_manager);
				cout << "\nNumber of nodes removed by Aig_ManSeqCleanupBasic = " << number_of_nodes_removed << endl;

				cout << "\nformula size after rewrite = " << computeSize(formula, aig_manager) << endl;

			}
			else if(apply_rewrites_on_networks)
			{
				cout << "\nformula size before rewrite = " << computeSize(formula, aig_manager) << endl;

				int number_of_pos_added = Aig_ManAntiCleanup(aig_manager);
				cout << "\nNumber of POs added by Aig_ManAntiCleanup = " << number_of_pos_added << endl;

				/* When the following code is used, the unsat formula 
				   for bj08amba2g1.aig becomes sat */

				Abc_Ntk_t* aig_manager_ntk = Abc_NtkFromAigPhase(aig_manager);
				assert(aig_manager_ntk != NULL);
				Abc_NtkRewrite(aig_manager_ntk, 0, 0, 0, 0, 0 );
				assert(aig_manager_ntk != NULL);
				aig_manager = Abc_NtkToDar(aig_manager_ntk, 0, 0);
				assert(aig_manager != NULL);

				cout << "\naig_manager recreated after rewriting\n";
				cout << "\nformula size after rewrite = " << computeSize(formula, aig_manager) << endl;

				// formula is an internal node
				// connect formula to a CO, formula_CO

				formula_CO = Aig_ObjCreateCo( aig_manager, formula );
				assert(formula_CO != NULL);
		
			}
			else if(apply_rewrite_after_cleanup) 
			{

				// formula is an internal node
				// connect formula to a CO, formula_CO

				formula_CO = Aig_ObjCreateCo( aig_manager, formula );
				assert(formula_CO != NULL);			

				cout << "\nformula size before cleanup = " << computeSize(formula, aig_manager) << endl;


				int number_of_nodes_removed = Aig_ManSeqCleanupBasic(aig_manager);
				cout << "\nNumber of nodes removed by Aig_ManSeqCleanupBasic = " << number_of_nodes_removed << endl;

				//Aig_ManShow(aig_manager, 0, NULL); 
			
				//aig_manager = Dar_ManRwsat(aig_manager, 1, 1);
				aig_manager = Dar_ManRewriteDefault(aig_manager); 
			
				cout << "\nformula size after rewrite = " << computeSize(formula, aig_manager) << endl;

				//Aig_ManShow(aig_manager, 0, NULL); 

				formula_CO = Aig_ManCo( aig_manager, Aig_ManCoNum( aig_manager ) - 1 );
			}
		}
		else
		{
			// formula is an internal node
			// connect formula to a CO, formula_CO

			formula_CO = Aig_ObjCreateCo( aig_manager, formula );
			assert(formula_CO != NULL);

		}

		simplification_time = 0;
		times_in_aig_simplification_in_cegar.push_back(simplification_time);

		formula_size = computeSize(formula, aig_manager);
		sizes_of_exactness_formulae_in_cegar.push_back(formula_size);

		unsigned long long int cnf_ms;
		struct timeval cnf_start_ms, cnf_finish_ms;
		gettimeofday (&cnf_start_ms, NULL); 	

	
		// derive CNF for all CO's of aig_manager
		Cnf_Dat_t* pCnf = Cnf_Derive( aig_manager, Aig_ManCoNum(aig_manager) ); 

		// showing CNF
		bool show_cnf = false; // note that this CNF may not be final as we need to assert Lit to Lit+1 literals
		if(show_cnf)
		{
			char cnf_file[100];
			strcpy(cnf_file, "temp.cnf");
			//Cnf_DataWriteIntoFile(pCnf, cnf_file, 1);
		}

		sat_solver * pSat = sat_solver_new();
	
	    	sat_solver_setnvars( pSat, pCnf->nVars );
		for (int i = 0; i < pCnf->nClauses; i++ )
	    	{
			if ( !sat_solver_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] ) )
			{
		    		assert( false );
			}
		}

		//printf( "CNF: Variables = %6d. Clauses = %7d. Literals = %8d. ", pCnf->nVars, pCnf->nClauses, pCnf->nLiterals );

		gettimeofday (&cnf_finish_ms, NULL);
		cnf_ms = cnf_finish_ms.tv_sec * 1000 + cnf_finish_ms.tv_usec / 1000;
		cnf_ms -= cnf_start_ms.tv_sec * 1000 + cnf_start_ms.tv_usec / 1000;
		//cout << "\ncnf generation finished in " << cnf_ms << " milliseconds\n";

		cnf_time = cnf_ms;
		times_in_cnf_generation_in_cegar.push_back(cnf_ms);


		unsigned long long int solver_ms;
		struct timeval solver_start_ms, solver_finish_ms;
		gettimeofday (&solver_start_ms, NULL); 

		bool return_value;
		bool apply_solver_simplify = true;// note that this CNF may not be final as we need to assert Lit to Lit+1 literals
		// But if this is already unsat, then even after adding the clauses, we will get unsat only

		int trivially_unsat = 1;

		if(apply_solver_simplify)
		{
			#ifdef DEBUG_SKOLEM
				cout << "\nApplying simplification\n";
			#endif

			trivially_unsat = sat_solver_simplify(pSat);
		}

		if(trivially_unsat == 0)
		{
			//cout << "\nFormula is trivially unsat\n";
			Model.clear();
			return_value = false;
		}
		else
		{

			int Lit = toLitCond( pCnf->pVarNums[formula_CO->Id], 0 );

			#ifdef DEBUG_SKOLEM
				cout << "\nLiteral added is " << lit_print(Lit) << endl;
			#endif
	
			#ifdef DEBUG_SKOLEM
				pSat->verbosity = 2;
			#endif

			int status = sat_solver_solve( pSat, &Lit, &Lit + 1, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );

			if ( status == l_False )
			{
				//cout << "\nFormula is unsat\n";
				Model.clear();
				return_value = false;
			}
			else if ( status == l_True )
			{
				//cout << "\nFormula is sat; get the CEX\n";  

				Vec_Int_t * vCiIds = Cnf_DataCollectPiSatNums( pCnf, aig_manager );
				int * pModel = Sat_SolverGetModel( pSat, vCiIds->pArray, vCiIds->nSize );
			
				// cout << "\nShowing the CEX\n";
				int j = 0;
				Aig_Obj_t* pCi;
				Aig_ManForEachCi( aig_manager, pCi, j )
				{
					// cout << "\n\nCi number = " << j ;
					// cout << "\nCi Id = " << pCi->Id;
			
					int Ci_id = pCi->Id;
					map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(Ci_id);
					assert(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end());

					string Ci_name = Ci_id_to_Ci_name_map_it->second;
					int Ci_value = pModel[j];
					//cout << "\nCi name = " << Ci_name << "\tCi value = " << Ci_value;

					Model.insert(make_pair(Ci_name, Ci_value));
				}

				return_value = true;           
			}
			else
			{
				cout << "\nUnknown value " << status <<" returned from solver inside helper.cc::isSat()\n";
				assert(false);
			}
		}

		sat_solver_delete( pSat );
		Cnf_DataFree( pCnf );	

		gettimeofday (&solver_finish_ms, NULL);
		solver_ms = solver_finish_ms.tv_sec * 1000 + solver_finish_ms.tv_usec / 1000;
		solver_ms -= solver_start_ms.tv_sec * 1000 + solver_start_ms.tv_usec / 1000;
		//cout << "\ninternal solver finished in " << solver_ms << " milliseconds\n";
		times_in_sat_solving_in_cegar.push_back(solver_ms);
	
		return return_value;
	}
}




void writeCNFToFile(vector< vector<int> > &CNF_1, vector< vector<int> > &CNF_2, int number_of_variables, int number_of_clauses, string filename)
{
	FILE *fcnf = fopen(filename.c_str(), "w+");
	assert(fcnf != NULL);

	fprintf(fcnf, "p cnf %d %d\n", number_of_variables, number_of_clauses);

	for(int i = 0; i < CNF_1.size(); i++)
    	{
		vector<int> clause;
		clause = CNF_1[i];

		for(int j = 0; j < clause.size(); j++)
    		{
	      		fprintf(fcnf, "%d ", clause[j]);
		}
		fprintf(fcnf, "0\n");
    	}

	for(int i = 0; i < CNF_2.size(); i++)
    	{
		vector<int> clause;
		clause = CNF_2[i];

		for(int j = 0; j < clause.size(); j++)
    		{
	      		fprintf(fcnf, "%d ", clause[j]);
		}
		fprintf(fcnf, "0\n");
    	}

	
	fclose(fcnf);
}



void showCNF(vector< vector<int> > &CNF)
{
	for(int i = 0; i < CNF.size(); i++)
    	{
		vector<int> clause;
		clause = CNF[i];

		for(int j = 0; j < clause.size(); j++)
    		{
	      		printf("%d ", clause[j]);
		}
		printf("0\n");
    	}
}




void insertCIIntoLabelTable(Aig_Obj_t* formula)
{
	assert(formula != NULL);
	assert(formula->Type == AIG_OBJ_CI);

	string key = toString(formula);
	t_HashTable<string, int>::iterator LabelTable_it = LabelTable.find(key);
	if (LabelTable_it != LabelTable.end()) // label exists already
	{
		return;
	}
	else
	{
		int node_label = LabelCount;
		LabelTable[key] = LabelCount;
		LabelCount++;

		int Ci_id = Aig_ObjId(formula); 
		map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(Ci_id);
		assert(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end());
		string Ci_name = Ci_id_to_Ci_name_map_it->second;			

		Ci_name_to_Ci_label_mapForGetCNF.insert(make_pair(Ci_name, node_label));
		Ci_label_to_Ci_name_mapForGetCNF.insert(make_pair(node_label, Ci_name));
	}
}



int getCNF(Aig_Man_t* aig_manager, Aig_Obj_t* formula, vector< vector<int> > &CNF)
{
	assert(formula != NULL);

	string key = toString(formula);

	t_HashTable<string, int>::iterator LabelTable_it = LabelTable.find(key);
	if (LabelTable_it != LabelTable.end()) // label exists already, i.e. traversed already
	{
		return LabelTable_it.getValue();;
	}
	else
	{
		int node_label = LabelCount;
		LabelTable[key] = LabelCount;
		LabelCount++;

		if(Aig_IsComplement(formula)) // ~ encountered
		{
			Aig_Obj_t* child_1 = Aig_Regular(formula);
			assert(child_1 != NULL);
			int child_1_label = getCNF(aig_manager, child_1, CNF);

			// clauses are ~1 \/ ~2 
			//	       1 \/ 2

			vector<int> clause_1;
			clause_1.push_back(-1*node_label);
			clause_1.push_back(-1*child_1_label);
			CNF.push_back(clause_1);	

			vector<int> clause_2;
			clause_2.push_back(node_label);
			clause_2.push_back(child_1_label);
			CNF.push_back(clause_2);

		} // if(Aig_IsComplement(formula)) ends here
		else if(formula->Type == AIG_OBJ_CI) //CI encountered
		{
			int Ci_id = Aig_ObjId(formula); 
			map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(Ci_id);
			assert(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end());
			string Ci_name = Ci_id_to_Ci_name_map_it->second;			

			Ci_name_to_Ci_label_mapForGetCNF.insert(make_pair(Ci_name, node_label));
			Ci_label_to_Ci_name_mapForGetCNF.insert(make_pair(node_label, Ci_name));
		}
		else if(formula->Type == AIG_OBJ_CO) //CO encountered
		{
			// do nothing
		}
		else if(formula->Type == AIG_OBJ_CONST1) // 1 encountered
		{
			vector<int> clause;
			clause.push_back(node_label); // clause is 1
			CNF.push_back(clause);
		}
		else if(formula->Type == AIG_OBJ_AND)// child_1 \wedge child_2 encountered
		{
			Aig_Obj_t* child_1 = Aig_ObjChild0(formula);
			Aig_Obj_t* child_2 = Aig_ObjChild1(formula);

			assert(child_1 != NULL);
			assert(child_2 != NULL);

			int child_1_label = getCNF(aig_manager, child_1, CNF);
			int child_2_label = getCNF(aig_manager, child_2, CNF);

			// clauses are 1 \/ ~2 \/ ~3
			//	       ~1 \/ 2
			//	       ~1 \/ 3

			vector<int> clause_1;
			clause_1.push_back(node_label);
			clause_1.push_back(-1*child_1_label);
			clause_1.push_back(-1*child_2_label);
			CNF.push_back(clause_1);	

			vector<int> clause_2;
			clause_2.push_back(-1*node_label);
			clause_2.push_back(child_1_label);
			CNF.push_back(clause_2);

			vector<int> clause_3;
			clause_3.push_back(-1*node_label);
			clause_3.push_back(child_2_label);
			CNF.push_back(clause_3);				
		}
		else
		{
			cout << "\nUnknown formula->Type encountered in helper.cpp::getCNF\n";		
			assert(false);
		}

		return node_label;
	} // if(!label exists already) ends here
}//function ends here				




void displayModelFromSATSolver(map<string, int> &Model)
{
	cout << "\nModel\n";
	for(map<string, int>::iterator model_it = Model.begin(); model_it != Model.end(); model_it++)
	{
		cout << model_it->first << "\t" << model_it->second << endl;
	}
}



bool giveCNFFiletoSATSolverAndQueryForSatisfiability(string cnf_filename, map<string, int> &Model)
{
	Model.clear();

	bool result_of_call;
	string model_file_name = "sat_result.txt";

	string command;

	if(solver == "glucose")
	{

		command = "glucose "; 
		
		command += cnf_filename;
		command += " ";
		command += model_file_name;

		system(command.c_str());

		ifstream *model_file = new ifstream();
	  	model_file->open(model_file_name.c_str()); // open the model_file
		assert(model_file->is_open());

		string word = "";
		while(!model_file->eof()) //read until end of file
	    	{
	      		*model_file>>word;
	      		
	      		if(word == "")
			{
				break;	
			}
			else if(word == "UNSAT")
			{
				result_of_call = false;
			}
			else if(word == "SAT")
			{
				result_of_call = true;
			}
			else if(word != "0")
			{
				// word is a literal
	
				int value;
				if(word[0] == '-')
				{
					value = 0;
					word = word.substr(1);
				}
				else
				{
					value = 1;				
				}
				int label = atoi(word.c_str());
				assert(label != 0);

				map<int, string>::iterator Ci_label_to_Ci_name_map_it = Ci_label_to_Ci_name_mapForGetCNF.find(label);
				string Ci_name;
				if(Ci_label_to_Ci_name_map_it != Ci_label_to_Ci_name_mapForGetCNF.end()) // label is label of a Ci
				{
					Ci_name = Ci_label_to_Ci_name_map_it->second;
					Model.insert(make_pair(Ci_name, value));
				}
			}
		}//while ends here

	}
	else if(solver == "lingeling")
	{

		command = "lingeling -q "; 
		// SAT-solver used is lingeling (SATCOMP'13 winner of application category)

		command += cnf_filename;
		command += " > ";
		command += model_file_name;

		system(command.c_str());

		ifstream *model_file = new ifstream();
	  	model_file->open(model_file_name.c_str()); // open the model_file
		assert(model_file->is_open());

		string word = "";
		while(!model_file->eof()) //read until end of file
	    	{
	      		*model_file>>word;
	      		
	      		if(word == "")
			{
				break;	
			}
			else if(word == "UNSATISFIABLE")
			{
				result_of_call = false;
			}
			else if(word == "SATISFIABLE")
			{
				result_of_call = true;
			}
			else if(word != "s" && word != "v" && word != "0")
			{
				// word is a literal
	
				int value;
				if(word[0] == '-')
				{
					value = 0;
					word = word.substr(1);
				}
				else
				{
					value = 1;				
				}
				int label = atoi(word.c_str());
				assert(label != 0);

				map<int, string>::iterator Ci_label_to_Ci_name_map_it = Ci_label_to_Ci_name_mapForGetCNF.find(label);
				string Ci_name;
				if(Ci_label_to_Ci_name_map_it != Ci_label_to_Ci_name_mapForGetCNF.end()) // label is label of a Ci
				{
					Ci_name = Ci_label_to_Ci_name_map_it->second;
					Model.insert(make_pair(Ci_name, value));
				}
			}
		}//while ends here

	}
	else
	{
		cout << "\nUnknown solver inside function giveCNFFiletoSATSolverAndQueryForSatisfiability in helper.cpp\n";
		assert(false);
	}
	
	return result_of_call;
}




void writeFormulaToFile(Aig_Man_t* aig_manager, Aig_Obj_t* formula, FILE* fp)
{
	static t_HashTable<string, int> nodes_encountered;
	writeFormulaToFile(aig_manager, formula, fp, nodes_encountered);
	nodes_encountered.clear();
}



void writeFormulaToFile(Aig_Man_t* aig_manager, Aig_Obj_t* formula, FILE* fp, t_HashTable<string, int> &nodes_encountered)
{
	assert(formula != NULL);

	string key = toString(formula);

	t_HashTable<string, int>::iterator nodes_encountered_it = nodes_encountered.find(key);
	if (nodes_encountered_it != nodes_encountered.end()) // formula traversed already
	{
		return;
	}
	else
	{
		nodes_encountered[key] = 1;

		if(Aig_IsComplement(formula)) // ~ encountered
		{
			Aig_Obj_t* child_1 = Aig_Regular(formula);
			assert(child_1 != NULL);
			
			fprintf(fp, "\n%p: ~ %p", formula, child_1);

			writeFormulaToFile(aig_manager, child_1, fp, nodes_encountered);

		} // if(Aig_IsComplement(formula)) ends here
		else if(formula->Type == AIG_OBJ_CI) //CI encountered
		{
			int Ci_id = Aig_ObjId(formula); 
			map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(Ci_id);
			if(Ci_id_to_Ci_name_map_it == Ci_id_to_Ci_name_map.end())
			{
				cout << "\nNo entry for " << Ci_id << " in Ci_id_to_Ci_name_map\n";
				assert(false);
			}
			string Ci_name = Ci_id_to_Ci_name_map_it->second;			

			fprintf(fp, "\n%p: %s", formula, Ci_name.c_str());
		}
		else if(formula->Type == AIG_OBJ_CO) //CO encountered
		{
			// do nothing
		}
		else if(formula->Type == AIG_OBJ_CONST1) // 1 encountered
		{
			fprintf(fp, "\n%p: true", formula);
		}
		else if(formula->Type == AIG_OBJ_AND)// child_1 \wedge child_2 encountered
		{
			Aig_Obj_t* child_1 = Aig_ObjChild0(formula);
			Aig_Obj_t* child_2 = Aig_ObjChild1(formula);

			assert(child_1 != NULL);
			assert(child_2 != NULL);

			fprintf(fp, "\n%p: & %p %p", formula, child_1, child_2);

			writeFormulaToFile(aig_manager, child_1, fp, nodes_encountered);
			writeFormulaToFile(aig_manager, child_2, fp, nodes_encountered);
		}
		else
		{
			cout << "\nUnknown formula->Type encountered in helper.cpp::writeFormulaToFile\n";		
			assert(false);
		}
	} // if(!label exists already) ends here
}//function ends here	



Aig_Man_t * simplifyUsingFraiging( Aig_Man_t * pManAig )
{
    Aig_Man_t * pFraig;
    Fra_Par_t Pars, * pPars = &Pars; 
    Fra_ParamsDefault( pPars );
    pPars->nBTLimitNode = 1000000;
    pPars->fChoicing    = 0;
    pPars->fDoSparse    = 1;
    pPars->fSpeculate   = 0;
    pPars->fProve       = 0;
    pPars->fVerbose     = 0;
    pPars->fDontShowBar = 1;
    pFraig = Fra_FraigPerform( pManAig, pPars );
    return pFraig;
} 
			


void showMap(map<int, set<int> > &integer_map, string whoami)
{
	cout << endl << whoami << "\n***************\n";

	for(map<int, set<int> >::iterator integer_map_it = integer_map.begin(); integer_map_it != integer_map.end(); integer_map_it++)
	{
		cout << integer_map_it->first << " -> ";
		
		set<int> integer_set = integer_map_it->second;
		for(set<int>::iterator integer_it = integer_set.begin(); integer_it != integer_set.end(); integer_it++)
		{
			cout << *integer_it << ", ";
		}
		
		cout << endl;
	}
}



Aig_Man_t * simplifyUsingConeOfInfluence( Aig_Man_t * p, int iPoNum, int fAddRegs )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i;
    //assert( Aig_ManRegNum(p) > 0 );
    assert( iPoNum < Aig_ManCoNum(p)-Aig_ManRegNum(p) );
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    // create the PIs
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachCi( p, pObj, i )
        pObj->pData = Aig_ObjCreateCi( pNew );
    // set registers
    pNew->nRegs    = fAddRegs? p->nRegs : 0;
    pNew->nTruePis = fAddRegs? p->nTruePis : p->nTruePis + p->nRegs;
    pNew->nTruePos = 1;
    // duplicate internal nodes
    Aig_ManForEachNode( p, pObj, i )
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    // create the PO
    pObj = Aig_ManCo( p, iPoNum );
    Aig_ObjCreateCo( pNew, Aig_ObjChild0Copy(pObj) );
    // create register inputs with MUXes
    if ( fAddRegs )
    {
        Aig_ManForEachLiSeq( p, pObj, i )
            Aig_ObjCreateCo( pNew, Aig_ObjChild0Copy(pObj) );
    }
    Aig_ManCleanup( pNew );
    return pNew;
}



void printSet(set<int> &int_set, string who_am_i, FILE* fptr)
{
	fprintf(fptr, "\n%s: ", who_am_i.c_str()); 

	for(set<int>::iterator int_it = int_set.begin(); int_it != int_set.end(); int_it++)
	{
		fprintf(fptr, "%d, ", *int_it);
	}	 	
}


Aig_Obj_t* Interpolate(Aig_Man_t *aig_manager, Aig_Obj_t* alpha, Aig_Obj_t* beta)
{
	if(Aig_IsComplement(alpha) && Aig_Regular(alpha) == createTrue(aig_manager))
	// alpha is false
	{
		Aig_Obj_t* interpolant;
		interpolant = createFalse(aig_manager);	
		return interpolant;		
	}
	else if(Aig_IsComplement(beta) && Aig_Regular(beta) == createTrue(aig_manager))
	// beta is false
	{
		Aig_Obj_t* interpolant;
		interpolant = createTrue(aig_manager);	
		return interpolant;
	}
	else if(Aig_Regular(alpha) == Aig_Regular(beta)) 
	// alpha and beta are negations of each other
	{
		Aig_Obj_t* interpolant;
		interpolant = alpha;
		return interpolant;
	}
	else
	{
		// create aig manager containing alpha
		assert(alpha != NULL);

		Aig_Obj_t* alpha_CO;
		alpha_CO = Aig_ObjCreateCo( aig_manager, alpha );
		assert(alpha_CO != NULL);

		Aig_Man_t* alpha_aig_manager;
		alpha_aig_manager = simplifyUsingConeOfInfluence( aig_manager, Aig_ManCoNum(aig_manager)-1, 1 );
		assert(alpha_aig_manager != NULL);

		// create aig manager containing beta
		assert(beta != NULL);

		Aig_Obj_t* beta_CO;
		beta_CO = Aig_ObjCreateCo( aig_manager, beta );
		assert(beta_CO != NULL);

		Aig_Man_t* beta_aig_manager;
		beta_aig_manager = simplifyUsingConeOfInfluence( aig_manager, Aig_ManCoNum(aig_manager)-1, 1 );
		assert(beta_aig_manager != NULL);

		// find interpolant as a manager
		Aig_Man_t* interpolant_aig_manager;
		interpolant_aig_manager = Aig_ManInterpolation( alpha_aig_manager, beta_aig_manager, 0, 1);	
		
		if(interpolant_aig_manager == NULL)
		{

			bool delete_unneeded_networks = true;
			if(delete_unneeded_networks)
			{
				Aig_ManStop(alpha_aig_manager);		
				Aig_ManStop(beta_aig_manager);
			}

			return NULL; // let's catch this at the caller
		}
		else
		{
	
			// transfer the interpolant to the aig manager
			int CiNum_aig_manager = Aig_ManCiNum( aig_manager );
	
			assert(Aig_ManCoNum(interpolant_aig_manager) == 1);
			Aig_Obj_t* CO_interpolant_aig_manager;
			CO_interpolant_aig_manager = Aig_ManCo(interpolant_aig_manager, 0);
			assert(CO_interpolant_aig_manager != NULL);	

			Aig_Obj_t* interpolant;
			interpolant = Aig_Transfer(interpolant_aig_manager, aig_manager, Aig_ObjChild0(CO_interpolant_aig_manager), CiNum_aig_manager );
			assert(interpolant != NULL);

			bool delete_unneeded_networks = true;
			if(delete_unneeded_networks)
			{
				Aig_ManStop(alpha_aig_manager);		
				Aig_ManStop(beta_aig_manager);
				Aig_ManStop(interpolant_aig_manager);
			}

			return interpolant;
		}
	}
}


// Copy of Aig_ManInter from aigInter.c
Aig_Man_t * Aig_ManInterpolation( Aig_Man_t * pManOn, Aig_Man_t * pManOff, int fRelation, int fVerbose )
{
    void * pSatCnf = NULL;
    Inta_Man_t * pManInter; 
    Aig_Man_t * pRes;
    sat_solver * pSat;
    Cnf_Dat_t * pCnfOn, * pCnfOff;
    Vec_Int_t * vVarsAB;
    Aig_Obj_t * pObj, * pObj2;
    int Lits[3], status, i;
    abctime clk, Cnf_Time, Inter_Time, Sat_Time ;
    int iLast = -1; // Suppress "might be used uninitialized"

    assert( Aig_ManCiNum(pManOn) == Aig_ManCiNum(pManOff) );

clk = Abc_Clock();
    // derive CNFs
//    pCnfOn  = Cnf_Derive( pManOn, 0 );
//    pCnfOff = Cnf_Derive( pManOff, 0 );
    pCnfOn  = Cnf_DeriveSimple( pManOn, 0 );
    pCnfOff = Cnf_DeriveSimple( pManOff, 0 );
    Cnf_DataLift( pCnfOff, pCnfOn->nVars );
Cnf_Time += Abc_Clock() - clk;

clk = Abc_Clock();
    // start the solver
    pSat = sat_solver_new();
    sat_solver_store_alloc( pSat );
    sat_solver_setnvars( pSat, pCnfOn->nVars + pCnfOff->nVars );

    // add clauses of A
    for ( i = 0; i < pCnfOn->nClauses; i++ )
    {
        if ( !sat_solver_addclause( pSat, pCnfOn->pClauses[i], pCnfOn->pClauses[i+1] ) )
        {
            Cnf_DataFree( pCnfOn );
            Cnf_DataFree( pCnfOff );
            sat_solver_delete( pSat );
            return NULL;
        }
    }
    sat_solver_store_mark_clauses_a( pSat );

    // update the last clause
    if ( fRelation )
    {
        //extern int sat_solver_store_change_last( sat_solver * pSat );
        iLast = sat_solver_store_change_last( pSat );
    }

    // add clauses of B
    for ( i = 0; i < pCnfOff->nClauses; i++ )
    {
        if ( !sat_solver_addclause( pSat, pCnfOff->pClauses[i], pCnfOff->pClauses[i+1] ) )
        {
            Cnf_DataFree( pCnfOn );
            Cnf_DataFree( pCnfOff );
            sat_solver_delete( pSat );
            return NULL;
        }
    }

    // add PI clauses
    // collect the common variables
    vVarsAB = Vec_IntAlloc( Aig_ManCiNum(pManOn) );
    if ( fRelation )
        Vec_IntPush( vVarsAB, iLast );

    Aig_ManForEachCi( pManOn, pObj, i )
    {
        Vec_IntPush( vVarsAB, pCnfOn->pVarNums[pObj->Id] );
        pObj2 = Aig_ManCi( pManOff, i );

        Lits[0] = toLitCond( pCnfOn->pVarNums[pObj->Id], 0 );
        Lits[1] = toLitCond( pCnfOff->pVarNums[pObj2->Id], 1 );
        if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
            assert( 0 );
        Lits[0] = toLitCond( pCnfOn->pVarNums[pObj->Id], 1 );
        Lits[1] = toLitCond( pCnfOff->pVarNums[pObj2->Id], 0 );
        if ( !sat_solver_addclause( pSat, Lits, Lits+2 ) )
            assert( 0 );
    }
    Cnf_DataFree( pCnfOn );
    Cnf_DataFree( pCnfOff );
    sat_solver_store_mark_roots( pSat );

/*
    status = sat_solver_simplify(pSat);
    if ( status == 0 )
    {
        Vec_IntFree( vVarsAB );
        Cnf_DataFree( pCnfOn );
        Cnf_DataFree( pCnfOff );
        sat_solver_delete( pSat );
        return NULL;
    }
*/

    // solve the problem
    status = sat_solver_solve( pSat, NULL, NULL, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
Sat_Time += Abc_Clock() - clk;
    if ( status == l_False )
    {
        pSatCnf = sat_solver_store_release( pSat );
//        printf( "unsat\n" );
    }
    else if ( status == l_True )
    {
//        printf( "sat\n" );
    }
    else
    {
//        printf( "undef\n" );
    }
    sat_solver_delete( pSat );
    if ( pSatCnf == NULL )
    {
        printf( "The SAT problem is not unsat.\n" );
        Vec_IntFree( vVarsAB );
        return NULL;
    }

    // create the resulting manager
clk = Abc_Clock();
    pManInter = Inta_ManAlloc();
    pRes = (Aig_Man_t *)Inta_ManInterpolate( pManInter, (Sto_Man_t *)pSatCnf, 0, vVarsAB, fVerbose );
    Inta_ManFree( pManInter );
Inter_Time += Abc_Clock() - clk;
/*
    // test UNSAT core computation
    {
        Intp_Man_t * pManProof;
        Vec_Int_t * vCore;
        pManProof = Intp_ManAlloc();
        vCore = Intp_ManUnsatCore( pManProof, pSatCnf, 0 );
        Intp_ManFree( pManProof );
        Vec_IntFree( vCore );
    }
*/
    Vec_IntFree( vVarsAB );
    Sto_ManFree( (Sto_Man_t *)pSatCnf );

//    Ioa_WriteAiger( pRes, "inter2.aig", 0, 0 );
    return pRes;
}


int sat_solver_store_change_last( sat_solver * s )
{
    if ( s->pStore ) return Sto_ManChangeLastClause( (Sto_Man_t *)s->pStore );
    return -1;
}


void showMap(map<int, set<string> > &string_map, string whoami)
{
	cout << endl << whoami << "\n***************\n";

	for(map<int, set<string> >::iterator string_map_it = string_map.begin(); string_map_it != string_map.end(); string_map_it++)
	{
		cout << string_map_it->first << " -> ";
		
		set<string> string_set = string_map_it->second;
		for(set<string>::iterator string_it = string_set.begin(); string_it != string_set.end(); string_it++)
		{
			cout << *string_it << ", ";
		}
		
		cout << endl;
	}
}


void showMap(map<string, Aig_Obj_t*> &replacement_map, string whoami, Aig_Man_t* aig_manager, map<string, int> &var_name_to_var_index_map)
{
	cout << endl << whoami << "\n***************\n";

	for(map<string, Aig_Obj_t*>::iterator replacement_map_it = replacement_map.begin(); replacement_map_it != replacement_map.end(); replacement_map_it++)
	{
		string source_string = replacement_map_it->first;
		int source_int = searchVarNameToVarIndexMap(var_name_to_var_index_map, source_string);
		if(source_int != -1)
		{
			cout << source_int << " -> ";
		}
		else
		{
			cout << source_string << " -> ";
		}
		
		Aig_Obj_t* connection_object = replacement_map_it->second;
		int Ci_id = Aig_ObjId(connection_object); 
		map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(Ci_id);

		string Ci_name;
		if(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end())
		{
			Ci_name = Ci_id_to_Ci_name_map_it->second;
		}
		else if(connection_object == createTrue(aig_manager))
		{
			Ci_name = "true"; 
		}
		else
		{
			cout << "\nUnallowed object inside showMap!!\n";
			assert(false);
		}
		
		cout << Ci_name << endl;
	}
}


void showMap(map<int, Aig_Obj_t*> &replacement_map, string whoami, Aig_Man_t* aig_manager, map<string, int> &var_name_to_var_index_map)
{
	cout << endl << whoami << "\n***************\n";

	for(map<int, Aig_Obj_t*>::iterator replacement_map_it = replacement_map.begin(); replacement_map_it != replacement_map.end(); replacement_map_it++)
	{
		cout << replacement_map_it->first << " -> ";
		
		Aig_Obj_t* connection_object = replacement_map_it->second;
		int Ci_id = Aig_ObjId(connection_object); 
		map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(Ci_id);

		string Ci_name;
		if(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end())
		{
			Ci_name = Ci_id_to_Ci_name_map_it->second;
		}
		else if(connection_object == createTrue(aig_manager))
		{
			Ci_name = "true"; 
		}
		else
		{
			cout << "\nUnallowed object inside showMap!!\n";
			assert(false);
		}
		
		cout << Ci_name << endl;
	}
}


void showVector(vector<int> &integer_vector, string who_am_i)
{
	cout << endl << endl << who_am_i << endl << endl;

	for(vector<int>::iterator integer_it = integer_vector.begin(); integer_it != integer_vector.end(); integer_it++)
	{
		cout << *integer_it << ", ";
	}

	cout << endl;
}



void showSolverStatus(sat_solver* pSat_for_incremental_solving)
{
	cout << endl << "#Variables = " << sat_solver_nvars(pSat_for_incremental_solving);
	cout << "\t" << "#Clauses = "   << sat_solver_nclauses(pSat_for_incremental_solving);
	cout << endl;
}



bool isExactnessCheckSatisfiable(Aig_Man_t* aig_manager, Aig_Obj_t* increment, map<string, int> &Model, unsigned long long int &cnf_time, int &formula_size, unsigned long long int &simplification_time, vector<Aig_Obj_t*> &positive_assumptions_in_exactness_check, vector<Aig_Obj_t*>  &negative_assumptions_in_exactness_check, sat_solver* pSat_for_incremental_solving, t_HashTable<int, int> & IncrementalLabelTable, int &IncrementalLabelCount, map<string, int> &Ci_name_to_Ci_label_map, map<int, string> &Ci_label_to_Ci_name_map)
{
	// Add the clauses from increment (unless it is NULL) to the solver pSat_for_incremental_solving
	simplification_time = 0;
	times_in_aig_simplification_in_cegar.push_back(simplification_time);
	
	assert(increment != NULL);

	// increment is an internal node
	// connect increment to a CO, increment_CO
	// to avoid unauthorized cleanup

	Aig_Obj_t* increment_CO = Aig_ObjCreateCo( aig_manager, increment );
	assert(increment_CO != NULL);
	intermediate_cos_created.insert(increment_CO);
	
	formula_size = computeSize(increment, aig_manager);
	sizes_of_exactness_formulae_in_cegar.push_back(formula_size);

	//cout << "\nformula_size = " << formula_size << endl;

	#ifdef DEBUG_SKOLEM
		cout << "\nSetting nvars to " << formula_size + IncrementalLabelCount << endl;
	#endif

	sat_solver_setnvars(pSat_for_incremental_solving, formula_size + IncrementalLabelCount );

	#ifdef DEBUG_SKOLEM
		showSolverStatus(pSat_for_incremental_solving);
		cout << "\nAdding clauses from increment to sat-solver\n";
	#endif

	struct timeval cnf_start_ms, cnf_finish_ms;
	gettimeofday (&cnf_start_ms, NULL);

	//cout << "\nAdding clauses from increment to sat-solver\n";

	addIncrementToExactnessCheck(aig_manager, increment, pSat_for_incremental_solving, IncrementalLabelTable, IncrementalLabelCount, Ci_name_to_Ci_label_map, Ci_label_to_Ci_name_map);

	//cout << "\nClauses added to sat-solver\n";

	#ifdef DEBUG_SKOLEM
		cout << "\nClauses added to sat-solver\n";
		showSolverStatus(pSat_for_incremental_solving);
	#endif
		
	gettimeofday (&cnf_finish_ms, NULL);
	cnf_time = cnf_finish_ms.tv_sec * 1000 + cnf_finish_ms.tv_usec / 1000;
	cnf_time -= cnf_start_ms.tv_sec * 1000 + cnf_start_ms.tv_usec / 1000;
	times_in_cnf_generation_in_cegar.push_back(cnf_time);

	// Check if the present set of clauses gives satisfiable under
	// positive_assumptions_in_exactness_check and negative_assumptions_in_exactness_check
	
	
	unsigned long long int solver_ms;
	struct timeval solver_start_ms, solver_finish_ms;
	gettimeofday (&solver_start_ms, NULL); 

	//cout << "\nCalling the sat-solver\n";

	bool return_value;
	
	int trivially_unsat = 1;

	if(apply_solver_simplify_in_incremental_sat)
	{
		//cout << "\nApplying simplification of CNF\n";
		trivially_unsat = sat_solver_simplify(pSat_for_incremental_solving);
	}

	if(trivially_unsat == 0)
	{
		//cout << "\nFormula is trivially unsat\n";
		Model.clear();
		return_value = false;
	}
	else
	{
		#ifdef DEBUG_SKOLEM
			cout << "\nCreating assumptions\n";
		#endif
		// Create assumptions
		Vec_Int_t *    vAssumptions;
		vAssumptions = Vec_IntAlloc( positive_assumptions_in_exactness_check.size() + negative_assumptions_in_exactness_check.size() );

		// for positive assumptions
		#ifdef DEBUG_SKOLEM
			cout << "\nPositive assumptions\n";
		#endif
		for(int assumption_it = 0; assumption_it < positive_assumptions_in_exactness_check.size(); assumption_it++)
		{
			Aig_Obj_t* assumption_obj = positive_assumptions_in_exactness_check[assumption_it];
			int assumption_obj_id = Aig_ObjId(assumption_obj); 

			map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(assumption_obj_id);
			assert(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end());
			string assumption_name = Ci_id_to_Ci_name_map_it->second;			

			map<string, int>::iterator Ci_name_to_Ci_label_map_it = Ci_name_to_Ci_label_map.find(assumption_name);
			if(Ci_name_to_Ci_label_map_it == Ci_name_to_Ci_label_map.end()) // assumption_name is not 
			// present in the clauses with pSat_for_incremental_solving (may be due to simplifications)
			{
				// do nothing
			}
			else
			{
				int assumption_label = Ci_name_to_Ci_label_map_it->second;
				int assumption_lit = toLitCond( assumption_label, 0 );
				Vec_IntPush( vAssumptions, assumption_lit );

				#ifdef DEBUG_SKOLEM
					cout << "\nname = " << assumption_name << "\tlabel = " << assumption_label << "\tlit = " << assumption_lit;
				#endif
			}			
		}
		
		// for negative assumptions
		#ifdef DEBUG_SKOLEM
			cout << "\nNegative assumptions\n";
		#endif
		for(int assumption_it = 0; assumption_it < negative_assumptions_in_exactness_check.size(); assumption_it++)
		{
			Aig_Obj_t* assumption_obj = negative_assumptions_in_exactness_check[assumption_it];
			int assumption_obj_id = Aig_ObjId(assumption_obj); 

			map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(assumption_obj_id);
			assert(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end());
			string assumption_name = Ci_id_to_Ci_name_map_it->second;			

			map<string, int>::iterator Ci_name_to_Ci_label_map_it = Ci_name_to_Ci_label_map.find(assumption_name);
			if(Ci_name_to_Ci_label_map_it == Ci_name_to_Ci_label_map.end()) // assumption_name is not 
			// present in the clauses with pSat_for_incremental_solving (may be due to simplifications)
			{
				// do nothing
			}
			else
			{
				int assumption_label = Ci_name_to_Ci_label_map_it->second;
				int assumption_lit = toLitCond( assumption_label, 1 );
				Vec_IntPush( vAssumptions, assumption_lit );

				#ifdef DEBUG_SKOLEM
					cout << "\nname = " << assumption_name << "\tlabel = " << assumption_label << "\tlit = " << assumption_lit;
				#endif
			}			
		}
		
		if(perform_cegar_on_arbitrary_boolean_formulas && cluster_global_time_out_enabled)
		// This is a case where we are finding Skolem functions for arbitrary Boolean formulas and 
		// we would like to have a graceful time-out. This is the only case where we set time-out
		// with sat_solver_solve
		{
			time_t present_machine_time;
			time(&present_machine_time);

			time_t elapsed_machine_time;
			elapsed_machine_time = present_machine_time - cluster_global_time_out_start;
		
			time_t remaining_machine_time;
			remaining_machine_time = cluster_global_time_out - elapsed_machine_time;

			abctime sat_solver_timeout_time = (((abctime)remaining_machine_time) * CLOCKS_PER_SEC) + Abc_Clock();	
			sat_solver_set_runtime_limit(pSat_for_incremental_solving, sat_solver_timeout_time);

			#ifdef DEBUG_SKOLEM
			cout << "\nsat_solver_set_runtime_limit called with abctime = " << sat_solver_timeout_time <<" ,i.e., remaining_machine_time = " << remaining_machine_time << endl;
			#endif
		}
		
		#ifdef DEBUG_SKOLEM
			pSat_for_incremental_solving->verbosity = 2;
		#endif

		// call sat_solver_solve under assumptions

		//cout << "\nsat_solver_solve called\n";

		#ifdef DEBUG_SKOLEM
			cout << "\ncall sat_solver_solve under assumptions\n";
			showSolverStatus(pSat_for_incremental_solving);
		#endif

		int status = sat_solver_solve( pSat_for_incremental_solving, Vec_IntArray(vAssumptions), Vec_IntArray(vAssumptions) + Vec_IntSize(vAssumptions), (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );

		#ifdef DEBUG_SKOLEM
			cout << "\nsat_solver_solve called under assumptions\n";
			showSolverStatus(pSat_for_incremental_solving);
		#endif

		if ( status == l_False )
		{
			//cout << "\nFormula is unsat\n";
			Model.clear();
			return_value = false;
		}
		else if ( status == l_True )
		{
			//cout << "\nFormula is sat; get the model\n";  

			// get the model

			/* Get the array of labels of CIs ordered as per Ci_name_to_Ci_label_map */
			Vec_Int_t * vCiIds = collectPiSatNums(Ci_name_to_Ci_label_map);

			/* Get the model from sat-solver ordered as per Ci_name_to_Ci_label_map */
			int * pModel = Sat_SolverGetModel( pSat_for_incremental_solving, vCiIds->pArray, vCiIds->nSize );
			
			int model_location = 0;
			for(map<string, int>::iterator Ci_name_to_Ci_label_map_it = Ci_name_to_Ci_label_map.begin(); Ci_name_to_Ci_label_map_it != Ci_name_to_Ci_label_map.end(); Ci_name_to_Ci_label_map_it++)
			{
				string Ci_name = Ci_name_to_Ci_label_map_it->first;
				int Ci_value = pModel[model_location];

				#ifdef DEBUG_SKOLEM
					cout << "\nCi name = " << Ci_name << "\tCi value = " << Ci_value;
				#endif

				Model.insert(make_pair(Ci_name, Ci_value));
				model_location++;
			}

			return_value = true; 
		
			free(pModel);	//Added by SS
			Vec_IntFree(vCiIds); //Added by SS          
		}
		else
		{
			assert( status == l_Undef );

			if(perform_cegar_on_arbitrary_boolean_formulas && cluster_global_time_out_enabled)
			{
				#ifdef DEBUG_SKOLEM
				cout << "\nWarning!!Time-out inside SAT solver\n";
				#endif
				cluster_global_timed_out = true; // cluster_global_timed_out flag set
				return_value = true; // it can be anything!! will be caught by the caller!
			}
			else
			{
				cout << "\nUnknown value " << status <<" returned from solver inside helper.cc::isExactnessCheckSatisfiable\n";
				assert(false);
			}
		}
		
		Vec_IntFree(vAssumptions); //Added by SS
	
	}// else of if(trivially_unsat == 0) ends here

	//cout << "\nSat-solver called\n";

	gettimeofday (&solver_finish_ms, NULL);
	solver_ms = solver_finish_ms.tv_sec * 1000 + solver_finish_ms.tv_usec / 1000;
	solver_ms -= solver_start_ms.tv_sec * 1000 + solver_start_ms.tv_usec / 1000;
	//cout << "\ninternal solver finished in " << solver_ms << " milliseconds\n";
	times_in_sat_solving_in_cegar.push_back(solver_ms);

	total_time_in_sat_solving_in_cegar = total_time_in_sat_solving_in_cegar + solver_ms;

	if(return_value)
	{
		total_time_in_true_sat_solving_in_cegar = total_time_in_true_sat_solving_in_cegar + solver_ms;
	}
	else
	{
		total_time_in_false_sat_solving_in_cegar = total_time_in_false_sat_solving_in_cegar + solver_ms;
	}

	return return_value;	
}



/* Returns the array of labels of CIs ordered as per Ci_name_to_Ci_label_map */
Vec_Int_t * collectPiSatNums(map<string, int> &Ci_name_to_Ci_label_map)
{
	Vec_Int_t * vCiIds;
	vCiIds = Vec_IntAlloc( Ci_name_to_Ci_label_map.size() );
	for(map<string, int>::iterator Ci_name_to_Ci_label_map_it = Ci_name_to_Ci_label_map.begin(); Ci_name_to_Ci_label_map_it != Ci_name_to_Ci_label_map.end(); Ci_name_to_Ci_label_map_it++)
	{
		Vec_IntPush( vCiIds, Ci_name_to_Ci_label_map_it->second );
	}
    	return vCiIds;
}



void addIncrementToExactnessCheck(Aig_Man_t* aig_manager, Aig_Obj_t* increment, sat_solver* pSat_for_incremental_solving, t_HashTable<int, int> & IncrementalLabelTable, int &IncrementalLabelCount, map<string, int> &Ci_name_to_Ci_label_map, map<int, string> &Ci_label_to_Ci_name_map)
{
	// Add the clauses from increment to the solver pSat_for_incremental_solving
	assert(increment != NULL);

	#ifdef DEBUG_SKOLEM
		cout << "\naddCNF called\n";
	#endif

	int increment_label = addCNF(aig_manager, increment, pSat_for_incremental_solving, IncrementalLabelTable, IncrementalLabelCount, Ci_name_to_Ci_label_map, Ci_label_to_Ci_name_map);

	#ifdef DEBUG_SKOLEM
		cout << "\nroot encountered\n";
	#endif

	#ifdef DEBUG_SKOLEM
		cout << "\nAdding clauses for (" << increment_label << ")" << endl;
	#endif

	// assert that the root node is true/false
	sat_solver_add_const(pSat_for_incremental_solving, increment_label, Aig_IsComplement(increment));		
}


int addCNF(Aig_Man_t* aig_manager, Aig_Obj_t* formula, sat_solver* pSat_for_incremental_solving, t_HashTable<int, int> & IncrementalLabelTable, int &IncrementalLabelCount, map<string, int> &Ci_name_to_Ci_label_map, map<int, string> &Ci_label_to_Ci_name_map)
{
	formula = Aig_Regular(formula);
	int key = Aig_ObjId(formula);

	#ifdef DEBUG_SKOLEM
		//cout << "\nformula = " << formula << "\tkey = " << key << endl;
	#endif

	t_HashTable<int, int>::iterator LabelTable_it = IncrementalLabelTable.find(key);
	if (LabelTable_it != IncrementalLabelTable.end()) // label exists already, i.e. traversed already
	{
		#ifdef DEBUG_SKOLEM
			//cout << "\nExists in hashtable\n";
		#endif

		return LabelTable_it.getValue();;
	}
	else
	{
		int node_label = IncrementalLabelCount;
		IncrementalLabelTable[key] = IncrementalLabelCount;
		IncrementalLabelCount++;

		if(formula->Type == AIG_OBJ_AND)// child_1 \wedge child_2 encountered
		{
			#ifdef DEBUG_SKOLEM
				//cout << "\nAIG_OBJ_AND encountered\n";
			#endif

			int child_1_label = addCNF(aig_manager, Aig_ObjChild0(formula), pSat_for_incremental_solving, IncrementalLabelTable, IncrementalLabelCount, Ci_name_to_Ci_label_map, Ci_label_to_Ci_name_map);
			int child_2_label = addCNF(aig_manager, Aig_ObjChild1(formula), pSat_for_incremental_solving, IncrementalLabelTable, IncrementalLabelCount, Ci_name_to_Ci_label_map, Ci_label_to_Ci_name_map);

			#ifdef DEBUG_SKOLEM
				//cout << "\nAdding clauses for (" << node_label << ", " << child_1_label << ", " << child_2_label << ")" << endl;
			#endif

			sat_solver_add_and(pSat_for_incremental_solving, node_label, child_1_label, child_2_label, Aig_ObjFaninC0(formula), Aig_ObjFaninC1(formula), 0);			
		}
		else if(formula->Type == AIG_OBJ_CI) //CI encountered
		{
			#ifdef DEBUG_SKOLEM
				//cout << "\nAIG_OBJ_CI encountered\n";
			#endif

			map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(key);
			assert(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end());
			string Ci_name = Ci_id_to_Ci_name_map_it->second;

			#ifdef DEBUG_SKOLEM
				//cout << "\nCi_name = " << Ci_name << endl;
			#endif			

			Ci_name_to_Ci_label_map.insert(make_pair(Ci_name, node_label));
			Ci_label_to_Ci_name_map.insert(make_pair(node_label, Ci_name));
		}
		else if(formula->Type == AIG_OBJ_CONST1) // 1 encountered
		{
			#ifdef DEBUG_SKOLEM
				//cout << "\nAIG_OBJ_CONST1 encountered\n";
			#endif

			#ifdef DEBUG_SKOLEM
				//cout << "\nAdding clauses for (" << node_label << ")" << endl;
			#endif
		
			sat_solver_add_const(pSat_for_incremental_solving, node_label, 0 );			
		}		
		else if(formula->Type == AIG_OBJ_CO) //CO encountered
		{
			#ifdef DEBUG_SKOLEM
				//cout << "\nAIG_OBJ_CO encountered\n";
			#endif

			// do nothing
		}
		else
		{
			cout << "\nUnknown formula->Type encountered in helper.cpp::addCNF\n";		
			assert(false);
		}

		return node_label;
	} // if(!label exists already) ends here
}//function ends here				




void showVariableWiseValueMap()
{
	cout << endl << "values_of_variables_from_bad_to_var" << "\n***************\n";

	for(map<int, map<int, int> >::iterator values_of_variables_from_bad_to_var_it = values_of_variables_from_bad_to_var.begin(); values_of_variables_from_bad_to_var_it != values_of_variables_from_bad_to_var.end(); values_of_variables_from_bad_to_var_it++)
	{
		cout << endl << "variable_index = " << values_of_variables_from_bad_to_var_it->first << ":" << endl;
		map<int, int> replacement_map = values_of_variables_from_bad_to_var_it->second;
		
		for(map<int, int>::iterator replacement_map_it = replacement_map.begin(); replacement_map_it != replacement_map.end(); replacement_map_it++)
		{
			cout << replacement_map_it->first << "\t" << replacement_map_it->second << endl;
		}

	}
	
	cout << endl;	
}



void showMap(map<int, int> &replacement_map, string whoami)
{
	cout << endl << whoami << "\n***************\n";

	for(map<int, int>::iterator replacement_map_it = replacement_map.begin(); replacement_map_it != replacement_map.end(); replacement_map_it++)
	{
		cout << replacement_map_it->first << "\t" << replacement_map_it->second << endl;
	}
	
	cout << endl;
}


void showMap(map<int, string> &my_map, string whoami)
{
	cout << endl << whoami << "\n***************\n";

	for(map<int, string>::iterator my_map_it = my_map.begin(); my_map_it != my_map.end(); my_map_it++)
	{
		cout << my_map_it->first << "\t" << my_map_it->second << endl;
	}
	
	cout << endl;
}



void showYMap()
{
	for(map<string, int>::iterator values_of_Y_variables_it = values_of_Y_variables.begin(); values_of_Y_variables_it != values_of_Y_variables.end(); values_of_Y_variables_it++)
	{
		cout << values_of_Y_variables_it->first << "\t" << values_of_Y_variables_it->second << endl;
	}
	
	cout << endl;
}


void printMap(map<int, int> &replacement_map, string whoami, FILE *fp)
{
	fprintf(fp, "\n%s\n***************\n", whoami.c_str());

	for(map<int, int>::iterator replacement_map_it = replacement_map.begin(); replacement_map_it != replacement_map.end(); replacement_map_it++)
	{
		fprintf(fp, "%d\t%d\n", replacement_map_it->first, replacement_map_it->second);
	}
	
	fprintf(fp, "\n");
}


void printYMap(FILE *fp)
{
	for(map<string, int>::iterator values_of_Y_variables_it = values_of_Y_variables.begin(); values_of_Y_variables_it != values_of_Y_variables.end(); values_of_Y_variables_it++)
	{
		fprintf(fp, "%s\t%d\n", (values_of_Y_variables_it->first).c_str(), values_of_Y_variables_it->second);
	}
	
	fprintf(fp, "\n");
}



void unsatCore(Aig_Man_t* aig_manager, Aig_Obj_t* formula, set<Aig_Obj_t*> &positive_variables, set<Aig_Obj_t*> &negative_variables, set<string> &variables_in_unsat_core)
{
	set<Aig_Obj_t*> positive_variable_COs;
	for(set<Aig_Obj_t*>::iterator positive_variables_it = positive_variables.begin(); positive_variables_it != positive_variables.end(); positive_variables_it++)
	{
		Aig_Obj_t* positive_variable = *positive_variables_it;
		Aig_Obj_t* positive_variable_CO = Aig_ObjCreateCo( aig_manager, positive_variable );
		assert(positive_variable_CO != NULL);
		positive_variable_COs.insert(positive_variable_CO);
	}
	
	set<Aig_Obj_t*> negative_variable_COs;
	for(set<Aig_Obj_t*>::iterator negative_variables_it = negative_variables.begin(); negative_variables_it != negative_variables.end(); negative_variables_it++)
	{
		Aig_Obj_t* negative_variable = *negative_variables_it;
		Aig_Obj_t* negative_variable_CO = Aig_ObjCreateCo( aig_manager, negative_variable );
		assert(negative_variable_CO != NULL);
		negative_variable_COs.insert(negative_variable_CO);
	}	

	assert(formula != NULL);
	Aig_Obj_t* formula_CO;
	// formula is an internal node
	// connect formula to a CO, formula_CO
	formula_CO = Aig_ObjCreateCo( aig_manager, formula );
	assert(formula_CO != NULL);
	
	// derive CNF
	Cnf_Dat_t* pCnf = Cnf_Derive( aig_manager, Aig_ManCoNum(aig_manager) ); 
	// showing CNF
	bool show_cnf = false;
	if(show_cnf)
	{
		char cnf_file[100];
		strcpy(cnf_file, "unsat_formula.cnf");
		Cnf_DataWriteIntoFile(pCnf, cnf_file, 0, (Vec_Int_t *)0, (Vec_Int_t *)0);
	}

	sat_solver2* pSat = sat_solver2_new();
	
	sat_solver2_setnvars( pSat, pCnf->nVars );

	int Clause_id_in_Cnf;
	int Number_of_clauses_from_formula;
	for (int i = 0; i < pCnf->nClauses; i++ )
	{
		Clause_id_in_Cnf = i+1;
		if ( !sat_solver2_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1], Clause_id_in_Cnf ) )
		{
	    		assert( false );
		}
		//cout << "Clause " << Clause_id_in_Cnf << ": ";	
		//int *pLit, *pStop;
		//for ( pLit = pCnf->pClauses[i], pStop = pCnf->pClauses[i+1]; pLit < pStop; pLit++ )
		//{
		//	printf("%d ", (*pLit & 1)? -(*pLit >> 1)-1 : (*pLit >> 1)+1);
		//}
		//printf("0\n" );		
	}
	Number_of_clauses_from_formula = Clause_id_in_Cnf+1;
	printf( "Unsatcore CNF: Variables = %6d. Clauses = %7d. Literals = %8d. ", pCnf->nVars, pCnf->nClauses, pCnf->nLiterals );

	vector<int> Clause_ids_from_variables;
	for(set<Aig_Obj_t*>::iterator positive_variable_COs_it = positive_variable_COs.begin(); positive_variable_COs_it != positive_variable_COs.end(); positive_variable_COs_it++)
	{
		Clause_id_in_Cnf++;

		Aig_Obj_t* positive_variable_CO = *positive_variable_COs_it;
		assert(positive_variable_CO != NULL);
		
		lit positive_variable_Lits[1];
		positive_variable_Lits[0] = toLitCond( pCnf->pVarNums[positive_variable_CO->Id], 0 );
		int clause_added = sat_solver2_addclause( pSat, positive_variable_Lits, positive_variable_Lits + 1, Clause_id_in_Cnf );
		assert(clause_added);

		Clause_ids_from_variables.push_back(positive_variable_Lits[0]);

		//cout << "Positive clause " << Clause_id_in_Cnf << ": ";
		//printf("%d 0\n", (positive_variable_Lits[0] & 1)? -(positive_variable_Lits[0] >> 1)-1 : (positive_variable_Lits[0] >> 1)+1);	
	}

	for(set<Aig_Obj_t*>::iterator negative_variable_COs_it = negative_variable_COs.begin(); negative_variable_COs_it != negative_variable_COs.end(); negative_variable_COs_it++)
	{
		Clause_id_in_Cnf++;

		Aig_Obj_t* negative_variable_CO = *negative_variable_COs_it;
		assert(negative_variable_CO != NULL);
		
		lit negative_variable_Lits[1];
		negative_variable_Lits[0] = toLitCond( pCnf->pVarNums[negative_variable_CO->Id], 1 );
		int clause_added = sat_solver2_addclause( pSat, negative_variable_Lits, negative_variable_Lits + 1, Clause_id_in_Cnf );
		assert(clause_added);

		Clause_ids_from_variables.push_back(negative_variable_Lits[0]);

		//cout << "Negative clause " << Clause_id_in_Cnf << ": ";
		//printf("%d 0\n", (negative_variable_Lits[0] & 1)? -(negative_variable_Lits[0] >> 1)-1 : (negative_variable_Lits[0] >> 1)+1);	
	}


	int Lit = toLitCond( pCnf->pVarNums[formula_CO->Id], 0 );
	cout << "\nLiteral added is " << lit_print(Lit) << endl;

	int blocks_to_allocate = 20;
	pSat->pPrf1 = Vec_SetAlloc( blocks_to_allocate );
	pSat->verbosity = 2;	
	int status = sat_solver2_solve( pSat, &Lit, &Lit + 1, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );
	assert( status == l_False );
	cout << "\nformula is unsat\n";
		

	// Derive the unsat core
	cout << "\nDeriving the unsat core\n";
	assert(pSat->pPrf1 != NULL);
	Vec_Int_t * vCore;
	vCore = (Vec_Int_t *)Sat_ProofCore( pSat );
	assert(vCore != NULL);
	cout << "\nUnsat core\n";
	Vec_IntPrint( vCore );

	//cout << "\nClauses in unsat core\n";
	int vCore_it, Clause_id;
	Vec_IntForEachEntry( vCore, Clause_id, vCore_it )
	{
		if(Clause_id < Number_of_clauses_from_formula)
		{
			int Clause_location = Clause_id-1;
			
			//int *pLit, *pStop;
			//for ( pLit = pCnf->pClauses[Clause_location], pStop = pCnf->pClauses[Clause_location+1]; pLit < pStop; pLit++ )
			//{
			//	printf("%d ", (*pLit & 1)? -(*pLit >> 1)-1 : (*pLit >> 1)+1);
			//}
		        //
			//printf("0\n" );	
		}
		else
		{
			int Clause_location = Clause_id-Number_of_clauses_from_formula;
			int Var_Lit = Clause_ids_from_variables[Clause_location];
			//printf("%d 0\n", (Var_Lit & 1)? -(Var_Lit >> 1)-1 : (Var_Lit >> 1)+1);
		}	
	}
	//printf("%d 0\n", lit_print(Lit));


	cout << "\nLabels of variables in unsat core\n";
	set<int> variable_labels;
	Vec_IntForEachEntry( vCore, Clause_id, vCore_it )
	{
		if(Clause_id < Number_of_clauses_from_formula)
		{
			int Clause_location = Clause_id-1;
			
			int *pLit, *pStop;
			for ( pLit = pCnf->pClauses[Clause_location], pStop = pCnf->pClauses[Clause_location+1]; pLit < pStop; pLit++ )
			{
				int variable_label = *pLit >> 1;
				variable_labels.insert(variable_label);
			} 
		}
		else
		{
			int Clause_location = Clause_id-Number_of_clauses_from_formula;
			int Var_Lit = Clause_ids_from_variables[Clause_location];
			int variable_label = Var_Lit >> 1;
			variable_labels.insert(variable_label);
		}
			
	}
	showSet(variable_labels, "variable_labels");

	
	cout << "\nVariables in unsat core\n";	
	int Ci_it;
	Aig_Obj_t* Ci_obj;
	Aig_ManForEachCi( aig_manager, Ci_obj, Ci_it )
	{
		int Ci_id = Ci_obj->Id;
		int Ci_label = pCnf->pVarNums[Ci_id];

		if(variable_labels.find(Ci_label) != variable_labels.end()) // Ci_label \in unsat_core
		{
			map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(Ci_id);
			assert(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end());
			string Ci_name = Ci_id_to_Ci_name_map_it->second;
			
			variables_in_unsat_core.insert(Ci_name);
		}	
	}
        showSet(variables_in_unsat_core, "variables_in_unsat_core");
	

	sat_solver2_delete( pSat );
	Cnf_DataFree( pCnf );	
	
}




void obtainFactorsAndVariablesToEliminatFromQdimacsFile(ABC* abcObj, Abc_Frame_t* abcFrame, set<Aig_Obj_t*> &Factors, Aig_Man_t* &aig_manager, list<string> &VariablesToEliminate)
{
	set<int> forall_variables;
	set<int> exists_variables;

	assert(benchmark_name != "");

	#ifdef DEBUG_SKOLEM
	cout << "\nbenchmark_name = " << benchmark_name << endl;
	#endif

	aig_manager = Aig_ManStart(0);//start the manager

	FILE *fptr = fopen (benchmark_name.c_str(), "r");
	assert(fptr != NULL);

	char C[100], c;
	int numVar, numClauses, tmpVar, i;	
	fscanf (fptr, "%c", &c);
	fscanf (fptr, "%s", C);
	while (strcmp (C, "cnf") != 0)
	{
		fscanf (fptr, "%s", C);
	}
	fscanf(fptr, "%d %d", &numVar, &numClauses); // read first line p cnf numVar numClauses

	#ifdef DEBUG_SKOLEM
	cout << "\nnumber of variables = " << numVar << "\tnumber of clauses = " << numClauses << endl;
	#endif

	fscanf (fptr, "%c", &c);
	tmpVar = 1;
	while (c != 'a')
	{
		fscanf (fptr, "%c", &c);
	}
	while (tmpVar != 0)
	{
		fscanf(fptr, "%d", &tmpVar); 
		if(tmpVar != 0)
		{
			forall_variables.insert(tmpVar);
		}
	}

	#ifdef DEBUG_SKOLEM
	showSet(forall_variables, "forall_variables");
	#endif
			
	fscanf (fptr, "%c", &c);
	tmpVar = 1;
	while (c != 'e')
	{
		fscanf (fptr, "%c", &c);
	}
	while (tmpVar !=0)
	{
		fscanf(fptr, "%d", &tmpVar); 
		if(tmpVar != 0)
		{
			exists_variables.insert(tmpVar);
		}
	}

	#ifdef DEBUG_SKOLEM
	showSet(exists_variables, "exists_variables");
	#endif

	set<string> VariablesToEliminate_Set;
	vector<string> variable_names;
	
	//create the primary inputs
	for (i = 0; i < numVar; i++)
	{
		Aig_ObjCreateCi(aig_manager); // Create numVar primary inputs

		int variable_number = i+1;
		char variable_number_char[100];
		sprintf(variable_number_char, "%d", variable_number);
		string variable_number_string(variable_number_char);
		string variable_name = "x_";
		variable_name += variable_number_string;

		variable_names.push_back(variable_name);

		if(exists_variables.find(variable_number) != exists_variables.end()) //variable is to be eliminated
		{
		  VariablesToEliminate_Set.insert(variable_name);
		}

		Ci_name_to_Ci_number_map.insert(make_pair(variable_name, i));

		number_of_Cis++;
	}

	#ifdef DEBUG_SKOLEM
	showSet(VariablesToEliminate_Set, "VariablesToEliminate_Set");
	cout << endl << "Ci_name_to_Ci_number_map" << endl;
	for(map<string, int>::iterator map_it = Ci_name_to_Ci_number_map.begin(); map_it != Ci_name_to_Ci_number_map.end(); map_it++)
	{
		cout << map_it->first << "\t" << map_it->second << endl;
	}
	#endif

	#ifdef DEBUG_SKOLEM
	cout << endl << numVar << " variables created\n";
	cout << endl << VariablesToEliminate_Set.size() << " to be quantified\n";
	#endif

	// start reading the clauses
	Aig_Obj_t *pObj1, *pObj2, *pTemp, *pO, *pCo, *pOut;
	
	//pOut = Aig_ManConst1(aig_manager);
	//pO = Aig_ObjCreateCo(aig_manager, Aig_ManConst0(aig_manager)); //This is the primary output

	for ( i = 0; i < numClauses ; i++)
	{
		fscanf(fptr, "%d", &tmpVar);

		#ifdef DEBUG_SKOLEM
		cout << endl << tmpVar << " read\n";
		#endif 

		pObj1 = Aig_ManConst0(aig_manager);
		while (tmpVar != 0)
		{
			pObj2 = Aig_ManCi (aig_manager, abs(tmpVar)-1);
			if (tmpVar < 0)
				pObj1 = Aig_Or(aig_manager, pTemp = pObj1, Aig_Not(pObj2)); 			
			else
				pObj1 = Aig_Or(aig_manager, pTemp = pObj1, pObj2); 
			
			fscanf(fptr, "%d", &tmpVar); 

			#ifdef DEBUG_SKOLEM
			cout << endl << tmpVar << " read\n";
			#endif 
		}

		pCo = Aig_ObjCreateCo(aig_manager, pObj1); //Co for each factor
		//Add pObj1 as fanin to pCo
		
		#ifdef DEBUG_SKOLEM
		cout << endl << "Created factor " << i << endl;
		#endif 
		
		//pOut = Aig_And (aig_manager, pTemp = pOut, pObj1);
	}
	//Add pOut as fanin to pO
	//Aig_ObjPatchFanin0(aig_manager, pO, pOut);

	Aig_ManCleanup(aig_manager);
	Aig_ManCheck(aig_manager);
	//Aig_ManDumpBlif (pMan, "t.blif", NULL, NULL);
	//Aig_ManShow (pMan, 0, NULL);

	cout << endl << numClauses << " clauses created\n";
	
	// Note that we still need to do as done in 
	// obtainFactorsAndVariablesToEliminatFromHWMCCFile

	// reading the factors
	Aig_Obj_t* factorObj;
	i = 0;

	set<Aig_Obj_t*> ClausesInFactors;

    	Aig_ManForEachCo(aig_manager, factorObj, i )
    	{
		assert(factorObj != NULL);
		Aig_Obj_t* Fanin0_factorObj = Aig_ObjChild0(factorObj);		 
		// Note that it is important to use Aig_ObjChild0 here
		// Earlier Aig_ObjFanin0 was used; but Aig_ObjFanin0 regularizes the dag,
		// Aig_ObjChild0 does not regularize the dag		

		assert(Fanin0_factorObj != NULL);
		int clause_id = i+1;

		if(clause_id % number_of_clauses_per_factor_in_qdimacs_benchmark == 0)
		{
			ClausesInFactors.insert(Fanin0_factorObj);
			Aig_Obj_t* NewFactor = createAnd(ClausesInFactors, aig_manager);

			Factors.insert(NewFactor);
			ClausesInFactors.clear();
		}
		else
		{
			ClausesInFactors.insert(Fanin0_factorObj);
		}
    	}

	if(ClausesInFactors.size() > 0)
	{
		Aig_Obj_t* NewFactor = createAnd(ClausesInFactors, aig_manager);
		Factors.insert(NewFactor);
	}

        // Let's get the IDs of the variables
	Aig_Obj_t* variable_obj;
	vector<int> variable_ids;
	i = 0;
	Aig_ManForEachCi(aig_manager, variable_obj, i )
	{
		int Id = Aig_ObjId(variable_obj); // no need to apply Aig_Regular() as variable_obj is CI
		variable_ids.push_back(Id);

		string variable_name = 	variable_names[i];	
		if(VariablesToEliminate_Set.find(variable_name) != VariablesToEliminate_Set.end())
		// variable_name is a Ci to be eliminated
		{
			Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.insert(make_pair(variable_name, variable_obj));
			VariablesToEliminate.push_back(variable_name);
		}

		Ci_name_to_Ci_object_map.insert(make_pair(variable_name, variable_obj));
	}

	// Let's create the variable_id ---> variable_name map

	assert(variable_ids.size() == variable_names.size());	
	for(int i = 0; i < variable_ids.size(); i++)
	{
		Ci_id_to_Ci_name_map.insert(make_pair(variable_ids[i], variable_names[i]));
	}

	#ifdef DEBUG_SKOLEM
	cout << endl << "Ci_id_to_Ci_name_map" << endl;
	for(map<int, string>::iterator map_it = Ci_id_to_Ci_name_map.begin(); map_it != Ci_id_to_Ci_name_map.end(); map_it++)
	{
		cout << map_it->first << "\t" << map_it->second << endl;
	}
	#endif

	cout << endl << "Reading the Qdimacs file finished\n";

}




bool checkEquivalenceUsingQBFSolver(Aig_Obj_t* quantifier_eliminated_formula, Aig_Obj_t* quantified_formula, list<string> &quantifiers, Aig_Man_t* aig_manager)
{
	// ensure that 	quantifier_eliminated_formula \equiv \exists.quantifiers(quantified_formula)

	// step 1: ~quantifier_eliminated_formula \wedge quantified_formula is unsat

	Aig_Obj_t* equivalence_check_part_1;
	equivalence_check_part_1 = createAnd(createNot(quantifier_eliminated_formula, aig_manager), quantified_formula, aig_manager);
	assert(equivalence_check_part_1 != NULL);
	
	// Give to SAT-Solver
	unsigned long long int cnf_time;
	int formula_size;
	unsigned long long int simplification_time;
	map<string, int> Model_of_equivalence_check_part_1;
	bool result_of_equivalence_check_part_1 = isSat(aig_manager, equivalence_check_part_1, Model_of_equivalence_check_part_1, cnf_time, formula_size, simplification_time);

	
	if(result_of_equivalence_check_part_1)
	{
		cout << "\nexists X.f => f[X --> psi] is NOT valid\n";
		cout << "\nCounterexample is\n";
		displayModelFromSATSolver(Model_of_equivalence_check_part_1);
		return false;
	}
	else
	{
		//cout << "\nexists X.f => f[X --> psi] is valid\n";
	}


	if(prove_correctness_of_skolem_functions_of_conjunctions)
	{
		return true;
	}
	else
	{
		// step 2: exists remaining_variables. forall quantifiers. (quantifier_eliminated_formula \wedge ~quantified_formula) is unsat
	
		bool result_of_equivalence_check_part_2 = isQbfSat(quantifier_eliminated_formula, quantified_formula, quantifiers, aig_manager);
	
		if(result_of_equivalence_check_part_2)
		{
			cout << "\nf' => exists X.f is NOT valid\n";
			return false;
		}
		else
		{
			cout << "\nf' => exists X.f is valid\n";
		}

		return true;
	}
}



bool isQbfSat(Aig_Obj_t* quantifier_eliminated_formula, Aig_Obj_t* quantified_formula, list<string> &quantifiers, Aig_Man_t* aig_manager)
{
	set<string> variables_to_eliminate_set(quantifiers.begin(), quantifiers.end());
	#ifdef DEBUG_SKOLEM
	showSet(variables_to_eliminate_set, "variables_to_eliminate_set");
	#endif

	Aig_Obj_t* equivalence_check;
	equivalence_check = createAnd(createNot(quantified_formula, aig_manager), quantifier_eliminated_formula, aig_manager);
	assert(equivalence_check != NULL);
	
	Aig_Obj_t* equivalence_check_CO = Aig_ObjCreateCo( aig_manager, equivalence_check );
	assert(equivalence_check_CO != NULL);
	
	Cnf_Dat_t * pCnf = Cnf_Derive( aig_manager, Aig_ManCoNum(aig_manager) );
	        
	Vec_Int_t * vVarMap, * vForAlls, * vExists, * vTemp;
        Aig_Obj_t * pObj;

	int nPars;
	nPars = variables_to_eliminate_set.size();
	#ifdef DEBUG_SKOLEM
	cout << "\nnPars = " << nPars << endl;
	#endif

	string qdimacs_file = benchmark_name_without_extension;
	qdimacs_file += "_correctness_of_skolem_functions.qdimacs";

	string model_file = benchmark_name_without_extension;
	model_file += "_correctness_of_skolem_functions.txt";

	        
        int i, Entry;
        // create var map
        vVarMap = Vec_IntStart( pCnf->nVars );
        Aig_ManForEachCi( aig_manager, pObj, i )
	{
		int Ci_id = pObj->Id;

		map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(Ci_id);
		assert(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end());
		string Ci_name = Ci_id_to_Ci_name_map_it->second;
		
		#ifdef DEBUG_SKOLEM
		cout << "\nCi_id = " << Ci_id << "\tCi_name = " << Ci_name << endl;
		#endif
		
		if(variables_to_eliminate_set.find(Ci_name) != variables_to_eliminate_set.end()) //Ci_name
		// is a variable to be eliminated; hence to be universally quantified
		{
			#ifdef DEBUG_SKOLEM
			cout << endl << Ci_name << " is a variable to be eliminated; hence to be universally quantified\n";
			#endif
                	Vec_IntWriteEntry( vVarMap, pCnf->pVarNums[Ci_id], 1 );
		}
		else //Ci_name is a variable to remain; hence to be ex.quantified
		{
			#ifdef DEBUG_SKOLEM
			cout << endl << Ci_name << " is a variable to remain; hence to be ex.quantified\n";
			#endif
                	Vec_IntWriteEntry( vVarMap, pCnf->pVarNums[Ci_id], 2 );
		}
	}

        // create various maps
        vForAlls = Vec_IntAlloc( nPars );	
        vExists = Vec_IntAlloc( Aig_ManCiNum(aig_manager) - nPars );
	vTemp = Vec_IntAlloc( pCnf->nVars - Aig_ManCiNum(aig_manager));

	#ifdef DEBUG_SKOLEM
	cout << "\nnPars = " << nPars << endl;
	cout << "\nAig_ManCiNum(aig_manager) - nPars = " << Aig_ManCiNum(aig_manager) - nPars << endl;
	cout << "\npCnf->nVars - Aig_ManCiNum(aig_manager) = " << pCnf->nVars - Aig_ManCiNum(aig_manager) << endl;
	#endif

        Vec_IntForEachEntry( vVarMap, Entry, i )
	{
         	if ( Entry == 1)
		{
                	Vec_IntPush( vForAlls, i );

			#ifdef DEBUG_SKOLEM
			cout << endl << i << " inserted into vForAlls";
			#endif
		}
            	else if ( Entry == 2)
		{
                	Vec_IntPush( vExists, i );
			
			#ifdef DEBUG_SKOLEM
			cout << endl << i << " inserted into vExists";
			#endif
		}
		else
		{
                	Vec_IntPush( vTemp, i );

			#ifdef DEBUG_SKOLEM
			cout << endl << i << " inserted into vTemp";
			#endif			
		}
	}
        
	// write CNF in to file
	int * pLit, * pStop, VarId;
   	FILE *pFile = fopen( qdimacs_file.c_str(), "w" );
	assert(pFile != NULL);
	
	fprintf( pFile, "c Qdimacs file from correctness checking of skolem functions\n" );
    	fprintf( pFile, "p cnf %d %d\n", pCnf->nVars, pCnf->nClauses+1 );
	if ( vExists )
    	{
        	fprintf( pFile, "e " );
        	Vec_IntForEachEntry( vExists, VarId, i )
        	    fprintf( pFile, "%d ", VarId+1 );
        	fprintf( pFile, "0\n" );
    	}
	if ( vForAlls )
	{
		fprintf( pFile, "a " );
		Vec_IntForEachEntry( vForAlls, VarId, i )
		    fprintf( pFile, "%d ", VarId+1 );
		fprintf( pFile, "0\n" );
	}
	if ( vTemp )
	{
		fprintf( pFile, "e " );
		Vec_IntForEachEntry( vTemp, VarId, i )
		    fprintf( pFile, "%d ", VarId+1 );
		fprintf( pFile, "0\n" );
	}

	for ( i = 0; i < pCnf->nClauses; i++ )
	{
		for ( pLit = pCnf->pClauses[i], pStop = pCnf->pClauses[i+1]; pLit < pStop; pLit++ )
		    fprintf( pFile, "%d ", (*pLit & 1)? -(*pLit >> 1)-1 : (*pLit >> 1)+1);
		fprintf( pFile, "0\n" );
	}
	int rootLit = toLitCond( pCnf->pVarNums[equivalence_check_CO->Id], 0 );
	fprintf( pFile, "%d 0\n", (rootLit & 1)? -(rootLit >> 1)-1 : (rootLit >> 1)+1);
	fprintf( pFile, "\n" );
	fclose( pFile );
        
	Cnf_DataFree( pCnf );
        Vec_IntFree( vForAlls );
        Vec_IntFree( vExists );
        Vec_IntFree( vVarMap );
	Vec_IntFree( vTemp );
        cout << "\nQBF formula written into file " << qdimacs_file << endl;

	if(qbf_solver_to_use == "depqbf")
	{

		string command = "depqbf "; 
		command += qdimacs_file;
		command += " > ";
		command += model_file;
		system(command.c_str());

		ifstream *model_file_ptr = new ifstream();
		model_file_ptr->open(model_file.c_str()); // open the model_file
		assert(model_file_ptr->is_open());

		string word = "";
		*model_file_ptr>>word;
		if(word == "SAT")
		{
			return true;
		}
		else if(word == "UNSAT")
		{
			return false;
		}
		else
		{
			assert(false);
		}

	}
	else if(qbf_solver_to_use == "QuBE7")
	{

		string command = "QuBE7 "; 
		command += qdimacs_file;
		command += " > ";
		command += model_file;
		system(command.c_str());

		ifstream *model_file_ptr = new ifstream();
		model_file_ptr->open(model_file.c_str()); // open the model_file
		assert(model_file_ptr->is_open());

		string word = "";
		*model_file_ptr>>word;
		if(word == "SAT")
		{
			return true;
		}
		else if(word == "UNSAT")
		{
			return false;
		}
		else
		{
			assert(false);
		}

		
	}
	else
	{
		assert(false);
	}
}


void FVS(UndrGraph &g, UndrGraph &g_copy, set<int> &fvs)
{
	set<int> candidate_fvs;
	stack<int> fvs_stack;
	g_copy.findCandidateFVS(candidate_fvs, fvs_stack);
	assert(g_copy.empty());

	#ifdef DEBUG_SKOLEM
	showSet(candidate_fvs, "candidate_fvs");
	#endif

	while(!fvs_stack.empty())
	{
		int u = fvs_stack.top();
		fvs_stack.pop();
			
		set<int> smaller_fvs;
		smaller_fvs = candidate_fvs;
		smaller_fvs.erase(u);

		#ifdef DEBUG_SKOLEM
		cout << "\nAfter deleting " << u << " from candidate_fvs\n";
		showSet(smaller_fvs, "smaller_fvs");
		#endif

		if(g.isFVS(smaller_fvs)) //u is redundant
		{
			#ifdef DEBUG_SKOLEM
			cout << "\nsmaller_fvs is fvs\nLet's remove " << u << " from candidate_fvs\n";
			#endif	

			candidate_fvs.erase(u);

			#ifdef DEBUG_SKOLEM
			showSet(candidate_fvs, "candidate_fvs");
			#endif
		}
		else
		{
			#ifdef DEBUG_SKOLEM
			cout << "\nsmaller_fvs is NOT fvs\nDon't remove " << u << " from candidate_fvs\n";
			#endif	
		}
	}

	fvs = candidate_fvs;	
}
 



void findOrderOfNodes(UndrGraph &g, set<int> &fvs, list<int> &variable_order)
{
	set<int> ordered_variables;

	#ifdef DEBUG_SKOLEM
	showSet(fvs, "fvs");
	#endif
	
	if(!fvs.empty()) // graph g is cyclic
	{
		#ifdef DEBUG_SKOLEM
		cout << "\nGraph is cyclic\n";
		#endif
		// push back the nodes in fvs into variable_order
		for(set<int>::iterator set_it = fvs.begin(); set_it != fvs.end(); set_it++)
		{
			if(ordered_variables.find(*set_it) == ordered_variables.end())
			{
				variable_order.push_back(*set_it);
				ordered_variables.insert(*set_it);
			}
		}

		// delete the vertices in fvs
		for(set<int>::iterator set_it = fvs.begin(); set_it != fvs.end(); set_it++)
		{
			int u = *set_it;
			g.deleteVertex(u);
		}
		
		#ifdef DEBUG_SKOLEM
		cout << "\nAfter removing fvs\n";
		g.showGraph();
		#endif	
	}
	else
	{
		// do nothing
	}

	// graph g is Acyclic

	// find the nodes with zero degree (i.e. dead nodes)
	bool graph_is_empty;
	set<int> dead_nodes;
	graph_is_empty = g.deadNodes(dead_nodes);

	#ifdef DEBUG_SKOLEM
	showSet(dead_nodes, "dead_nodes");
	#endif

	// push back the dead nodes into variable_order
	for(set<int>::iterator set_it = dead_nodes.begin(); set_it != dead_nodes.end(); set_it++)
	{
		if(ordered_variables.find(*set_it) == ordered_variables.end())
		{
			variable_order.push_back(*set_it);
			ordered_variables.insert(*set_it);
		}
	}

	while(!graph_is_empty) // while all nodes are not dead
	{

		#ifdef DEBUG_SKOLEM
		cout << "\nGraph is NOT empty\n";
		#endif

		// find the centric nodes of all non-trivial trees

		set<int> centric_nodes;

		vector<bool> visited;
	    	for(int u = 0; u < g.size(); u++)
	    	{
			visited.push_back(false);
		}

		for (int u = 0; u < g.size(); u++)
		{
			if (!visited[u] && g.degree(u) > 0) // new non-trivial tree in graph g involving vertex u encountered
			{
				#ifdef DEBUG_SKOLEM
				cout << "\nnew non-trivial tree involving vertex " << u << " encountered\n";
				#endif

			  	int centre_node = g.findCentreNodeOfTree(u, visited);
				centric_nodes.insert(centre_node);

				#ifdef DEBUG_SKOLEM
				cout << "\nCentre node of the tree is " << centre_node << "\n";
				#endif
			}
		 }

		#ifdef DEBUG_SKOLEM
		showSet(centric_nodes, "centric_nodes");
		#endif

		// push back the centric nodes into variable_order
		for(set<int>::iterator set_it = centric_nodes.begin(); set_it != centric_nodes.end(); set_it++)
		{
			if(ordered_variables.find(*set_it) == ordered_variables.end())
			{
				variable_order.push_back(*set_it);
				ordered_variables.insert(*set_it);
			}
		}

		// delete the centric nodes
		for(set<int>::iterator set_it = centric_nodes.begin(); set_it != centric_nodes.end(); set_it++)
		{
			int u = *set_it;
			g.deleteVertex(u);
		}

		#ifdef DEBUG_SKOLEM
		cout << "\nAfter removing centric_nodes\n";
		g.showGraph();
		#endif

		// find the nodes with zero degree (i.e. dead nodes)
		dead_nodes.clear();
		graph_is_empty = g.deadNodes(dead_nodes);

		#ifdef DEBUG_SKOLEM
		showSet(dead_nodes, "dead_nodes");
		#endif

		// push back the dead nodes into variable_order
		for(set<int>::iterator set_it = dead_nodes.begin(); set_it != dead_nodes.end(); set_it++)
		{
			if(ordered_variables.find(*set_it) == ordered_variables.end())
			{
				variable_order.push_back(*set_it);
				ordered_variables.insert(*set_it);
			}
		}
	}// while graph is not empty
}




void obtainFactorGraphBasedOrdering(map<Aig_Obj_t*, set<string> > &VarsToElim_in_Supports_of_Factors, set<string> &Final_VariablesToEliminate_Set, list<string> &VariablesToEliminate)
{
	cout << "\ncreating the variable_graph\n";

	map<string, int> variablename_to_nodeindex_map;
	map<int, string> nodeindex_to_variablename_map;

	int node_index = 0;
	for(set<string>::iterator it = Final_VariablesToEliminate_Set.begin(); it != Final_VariablesToEliminate_Set.end(); it++)
	{
		string variablename = *it;
		#ifdef DEBUG_SKOLEM
		cout << "\nvariablename = " << variablename <<"\tnode_index = " << node_index << endl;
		#endif
		variablename_to_nodeindex_map.insert(make_pair(variablename, node_index));
		nodeindex_to_variablename_map.insert(make_pair(node_index, variablename));
		node_index++;
	}

	UndrGraph variable_graph(Final_VariablesToEliminate_Set.size());
	UndrGraph variable_graph_copy(Final_VariablesToEliminate_Set.size());

	cout << "\nvertices of variable_graph created\n";

	#ifdef DEBUG_SKOLEM
	cout << "\nEdges" << endl;
	#endif

	cout << "\ncreating edges of variable_graph\n";

	for(map<Aig_Obj_t*, set<string> >::iterator map_it = VarsToElim_in_Supports_of_Factors.begin(); map_it != VarsToElim_in_Supports_of_Factors.end(); map_it++)//take each factor
	{
		set<string> varstoelim_in_support = map_it->second;
		#ifdef DEBUG_SKOLEM
		showSet(varstoelim_in_support, "varstoelim_in_support");
		#endif

		vector<int> varstoelim_indices_in_support;
		for(set<string>::iterator set_it = varstoelim_in_support.begin(); set_it != varstoelim_in_support.end(); set_it++)
		{
			string variable_name = *set_it;
			map<string, int>::iterator variablename_to_nodeindex_map_it = variablename_to_nodeindex_map.find(variable_name);
			assert(variablename_to_nodeindex_map_it != variablename_to_nodeindex_map.end());

			int node_index = variablename_to_nodeindex_map_it->second;
			varstoelim_indices_in_support.push_back(node_index);
		}

		#ifdef DEBUG_SKOLEM
		showVector(varstoelim_indices_in_support, "varstoelim_indices_in_support");
		#endif

		cout << "\nfactor with " << varstoelim_indices_in_support.size() << " encountered\n";

		cout << "\nadding edges for this factor\n";

		//add the edges
		for(int i = 0; i < varstoelim_indices_in_support.size(); i++)
			for(int j = i+1; j < varstoelim_indices_in_support.size(); j++)
			{
				int v_index = varstoelim_indices_in_support[i];
				int w_index = varstoelim_indices_in_support[j];
				
				#ifdef DEBUG_SKOLEM
				cout << "\nEdge " << v_index << " ---- " << w_index << endl;
				#endif

				variable_graph.addEdge(v_index, w_index);
				variable_graph_copy.addEdge(v_index, w_index);
			}

		cout << "\nedges added for this factor\n";

	}//take each factor ends here

	cout << "\nedges of variable_graph created\n";

	#ifdef DEBUG_SKOLEM
	variable_graph.showGraph();
	#endif

	cout << "\nvariable_graph formed\n";

	list<int> variable_order;
	set<int> disabled_nodes_local;
	set<int> fvs;
	if(variable_graph.isCyclic(disabled_nodes_local))
	{
		#ifdef DEBUG_SKOLEM
		cout << "\nvariable_graph HAS cycles\n";
		#endif
		
		FVS(variable_graph, variable_graph_copy, fvs);

		#ifdef DEBUG_SKOLEM
		showSet(fvs, "fvs");
		#endif				

	}
	else
	{
		#ifdef DEBUG_SKOLEM
		cout << "\nvariable_graph HAS NO cycles\n";
		#endif
		// do nothing

		assert(fvs.empty());
		// fvs is empty
	}

	cout << "\nGetting order from fvs and the disjoint components obtained by removing the fvs\n";

	// get order from fvs and the disjoint components obtained by removing the fvs
	findOrderOfNodes(variable_graph, fvs, variable_order);	

	#ifdef DEBUG_SKOLEM
	showList(variable_order, "variable_order");
	#endif

	// map the order back to strings
	for(list<int>::iterator list_it = variable_order.begin(); list_it != variable_order.end(); list_it++)
	{
		int node_index = *list_it;
		map<int,string>::iterator nodeindex_to_variablename_map_it = nodeindex_to_variablename_map.find(node_index);
		assert(nodeindex_to_variablename_map_it != nodeindex_to_variablename_map.end());

		string variable_name = nodeindex_to_variablename_map_it->second;
		VariablesToEliminate.push_back(variable_name);
	}

	#ifdef DEBUG_SKOLEM
	cout << "\nVariablesToEliminate\n";
	showList(VariablesToEliminate);
	#endif	
}



void showList(list<int> &integer_list, string who_am_i)
{
	cout << endl << endl << who_am_i << endl << endl;

	for(list<int>::iterator integer_it = integer_list.begin(); integer_it != integer_list.end(); integer_it++)
	{
		cout << *integer_it << ", ";
	}

	cout << endl;

}



void show_cannot_be_string_to_cannot_be_object_map()
{
	cout << "\ncannot_be_string_to_cannot_be_object_map\n";
	for(map<string, Aig_Obj_t*>::iterator cannot_be_string_to_cannot_be_object_map_it = cannot_be_string_to_cannot_be_object_map.begin(); cannot_be_string_to_cannot_be_object_map_it != cannot_be_string_to_cannot_be_object_map.end(); cannot_be_string_to_cannot_be_object_map_it++)
	{
		cout << cannot_be_string_to_cannot_be_object_map_it->first << "\t" << cannot_be_string_to_cannot_be_object_map_it->second << endl;
	}
}



void show_cannot_be_object_to_cannot_be_dag_map()
{
	cout << "\ncannot_be_object_to_cannot_be_dag_map\n";
	for(map<Aig_Obj_t*, Aig_Obj_t*>::iterator cannot_be_object_to_cannot_be_dag_map_it = cannot_be_object_to_cannot_be_dag_map.begin(); cannot_be_object_to_cannot_be_dag_map_it != cannot_be_object_to_cannot_be_dag_map.end(); cannot_be_object_to_cannot_be_dag_map_it++)
	{
		cout << cannot_be_object_to_cannot_be_dag_map_it->first << "\t" << cannot_be_object_to_cannot_be_dag_map_it->second << endl;
	}
}


void showCannotBeSets()
{
	cout << "\ncannot_be_one_set\n";	

	for(map<int, set<Aig_Obj_t*> >::iterator cannot_be_one_set_it = cannot_be_one_set.begin(); cannot_be_one_set_it != cannot_be_one_set.end(); cannot_be_one_set_it++)
	{
		cout << "\nvar_to_elim_index = " << cannot_be_one_set_it->first << endl;

		for(set<Aig_Obj_t*>::iterator set_it = (cannot_be_one_set_it->second).begin(); set_it != (cannot_be_one_set_it->second).end(); set_it++)
		{
			cout << *set_it << "\t";
		} 
	}

	cout << "\n\n\ncannot_be_zero_set\n";	

	for(map<int, set<Aig_Obj_t*> >::iterator cannot_be_zero_set_it = cannot_be_zero_set.begin(); cannot_be_zero_set_it != cannot_be_zero_set.end(); cannot_be_zero_set_it++)
	{
		cout << "\nvar_to_elim_index = " << cannot_be_zero_set_it->first << endl;

		for(set<Aig_Obj_t*>::iterator set_it = (cannot_be_zero_set_it->second).begin(); set_it != (cannot_be_zero_set_it->second).end(); set_it++)
		{
			cout << *set_it << "\t";
		} 
	}
}



void obtainFactorsAndVariablesToEliminatFromHWMCCFile(ABC* abcObj, Abc_Frame_t* abcFrame, set<Aig_Obj_t*> &Factors, set<Aig_Obj_t*> &RHS_of_Factors, list<string> &VariablesToEliminate, map<Aig_Obj_t*, Aig_Obj_t*> &Output_Object_to_RHS_of_Factors, map<Aig_Obj_t*, Aig_Obj_t*> &Output_Object_to_RHS_of_PrimaryOutputs, Aig_Man_t* &aig_manager)
{
	assert(benchmark_name != "");

	string command = "read " + benchmark_name + ";" + initCommand;

	#ifdef DEBUG_SKOLEM
	cout << command << endl;
	#endif

	if (abcObj->comExecute(abcFrame, command))
    	{
	 	cout << "cannot execute " << command << endl;
		assert(false);
	}

	#ifdef DEBUG_SKOLEM //Printing original circuit
	command = "write ckt.v;";
	cout << command << endl;
		
	if (abcObj->comExecute(abcFrame, command))
	{
		cout << "cannot execute command " << command << endl;
		assert(false);
	}
	#endif	
	
	//ofstream cktInfo("cktInfo");
	//int pis = Abc_NtkPiNum(abcFrame->pNtkCur);
    	//cktInfo << "Inputs:" << pis << endl;
    	//int states = Abc_NtkLatchNum(abcFrame->pNtkCur);
    	//cktInfo << "Latches:" << states << endl;    

	#ifdef DEBUG_SKOLEM
	cout << "Changing names" << endl;
	#endif

	changeNamesAndRemovePos(abcFrame->pNtkCur, PREFPREFIX, 0); // last argument zero: hence POs are not removed
	

	#ifdef DEBUG_SKOLEM //Printing po-deleted and pi-renamed circuit
	command = "write ckt_after_pi_renaming.v;";
	cout << command << endl;
		
	if (abcObj->comExecute(abcFrame, command))
	{
		cout << "cannot execute command " << command << endl;
		assert(false);
	}
	#endif	


	int number_of_latches_in_original_circuit = Abc_NtkBoNum(abcFrame->pNtkCur);

	#ifdef DEBUG_SKOLEM
	cout << "\nNumber of latches in the original circuit = " <<  number_of_latches_in_original_circuit << endl;
	#endif	


    	command = ";comb";

	#ifdef DEBUG_SKOLEM
	cout << command << endl;
	#endif
	if (abcObj->comExecute(abcFrame, command))
    	{
		cout << "cannot execute " << command << endl;
		assert(false);
	}   

	#ifdef DEBUG_SKOLEM //Printing circuit after comb
	command = "write comb_ckt.v;";
	cout << command << endl;
		
	if (abcObj->comExecute(abcFrame, command))
	{
		cout << "cannot execute command " << command << endl;
		assert(false);
	}
	#endif	 		

	#ifdef DEBUG_SKOLEM	
	cout << "Renaming latches and outputs" << endl;
	#endif

	// The last number_of_latches_in_original_circuit POs are latches
	// The first Abc_NtkPoNum(abcFrame->pNtkCur) -  number_of_latches_in_original_circuit POs are outputs

	int index_of_first_latch = Abc_NtkPoNum(abcFrame->pNtkCur) - number_of_latches_in_original_circuit;

	string lastLatch = renameLatchesAndOutputs(abcFrame->pNtkCur, number_of_latches_in_original_circuit);

	#ifdef DEBUG_SKOLEM	
	cout << "Latches and outputs renamed" << endl;
	#endif


	#ifdef DEBUG_SKOLEM //Printing latch-renamed  circuit 
	command = "write comb_ckt_after_latch_renaming.v;";
	cout << command << endl;
		
	if (abcObj->comExecute(abcFrame, command))
	{
		cout << "cannot execute command " << command << endl;
		assert(false);
	}
	#endif	 

	command = "fraig;write F.aig;";		

	#ifdef DEBUG_SKOLEM
	cout << command << endl;
	#endif

	if (abcObj->comExecute(abcFrame, command))
	{
	 	cout << "cannot execute " << command << endl;
		assert(false);
	}

	#ifdef PRINT_SKOLEM_FUNCTIONS
	//Printing original transition function
	command = "write ";
	command += benchmark_name_without_extension;
	command += "_transition_function.v;";
	cout << command << endl;
		
	if (abcObj->comExecute(abcFrame, command))
	{
		cout << "cannot execute command " << command << endl;
		assert(false);
	}
	#endif	

	Abc_Ntk_t* transition_function = abcFrame->pNtkCur;
	transition_function = Abc_NtkDup(transition_function);


	// Let's find VariablesToEliminate now

	Abc_Obj_t* tempInputObj;
	int j = 0;
	set<string> input_names;
	Abc_NtkForEachPi(transition_function, tempInputObj, j)
	{
		string input_name = Abc_ObjName(tempInputObj);
		if(input_name[0] == 'z' && input_name[1] == 'z' && input_name[2] == 'p')
		{  
			input_names.insert(input_name);
		}			
	} 

	input_names_in_circuit = input_names;


	for(set<string>::iterator input_it = input_names.begin(); input_it != input_names.end(); input_it++)
	{
		VariablesToEliminate.push_back(*input_it);
	}

	// Let's get all the variable names and
	// Ci_name_to_Ci_number_map
	j = 0;
	vector<string> variable_names;
	Abc_NtkForEachCi(transition_function, tempInputObj, j)
	{
		string variable_name = Abc_ObjName(tempInputObj);
		variable_names.push_back(variable_name);

		Ci_name_to_Ci_number_map.insert(make_pair(variable_name, j));

		number_of_Cis++;				
	} 

	//if(to include POs in transition relation)
	//start here
	Abc_Obj_t* tempOutputObj;
	int k = 0;
	vector<string> output_names;
	Abc_NtkForEachPo(transition_function, tempOutputObj, k)
	{
		string variable_name = Abc_ObjName(tempOutputObj);
		variable_names.push_back(variable_name);
		output_names.push_back(variable_name);

		Ci_name_to_Ci_number_map.insert(make_pair(variable_name, j));	
					
		j++;

		number_of_Cis++;
	} 
	//end here

	// Let's split the transition_function into factors

	aig_manager = Abc_NtkToDar(transition_function, 0, 0);
	// transition function converted to aig_manager	

	// reading the factors
	Aig_Obj_t* factorObj;
    	int i = 0;

	Aig_ManForEachPoSeq(aig_manager, factorObj, i )
    	{
		assert(factorObj != NULL);

		Aig_Obj_t* Fanin0_factorObj = Aig_ObjChild0(factorObj);		 
		// Note that it is important to use Aig_ObjChild0 here
		// Earlier Aig_ObjFanin0 was used; but Aig_ObjFanin0 regularizes the dag,
		// Aig_ObjChild0 does not regularize the dag		

		assert(Fanin0_factorObj != NULL);

		//if(to include POs in transition relation)
		//start here
		Aig_Obj_t* output_obj = Aig_ObjCreateCi(aig_manager);
		Aig_Obj_t* Factor = createEquivalence(output_obj, Fanin0_factorObj, aig_manager);


		if(i >= index_of_first_latch) //latch
		{
			Factors.insert(Factor);
			RHS_of_Factors.insert(Fanin0_factorObj);
			Output_Object_to_RHS_of_Factors.insert(make_pair(output_obj, Fanin0_factorObj));
		}
		else // output
		{
			Output_Object_to_RHS_of_PrimaryOutputs.insert(make_pair(output_obj, Fanin0_factorObj));

			if(i == failure_condition_location)
			{
				failure_condition_aig = Fanin0_factorObj;
			}
		}
		// Let's add output_name as a new CI
		//otherwise
		//Factors.insert(Fanin0_factorObj);
    	}

	// Let's get the IDs of the variables

	vector<int> variable_ids;
	i = 0;
	Aig_ManForEachCi(aig_manager, factorObj, i )
	{
		int Id = Aig_ObjId(factorObj); // no need to apply Aig_Regular() as factorObj is CI
		variable_ids.push_back(Id);

		string variable_name = 	variable_names[i];	
		if(input_names.find(variable_name) != input_names.end())
		// variable_name is an input; it is a Ci to be eliminated
		{
			Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.insert(make_pair(variable_name, factorObj));
		}

		Ci_name_to_Ci_object_map.insert(make_pair(variable_name, factorObj));
		
	}

	// Let's create the variable_id ---> variable_name map

	assert(variable_ids.size() == variable_names.size());	
	for(int i = 0; i < variable_ids.size(); i++)
	{
		Ci_id_to_Ci_name_map.insert(make_pair(variable_ids[i], variable_names[i]));
	}

	command = "rm F.aig";
	system(command.c_str());
}



void obtainFactorsAndVariablesToEliminatFromHWMCCFile(ABC* abcObj, Abc_Frame_t* abcFrame, set<Aig_Obj_t*> &Factors, map<string, Aig_Obj_t*> &Output_String_to_RHS_of_Factors, list<string> &VariablesToEliminate, Aig_Man_t* &aig_manager)
{
	assert(benchmark_name != "");

	string command = "read " + benchmark_name + ";" + initCommand;

	#ifdef DEBUG_SKOLEM
	cout << command << endl;
	#endif

	if (abcObj->comExecute(abcFrame, command))
    	{
	 	cout << "cannot execute " << command << endl;
		assert(false);
	}

	#ifdef DEBUG_SKOLEM //Printing original circuit
	command = "write ckt.v;";
	cout << command << endl;
		
	if (abcObj->comExecute(abcFrame, command))
	{
		cout << "cannot execute command " << command << endl;
		assert(false);
	}
	#endif	
	
	//ofstream cktInfo("cktInfo");
	//int pis = Abc_NtkPiNum(abcFrame->pNtkCur);
    	//cktInfo << "Inputs:" << pis << endl;
    	//int states = Abc_NtkLatchNum(abcFrame->pNtkCur);
    	//cktInfo << "Latches:" << states << endl;    

	#ifdef DEBUG_SKOLEM
	cout << "Changing names and removing POs" << endl;
	#endif

	changeNamesAndRemovePos(abcFrame->pNtkCur, PREFPREFIX, 1);


	#ifdef DEBUG_SKOLEM //Printing po-deleted and pi-renamed circuit
	command = "write ckt_after_po_deletion_pi_renaming.v;";
	cout << command << endl;
		
	if (abcObj->comExecute(abcFrame, command))
	{
		cout << "cannot execute command " << command << endl;
		assert(false);
	}
	#endif	

    	command = ";comb";

	#ifdef DEBUG_SKOLEM
	cout << command << endl;
	#endif
	if (abcObj->comExecute(abcFrame, command))
    	{
		cout << "cannot execute " << command << endl;
		assert(false);
	}   

	#ifdef DEBUG_SKOLEM //Printing circuit after comb
	command = "write comb_ckt.v;";
	cout << command << endl;
		
	if (abcObj->comExecute(abcFrame, command))
	{
		cout << "cannot execute command " << command << endl;
		assert(false);
	}
	#endif	 		

	#ifdef DEBUG_SKOLEM	
	cout << "Renaming latches" << endl;
	#endif

	string lastLatch = renameLatches(abcFrame->pNtkCur);

	#ifdef DEBUG_SKOLEM //Printing latch-renamed  circuit 
	command = "write comb_ckt_after_latch_renaming.v;";
	cout << command << endl;
		
	if (abcObj->comExecute(abcFrame, command))
	{
		cout << "cannot execute command " << command << endl;
		assert(false);
	}
	#endif	 

	command = "fraig;write F.aig;";		

	#ifdef DEBUG_SKOLEM
	cout << command << endl;
	#endif

	if (abcObj->comExecute(abcFrame, command))
	{
	 	cout << "cannot execute " << command << endl;
		assert(false);
	}

	#ifdef PRINT_SKOLEM_FUNCTIONS
	//Printing original transition function
	command = "write ";
	command += benchmark_name_without_extension;
	command += "_transition_function.v;";
	cout << command << endl;
		
	if (abcObj->comExecute(abcFrame, command))
	{
		cout << "cannot execute command " << command << endl;
		assert(false);
	}
	#endif	

	Abc_Ntk_t* transition_function = abcFrame->pNtkCur;
	transition_function = Abc_NtkDup(transition_function);


	// Let's find VariablesToEliminate now

	Abc_Obj_t* tempInputObj;
	int j = 0;
	set<string> input_names;
	Abc_NtkForEachPi(transition_function, tempInputObj, j)
	{
		string input_name = Abc_ObjName(tempInputObj);
		if(input_name[0] == 'z' && input_name[1] == 'z' && input_name[2] == 'p')
		{  
			input_names.insert(input_name);
		}			
	} 

	for(set<string>::iterator input_it = input_names.begin(); input_it != input_names.end(); input_it++)
	{
		VariablesToEliminate.push_back(*input_it);
	}

	// Let's get all the variable names and
	// Ci_name_to_Ci_number_map
	j = 0;
	vector<string> variable_names;
	Abc_NtkForEachCi(transition_function, tempInputObj, j)
	{
		string variable_name = Abc_ObjName(tempInputObj);
		variable_names.push_back(variable_name);

		Ci_name_to_Ci_number_map.insert(make_pair(variable_name, j));

		number_of_Cis++;				
	} 

	//if(to include POs in transition relation)
	//start here
	Abc_Obj_t* tempOutputObj;
	int k = 0;
	vector<string> output_names;
	Abc_NtkForEachPo(transition_function, tempOutputObj, k)
	{
		string variable_name = Abc_ObjName(tempOutputObj);
		variable_names.push_back(variable_name);
		output_names.push_back(variable_name);

		Ci_name_to_Ci_number_map.insert(make_pair(variable_name, j));	
					
		j++;

		number_of_Cis++;
	} 
	//end here

	// Let's split the transition_function into factors

	aig_manager = Abc_NtkToDar(transition_function, 0, 0);
	// transition function converted to aig_manager	

	// reading the factors
	Aig_Obj_t* factorObj;
    	int i = 0;

	Aig_ManForEachPoSeq(aig_manager, factorObj, i )
    	{
		assert(factorObj != NULL);

		Aig_Obj_t* Fanin0_factorObj = Aig_ObjChild0(factorObj);		 
		// Note that it is important to use Aig_ObjChild0 here
		// Earlier Aig_ObjFanin0 was used; but Aig_ObjFanin0 regularizes the dag,
		// Aig_ObjChild0 does not regularize the dag		

		assert(Fanin0_factorObj != NULL);

		//if(to include POs in transition relation)
		//start here
		Aig_Obj_t* output_obj = Aig_ObjCreateCi(aig_manager);
		Aig_Obj_t* Factor = createEquivalence(output_obj, Fanin0_factorObj, aig_manager);
		Factors.insert(Factor);
		
		string output_name = output_names[i];
		Output_String_to_RHS_of_Factors.insert(make_pair(output_name, Fanin0_factorObj));
		// Let's add output_name as a new CI
		//otherwise
		//Factors.insert(Fanin0_factorObj);
    	}

	// Let's get the IDs of the variables

	vector<int> variable_ids;
	i = 0;
	Aig_ManForEachCi(aig_manager, factorObj, i )
	{
		int Id = Aig_ObjId(factorObj); // no need to apply Aig_Regular() as factorObj is CI
		variable_ids.push_back(Id);

		string variable_name = 	variable_names[i];	
		if(input_names.find(variable_name) != input_names.end())
		// variable_name is an input; it is a Ci to be eliminated
		{
			Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.insert(make_pair(variable_name, factorObj));
		}

		Ci_name_to_Ci_object_map.insert(make_pair(variable_name, factorObj));
		
	}

	// Let's create the variable_id ---> variable_name map

	assert(variable_ids.size() == variable_names.size());	
	for(int i = 0; i < variable_ids.size(); i++)
	{
		Ci_id_to_Ci_name_map.insert(make_pair(variable_ids[i], variable_names[i]));
	}

	command = "rm F.aig";
	system(command.c_str());
}


void writeCombinationalCircuitInVerilog( Aig_Man_t * p, int number_of_variables_to_eliminate, int original_no_of_cis, int no_of_cis_with_f_variables, int total_no_of_cis, char * pFileName, bool print_tseitin_variable_as_input )
{
    map<Aig_Obj_t*, string> node_name_map;

    FILE * pFile;
    Vec_Ptr_t * vNodes;
    Aig_Obj_t * pObj, * pObjLi, * pObjLo, * pConst1 = NULL;
    int i;
    if ( Aig_ManCoNum(p) == 0 )
    {
        printf( "Aig_ManDumpBlif(): AIG manager does not have POs.\n" );
        return;
    }
    // check if constant is used
    Aig_ManForEachCo( p, pObj, i )
        if ( Aig_ObjIsConst1(Aig_ObjFanin0(pObj)) )
            pConst1 = Aig_ManConst1(p);
    // collect nodes in the DFS order
    vNodes = Aig_ManDfs( p, 1 );
    // assign IDs to objects

    char node_count_char[100];
    sprintf(node_count_char, "%d", 1);
    string node_count_string(node_count_char);
    string node_string = "c_";
    node_string += node_count_string;
    node_name_map.insert(make_pair(Aig_ManConst1(p), node_string));
	
    int Counter = 1;  
    Aig_ManForEachCi( p, pObj, i )
	{
	char node_count_char[100];
	sprintf(node_count_char, "%d", Counter);
	string node_count_string(node_count_char);
	string node_string;
	if(Counter <= number_of_variables_to_eliminate)
	{
		node_string = "i_";
	}
	else if(Counter > number_of_variables_to_eliminate && Counter <= original_no_of_cis)
	{
		node_string = "x_";
	}
	else if(Counter > original_no_of_cis && Counter <= no_of_cis_with_f_variables)
	{
		if(print_tseitin_variable_as_input)
		{
			node_string = "i_";
		}
		else
		{
			node_string = "f_";
		}
	}
	else if(Counter > no_of_cis_with_f_variables && Counter <= total_no_of_cis)
	{
		if(print_tseitin_variable_as_input)
		{
			node_string = "i_";
		}
		else
		{
			node_string = "g_";
		}
	}
	node_string += node_count_string;
	node_name_map.insert(make_pair(pObj, node_string));
	Counter++;
	}
    assert(Counter-1 == total_no_of_cis);

    Counter = 1; 
    Aig_ManForEachCo( p, pObj, i )
	{
	char node_count_char[100];
	sprintf(node_count_char, "%d", Counter);
	string node_count_string(node_count_char);
	string node_string = "o_";
	node_string += node_count_string;
	node_name_map.insert(make_pair(pObj, node_string));
	Counter++;
	}    

    Counter = 1;   
    Vec_PtrForEachEntry( Aig_Obj_t *, vNodes, pObj, i )
	{
	char node_count_char[100];
	sprintf(node_count_char, "%d", Counter);
	string node_count_string(node_count_char);
	string node_string = "n_";
	node_string += node_count_string;
	node_name_map.insert(make_pair(pObj, node_string));
	Counter++;
	}
    
    // write the file
    pFile = fopen( pFileName, "w" );
    fprintf( pFile, "// Verilog file written by procedure writeCombinationalCircuitInVerilog\n//Skolem functions to be generated for i_ variables\n" );
//    fprintf( pFile, "// http://www.eecs.berkeley.edu/~alanmi/abc/\n" );
    if ( Aig_ManRegNum(p) )
        fprintf( pFile, "module %s ( clock", p->pName? p->pName: "test" );
    else
        fprintf( pFile, "module %s (", p->pName? p->pName: "test" );
    Aig_ManForEachPiSeq( p, pObj, i )
        fprintf( pFile, "%s %s", ((Aig_ManRegNum(p) || i)? ",":""), node_name_map[pObj].c_str() );
    Aig_ManForEachPoSeq( p, pObj, i )
        fprintf( pFile, ", %s", node_name_map[pObj].c_str() );
    fprintf( pFile, " );\n" );

    // write PIs
    if ( Aig_ManRegNum(p) )
        fprintf( pFile, "input clock;\n" );
    Aig_ManForEachPiSeq( p, pObj, i )
        fprintf( pFile, "input %s;\n", node_name_map[pObj].c_str() );
    // write POs
    Aig_ManForEachPoSeq( p, pObj, i )
        fprintf( pFile, "output %s;\n", node_name_map[pObj].c_str() );
    // write latches
    if ( Aig_ManRegNum(p) )
    {
    Aig_ManForEachLiLoSeq( p, pObjLi, pObjLo, i )
        fprintf( pFile, "reg %s;\n", node_name_map[pObjLo].c_str());
    Aig_ManForEachLiLoSeq( p, pObjLi, pObjLo, i )
        fprintf( pFile, "wire %s;\n", node_name_map[pObjLi].c_str() );
    }
    // write nodes
    Vec_PtrForEachEntry( Aig_Obj_t *, vNodes, pObj, i )
        fprintf( pFile, "wire %s;\n", node_name_map[pObj].c_str() );
    if ( pConst1 )
        fprintf( pFile, "wire %s;\n", node_name_map[pConst1].c_str());
    // write nodes
    if ( pConst1 )
        fprintf( pFile, "assign %s = 1\'b1;\n", node_name_map[pConst1].c_str() );
    Vec_PtrForEachEntry( Aig_Obj_t *, vNodes, pObj, i )
    {
        fprintf( pFile, "assign %s = %s%s & %s%s;\n", 
            node_name_map[pObj].c_str(),
            !Aig_ObjFaninC0(pObj) ? " " : "~", node_name_map[Aig_ObjFanin0(pObj)].c_str(), 
            !Aig_ObjFaninC1(pObj) ? " " : "~", node_name_map[Aig_ObjFanin1(pObj)].c_str()
            );
    }
    // write POs
    Aig_ManForEachPoSeq( p, pObj, i )
    {
        fprintf( pFile, "assign %s = %s%s;\n", 
            node_name_map[pObj].c_str(),
            !Aig_ObjFaninC0(pObj) ? " " : "~", node_name_map[Aig_ObjFanin0(pObj)].c_str() );
    }
    if ( Aig_ManRegNum(p) )
    {
        Aig_ManForEachLiLoSeq( p, pObjLi, pObjLo, i )
        {
            fprintf( pFile, "assign %s = %s%s;\n", 
                node_name_map[pObjLi].c_str(),
                !Aig_ObjFaninC0(pObjLi) ? " " : "~", node_name_map[Aig_ObjFanin0(pObjLi)].c_str() );
        }
    }

    // write initial state
    if ( Aig_ManRegNum(p) )
    {
        Aig_ManForEachLiLoSeq( p, pObjLi, pObjLo, i )
            fprintf( pFile, "always @ (posedge clock) begin %s <= %s; end\n", 
                 node_name_map[pObjLo].c_str(),
                 node_name_map[pObjLi].c_str() );
        Aig_ManForEachLiLoSeq( p, pObjLi, pObjLo, i )
            fprintf( pFile, "initial begin %s <= 1\'b0; end\n", 
                 node_name_map[pObjLo].c_str() );
    }

    fprintf( pFile, "endmodule\n\n" );
    fclose( pFile );
    Vec_PtrFree( vNodes );
}


void obtainFactorsAndVariablesToEliminateFromGeneratedBenchmark(ABC* abcObj, Abc_Frame_t* abcFrame, set<Aig_Obj_t*> &Factors, Aig_Man_t* &aig_manager, list<string> &VariablesToEliminate)
{
	assert(benchmark_name != "");

	string command = "read " + benchmark_name + ";" + initCommand;
	
	#ifdef DEBUG_SKOLEM
	cout << command << endl;
	#endif

	if (abcObj->comExecute(abcFrame, command))
    	{
	 	cout << "cannot execute " << command << endl;
		assert(false);
	}

	#ifdef DEBUG_SKOLEM //Printing original circuit
	command = "write ckt.v;";
	cout << command << endl;
		
	if (abcObj->comExecute(abcFrame, command))
	{
		cout << "cannot execute command " << command << endl;
		assert(false);
	}
	#endif	

	Abc_Ntk_t* transition_function = abcFrame->pNtkCur;
	transition_function = Abc_NtkDup(transition_function);

	// Let's get all the variable names and
	// Ci_name_to_Ci_number_map
	Abc_Obj_t* tempInputObj;
	int j = 0;
	vector<string> variable_names;
	Abc_NtkForEachCi(transition_function, tempInputObj, j)
	{
		string variable_name = Abc_ObjName(tempInputObj);
		variable_names.push_back(variable_name);

		Ci_name_to_Ci_number_map.insert(make_pair(variable_name, j));

		number_of_Cis++;				
	} 

	// Let's split the transition_function into factors

	aig_manager = Abc_NtkToDar(transition_function, 0, 0);
	// transition function converted to aig_manager	

	// reading the factors: follow unnegated AND nodes to
	// do AND-flattening
	assert(Aig_ManCoNum(aig_manager) == 1);
	Aig_Obj_t* CO_aig_manager;
	CO_aig_manager = Aig_ManCo(aig_manager, 0);
	assert(CO_aig_manager != NULL);

	Aig_Obj_t* root_of_conjunction;
	root_of_conjunction = Aig_ObjChild0(CO_aig_manager);	
	assert(root_of_conjunction != NULL);
	vector<Aig_Obj_t*> roots_of_conjunction;

	if(!Aig_IsComplement(root_of_conjunction) && root_of_conjunction->Type == AIG_OBJ_AND)
	{
		roots_of_conjunction.push_back(root_of_conjunction);
	}
	else
	{
		Factors.insert(root_of_conjunction);	
	}
    	
	while(roots_of_conjunction.size() > 0)
	{
		root_of_conjunction = roots_of_conjunction[0];
		roots_of_conjunction.erase(roots_of_conjunction.begin());

		Aig_Obj_t* child1 = Aig_ObjChild0(root_of_conjunction);
		assert(child1 != NULL);
		if(!Aig_IsComplement(child1) && child1->Type == AIG_OBJ_AND)
		{
			roots_of_conjunction.push_back(child1);
		}
		else
		{
			Factors.insert(child1);	
		}	

		Aig_Obj_t* child2 = Aig_ObjChild1(root_of_conjunction);
		assert(child2 != NULL);
		if(!Aig_IsComplement(child2) && child2->Type == AIG_OBJ_AND)
		{
			roots_of_conjunction.push_back(child2);
		}
		else
		{
			Factors.insert(child2);	
		}
	}

	// Limiting no: of varsto elim if needed
	Aig_Obj_t* ciObj_temp;
	int k = 0;
	int input_var_count_temp = 0;
	Aig_ManForEachCi(aig_manager, ciObj_temp, k )
	{
		string variable_name = 	variable_names[k];
		if(variable_name[0] == 'i' && variable_name[1] == '_')
			input_var_count_temp++;
		else if(variable_name[0] == 'i')//Added for POPL'17
			input_var_count_temp++;
	}

	if(limit_on_variables_to_eliminate != -1)
	{
		assert(limit_on_variables_to_eliminate >=1 && limit_on_variables_to_eliminate <= 100);
		limit_on_variables_to_eliminate = (input_var_count_temp * limit_on_variables_to_eliminate)/100;
	}

	//cout << "\nlimit_on_variables_to_eliminate = " << limit_on_variables_to_eliminate << endl;

	// Let's get the IDs of the variables
	
	Aig_Obj_t* ciObj;
	vector<int> variable_ids;
	int i = 0;

	int vars_to_elim_limiting_count = 0;
	Aig_ManForEachCi(aig_manager, ciObj, i )
	{
		int Id = Aig_ObjId(ciObj); // no need to apply Aig_Regular() as ciObj is CI
		variable_ids.push_back(Id);

		string variable_name = 	variable_names[i];
		if(variable_name[0] == 'i' && variable_name[1] == '_')
		// variable_name is a Ci to be eliminated
		{
			if(limit_on_variables_to_eliminate == -1 || vars_to_elim_limiting_count < limit_on_variables_to_eliminate)
			{
				VariablesToEliminate.push_back(variable_name);
				Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.insert(make_pair(variable_name, ciObj));
				vars_to_elim_limiting_count++;
			}
		}
		else if(variable_name[0] == 'i')//Added for POPL'17
		// variable_name is a Ci to be eliminated
		{
			if(limit_on_variables_to_eliminate == -1 || vars_to_elim_limiting_count < limit_on_variables_to_eliminate)
			{
				VariablesToEliminate.push_back(variable_name);
				Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.insert(make_pair(variable_name, ciObj));
				vars_to_elim_limiting_count++;
			}
		}

		Ci_name_to_Ci_object_map.insert(make_pair(variable_name, ciObj));
	}

	// Let's create the variable_id ---> variable_name map

	assert(variable_ids.size() == variable_names.size());	
	for(int i = 0; i < variable_ids.size(); i++)
	{
		Ci_id_to_Ci_name_map.insert(make_pair(variable_ids[i], variable_names[i]));
	}

	#ifdef DEBUG_SKOLEM
	cout << "\nNumber of factors = " << Factors.size() << endl;
	Aig_Obj_t* and_of_factors = createAnd(Factors, aig_manager);
	assert(and_of_factors != NULL);	
	writeFormulaToFile(aig_manager, and_of_factors, "and_of_factors.v");
	#endif
}



Abc_Ntk_t* obtainNetworkFromAIGWithIdNames(Aig_Man_t * pMan, map<int, string> &idName, string single_po_name)
{


    Vec_Ptr_t * vNodes;
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pObjNew;
    Aig_Obj_t * pObj, * pObjLo, * pObjLi;
    int i;
    assert(pMan->nAsserts == 0);
    // perform strashing
    pNtkNew = Abc_NtkAlloc(ABC_NTK_STRASH, ABC_FUNC_AIG, 1);
    pNtkNew->nConstrs = pMan->nConstrs;
    // duplicate the name and the spec
    pNtkNew->pName = Extra_UtilStrsav(pMan->pName);
    pNtkNew->pSpec = Extra_UtilStrsav(pMan->pSpec);
    Aig_ManConst1(pMan)->pData = Abc_AigConst1(pNtkNew);
    // create PIs

    Aig_ManForEachPiSeq(pMan, pObj, i)
    {
        pObjNew = Abc_NtkCreatePi(pNtkNew);

	#ifdef DEBUG_SKOLEM 
	cout << endl << "pObj->Id = " << pObj->Id;
	#endif

	assert(idName.find(pObj->Id) != idName.end());

	#ifdef DEBUG_SKOLEM 
	cout << "\tidName[pObj->Id] = " << idName[pObj->Id];
	#endif

        Abc_ObjAssignName(pObjNew, (char*) idName[pObj->Id].c_str(), NULL);
        //        Abc_ObjAssignName( pObjNew, Abc_ObjName(pObjNew), NULL );
        //cout<<pObj->Id<<endl;
        pObj->pData = pObjNew;
    }
    // create POs
    assert(Aig_ManCoNum(pMan) == 1);

    Aig_ManForEachPoSeq(pMan, pObj, i)
    {
        pObjNew = Abc_NtkCreatePo(pNtkNew);

	string po_name = single_po_name;

	//cout<<"POS "<<pObj->Id<<endl;
        Abc_ObjAssignName(pObjNew, (char*) po_name.c_str(), NULL);
        pObj->pData = pObjNew;
    }
    assert(Abc_NtkCiNum(pNtkNew) == Aig_ManCiNum(pMan) - Aig_ManRegNum(pMan));
    assert(Abc_NtkCoNum(pNtkNew) == Aig_ManCoNum(pMan) - Aig_ManRegNum(pMan));
    // create as many latches as there are registers in the manager

    Aig_ManForEachLiLoSeq(pMan, pObjLi, pObjLo, i)
    {
        pObjNew = Abc_NtkCreateLatch(pNtkNew);
        pObjLi->pData = Abc_NtkCreateBi(pNtkNew);
        pObjLo->pData = Abc_NtkCreateBo(pNtkNew);
        Abc_ObjAddFanin(pObjNew, (Abc_Obj_t *) pObjLi->pData);
        Abc_ObjAddFanin((Abc_Obj_t *) pObjLo->pData, pObjNew);
        Abc_LatchSetInit0(pObjNew);
        //Abc_ObjName((Abc_Obj_t *)pObjLi->pData)
        //        string name = "LatchIn"+IntegerToString(i);
        //      Abc_ObjAssignName( (Abc_Obj_t *)pObjLi->pData, (char*)name.c_str(), NULL );
        //      name = "LatchOut_"+IntegerToString(i);
        //       Abc_ObjAssignName( (Abc_Obj_t *)pObjLo->pData,(char*)name.c_str(), NULL );
    }
    // rebuild the AIG
    vNodes = Aig_ManDfs(pMan, 1);
    Vec_PtrForEachEntry(Aig_Obj_t *, vNodes, pObj, i)
    if (Aig_ObjIsBuf(pObj))
        pObj->pData = (Abc_Obj_t *) Aig_ObjChild0Copy(pObj);
    else
        pObj->pData = Abc_AigAnd((Abc_Aig_t *) pNtkNew->pManFunc, (Abc_Obj_t *) Aig_ObjChild0Copy(pObj), (Abc_Obj_t *) Aig_ObjChild1Copy(pObj));
    Vec_PtrFree(vNodes);
    // connect the PO nodes

    Aig_ManForEachCo(pMan, pObj, i)
    {
        pObjNew = (Abc_Obj_t *) Aig_ObjChild0Copy(pObj);
        Abc_ObjAddFanin(Abc_NtkCo(pNtkNew, i), pObjNew);
    }

    //  Abc_NtkAddDummyPiNames( pNtkNew );
    //Abc_NtkAddDummyPoNames( pNtkNew );
    //    Abc_NtkAddDummyBoxNames( pNtkNew );

    // check the resulting AIG
    if (!Abc_NtkCheck(pNtkNew))
        cout << "obtainNetworkFromAIGWithIdNames(): Network check has failed.\n";
    return pNtkNew;
}



Aig_Obj_t* performDontCareOptimization(Aig_Man_t *aig_manager, Aig_Obj_t* should_be_one, Aig_Obj_t* dont_care)
{
	assert(should_be_one != NULL);
	assert(dont_care != NULL);
	if(Aig_IsComplement(dont_care) && Aig_Regular(dont_care) == createTrue(aig_manager)) //dont_care is false
	{
		return should_be_one;
	}

	unsigned long long int optimize_ms;
	struct timeval optimize_start_ms, optimize_finish_ms;
	gettimeofday (&optimize_start_ms, NULL); 

	// check the pre-condition
	set<string> support_should_be_one;
	computeSupport(should_be_one, support_should_be_one, aig_manager);
	set<string> support_dont_care;
	computeSupport(dont_care, support_dont_care, aig_manager);

	set<string> extra_variables;	
	set_difference(support_should_be_one.begin(), support_should_be_one.end(), original_variables.begin(), original_variables.end(),inserter(extra_variables, extra_variables.begin()));
	assert(extra_variables.empty());
	extra_variables.clear();
	set_difference(support_dont_care.begin(), support_dont_care.end(), original_variables.begin(), original_variables.end(),inserter(extra_variables, extra_variables.begin()));
	assert(extra_variables.empty());


	// create aig manager containing should_be_one
	Aig_Obj_t* should_be_one_CO;
	should_be_one_CO = Aig_ObjCreateCo( aig_manager, should_be_one );
	assert(should_be_one_CO != NULL);

	Aig_Man_t* should_be_one_aig_manager;
	should_be_one_aig_manager = simplifyUsingConeOfInfluence( aig_manager, Aig_ManCoNum(aig_manager)-1, 1);
	assert(should_be_one_aig_manager != NULL);

	// create aig manager containing care
	Aig_Obj_t* care_CO;
	care_CO = Aig_ObjCreateCo( aig_manager, Aig_Not(dont_care) );
	assert(care_CO != NULL);

	Aig_Man_t* care_aig_manager;
	care_aig_manager = simplifyUsingConeOfInfluence( aig_manager, Aig_ManCoNum(aig_manager)-1, 1);
	assert(care_aig_manager != NULL);

	// create the name maps
	map<int, string> should_be_one_name_map;
	map<int, string> care_name_map;

	int Ci_index = 1;
	for(map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.begin(); Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end(); Ci_id_to_Ci_name_map_it++)
	{
		int Ci_id_to_set = Ci_id_to_Ci_name_map_it->first;
		string Ci_name_to_set = Ci_id_to_Ci_name_map_it->second;

		if(Ci_id_to_set == Ci_index)
		{
			should_be_one_name_map.insert(make_pair(Ci_id_to_set, Ci_name_to_set));
			care_name_map.insert(make_pair(Ci_id_to_set, Ci_name_to_set));
		}
		else
		{
			Ci_id_to_set = Ci_index;
			Ci_name_to_set = "unused_";
			char Ci_index_char[100];
			sprintf(Ci_index_char, "%d", Ci_index);
			string Ci_index_string(Ci_index_char);
			Ci_name_to_set += Ci_index_string;

			should_be_one_name_map.insert(make_pair(Ci_id_to_set, Ci_name_to_set));
			care_name_map.insert(make_pair(Ci_id_to_set, Ci_name_to_set));
		}

		#ifdef DEBUG_SKOLEM 
		cout << endl << Ci_id_to_set << " --> " << Ci_name_to_set << " added to should_be_one_aig_manager and care_name_map";
		#endif

		Ci_index++;		
	}

	string Co_name_to_set = "po";
	Abc_Ntk_t* should_be_one_ntk = obtainNetworkFromAIGWithIdNames(should_be_one_aig_manager, should_be_one_name_map, Co_name_to_set);
	assert(should_be_one_ntk != NULL);
	Abc_Ntk_t* should_be_one_ntk_before_logic = should_be_one_ntk;
	should_be_one_ntk = Abc_NtkToLogic(should_be_one_ntk);
	assert(should_be_one_ntk != NULL);

	#ifdef DEBUG_SKOLEM 
	//Abc_FrameSetCurrentNetwork(abcFrame, Abc_NtkDup(should_be_one_ntk));
	//string command = "w should_be_one.v;";
	//cout << command << endl;
		
	//if (abcObj->comExecute(abcFrame, command))
	//{
	//	cout << "cannot execute command " << command << endl;
	//	assert(false);
	//}
	cout << "\nshould_be_one network created\n";
	#endif

	Abc_Ntk_t* care_ntk = obtainNetworkFromAIGWithIdNames(care_aig_manager, care_name_map, Co_name_to_set);
	assert(care_ntk != NULL);
	Abc_Ntk_t* care_ntk_before_logic = care_ntk;
	care_ntk = Abc_NtkToLogic(care_ntk);
	assert(care_ntk != NULL);

	#ifdef DEBUG_SKOLEM 
	//Abc_FrameSetCurrentNetwork(abcFrame, Abc_NtkDup(care_ntk));
	//command = "w care.v;";
	//cout << command << endl;
	//	
	//if (abcObj->comExecute(abcFrame, command))
	//{
	//	cout << "cannot execute command " << command << endl;
	//	assert(false);
	//}
	cout << "\ncare network created\n";
	#endif

	#ifdef DEBUG_SKOLEM
	cout << "\ncalling Abc_NtkMfs\n";	
	#endif

	should_be_one_ntk->pExcare = care_ntk;
	Mfs_Par_t Pars, * pPars = &Pars;
    	// set defaults
    	Abc_NtkMfsParsDefault( pPars );
    	// modify the current network
	pPars->fResub = 0; //resubstitution not necessary

	#ifdef DEBUG_SKOLEM
	pPars->fVeryVerbose = 1; 
	#endif

	int c = Abc_NtkMfs( should_be_one_ntk, pPars );
	assert(c != 0);
	assert(should_be_one_ntk != NULL);

	#ifdef DEBUG_SKOLEM
        cout << "\nAbc_NtkMfs finished\n";
	#endif

	Abc_Ntk_t* optimized_ntk = should_be_one_ntk;
	Abc_Ntk_t* optimized_ntk_before_strash = optimized_ntk;
	optimized_ntk = Abc_NtkStrash( optimized_ntk, 0, 0, 0 );
	assert(optimized_ntk != NULL);

	#ifdef DEBUG_SKOLEM 
	//Abc_FrameSetCurrentNetwork(abcFrame, Abc_NtkDup(optimized_ntk));
	//command = "w optimized.v;";
	//cout << command << endl;
	//	
	//if (abcObj->comExecute(abcFrame, command))
	//{
	//	cout << "cannot execute command " << command << endl;
	//	assert(false);
	//}
	cout << "\noptimized network created\n";
	#endif	
	
	// find optimized as a manager
	Aig_Man_t* optimized_aig_manager;
	optimized_aig_manager = Abc_NtkToDar(optimized_ntk, 0, 0);	
	assert(optimized_aig_manager != NULL);
	
	// transfer optimized to the aig manager
	int CiNum_aig_manager = Aig_ManCiNum( aig_manager );
	
	assert(Aig_ManCoNum(optimized_aig_manager) == 1);
	Aig_Obj_t* CO_optimized_aig_manager;
	CO_optimized_aig_manager = Aig_ManCo(optimized_aig_manager, 0);
	assert(CO_optimized_aig_manager != NULL);	

	Aig_Obj_t* optimized;
	optimized = Aig_Transfer(optimized_aig_manager, aig_manager, Aig_ObjChild0(CO_optimized_aig_manager), CiNum_aig_manager );
	assert(optimized != NULL);

	#ifdef DEBUG_SKOLEM 
	writeFormulaToFile(aig_manager, optimized, "optimized_function", ".v", 0, 0);
	#endif

	bool delete_unneeded_networks = true;
	if(delete_unneeded_networks)
	{
		Aig_ManStop(optimized_aig_manager);
		
		Aig_ManStop(care_aig_manager);

		Aig_ManStop(should_be_one_aig_manager);	

		Abc_NtkDelete( optimized_ntk );	

		Abc_NtkDelete(optimized_ntk_before_strash);

		Abc_NtkDelete(should_be_one_ntk_before_logic);

		Abc_NtkDelete(care_ntk_before_logic);
	}

	gettimeofday (&optimize_finish_ms, NULL);
   	optimize_ms = optimize_finish_ms.tv_sec * 1000 + optimize_finish_ms.tv_usec / 1000;
   	optimize_ms -= optimize_start_ms.tv_sec * 1000 + optimize_start_ms.tv_usec / 1000;
	//cout << "\nperformDontCareOptimization finished in " << optimize_ms << " milliseconds\n";
	total_time_in_dontcare_optimization_in_cegar = total_time_in_dontcare_optimization_in_cegar + optimize_ms;

	return optimized;
}


/* The functions related to dont' care optimization start here: we need to clean this part */

void testDontCareOptimization(ABC* abcObj, Abc_Frame_t* abcFrame)
{
	string original_circuit = "original_circuit.v";
	string command = "read " + original_circuit + ";";
	
	#ifdef DEBUG_SKOLEM
	cout << command << endl;
	#endif

	if (abcObj->comExecute(abcFrame, command))
    	{
	 	cout << "cannot execute " << command << endl;
		assert(false);
	}

	#ifdef DEBUG_SKOLEM //Printing original circuit
	command = "write original_circuit_read.v;";
	cout << command << endl;
		
	if (abcObj->comExecute(abcFrame, command))
	{
		cout << "cannot execute command " << command << endl;
		assert(false);
	}
	#endif	

	Abc_Ntk_t* original_circuit_ntk = abcFrame->pNtkCur;
	original_circuit_ntk = Abc_NtkDup(original_circuit_ntk);

	
	string dontcare_circuit = "dontcare_circuit.v";
	command = "read " + dontcare_circuit + ";";
	
	#ifdef DEBUG_SKOLEM
	cout << command << endl;
	#endif

	if (abcObj->comExecute(abcFrame, command))
    	{
	 	cout << "cannot execute " << command << endl;
		assert(false);
	}

	#ifdef DEBUG_SKOLEM //Printing dontcare_circuit
	command = "write dontcare_circuit_read.v;";
	cout << command << endl;
		
	if (abcObj->comExecute(abcFrame, command))
	{
		cout << "cannot execute command " << command << endl;
		assert(false);
	}
	#endif	

	Abc_Ntk_t* dontcare_circuit_ntk = abcFrame->pNtkCur;
	dontcare_circuit_ntk = Abc_NtkDup(dontcare_circuit_ntk);


	original_circuit_ntk->pExcare = dontcare_circuit_ntk;
	Mfs_Par_t Pars, * pPars = &Pars;
    	int c;
    	// set defaults
    	Abc_NtkMfsParsDefault( pPars );
    	//Extra_UtilGetoptReset();
    	assert(original_circuit_ntk != NULL);
        assert(Abc_NtkIsLogic(original_circuit_ntk));
	 // modify the current network
	pPars->fResub = 0; //This is fine!!
	pPars->fVeryVerbose =    1; //Just trying!!

	int option_of_function = 2;
	if(option_of_function == 1)
	{
		cout << "\nUsing the function dontCareOptimization\n";
        	c = dontCareOptimization( original_circuit_ntk, pPars );
	}
	else
	{	
		cout << "\nUsing the function Abc_NtkMfs\n";
		c = Abc_NtkMfs( original_circuit_ntk, pPars );
	}

	assert(c != 0);
        cout << "\nresynthesis done\n";

	#ifdef DEBUG_SKOLEM //Printing optimized circuit
	Abc_FrameSetCurrentNetwork(abcFrame, Abc_NtkDup(original_circuit_ntk));
	command = "write original_circuit_optimized.v;";
	cout << command << endl;
		
	if (abcObj->comExecute(abcFrame, command))
	{
		cout << "cannot execute command " << command << endl;
		assert(false);
	}
	#endif	
	
	#ifdef DEBUG_SKOLEM //Printing dontcare circuit
	Abc_FrameSetCurrentNetwork(abcFrame, Abc_NtkDup((Abc_Ntk_t *)original_circuit_ntk->pExcare));
	command = "write dontcare_circuit_after_optimization.v;";
	cout << command << endl;
		
	if (abcObj->comExecute(abcFrame, command))
	{
		cout << "cannot execute command " << command << endl;
		assert(false);
	}
	#endif
}




//extern int Abc_NtkMfsSolveSatResub( Mfs_Man_t * p, Abc_Obj_t * pNode, int iFanin, int fOnlyRemove, int fSkipUpdate );

int dontCareOptimization( Abc_Ntk_t * pNtk, Mfs_Par_t * pPars )
{
    extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );

    Bdc_Par_t Pars = {0}, * pDecPars = &Pars;
    ProgressBar * pProgress;
    Mfs_Man_t * p;
    Abc_Obj_t * pObj;
    Vec_Vec_t * vLevels;
    Vec_Ptr_t * vNodes;
    int i, k, nNodes, nFaninMax;
    abctime clk = Abc_Clock(), clk2;
    int nTotalNodesBeg = Abc_NtkNodeNum(pNtk);
    int nTotalEdgesBeg = Abc_NtkGetTotalFanins(pNtk);

    assert( Abc_NtkIsLogic(pNtk) );
    nFaninMax = Abc_NtkGetFaninMax(pNtk);
    if ( pPars->fResub )
    {
        if ( nFaninMax > 8 )
        {
            printf( "Nodes with more than %d fanins will not be processed.\n", 8 );
            nFaninMax = 8;
        }
    }
    else
    {
        if ( nFaninMax > MFS_FANIN_MAX )
        {
            printf( "Nodes with more than %d fanins will not be processed.\n", MFS_FANIN_MAX );
            nFaninMax = MFS_FANIN_MAX;
        }
    }
    // perform the network sweep
//    Abc_NtkSweep( pNtk, 0 );
    // convert into the AIG
    if ( !Abc_NtkToAig(pNtk) )
    {
        fprintf( stdout, "Converting to AIGs has failed.\n" );
        return 0;
    }
    assert( Abc_NtkHasAig(pNtk) );

    // start the manager
    p = Mfs_ManAlloc( pPars );
    p->pNtk = pNtk;
    p->nFaninMax = nFaninMax;

    // precomputer power-aware metrics
    /* Commented by Ajith 
    if ( pPars->fPower )
    {
        extern Vec_Int_t * Abc_NtkPowerEstimate( Abc_Ntk_t * pNtk, int fProbOne );
        if ( pPars->fResub )
            p->vProbs = Abc_NtkPowerEstimate( pNtk, 0 );
        else
            p->vProbs = Abc_NtkPowerEstimate( pNtk, 1 );
#if 0
        printf( "Total switching before = %7.2f.\n", Abc_NtkMfsTotalSwitching(pNtk) );
#else
		p->TotalSwitchingBeg = Abc_NtkMfsTotalSwitching(pNtk);
#endif
    }
    Commented by Ajith  ends here */

    if ( pNtk->pExcare )
    {
	cout << "\npExcare is there!!\n";

        Abc_Ntk_t * pTemp;
        if ( Abc_NtkPiNum((Abc_Ntk_t *)pNtk->pExcare) != Abc_NtkCiNum(pNtk) )
            printf( "The PI count of careset (%d) and logic network (%d) differ. Careset is not used.\n",
                Abc_NtkPiNum((Abc_Ntk_t *)pNtk->pExcare), Abc_NtkCiNum(pNtk) );
        else
        {
	    printf( "The PI count of careset (%d) and logic network (%d) same. \n",
                Abc_NtkPiNum((Abc_Ntk_t *)pNtk->pExcare), Abc_NtkCiNum(pNtk) );

            pTemp = Abc_NtkStrash( (Abc_Ntk_t *)pNtk->pExcare, 0, 0, 0 );
            p->pCare = Abc_NtkToDar( pTemp, 0, 0 );
            Abc_NtkDelete( pTemp );
            p->vSuppsInv = Aig_ManSupportsInverse( p->pCare );
        }
    }
    if ( p->pCare != NULL )
        printf( "Performing optimization with %d external care clauses.\n", Aig_ManCoNum(p->pCare) );
    
    // prepare the BDC manager
    if ( !pPars->fResub )
    {
	cout << "\nprepare the BDC manager\n";
        pDecPars->nVarsMax = (nFaninMax < 3) ? 3 : nFaninMax;
        pDecPars->fVerbose = pPars->fVerbose;
        p->vTruth = Vec_IntAlloc( 0 );
        p->pManDec = Bdc_ManAlloc( pDecPars );
    }

    // label the register outputs
    
    if ( p->pCare )
    {
	cout << "\nlabel the register outputs\n";

        Abc_NtkForEachCi( pNtk, pObj, i )
            pObj->pData = (void *)(ABC_PTRUINT_T)i;
    }

    // compute levels
    cout << "\ncompute levels\n";

    Abc_NtkLevel( pNtk );
    Abc_NtkStartReverseLevels( pNtk, pPars->nGrowthLevel );

    // compute don't-cares for each node
    cout << "\ncompute don't-cares for each node\n";

    nNodes = 0;
    p->nTotalNodesBeg = nTotalNodesBeg;
    p->nTotalEdgesBeg = nTotalEdgesBeg;
    if ( pPars->fResub )
    {
#if 0
        printf( "TotalSwitching (%7.2f --> ", Abc_NtkMfsTotalSwitching(pNtk) );
#endif
		/* Commented by Ajith 
		if (pPars->fPower)
		{
			Abc_NtkMfsPowerResub( p, pPars);
		} else
		Commented by Ajith  ends here */

		// { Commented by Ajith
	cout << "\nInside pPars->fResub\n";

        pProgress = Extra_ProgressBarStart( stdout, Abc_NtkObjNumMax(pNtk) );
        Abc_NtkForEachNode( pNtk, pObj, i )
        {
            if ( p->pPars->nDepthMax && (int)pObj->Level > p->pPars->nDepthMax )
                continue;
            if ( Abc_ObjFaninNum(pObj) < 2 || Abc_ObjFaninNum(pObj) > nFaninMax )
                continue;
            if ( !p->pPars->fVeryVerbose )
                Extra_ProgressBarUpdate( pProgress, i, NULL );
            if ( pPars->fResub )
                Abc_NtkMfsResub( p, pObj );
            else
                Abc_NtkMfsNode( p, pObj );
        }
        Extra_ProgressBarStop( pProgress );
#if 0
        printf( " %7.2f )\n", Abc_NtkMfsTotalSwitching(pNtk) );
#endif
   // } commented by Ajith
	} else
    {
#if 0
        printf( "Total switching before  = %7.2f,  ----> ", Abc_NtkMfsTotalSwitching(pNtk) );
#endif
	cout << "\nInside !pPars->fResub\n";

        pProgress = Extra_ProgressBarStart( stdout, Abc_NtkNodeNum(pNtk) );
        vLevels = Abc_NtkLevelize( pNtk );
        Vec_VecForEachLevelStart( vLevels, vNodes, k, 1 )
        {
            if ( !p->pPars->fVeryVerbose )
                Extra_ProgressBarUpdate( pProgress, nNodes, NULL );
            p->nNodesGainedLevel = 0;
            p->nTotConfLevel = 0;
            p->nTimeOutsLevel = 0;
            clk2 = Abc_Clock();
            Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pObj, i )
            {
                if ( p->pPars->nDepthMax && (int)pObj->Level > p->pPars->nDepthMax )
                    break;
                if ( Abc_ObjFaninNum(pObj) < 2 || Abc_ObjFaninNum(pObj) > nFaninMax )
                    continue;
                if ( pPars->fResub )
                    Abc_NtkMfsResub( p, pObj );
                else
                    Abc_NtkMfsNode( p, pObj );
            }
            nNodes += Vec_PtrSize(vNodes);
            if ( pPars->fVerbose )
            {
				/*
            printf( "Lev = %2d. Node = %5d. Ave gain = %5.2f. Ave conf = %5.2f. T/o = %6.2f %%  ",
                k, Vec_PtrSize(vNodes),
                1.0*p->nNodesGainedLevel/Vec_PtrSize(vNodes),
                1.0*p->nTotConfLevel/Vec_PtrSize(vNodes),
                100.0*p->nTimeOutsLevel/Vec_PtrSize(vNodes) );
            ABC_PRT( "Time", Abc_Clock() - clk2 );
			*/
            }
        }
        Extra_ProgressBarStop( pProgress );
        Vec_VecFree( vLevels );
#if 0
        printf( " %7.2f.\n", Abc_NtkMfsTotalSwitching(pNtk) );
#endif
    }
    Abc_NtkStopReverseLevels( pNtk );

    // perform the sweeping
    cout << "\nperform the sweeping\n";

    if ( !pPars->fResub )
    {
        extern void Abc_NtkBidecResyn( Abc_Ntk_t * pNtk, int fVerbose );
//        Abc_NtkSweep( pNtk, 0 );
//        Abc_NtkBidecResyn( pNtk, 0 );
    }

    p->nTotalNodesEnd = Abc_NtkNodeNum(pNtk);
    p->nTotalEdgesEnd = Abc_NtkGetTotalFanins(pNtk);

    // undo labesl
    cout << "\nundo labesl\n";

    if ( p->pCare )
    {
        Abc_NtkForEachCi( pNtk, pObj, i )
            pObj->pData = NULL;
    }

    /* Commented by Ajith 
    if ( pPars->fPower )
	{
#if 1
		p->TotalSwitchingEnd = Abc_NtkMfsTotalSwitching(pNtk);
//        printf( "Total switching after  = %7.2f.\n", Abc_NtkMfsTotalSwitching(pNtk) );
#else
        printf( "Total switching after  = %7.2f.\n", Abc_NtkMfsTotalSwitching(pNtk) );
#endif
	}
     commented by Ajith ends here */

    // free the manager
    p->timeTotal = Abc_Clock() - clk;
    Mfs_ManStop( p );
    return 1;
}

/* Commented by Ajith 
void Abc_NtkMfsPowerResub( Mfs_Man_t * p, Mfs_Par_t * pPars)
{
	int i, k;
	Abc_Obj_t *pFanin, *pNode;
	Abc_Ntk_t *pNtk = p->pNtk;
	int nFaninMax = Abc_NtkGetFaninMax(p->pNtk);

	Abc_NtkForEachNode( pNtk, pNode, k )
	{
		if ( p->pPars->nDepthMax && (int)pNode->Level > p->pPars->nDepthMax )
			continue;
		if ( Abc_ObjFaninNum(pNode) < 2 || Abc_ObjFaninNum(pNode) > nFaninMax )
			continue;
		if (Abc_WinNode(p, pNode) )  // something wrong
			continue;

		// solve the SAT problem
		// Abc_NtkMfsEdgePower( p, pNode );
		// try replacing area critical fanins
		Abc_ObjForEachFanin( pNode, pFanin, i )
			if ( Abc_MfsObjProb(p, pFanin) >= 0.35 && Abc_NtkMfsSolveSatResub( p, pNode, i, 0, 0 ) )
				continue;
	}

	Abc_NtkForEachNode( pNtk, pNode, k )
	{
		if ( p->pPars->nDepthMax && (int)pNode->Level > p->pPars->nDepthMax )
			continue;
		if ( Abc_ObjFaninNum(pNode) < 2 || Abc_ObjFaninNum(pNode) > nFaninMax )
			continue;
		if (Abc_WinNode(p, pNode) )  // something wrong
			continue;

		// solve the SAT problem
		// Abc_NtkMfsEdgePower( p, pNode );
		// try replacing area critical fanins
		Abc_ObjForEachFanin( pNode, pFanin, i )
			if ( Abc_MfsObjProb(p, pFanin) >= 0.35 && Abc_NtkMfsSolveSatResub( p, pNode, i, 0, 0 ) )
				continue;
	}

	Abc_NtkForEachNode( pNtk, pNode, k )
	{
		if ( p->pPars->nDepthMax && (int)pNode->Level > p->pPars->nDepthMax )
			continue;
		if ( Abc_ObjFaninNum(pNode) < 2 || Abc_ObjFaninNum(pNode) > nFaninMax )
			continue;
		if (Abc_WinNode(p, pNode) ) // something wrong
			continue;

		Abc_ObjForEachFanin( pNode, pFanin, i )
			if ( Abc_MfsObjProb(p, pFanin) >= 0.2 && Abc_NtkMfsSolveSatResub( p, pNode, i, 1, 0 ) )
				continue;
	}
/*
	Abc_NtkForEachNode( pNtk, pNode, k )
	{
		if ( p->pPars->nDepthMax && (int)pNode->Level > p->pPars->nDepthMax )
			continue;
		if ( Abc_ObjFaninNum(pNode) < 2 || Abc_ObjFaninNum(pNode) > nFaninMax - 2)
			continue;
		if (Abc_WinNode(p, pNode) ) // something wrong
			continue;

		Abc_ObjForEachFanin( pNode, pFanin, i )
			if ( Abc_MfsObjProb(p, pFanin) >= 0.37 && Abc_NtkMfsSolveSatResub2( p, pNode, i, -1 ) )
				continue;
	}
commented by Ajith ends here */
/* commented by Ajith
}
commented by Ajith ends here */

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkMfsResub( Mfs_Man_t * p, Abc_Obj_t * pNode )
{
    abctime clk;
    p->nNodesTried++;
    // prepare data structure for this node
    Mfs_ManClean( p );
    // compute window roots, window support, and window nodes
clk = Abc_Clock();
    p->vRoots = Abc_MfsComputeRoots( pNode, p->pPars->nWinTfoLevs, p->pPars->nFanoutsMax );
    p->vSupp  = Abc_NtkNodeSupport( p->pNtk, (Abc_Obj_t **)Vec_PtrArray(p->vRoots), Vec_PtrSize(p->vRoots) );
    p->vNodes = Abc_NtkDfsNodes( p->pNtk, (Abc_Obj_t **)Vec_PtrArray(p->vRoots), Vec_PtrSize(p->vRoots) );
p->timeWin += Abc_Clock() - clk;
    if ( p->pPars->nWinMax && Vec_PtrSize(p->vNodes) > p->pPars->nWinMax )
    {
        p->nMaxDivs++;
        return 1;
    }
    // compute the divisors of the window
clk = Abc_Clock();
    p->vDivs  = Abc_MfsComputeDivisors( p, pNode, Abc_ObjRequiredLevel(pNode) - 1 );
    p->nTotalDivs += Vec_PtrSize(p->vDivs) - Abc_ObjFaninNum(pNode);
p->timeDiv += Abc_Clock() - clk;
    // construct AIG for the window
clk = Abc_Clock();
    p->pAigWin = Abc_NtkConstructAig( p, pNode );
p->timeAig += Abc_Clock() - clk;
    // translate it into CNF
clk = Abc_Clock();
    p->pCnf = Cnf_DeriveSimple( p->pAigWin, 1 + Vec_PtrSize(p->vDivs) );
p->timeCnf += Abc_Clock() - clk;
    // create the SAT problem
clk = Abc_Clock();
    p->pSat = Abc_MfsCreateSolverResub( p, NULL, 0, 0 );
    if ( p->pSat == NULL )
    {
        p->nNodesBad++;
        return 1;
    }
//clk = Abc_Clock();
//    if ( p->pPars->fGiaSat )
//        Abc_NtkMfsConstructGia( p );
//p->timeGia += Abc_Clock() - clk;
    // solve the SAT problem
    if ( p->pPars->fPower )
        Abc_NtkMfsEdgePower( p, pNode );
    else if ( p->pPars->fSwapEdge )
        Abc_NtkMfsEdgeSwapEval( p, pNode );
    else
    {
        Abc_NtkMfsResubNode( p, pNode );
        if ( p->pPars->fMoreEffort )
            Abc_NtkMfsResubNode2( p, pNode );
    }
p->timeSat += Abc_Clock() - clk;
//    if ( p->pPars->fGiaSat )
//        Abc_NtkMfsDeconstructGia( p );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkMfsNode( Mfs_Man_t * p, Abc_Obj_t * pNode )
{
    Hop_Obj_t * pObj;
    int RetValue;
    float dProb;
    extern Hop_Obj_t * Abc_NodeIfNodeResyn( Bdc_Man_t * p, Hop_Man_t * pHop, Hop_Obj_t * pRoot, int nVars, Vec_Int_t * vTruth, unsigned * puCare, float dProb );

    int nGain;
    abctime clk;
    p->nNodesTried++;
    // prepare data structure for this node
    Mfs_ManClean( p );
    // compute window roots, window support, and window nodes
clk = Abc_Clock();
    p->vRoots = Abc_MfsComputeRoots( pNode, p->pPars->nWinTfoLevs, p->pPars->nFanoutsMax );
    p->vSupp  = Abc_NtkNodeSupport( p->pNtk, (Abc_Obj_t **)Vec_PtrArray(p->vRoots), Vec_PtrSize(p->vRoots) );
    p->vNodes = Abc_NtkDfsNodes( p->pNtk, (Abc_Obj_t **)Vec_PtrArray(p->vRoots), Vec_PtrSize(p->vRoots) );
p->timeWin += Abc_Clock() - clk;
    // count the number of patterns
//    p->dTotalRatios += Abc_NtkConstraintRatio( p, pNode );
    // construct AIG for the window
clk = Abc_Clock();
    p->pAigWin = Abc_NtkConstructAig( p, pNode );
p->timeAig += Abc_Clock() - clk;
    // translate it into CNF
clk = Abc_Clock();
    p->pCnf = Cnf_DeriveSimple( p->pAigWin, Abc_ObjFaninNum(pNode) );
p->timeCnf += Abc_Clock() - clk;
    // create the SAT problem
clk = Abc_Clock();
    p->pSat = (sat_solver *)Cnf_DataWriteIntoSolver( p->pCnf, 1, 0 );
    if ( p->pSat && p->pPars->fOneHotness )
        Abc_NtkAddOneHotness( p );
    if ( p->pSat == NULL )
        return 0;
    // solve the SAT problem
    RetValue = Abc_NtkMfsSolveSat( p, pNode );
    p->nTotConfLevel += p->pSat->stats.conflicts;
p->timeSat += Abc_Clock() - clk;
    if ( RetValue == 0 )
    {
        p->nTimeOutsLevel++;
        p->nTimeOuts++;
        return 0;
    }
    // minimize the local function of the node using bi-decomposition
    assert( p->nFanins == Abc_ObjFaninNum(pNode) );
    dProb = p->pPars->fPower? ((float *)p->vProbs->pArray)[pNode->Id] : -1.0;
    pObj = Abc_NodeIfNodeResyn( p->pManDec, (Hop_Man_t *)pNode->pNtk->pManFunc, (Hop_Obj_t *)pNode->pData, p->nFanins, p->vTruth, p->uCare, dProb );
    nGain = Hop_DagSize((Hop_Obj_t *)pNode->pData) - Hop_DagSize(pObj);
    if ( nGain >= 0 )
    {
        p->nNodesDec++;
        p->nNodesGained += nGain;
        p->nNodesGainedLevel += nGain;
        pNode->pData = pObj;
    }
    return 1;
}


int Abc_WinNode(Mfs_Man_t * p, Abc_Obj_t *pNode)
{
//    abctime clk;
//    Abc_Obj_t * pFanin;
//    int i;

    p->nNodesTried++;
    // prepare data structure for this node
    Mfs_ManClean( p );
    // compute window roots, window support, and window nodes
    p->vRoots = Abc_MfsComputeRoots( pNode, p->pPars->nWinTfoLevs, p->pPars->nFanoutsMax );
    p->vSupp  = Abc_NtkNodeSupport( p->pNtk, (Abc_Obj_t **)Vec_PtrArray(p->vRoots), Vec_PtrSize(p->vRoots) );
    p->vNodes = Abc_NtkDfsNodes( p->pNtk, (Abc_Obj_t **)Vec_PtrArray(p->vRoots), Vec_PtrSize(p->vRoots) );
    if ( p->pPars->nWinMax && Vec_PtrSize(p->vNodes) > p->pPars->nWinMax )
        return 1;
    // compute the divisors of the window
    p->vDivs  = Abc_MfsComputeDivisors( p, pNode, Abc_ObjRequiredLevel(pNode) - 1 );
    p->nTotalDivs += Vec_PtrSize(p->vDivs) - Abc_ObjFaninNum(pNode);
    // construct AIG for the window
    p->pAigWin = Abc_NtkConstructAig( p, pNode );
    // translate it into CNF
    p->pCnf = Cnf_DeriveSimple( p->pAigWin, 1 + Vec_PtrSize(p->vDivs) );
    // create the SAT problem
    p->pSat = Abc_MfsCreateSolverResub( p, NULL, 0, 0 );
    if ( p->pSat == NULL )
    {
        p->nNodesBad++;
        return 1;
    }
	return 0;
}


static inline Hop_Obj_t * Bdc_FunCopyHop( Bdc_Fun_t * pObj )  { return Hop_NotCond( (Hop_Obj_t *)Bdc_FuncCopy(Bdc_Regular(pObj)), Bdc_IsComplement(pObj) );  }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Resynthesizes nodes using bi-decomposition.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Hop_Obj_t * Abc_NodeIfNodeResyn( Bdc_Man_t * p, Hop_Man_t * pHop, Hop_Obj_t * pRoot, int nVars, Vec_Int_t * vTruth, unsigned * puCare, float dProb )
{
    unsigned * pTruth;
    Bdc_Fun_t * pFunc;
    int nNodes, i;
    assert( nVars <= 16 );
    // derive truth table
    pTruth = Hop_ManConvertAigToTruth( pHop, Hop_Regular(pRoot), nVars, vTruth, 0 );
    if ( Hop_IsComplement(pRoot) )
        Extra_TruthNot( pTruth, pTruth, nVars );
    // perform power-aware decomposition
    if ( dProb >= 0.0 )
    {
        float Prob = (float)2.0 * dProb * (1.0 - dProb);
        assert( Prob >= 0.0 && Prob <= 0.5 );
        if ( Prob >= 0.4 )
        {
            Extra_TruthNot( puCare, puCare, nVars );
            if ( dProb > 0.5 ) // more 1s than 0s
                Extra_TruthOr( pTruth, pTruth, puCare, nVars );
            else
                Extra_TruthSharp( pTruth, pTruth, puCare, nVars );
            Extra_TruthNot( puCare, puCare, nVars );
            // decompose truth table
            Bdc_ManDecompose( p, pTruth, NULL, nVars, NULL, 1000 );
        }
        else
        {
            // decompose truth table
            Bdc_ManDecompose( p, pTruth, puCare, nVars, NULL, 1000 );
        }
    }
    else
    {
        // decompose truth table
        Bdc_ManDecompose( p, pTruth, puCare, nVars, NULL, 1000 );
    }
    // convert back into HOP
    Bdc_FuncSetCopy( Bdc_ManFunc( p, 0 ), Hop_ManConst1( pHop ) );
    for ( i = 0; i < nVars; i++ )
        Bdc_FuncSetCopy( Bdc_ManFunc( p, i+1 ), Hop_ManPi( pHop, i ) );
    nNodes = Bdc_ManNodeNum(p);
    for ( i = nVars + 1; i < nNodes; i++ )
    {
        pFunc = Bdc_ManFunc( p, i );
        Bdc_FuncSetCopy( pFunc, Hop_And( pHop, Bdc_FunCopyHop(Bdc_FuncFanin0(pFunc)), Bdc_FunCopyHop(Bdc_FuncFanin1(pFunc)) ) );
    }
    return Bdc_FunCopyHop( Bdc_ManRoot(p) );
}

/**Function*************************************************************

  Synopsis    [Resynthesizes nodes using bi-decomposition.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkBidecResyn( Abc_Ntk_t * pNtk, int fVerbose )
{
    Bdc_Par_t Pars = {0}, * pPars = &Pars;
    Bdc_Man_t * p;
    Abc_Obj_t * pObj;
    Vec_Int_t * vTruth;
    int i, nGainTotal = 0, nNodes1, nNodes2;
    abctime clk = Abc_Clock();
    assert( Abc_NtkIsLogic(pNtk) );
    if ( !Abc_NtkToAig(pNtk) )
        return;
    pPars->nVarsMax = Abc_NtkGetFaninMax( pNtk );
    pPars->fVerbose = fVerbose;
    if ( pPars->nVarsMax > 15 )
    {
        if ( fVerbose )
        printf( "Resynthesis is not performed for nodes with more than 15 inputs.\n" );
        pPars->nVarsMax = 15;
    }
    vTruth = Vec_IntAlloc( 0 );
    p = Bdc_ManAlloc( pPars );
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        if ( Abc_ObjFaninNum(pObj) > 15 )
            continue;
        nNodes1 = Hop_DagSize((Hop_Obj_t *)pObj->pData);
        pObj->pData = Abc_NodeIfNodeResyn( p, (Hop_Man_t *)pNtk->pManFunc, (Hop_Obj_t *)pObj->pData, Abc_ObjFaninNum(pObj), vTruth, NULL, -1.0 );
        nNodes2 = Hop_DagSize((Hop_Obj_t *)pObj->pData);
        nGainTotal += nNodes1 - nNodes2;
    }
    Bdc_ManFree( p );
    Vec_IntFree( vTruth );
    if ( fVerbose )
    {
    printf( "Total gain in AIG nodes = %d.  ", nGainTotal );
    ABC_PRT( "Total runtime", Abc_Clock() - clk );
    }
}


/*
Aig_Man_t * simplifyUsingConeOfInfluenceWithNameMapForCone( Aig_Man_t * p, int iPoNum, int fAddRegs, map<int, string> &name_map_of_clone)
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i;
    //assert( Aig_ManRegNum(p) > 0 );
    assert( iPoNum < Aig_ManCoNum(p)-Aig_ManRegNum(p) );
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    // create the PIs
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachCi( p, pObj, i )
    {
	int pObj_id = pObj->Id;
	map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(pObj_id);
	assert(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end());
	string Ci_name = Ci_id_to_Ci_name_map_it->second;

        pObj->pData = Aig_ObjCreateCi( pNew );
    }
    // set registers
    pNew->nRegs    = fAddRegs? p->nRegs : 0;
    pNew->nTruePis = fAddRegs? p->nTruePis : p->nTruePis + p->nRegs;
    pNew->nTruePos = 1;
    // duplicate internal nodes
    Aig_ManForEachNode( p, pObj, i )
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    // create the PO
    pObj = Aig_ManCo( p, iPoNum );
    Aig_ObjCreateCo( pNew, Aig_ObjChild0Copy(pObj) );
    // create register inputs with MUXes
    if ( fAddRegs )
    {
        Aig_ManForEachLiSeq( p, pObj, i )
            Aig_ObjCreateCo( pNew, Aig_ObjChild0Copy(pObj) );
    }
    Aig_ManCleanup( pNew );
    return pNew;
}*/


/* The functions related to dont' care optimization end here */



void convertToQDimacs(Aig_Obj_t* formula, set<string> &ex_quantifiers, Aig_Man_t* aig_manager, string qdimacs_file)
{
	#ifdef DEBUG_SKOLEM
	showSet(ex_quantifiers, "ex_quantifiers");
	#endif

	assert(formula != NULL);
	
	Aig_Obj_t* formula_CO = Aig_ObjCreateCo( aig_manager, formula );
	assert(formula_CO != NULL);
	
	Cnf_Dat_t * pCnf = Cnf_Derive( aig_manager, Aig_ManCoNum(aig_manager) );
	        
	Vec_Int_t * vVarMap, * vForAlls, * vExists, * vTemp;
        Aig_Obj_t * pObj;

	int nPars;
	nPars = ex_quantifiers.size();
	#ifdef DEBUG_SKOLEM
	cout << "\nnPars = " << nPars << endl;
	#endif

	  
        int i, Entry;
        // create var map
        vVarMap = Vec_IntStart( pCnf->nVars );
        Aig_ManForEachCi( aig_manager, pObj, i )
	{
		int Ci_id = pObj->Id;

		map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(Ci_id);
		assert(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end());
		string Ci_name = Ci_id_to_Ci_name_map_it->second;
		
		#ifdef DEBUG_SKOLEM
		cout << "\nCi_id = " << Ci_id << "\tCi_name = " << Ci_name << endl;
		#endif
		
		if(ex_quantifiers.find(Ci_name) != ex_quantifiers.end()) //Ci_name
		// is a variable to be eliminated; hence to be existentially quantified
		{
			#ifdef DEBUG_SKOLEM
			cout << endl << Ci_name << " is a variable to be eliminated; hence to be existentially quantified\n";
			#endif
                	Vec_IntWriteEntry( vVarMap, pCnf->pVarNums[Ci_id], 1 );
		}
		else //Ci_name is a variable to remain; hence to be universally quantified
		{
			#ifdef DEBUG_SKOLEM
			cout << endl << Ci_name << " is a variable to remain; hence to be universally quantified\n";
			#endif
                	Vec_IntWriteEntry( vVarMap, pCnf->pVarNums[Ci_id], 2 );
		}
	}

        // create various maps
        vExists = Vec_IntAlloc( nPars );	
        vForAlls = Vec_IntAlloc( Aig_ManCiNum(aig_manager) - nPars );
	vTemp = Vec_IntAlloc( pCnf->nVars - Aig_ManCiNum(aig_manager));

	#ifdef DEBUG_SKOLEM
	cout << "\nnPars = " << nPars << endl;
	cout << "\nAig_ManCiNum(aig_manager) - nPars = " << Aig_ManCiNum(aig_manager) - nPars << endl;
	cout << "\npCnf->nVars - Aig_ManCiNum(aig_manager) = " << pCnf->nVars - Aig_ManCiNum(aig_manager) << endl;
	#endif

        Vec_IntForEachEntry( vVarMap, Entry, i )
	{
         	if ( Entry == 1)
		{
                	Vec_IntPush( vExists, i );

			#ifdef DEBUG_SKOLEM
			cout << endl << i << " inserted into vExists";
			#endif
		}
            	else if ( Entry == 2)
		{
                	Vec_IntPush( vForAlls, i );
			
			#ifdef DEBUG_SKOLEM
			cout << endl << i << " inserted into vForAlls";
			#endif
		}
		else
		{
                	Vec_IntPush( vTemp, i );

			#ifdef DEBUG_SKOLEM
			cout << endl << i << " inserted into vTemp";
			#endif			
		}
	}
        
	// write CNF in to file
	int * pLit, * pStop, VarId;
   	FILE *pFile = fopen( qdimacs_file.c_str(), "w" );
	assert(pFile != NULL);
	
	fprintf( pFile, "c Qdimacs file from skolem function generator\n" );
    	fprintf( pFile, "p cnf %d %d\n", pCnf->nVars, pCnf->nClauses+1 );
	if ( vForAlls )
	{
		fprintf( pFile, "a " );
		Vec_IntForEachEntry( vForAlls, VarId, i )
		    fprintf( pFile, "%d ", VarId+1 );
		fprintf( pFile, "0\n" );
	}
	if ( vExists )
    	{
        	fprintf( pFile, "e " );
        	Vec_IntForEachEntry( vExists, VarId, i )
        	    fprintf( pFile, "%d ", VarId+1 );
        	//fprintf( pFile, "0\n" );
    	}
	if ( vTemp )
	{
		//fprintf( pFile, "e " );
		Vec_IntForEachEntry( vTemp, VarId, i )
		    fprintf( pFile, "%d ", VarId+1 );
		fprintf( pFile, "0\n" );
	}

	for ( i = 0; i < pCnf->nClauses; i++ )
	{
		for ( pLit = pCnf->pClauses[i], pStop = pCnf->pClauses[i+1]; pLit < pStop; pLit++ )
		    fprintf( pFile, "%d ", (*pLit & 1)? -(*pLit >> 1)-1 : (*pLit >> 1)+1);
		fprintf( pFile, "0\n" );
	}
	int rootLit = toLitCond( pCnf->pVarNums[formula_CO->Id], 0 );
	fprintf( pFile, "%d 0\n", (rootLit & 1)? -(rootLit >> 1)-1 : (rootLit >> 1)+1);
	fprintf( pFile, "\n" );
	fclose( pFile );
        
	Cnf_DataFree( pCnf );
        Vec_IntFree( vForAlls );
        Vec_IntFree( vExists );
        Vec_IntFree( vVarMap );
	Vec_IntFree( vTemp );
        cout << "\nQBF formula written into file " << qdimacs_file << endl;

}

void getFactorsThroughTsietinInTopologicalManner(Aig_Man_t* aig_manager, Aig_Obj_t* formula, set<Aig_Obj_t*> &factors, vector<string> &tsietin_variables)
{
	// Ideally wanted t_HashTable<int, Aig_Obj_t*> tsietin_label_table; but there's some
	// problem with this hash_table declaration

	map<int, Aig_Obj_t*> tsietin_label_table;
	int tsietin_count = 1;

	#ifdef DEBUG_SKOLEM
	cout << "\nLabeling nodes in formula with Tsietin variables\n";
	#endif
	
	// label the nodes in formula by Tsietin variables in Topological manner
	labelNodesByTsietinVariables(aig_manager, formula, tsietin_label_table, tsietin_count, tsietin_variables);

	#ifdef DEBUG_SKOLEM
	cout << "\nNodes in formula labeled with Tsietin variables; tsietin_count = " << tsietin_count << endl;
	#endif

	#ifdef DEBUG_SKOLEM
	cout << "\nObtaining factors\n";
	#endif	
	
	// obtain the factors
	t_HashTable<int, bool> visited;
	Aig_Obj_t* root_tsietin_variable = getFactorsThroughTsietinRecursiveWithLabeledNodes(aig_manager, formula, factors, tsietin_label_table, visited);
	assert(root_tsietin_variable != NULL);

	#ifdef DEBUG_SKOLEM
	cout << "\nFactors obtained\n";
	#endif	
	
	if(Aig_IsComplement(formula))
	{
		factors.insert(createNot(root_tsietin_variable, aig_manager));
	}
	else
	{
		factors.insert(root_tsietin_variable);
	}

	number_of_tsietin_variables = tsietin_count - 1;		
}


void labelNodesByTsietinVariables(Aig_Man_t* aig_manager, Aig_Obj_t* formula, map<int, Aig_Obj_t*>  &tsietin_label_table, int &tsietin_count, vector<string> &tsietin_variables)
{
	stack<Aig_Obj_t*> topo_stack;

	t_HashTable<int, bool> visited;
	obtainNodesInTopologicalOrder(aig_manager, formula, topo_stack, visited);

	while(!topo_stack.empty())
	{
		Aig_Obj_t* node_to_process = topo_stack.top();
		assert(node_to_process != NULL);

		topo_stack.pop();
		
		// no need to apply Aig_Regular as only regular nodes are inserted
		assert(Aig_IsComplement(node_to_process) == 0);
		int key = Aig_ObjId(node_to_process);

		map<int, Aig_Obj_t*>::iterator tsietin_label_table_it = tsietin_label_table.find(key);
		assert(tsietin_label_table_it == tsietin_label_table.end());

		Aig_Obj_t* tsietin_variable_object = Aig_ObjCreateCi(aig_manager);	
		assert(tsietin_variable_object != NULL);
								
		char tsietin_count_char[100];
		sprintf(tsietin_count_char, "%d", tsietin_count);
		string tsietin_count_string(tsietin_count_char);
		string tsietin_object_string = "tsietin_";
		tsietin_object_string += tsietin_count_string;
		tsietin_count++;
		tsietin_variables.push_back(tsietin_object_string);

		int tsietin_object_id = Aig_ObjId(tsietin_variable_object); 
		Ci_id_to_Ci_name_map.insert(make_pair(tsietin_object_id, tsietin_object_string));
		Ci_name_to_Ci_number_map.insert(make_pair(tsietin_object_string, number_of_Cis));	
		number_of_Cis++;

		tsietin_label_table.insert(make_pair(key, tsietin_variable_object));
	}
}


void obtainNodesInTopologicalOrder(Aig_Man_t* aig_manager, Aig_Obj_t* formula, stack<Aig_Obj_t*> &topo_stack, t_HashTable<int, bool> &visited)
{
	formula = Aig_Regular(formula);
	int key = Aig_ObjId(formula);

	#ifdef DEBUG_SKOLEM
		cout << "\nformula = " << formula << "\tkey = " << key << endl;
	#endif

	t_HashTable<int, bool>::iterator visited_it = visited.find(key);
	if (visited_it != visited.end()) // visited already
	{
		#ifdef DEBUG_SKOLEM
			cout << "\nExists in hashtable\n";
		#endif	
		// don't go down
	}
	else if(formula->Type == AIG_OBJ_AND)// child_1 \wedge child_2 encountered
	{	
		visited[key] = true;
			
		// go down and call recursively			
		obtainNodesInTopologicalOrder(aig_manager, Aig_ObjChild0(formula), topo_stack, visited);
		obtainNodesInTopologicalOrder(aig_manager, Aig_ObjChild1(formula), topo_stack, visited);
		
		// push on to topo_stack
		topo_stack.push(formula);
	}
}


Aig_Obj_t* getFactorsThroughTsietinRecursiveWithLabeledNodes(Aig_Man_t* aig_manager, Aig_Obj_t* formula, set<Aig_Obj_t*> &factors, map<int, Aig_Obj_t*>  &tsietin_label_table, t_HashTable<int, bool> &visited)
{
	formula = Aig_Regular(formula);
	int key = Aig_ObjId(formula);

	#ifdef DEBUG_SKOLEM
		cout << "\nformula = " << formula << "\tkey = " << key << endl;
	#endif

	t_HashTable<int, bool>::iterator visited_it = visited.find(key);
	if (visited_it != visited.end()) // visited already
	{
		#ifdef DEBUG_SKOLEM
			cout << "\nExists in hashtable\n";
		#endif
		
		// don't go down; return the object of Tsietin variable
		Aig_Obj_t* tsietin_variable_object;
		map<int, Aig_Obj_t*>::iterator tsietin_label_table_it = tsietin_label_table.find(key);
		assert(tsietin_label_table_it != tsietin_label_table.end());
		tsietin_variable_object = tsietin_label_table_it->second;	
		assert(tsietin_variable_object != NULL);
		return tsietin_variable_object;
	}
	else
	{
		if(formula->Type == AIG_OBJ_AND)// child_1 \wedge child_2 encountered
		{
			#ifdef DEBUG_SKOLEM
				cout << "\nAIG_OBJ_AND encountered\n";
			#endif

			// new AND node encountered; get the object of Tsietin variable
			Aig_Obj_t* tsietin_variable_object;
			map<int, Aig_Obj_t*>::iterator tsietin_label_table_it = tsietin_label_table.find(key);
			assert(tsietin_label_table_it != tsietin_label_table.end());
			tsietin_variable_object = tsietin_label_table_it->second;	
			assert(tsietin_variable_object != NULL);

			string tsietin_object_string;
			int tsietin_object_id = Aig_ObjId(tsietin_variable_object); 
			map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(tsietin_object_id);
			tsietin_object_string = Ci_id_to_Ci_name_map_it->second;

			visited[key] = true;
			
			// go down and call recursively			
			Aig_Obj_t* child_1_object = getFactorsThroughTsietinRecursiveWithLabeledNodes(aig_manager, Aig_ObjChild0(formula), factors, tsietin_label_table, visited);
			assert(child_1_object != NULL);

			Aig_Obj_t* child_2_object = getFactorsThroughTsietinRecursiveWithLabeledNodes(aig_manager, Aig_ObjChild1(formula), factors, tsietin_label_table, visited);
			assert(child_2_object != NULL);

			#ifdef DEBUG_SKOLEM
				cout << "\nCreating factors for the new conjunction " << tsietin_variable_object << "(" << child_1_object << "," << child_2_object <<")\n";
			#endif

			getNewTsietinFactors(aig_manager, tsietin_variable_object, child_1_object, child_2_object, Aig_ObjFaninC0(formula), Aig_ObjFaninC1(formula), factors); 

			collectExactSkolemFunctionForTsietinVariable(aig_manager, tsietin_object_string, child_1_object, child_2_object, Aig_ObjFaninC0(formula), Aig_ObjFaninC1(formula));			

			return tsietin_variable_object;
						
		}
		else if(formula->Type == AIG_OBJ_CI) //CI encountered
		{
			#ifdef DEBUG_SKOLEM
				cout << "\nAIG_OBJ_CI encountered\n";
			#endif
			
			// return the CI
			visited[key] = true;
			tsietin_label_table.insert(make_pair(key, formula));
			return formula;
			
		}
		else if(formula->Type == AIG_OBJ_CONST1) // 1 encountered
		{
			#ifdef DEBUG_SKOLEM
				cout << "\nAIG_OBJ_CONST1 encountered\n";
			#endif

			// return constant-one
			visited[key] = true;
			tsietin_label_table.insert(make_pair(key, formula));
			return formula;			
		}		
		else if(formula->Type == AIG_OBJ_CO) //CO encountered
		{
			#ifdef DEBUG_SKOLEM
				cout << "\nAIG_OBJ_CO encountered\n";
			#endif
			assert(false);
			
		}
		else
		{
			cout << "\nUnknown formula->Type encountered in helper.cpp::getFactorsThroughTsietinRecursiveWithLabeledNodes\n";		
			assert(false);
		}
	} // if(!label exists already) ends here
}//function ends here				




void getFactorsThroughTsietin(Aig_Man_t* aig_manager, Aig_Obj_t* formula, set<Aig_Obj_t*> &factors, vector<string> &tsietin_variables)
{
	//Ideally wanted t_HashTable<int, Aig_Obj_t*> tsietin_label_table; but there's some
	// problem with this hash_table declaration

	map<int, Aig_Obj_t*> tsietin_label_table;
	int tsietin_count = 1;
	
	Aig_Obj_t* root_tsietin_variable = getFactorsThroughTsietinRecursive(aig_manager, formula, factors, tsietin_label_table, tsietin_count, tsietin_variables);
	assert(root_tsietin_variable != NULL);
	
	if(Aig_IsComplement(formula))
	{
		factors.insert(createNot(root_tsietin_variable, aig_manager));
	}
	else
	{
		factors.insert(root_tsietin_variable);
	}

	number_of_tsietin_variables = tsietin_count - 1;
		
}

Aig_Obj_t* getFactorsThroughTsietinRecursive(Aig_Man_t* aig_manager, Aig_Obj_t* formula, set<Aig_Obj_t*> &factors,map<int, Aig_Obj_t*>  &tsietin_label_table, int &tsietin_count, vector<string> &tsietin_variables)
{
	formula = Aig_Regular(formula);
	int key = Aig_ObjId(formula);

	#ifdef DEBUG_SKOLEM
		cout << "\nformula = " << formula << "\tkey = " << key << endl;
	#endif

	map<int, Aig_Obj_t*>::iterator LabelTable_it = tsietin_label_table.find(key);
	if (LabelTable_it != tsietin_label_table.end()) // label exists already, i.e. traversed already
	{
		#ifdef DEBUG_SKOLEM
			cout << "\nExists in hashtable\n";
		#endif

		return LabelTable_it->second;
	}
	else
	{
		if(formula->Type == AIG_OBJ_AND)// child_1 \wedge child_2 encountered
		{
			#ifdef DEBUG_SKOLEM
				cout << "\nAIG_OBJ_AND encountered\n";
			#endif

			// new AND node encountered; need to create new variable
			// representing the AND node
			Aig_Obj_t* tsietin_variable_object = Aig_ObjCreateCi(aig_manager);	
			assert(tsietin_variable_object != NULL);
			
			char tsietin_count_char[100];
			sprintf(tsietin_count_char, "%d", tsietin_count);
			string tsietin_count_string(tsietin_count_char);
			string tsietin_object_string = "tsietin_";
			tsietin_object_string += tsietin_count_string;
			tsietin_count++;
			tsietin_variables.push_back(tsietin_object_string);

			int tsietin_object_id = Aig_ObjId(tsietin_variable_object); 
			Ci_id_to_Ci_name_map.insert(make_pair(tsietin_object_id, tsietin_object_string));
			Ci_name_to_Ci_number_map.insert(make_pair(tsietin_object_string, number_of_Cis));	
			number_of_Cis++;

			tsietin_label_table.insert(make_pair(key, tsietin_variable_object));
			// variable representing the node created

			Aig_Obj_t* child_1_object = getFactorsThroughTsietinRecursive(aig_manager, Aig_ObjChild0(formula), factors, tsietin_label_table, tsietin_count, tsietin_variables);
			assert(child_1_object != NULL);

			Aig_Obj_t* child_2_object = getFactorsThroughTsietinRecursive(aig_manager, Aig_ObjChild1(formula), factors, tsietin_label_table, tsietin_count, tsietin_variables);
			assert(child_2_object != NULL);

			#ifdef DEBUG_SKOLEM
				cout << "\nCreating factors for the new conjunction " << tsietin_variable_object << "(" << child_1_object << "," << child_2_object <<")\n";
			#endif

			getNewTsietinFactors(aig_manager, tsietin_variable_object, child_1_object, child_2_object, Aig_ObjFaninC0(formula), Aig_ObjFaninC1(formula), factors); 

			collectExactSkolemFunctionForTsietinVariable(aig_manager, tsietin_object_string, child_1_object, child_2_object, Aig_ObjFaninC0(formula), Aig_ObjFaninC1(formula));			

			return tsietin_variable_object;
						
		}
		else if(formula->Type == AIG_OBJ_CI) //CI encountered
		{
			#ifdef DEBUG_SKOLEM
				cout << "\nAIG_OBJ_CI encountered\n";
			#endif
			
			tsietin_label_table.insert(make_pair(key, formula));
			return formula;
			
		}
		else if(formula->Type == AIG_OBJ_CONST1) // 1 encountered
		{
			#ifdef DEBUG_SKOLEM
				cout << "\nAIG_OBJ_CONST1 encountered\n";
			#endif

			tsietin_label_table.insert(make_pair(key, formula));
			return formula;			
		}		
		else if(formula->Type == AIG_OBJ_CO) //CO encountered
		{
			#ifdef DEBUG_SKOLEM
				cout << "\nAIG_OBJ_CO encountered\n";
			#endif
			assert(false);
			
		}
		else
		{
			cout << "\nUnknown formula->Type encountered in helper.cpp::getFactorsThroughTsietinRecursive\n";		
			assert(false);
		}
	} // if(!label exists already) ends here
}//function ends here				


void getNewTsietinFactors(Aig_Man_t* aig_manager, Aig_Obj_t* tsietin_variable_object, Aig_Obj_t* child_1_object, Aig_Obj_t* child_2_object, int child_1_complemented, int child_2_complemented, set<Aig_Obj_t*> &factors)
{
	bool make_single_factor = true; 
	if(make_single_factor)
	{
		if(child_1_complemented == 1)
		{
			child_1_object = createNot(child_1_object, aig_manager);
			assert(child_1_object != NULL);
		}

		if(child_2_complemented == 1)
		{
			child_2_object = createNot(child_2_object, aig_manager);
			assert(child_2_object != NULL);
		}

		Aig_Obj_t* factor = createEquivalence(tsietin_variable_object, createAnd(child_1_object, child_2_object, aig_manager),  aig_manager);
		assert(factor != NULL);
		factors.insert(factor);
	}
	else
	{
		if(child_1_complemented == 1)
		{
			child_1_object = createNot(child_1_object, aig_manager);
			assert(child_1_object != NULL);
		}

		if(child_2_complemented == 1)
		{
			child_2_object = createNot(child_2_object, aig_manager);
			assert(child_2_object != NULL);
		}
	
		Aig_Obj_t* factor1 = createOr(createNot(tsietin_variable_object, aig_manager), child_1_object, aig_manager);
		assert(factor1 != NULL);
		factors.insert(factor1);

		Aig_Obj_t* factor2 = createOr(createNot(tsietin_variable_object, aig_manager), child_2_object, aig_manager);
		assert(factor2 != NULL);
		factors.insert(factor2);

		Aig_Obj_t* factor3 = createOr(tsietin_variable_object, createOr(createNot(child_1_object, aig_manager), createNot(child_2_object, aig_manager), aig_manager), aig_manager);
		assert(factor3 != NULL);
		factors.insert(factor3);
	}
}



void obtainFactorsThroughTsietinAndVariablesToEliminateFromGeneratedBenchmark(ABC* abcObj, Abc_Frame_t* abcFrame, set<Aig_Obj_t*> &Factors, Aig_Man_t* &aig_manager, list<string> &VariablesToEliminate)
{
	assert(benchmark_name != "");

	string command = "read " + benchmark_name + ";" + initCommand;
	
	#ifdef DEBUG_SKOLEM
	cout << command << endl;
	#endif

	if (abcObj->comExecute(abcFrame, command))
    	{
	 	cout << "cannot execute " << command << endl;
		assert(false);
	}

	#ifdef DEBUG_SKOLEM //Printing original circuit
	command = "write ckt.v;";
	cout << command << endl;
		
	if (abcObj->comExecute(abcFrame, command))
	{
		cout << "cannot execute command " << command << endl;
		assert(false);
	}
	#endif	

	Abc_Ntk_t* transition_function = abcFrame->pNtkCur;
	transition_function = Abc_NtkDup(transition_function);

	// Let's get all the variable names and
	// Ci_name_to_Ci_number_map
	Abc_Obj_t* tempInputObj;
	int j = 0;
	vector<string> variable_names;
	Abc_NtkForEachCi(transition_function, tempInputObj, j)
	{
		string variable_name = Abc_ObjName(tempInputObj);
		variable_names.push_back(variable_name);

		Ci_name_to_Ci_number_map.insert(make_pair(variable_name, j));

		number_of_Cis++;				
	} 

	// Let's split the transition_function into factors

	aig_manager = Abc_NtkToDar(transition_function, 0, 0);
	// transition function converted to aig_manager	

	// reading the factors: follow unnegated AND nodes to
	// do AND-flattening
	assert(Aig_ManCoNum(aig_manager) == 1);
	Aig_Obj_t* CO_aig_manager;
	CO_aig_manager = Aig_ManCo(aig_manager, 0);
	assert(CO_aig_manager != NULL);

	Aig_Obj_t* root_of_conjunction;
	root_of_conjunction = Aig_ObjChild0(CO_aig_manager);	
	assert(root_of_conjunction != NULL);

	vector<string> tsietin_variables;

	if(obtain_tsietin_variables_in_bfs_order)
	{
		getFactorsThroughTsietinInTopologicalManner(aig_manager, root_of_conjunction, Factors, tsietin_variables);
	}
	else
	{
		if(threshold_for_tsietin_encoding != -1)
		{
			map<string, Aig_Obj_t*> tsietin_variable_to_object_map; //just a place holder here
			getFactorsThroughTsietinUptoThreshold(aig_manager, root_of_conjunction, Factors, tsietin_variables, true, tsietin_variable_to_object_map);
		}
		else // threshold_for_tsietin_encoding == -1 means that we need to do complete tsietin encoding
		{
			getFactorsThroughTsietin(aig_manager, root_of_conjunction, Factors, tsietin_variables);
		}
	}

	for(int tsietin_variables_it = 0; tsietin_variables_it < tsietin_variables.size(); tsietin_variables_it++)
	{
		string variable_name = tsietin_variables[tsietin_variables_it];
		variable_names.push_back(variable_name);
	}
	
	// Limiting no: of varsto elim if needed
	Aig_Obj_t* ciObj_temp;
	int k = 0;
	int input_var_count_temp = 0;
	Aig_ManForEachCi(aig_manager, ciObj_temp, k )
	{
		string variable_name = 	variable_names[k];
		if(variable_name[0] == 'i' && variable_name[1] == '_')
		{
			input_var_count_temp++;
		}
		else if(variable_name[0] == 't' && variable_name[1] == 's' && variable_name[2] == 'i' && variable_name[3] == 'e' && variable_name[4] == 't' && variable_name[5] == 'i' && variable_name[6] == 'n' && variable_name[7] == '_')
		{
			input_var_count_temp++;
		}
	}

	if(limit_on_variables_to_eliminate != -1)
	{
		assert(limit_on_variables_to_eliminate >=1 && limit_on_variables_to_eliminate <= 100);
		limit_on_variables_to_eliminate = (input_var_count_temp * limit_on_variables_to_eliminate)/100;
	}

	//cout << "\nlimit_on_variables_to_eliminate = " << limit_on_variables_to_eliminate << endl;

	// Let's get the IDs of the variables
	
	Aig_Obj_t* ciObj;
	vector<int> variable_ids;
	int i = 0;

	int vars_to_elim_limiting_count = 0;
	Aig_ManForEachCi(aig_manager, ciObj, i )
	{
		int Id = Aig_ObjId(ciObj); // no need to apply Aig_Regular() as ciObj is CI
		variable_ids.push_back(Id);

		string variable_name = 	variable_names[i];
		if(variable_name[0] == 'i' && variable_name[1] == '_')
		// variable_name is a Ci to be eliminated
		{
			if(limit_on_variables_to_eliminate == -1 || vars_to_elim_limiting_count < limit_on_variables_to_eliminate)
			{
				VariablesToEliminate.push_back(variable_name);
				Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.insert(make_pair(variable_name, ciObj));
				vars_to_elim_limiting_count++;
			}
		}
		else if(variable_name[0] == 't' && variable_name[1] == 's' && variable_name[2] == 'i' && variable_name[3] == 'e' && variable_name[4] == 't' && variable_name[5] == 'i' && variable_name[6] == 'n' && variable_name[7] == '_') 
		{
			if(limit_on_variables_to_eliminate == -1 || vars_to_elim_limiting_count < limit_on_variables_to_eliminate)
			{
				VariablesToEliminate.push_back(variable_name);
				Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.insert(make_pair(variable_name, ciObj));
				vars_to_elim_limiting_count++;
			}
		}

		Ci_name_to_Ci_object_map.insert(make_pair(variable_name, ciObj));
	}

	// Let's create the variable_id ---> variable_name map

	assert(variable_ids.size() == variable_names.size());	
	for(int i = 0; i < variable_ids.size(); i++)
	{
		Ci_id_to_Ci_name_map.insert(make_pair(variable_ids[i], variable_names[i]));
	}

	#ifdef DEBUG_SKOLEM
	cout << "\nNumber of factors = " << Factors.size() << endl;
	Aig_Obj_t* and_of_factors = createAnd(Factors, aig_manager);
	assert(and_of_factors != NULL);	
	writeFormulaToFile(aig_manager, and_of_factors, "and_of_factors.v");
	cout << "\nVariablesToEliminate\n";
	showList(VariablesToEliminate);
	#endif
	
}



void obtainFactorsThroughTsietin(ABC* abcObj, Abc_Frame_t* abcFrame, set<Aig_Obj_t*> &Factors, Aig_Man_t* &aig_manager, list<string> &VariablesToEliminate)
{
	assert(benchmark_name != "");

	string command = "read " + benchmark_name + ";" + initCommand;

	#ifdef DEBUG_SKOLEM
	cout << command << endl;
	#endif

	if (abcObj->comExecute(abcFrame, command))
    	{
	 	cout << "cannot execute " << command << endl;
		assert(false);
	}

	Abc_Ntk_t* transition_function = abcFrame->pNtkCur;
	transition_function = Abc_NtkDup(transition_function);

	set<string> VariablesToEliminate_Set(VariablesToEliminate.begin(), VariablesToEliminate.end());

	// Let's get all the variable names and
	// Ci_name_to_Ci_number_map
	Abc_Obj_t* tempInputObj;
	int j = 0;
	vector<string> variable_names;
	Abc_NtkForEachCi(transition_function, tempInputObj, j)
	{
		string variable_name = Abc_ObjName(tempInputObj);
		variable_names.push_back(variable_name);

		Ci_name_to_Ci_number_map.insert(make_pair(variable_name, j));

		number_of_Cis++;				
	} 

	// Let's get the conjunction of factors

	aig_manager = Abc_NtkToDar(transition_function, 0, 0);
	// transition function converted to aig_manager	

	// reading the factors
	Aig_Obj_t* factorObj;
    	int i = 0;
	set<Aig_Obj_t*> roots;

	Aig_ManForEachPoSeq(aig_manager, factorObj, i )
    	{
		assert(factorObj != NULL);

		Aig_Obj_t* Fanin0_factorObj = Aig_ObjChild0(factorObj);		 
		// Note that it is important to use Aig_ObjChild0 here
		// Earlier Aig_ObjFanin0 was used; but Aig_ObjFanin0 regularizes the dag,
		// Aig_ObjChild0 does not regularize the dag		

		assert(Fanin0_factorObj != NULL);

		roots.insert(Fanin0_factorObj);
    	}

	Aig_Obj_t* root_of_conjunction;
	root_of_conjunction = createAnd(roots, aig_manager);	
	assert(root_of_conjunction != NULL);
	
	vector<string> tsietin_variables;
	if(obtain_tsietin_variables_in_bfs_order)
	{
		getFactorsThroughTsietinInTopologicalManner(aig_manager, root_of_conjunction, Factors, tsietin_variables);
	}
	else
	{
		if(threshold_for_tsietin_encoding != -1)
		{
			map<string, Aig_Obj_t*> tsietin_variable_to_object_map; //just a place holder here
			getFactorsThroughTsietinUptoThreshold(aig_manager, root_of_conjunction, Factors, tsietin_variables, true, tsietin_variable_to_object_map);
		}
		else // threshold_for_tsietin_encoding == -1 means that we need to do complete tsietin encoding
		{
			getFactorsThroughTsietin(aig_manager, root_of_conjunction, Factors, tsietin_variables);
		}
	}

	for(int tsietin_variables_it = 0; tsietin_variables_it < tsietin_variables.size(); tsietin_variables_it++)
	{
		string variable_name = tsietin_variables[tsietin_variables_it];
		variable_names.push_back(variable_name);
	}

	// Let's get the IDs of the variables

	vector<int> variable_ids;
	i = 0;
	Aig_ManForEachCi(aig_manager, factorObj, i )
	{
		int Id = Aig_ObjId(factorObj); // no need to apply Aig_Regular() as factorObj is CI
		variable_ids.push_back(Id);

		string variable_name = 	variable_names[i];	
		if(VariablesToEliminate_Set.find(variable_name) != VariablesToEliminate_Set.end())
		// variable_name is an input; it is a Ci to be eliminated
		{
			Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.insert(make_pair(variable_name, factorObj));
		}
		else if(variable_name[0] == 't' && variable_name[1] == 's' && variable_name[2] == 'i' && variable_name[3] == 'e' && variable_name[4] == 't' && variable_name[5] == 'i' && variable_name[6] == 'n' && variable_name[7] == '_') 
		{
			VariablesToEliminate.push_back(variable_name);
			Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.insert(make_pair(variable_name, factorObj));
		}

		Ci_name_to_Ci_object_map.insert(make_pair(variable_name, factorObj));
	}

	// Let's create the variable_id ---> variable_name map

	assert(variable_ids.size() == variable_names.size());	
	for(int i = 0; i < variable_ids.size(); i++)
	{
		Ci_id_to_Ci_name_map.insert(make_pair(variable_ids[i], variable_names[i]));
	}

	#ifdef DEBUG_SKOLEM
	cout << "\nNumber of factors = " << Factors.size() << endl;
	Aig_Obj_t* and_of_factors = createAnd(Factors, aig_manager);
	assert(and_of_factors != NULL);	
	writeFormulaToFile(aig_manager, and_of_factors, "and_of_factors.v");
	cout << "\nVariablesToEliminate\n";
	showList(VariablesToEliminate);
	#endif
}


bool compare_tsietin(const string& first, const string& second)
{
	int first_location = first.find_last_of("_");
	string first_index_string = first.substr(first_location+1);
	int first_index = atoi(first_index_string.c_str());

	int second_location = second.find_last_of("_");
	string second_index_string = second.substr(first_location+1);
	int second_index = atoi(second_index_string.c_str());

	return ( first_index < second_index );
}


void pushTsietinVariablesUpInOrder(list<string> &VariablesToEliminate)
{
	list<string> NonTsietinOrder;
	list<string> TsietinVariables;

	for(list<string>::iterator VariablesToEliminate_it = VariablesToEliminate.begin(); VariablesToEliminate_it != VariablesToEliminate.end(); VariablesToEliminate_it++)
	{
		string variable_name = *VariablesToEliminate_it;
		if(variable_name[0] == 't' && variable_name[1] == 's' && variable_name[2] == 'i' && variable_name[3] == 'e' && variable_name[4] == 't' && variable_name[5] == 'i' && variable_name[6] == 'n' && variable_name[7] == '_')
		{
			TsietinVariables.push_back(variable_name);	
		}
		else
		{
			NonTsietinOrder.push_back(variable_name);	
		}
	} 

	TsietinVariables.sort(compare_tsietin);

	VariablesToEliminate.clear();
	
	for(list<string>::iterator TsietinVariables_it = TsietinVariables.begin(); TsietinVariables_it != TsietinVariables.end(); TsietinVariables_it++)
	{
		string variable_name = *TsietinVariables_it;
		VariablesToEliminate.push_back(variable_name);
	}

	for(list<string>::iterator NonTsietinOrder_it = NonTsietinOrder.begin(); NonTsietinOrder_it != NonTsietinOrder.end(); NonTsietinOrder_it++)
	{
		string variable_name = *NonTsietinOrder_it;
		VariablesToEliminate.push_back(variable_name);
	}	
}



void collectExactSkolemFunctionForTsietinVariable(Aig_Man_t* aig_manager, string tsietin_object_string, Aig_Obj_t* child_1_object, Aig_Obj_t* child_2_object, int child_1_complemented, int child_2_complemented)
{
	if(child_1_complemented == 1)
	{
		child_1_object = createNot(child_1_object, aig_manager);
		assert(child_1_object != NULL);
	}

	if(child_2_complemented == 1)
	{
		child_2_object = createNot(child_2_object, aig_manager);
		assert(child_2_object != NULL);
	}

	Aig_Obj_t* skolem_function = createAnd(child_1_object, child_2_object, aig_manager);
	assert(skolem_function != NULL);

	tsietin_variable_to_exact_skolem_function_map.insert(make_pair(tsietin_object_string, skolem_function));
}



void Aig_ManDfs_Fragment_rec( Aig_Man_t * p, Aig_Obj_t * pObj, Vec_Ptr_t * vNodes )
{
    if ( pObj == NULL )
        return;
    assert( !Aig_IsComplement(pObj) );
    if ( Aig_ObjIsTravIdCurrent(p, pObj) )
        return;
    Aig_ObjSetTravIdCurrent(p, pObj);
    if ( p->pEquivs && Aig_ObjEquiv(p, pObj) )
        Aig_ManDfs_Fragment_rec( p, Aig_ObjEquiv(p, pObj), vNodes );
    Aig_ManDfs_Fragment_rec( p, Aig_ObjFanin0(pObj), vNodes );
    Aig_ManDfs_Fragment_rec( p, Aig_ObjFanin1(pObj), vNodes );
    Vec_PtrPush( vNodes, pObj );
}


Vec_Ptr_t * Aig_ManDfs_Fragment( Aig_Man_t * p, int fNodesOnly, set<int> &Interested_POs)
{
    Vec_Ptr_t * vNodes;
    Aig_Obj_t * pObj;
    int i;
    Aig_ManIncrementTravId( p );
    Aig_ObjSetTravIdCurrent( p, Aig_ManConst1(p) );
    // start the array of nodes
    vNodes = Vec_PtrAlloc( Aig_ManObjNumMax(p) );
    // mark PIs if they should not be collected
    if ( fNodesOnly )
        Aig_ManForEachCi( p, pObj, i )
            Aig_ObjSetTravIdCurrent( p, pObj );
    else
        Vec_PtrPush( vNodes, Aig_ManConst1(p) );
    // collect nodes reachable in the DFS order
    Aig_ManForEachCo( p, pObj, i )
    {
	if(Interested_POs.find(pObj->Id) != Interested_POs.end()) // pObj is a PO of interest
	{
     		Aig_ManDfs_Fragment_rec( p, fNodesOnly? Aig_ObjFanin0(pObj): pObj, vNodes );
	}
    }

  //  if ( fNodesOnly )
  //      assert( Vec_PtrSize(vNodes) == Aig_ManNodeNum(p) );
  //  else
  //      assert( Vec_PtrSize(vNodes) == Aig_ManObjNum(p) );
    return vNodes;
}


Abc_Ntk_t* obtainNetworkFromFragmentOfAIGWithIdNames(Aig_Man_t * pMan, map<int, string> &idName)
{
    Vec_Ptr_t * vNodes;
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pObjNew;
    Aig_Obj_t * pObj, * pObjLo, * pObjLi;
    int i;
    assert(pMan->nAsserts == 0);
    // perform strashing
    pNtkNew = Abc_NtkAlloc(ABC_NTK_STRASH, ABC_FUNC_AIG, 1);
    pNtkNew->nConstrs = pMan->nConstrs;
    // duplicate the name and the spec
    pNtkNew->pName = Extra_UtilStrsav(pMan->pName);
    pNtkNew->pSpec = Extra_UtilStrsav(pMan->pSpec);
    Aig_ManConst1(pMan)->pData = Abc_AigConst1(pNtkNew);

    set<int> Interested_POs;

    // create PIs

    Aig_ManForEachPiSeq(pMan, pObj, i)
    {
	if(idName.find(pObj->Id) != idName.end()) // interested PI
	{
		pObjNew = Abc_NtkCreatePi(pNtkNew);


		#ifdef DEBUG_SKOLEM 
		cout << endl << "Interested PI: ";
		cout << "pObj->Id = " << pObj->Id;
		cout << "\tidName[pObj->Id] = " << idName[pObj->Id];
		#endif

		Abc_ObjAssignName(pObjNew, (char*) idName[pObj->Id].c_str(), NULL);
		//        Abc_ObjAssignName( pObjNew, Abc_ObjName(pObjNew), NULL );
		//cout<<pObj->Id<<endl;
		pObj->pData = pObjNew;
	}
    }
    // create POs
    //assert(Aig_ManCoNum(pMan) == 1);
    
    Aig_ManForEachCo(pMan, pObj, i)
    {
	#ifdef DEBUG_SKOLEM 
	cout << endl << "i = " << i << "\tpObj->Id = " << pObj->Id;
	#endif


        if(idName.find(pObj->Id) != idName.end() && Interested_POs.find(pObj->Id) == Interested_POs.end()) // interested PO
	{
		pObjNew = Abc_NtkCreatePo(pNtkNew);

		#ifdef DEBUG_SKOLEM 
		cout << endl << "Interested PO: ";
		cout << "pObj->Id = " << pObj->Id;
		cout << "\tidName[pObj->Id] = " << idName[pObj->Id];
		cout << "\tpObjNew->Id = " << pObjNew->Id;
		#endif

		Abc_ObjAssignName(pObjNew, (char*) idName[pObj->Id].c_str(), NULL);
		//        Abc_ObjAssignName( pObjNew, Abc_ObjName(pObjNew), NULL );
		//cout<<pObj->Id<<endl;
		pObj->pData = pObjNew;

		Interested_POs.insert(pObj->Id);

		#ifdef DEBUG_SKOLEM 
		showSet(Interested_POs, "Interested_POs");
		#endif
	}
    }

    //assert(Abc_NtkCiNum(pNtkNew) == Aig_ManCiNum(pMan) - Aig_ManRegNum(pMan));
    //assert(Abc_NtkCoNum(pNtkNew) == Aig_ManCoNum(pMan) - Aig_ManRegNum(pMan));
    // create as many latches as there are registers in the manager

    Aig_ManForEachLiLoSeq(pMan, pObjLi, pObjLo, i)
    {
        pObjNew = Abc_NtkCreateLatch(pNtkNew);
        pObjLi->pData = Abc_NtkCreateBi(pNtkNew);
        pObjLo->pData = Abc_NtkCreateBo(pNtkNew);
        Abc_ObjAddFanin(pObjNew, (Abc_Obj_t *) pObjLi->pData);
        Abc_ObjAddFanin((Abc_Obj_t *) pObjLo->pData, pObjNew);
        Abc_LatchSetInit0(pObjNew);
        //Abc_ObjName((Abc_Obj_t *)pObjLi->pData)
        //        string name = "LatchIn"+IntegerToString(i);
        //      Abc_ObjAssignName( (Abc_Obj_t *)pObjLi->pData, (char*)name.c_str(), NULL );
        //      name = "LatchOut_"+IntegerToString(i);
        //       Abc_ObjAssignName( (Abc_Obj_t *)pObjLo->pData,(char*)name.c_str(), NULL );
    }
    // rebuild the AIG
    vNodes = Aig_ManDfs_Fragment(pMan, 1, Interested_POs);

    Vec_PtrForEachEntry(Aig_Obj_t *, vNodes, pObj, i)
    if (Aig_ObjIsBuf(pObj))
        pObj->pData = (Abc_Obj_t *) Aig_ObjChild0Copy(pObj);
    else
        pObj->pData = Abc_AigAnd((Abc_Aig_t *) pNtkNew->pManFunc, (Abc_Obj_t *) Aig_ObjChild0Copy(pObj), (Abc_Obj_t *) Aig_ObjChild1Copy(pObj));
    Vec_PtrFree(vNodes);

    
    // connect the PO nodes

    /*Aig_ManForEachCo(pMan, pObj, i)
    {
	if(idName.find(pObj->Id) != idName.end()) // interested PO
	{
        	pObjNew = (Abc_Obj_t *) Aig_ObjChild0Copy(pObj);
        	Abc_ObjAddFanin(Abc_NtkCo(pNtkNew, i), pObjNew);
	}
    }*/

    #ifdef DEBUG_SKOLEM 
    cout << endl << "connecting the PO nodes " << endl;
    #endif

    int po_index = 0;
    set<int> Interested_POs_Considered;

    Aig_ManForEachCo(pMan, pObj, i)
    {
	#ifdef DEBUG_SKOLEM 
	cout << endl << "i = " << i << endl;
	#endif

        if(idName.find(pObj->Id) != idName.end() && Interested_POs_Considered.find(pObj->Id) == Interested_POs_Considered.end()) // interested PO
	{
		#ifdef DEBUG_SKOLEM 
		cout << endl << "pObj->Id = " << pObj->Id;
		cout << "\tidName[pObj->Id] = " << idName[pObj->Id];
		#endif

        	pObjNew = (Abc_Obj_t *) Aig_ObjChild0Copy(pObj);
        	Abc_ObjAddFanin(Abc_NtkPo(pNtkNew, po_index), pObjNew);	
		po_index++;	

		#ifdef DEBUG_SKOLEM 
		cout << endl << "po added" << endl;
		#endif

		Interested_POs_Considered.insert(pObj->Id);
	}
    }

    //  Abc_NtkAddDummyPiNames( pNtkNew );
    //Abc_NtkAddDummyPoNames( pNtkNew );
    //    Abc_NtkAddDummyBoxNames( pNtkNew );

   

    // check the resulting AIG
    if (!Abc_NtkCheck(pNtkNew))
        cout << "obtainNetworkFromFragmentOfAIGWithIdNames: Network check has failed.\n";
    return pNtkNew;
}




void Abc_NtkMakeSequential( Abc_Ntk_t * pNtk, int nLatchesToAdd )
{
    Abc_Obj_t * pObjLi, * pObjLo, * pObj;
    int i;
    assert( Abc_NtkBoxNum(pNtk) == 0 );
    if ( !Abc_NtkIsComb(pNtk) )
    {
        printf( "The network is a not a combinational one.\n" );
        return;
    }
   /* if ( nLatchesToAdd >= Abc_NtkPiNum(pNtk) )
    {
        printf( "The number of latches is more or equal than the number of PIs.\n" );
        return;
    }
    if ( nLatchesToAdd >= Abc_NtkPoNum(pNtk) )
    {
        printf( "The number of latches is more or equal than the number of POs.\n" );
        return;
    }*/

    // move the last PIs to become CIs
    Vec_PtrClear( pNtk->vPis );
    Abc_NtkForEachCi( pNtk, pObj, i )
    {
        if ( i < Abc_NtkCiNum(pNtk) - nLatchesToAdd )
        {
            Vec_PtrPush( pNtk->vPis, pObj );
            continue;
        }
        pObj->Type = ABC_OBJ_BO;
        pNtk->nObjCounts[ABC_OBJ_PI]--;
        pNtk->nObjCounts[ABC_OBJ_BO]++;
    }

    // move the last POs to become COs
    Vec_PtrClear( pNtk->vPos );
    Abc_NtkForEachCo( pNtk, pObj, i )
    {
	#ifdef DEBUG_SKOLEM
	cout << "\nCO with pObj->Id = " << pObj->Id << " is ";
	#endif

        if ( i < Abc_NtkCoNum(pNtk) - nLatchesToAdd )
        {
	    #ifdef DEBUG_SKOLEM
	    cout << " PO\n";
	    #endif

            Vec_PtrPush( pNtk->vPos, pObj );
            continue;
        }
	
	#ifdef DEBUG_SKOLEM
	cout << " Latch\n";
	#endif

        pObj->Type = ABC_OBJ_BI;
        pNtk->nObjCounts[ABC_OBJ_PO]--;
        pNtk->nObjCounts[ABC_OBJ_BI]++;
    }

    // create latches
    for ( i = 0; i < nLatchesToAdd; i++ )
    {
        pObjLo = Abc_NtkCi( pNtk, Abc_NtkCiNum(pNtk) - nLatchesToAdd + i );
        pObjLi = Abc_NtkCo( pNtk, Abc_NtkCoNum(pNtk) - nLatchesToAdd + i );
        pObj = Abc_NtkCreateLatch( pNtk );
        Abc_ObjAddFanin( pObj, pObjLi );
        Abc_ObjAddFanin( pObjLo, pObj );
        Abc_LatchSetInit0( pObj );
    }

    if ( !Abc_NtkCheck( pNtk ) )
        fprintf( stdout, "Abc_NtkMakeSequential(): Network check has failed.\n" );
}



string renameLatchesAndOutputs(Abc_Ntk_t*& c1, int number_of_latches_in_original_circuit)
{
    map<int, string> origNames;

    int j = 0;
    int i = 0;
    Abc_Obj_t* tempObj;
#ifdef HWMCC_BENCHMARK
    assert(Abc_NtkFindCo(c1,(char*)"extra_latch_in") != NULL);
#endif
    Abc_NtkForEachPi(c1, tempObj, i)
    {
        origNames[tempObj->Id] = Abc_ObjName(tempObj);
    }
//    Nm_ManFree(c1->pManName);
//    cout << "here " << endl << Abc_NtkPiNum(c1) << endl;
//    c1->pManName = Nm_ManCreate(Abc_NtkCiNum(c1) + Abc_NtkCoNum(c1) + Abc_NtkBoxNum(c1));

    string name;
    Nm_Man_t* t = c1->pManName;
    Abc_NtkForEachPi(c1, tempObj, i)
    {
        name = origNames[tempObj->Id];
        if (name.find(PREFPREFIX) != string::npos)
        {
	    #ifdef DEBUG_SKOLEM
            cout<<"assigning name "<<endl;
            #endif

	    Nm_Entry_t * pEntry;
            if ( (pEntry = Nm_ManTableLookupId(t, tempObj->Id)) )
    	    {
		#ifdef DEBUG_SKOLEM
        	cout << "Nm_ManStoreIdName(): Entry with the same ID already exists.\n";
		#endif
    	    }
	    else
            {
		Abc_ObjAssignName(tempObj, (char*) name.c_str(), NULL);
            }

	    #ifdef DEBUG_SKOLEM
            cout<<"assigning name DONE"<<endl;
            #endif
        }
        else
        {
	    #ifdef DEBUG_SKOLEM
            cout<<"deleting name and reassigning name "<<endl;
            #endif	    

            Nm_ManTableDelete(t,tempObj->Id);
            name = LATCHPREFIX + IntegerToString(++j);

            Abc_ObjAssignName(tempObj, (char*) name.c_str(), NULL);
            

	    #ifdef DEBUG_SKOLEM
            cout<<"deleting name and reassigning name DONE"<<endl;
            #endif
        }
    }

    j = 0;
    int k = 0;

    int index_of_first_latch = Abc_NtkPoNum(c1) - number_of_latches_in_original_circuit;

    Abc_NtkForEachPo(c1, tempObj, i)
    {
//        if(Abc_ObjName(tempObj) == EXTRA_LATCH+"_in")
//        {
//            cout<<"continuing"<<endl;
//           
//            continue;
//        }

	if(i >= index_of_first_latch) // latch
	{

		#ifdef DEBUG_SKOLEM 
		cout<<"renaming "<<Abc_ObjName(tempObj)<<" to suffix "<<j+1<<endl;;
		#endif

		 Nm_ManTableDelete(t,tempObj->Id);
		name = LATCHOUTPREFIX + IntegerToString(++j);

		#ifdef DEBUG_SKOLEM 
		cout << "latch:" << Abc_ObjName(tempObj) << tempObj->Id << endl;
		#endif

		Abc_ObjAssignName(tempObj, (char*) name.c_str(), NULL);
	

	}
	else // output
	{

		#ifdef DEBUG_SKOLEM 
		cout<<"renaming "<<Abc_ObjName(tempObj)<<" to suffix "<<k+1<<endl;;
		#endif

		 Nm_ManTableDelete(t,tempObj->Id);
		name = CIRCUITOUTPREFIX + IntegerToString(++k);

		#ifdef DEBUG_SKOLEM 
		cout << "output:" << Abc_ObjName(tempObj) << tempObj->Id << endl;
		#endif

		Abc_ObjAssignName(tempObj, (char*) name.c_str(), NULL);

	}
    }
    return name;
   // getchar();
}





void obtainFactorsAndVariablesToEliminatFromGameQdimacsFile(ABC* abcObj, Abc_Frame_t* abcFrame, set<Aig_Obj_t*> &Factors, Aig_Man_t* &aig_manager, vector< list<string> > &VariablesToEliminate, char &TypeOfInnerQuantifier)
{
	set<int> forall_variables;
	set<int> exists_variables;

	assert(benchmark_name != "");

	#ifdef DEBUG_SKOLEM
	cout << "\nbenchmark_name = " << benchmark_name << endl;
	#endif

	aig_manager = Aig_ManStart(0);//start the manager

	FILE *fptr = fopen (benchmark_name.c_str(), "r");
	assert(fptr != NULL);

	char C[100], c;
	int numVar, numClauses, tmpVar, i;	
	fscanf (fptr, "%c", &c);
	fscanf (fptr, "%s", C);
	while (strcmp (C, "cnf") != 0)
	{
		fscanf (fptr, "%s", C);
	}
	fscanf(fptr, "%d %d", &numVar, &numClauses); // read first line p cnf numVar numClauses

	#ifdef DEBUG_SKOLEM
	cout << "\nnumber of variables = " << numVar << "\tnumber of clauses = " << numClauses << endl;
	#endif

	fscanf (fptr, "%c", &c);
	tmpVar = 1;
	while (c != 'a')
	{
		fscanf (fptr, "%c", &c);
	}
	while (tmpVar != 0)
	{
		fscanf(fptr, "%d", &tmpVar); 
		if(tmpVar != 0)
		{
			forall_variables.insert(tmpVar);
		}
	}

	#ifdef DEBUG_SKOLEM
	showSet(forall_variables, "forall_variables");
	#endif
			
	fscanf (fptr, "%c", &c);
	tmpVar = 1;
	while (c != 'e')
	{
		fscanf (fptr, "%c", &c);
	}
	while (tmpVar !=0)
	{
		fscanf(fptr, "%d", &tmpVar); 
		if(tmpVar != 0)
		{
			exists_variables.insert(tmpVar);
		}
	}

	#ifdef DEBUG_SKOLEM
	showSet(exists_variables, "exists_variables");
	#endif

	list<string> forall_string_variables;
	list<string> exists_string_variables;
	vector<string> variable_names;
	
	//create the primary inputs
	for (i = 0; i < numVar; i++)
	{
		Aig_ObjCreateCi(aig_manager); // Create numVar primary inputs

		int variable_number = i+1;
		char variable_number_char[100];
		sprintf(variable_number_char, "%d", variable_number);
		string variable_number_string(variable_number_char);
		string variable_name = "x_";
		variable_name += variable_number_string;

		variable_names.push_back(variable_name);

		if(exists_variables.find(variable_number) != exists_variables.end()) //exists variable
		{
		  exists_string_variables.push_back(variable_name);
		}
		else if(forall_variables.find(variable_number) != forall_variables.end()) //forall variable
		{
		  forall_string_variables.push_back(variable_name);
		}
		else
		{
		  assert(false);
		}

		Ci_name_to_Ci_number_map.insert(make_pair(variable_name, i));
		initial_Ci_name_to_Ci_number_map.insert(make_pair(variable_name, i));

		number_of_Cis++;
		initial_number_of_Cis++;
	}


	VariablesToEliminate.push_back(exists_string_variables); // exists comes first from inside
	VariablesToEliminate.push_back(forall_string_variables); // forall comes next
	TypeOfInnerQuantifier = 'e';

	#ifdef DEBUG_SKOLEM
	cout << endl << "Ci_name_to_Ci_number_map" << endl;
	for(map<string, int>::iterator map_it = Ci_name_to_Ci_number_map.begin(); map_it != Ci_name_to_Ci_number_map.end(); map_it++)
	{
		cout << map_it->first << "\t" << map_it->second << endl;
	}

	cout << "\nVariablesToEliminate[0], i.e., forall variables\n";
	showList(VariablesToEliminate[0]);
	cout << "\nVariablesToEliminate[1], i.e., exists variables\n";
	showList(VariablesToEliminate[1]);
	#endif

	#ifdef DEBUG_SKOLEM
	cout << endl << numVar << " variables created\n";
	#endif

	// start reading the clauses
	Aig_Obj_t *pObj1, *pObj2, *pTemp, *pO, *pCo, *pOut;
	
	//pOut = Aig_ManConst1(aig_manager);
	//pO = Aig_ObjCreateCo(aig_manager, Aig_ManConst0(aig_manager)); //This is the primary output

	for ( i = 0; i < numClauses ; i++)
	{
		fscanf(fptr, "%d", &tmpVar);

		#ifdef DEBUG_SKOLEM
		cout << endl << tmpVar << " read\n";
		#endif 

		pObj1 = Aig_ManConst0(aig_manager);
		while (tmpVar != 0)
		{
			pObj2 = Aig_ManCi (aig_manager, abs(tmpVar)-1);
			if (tmpVar < 0)
				pObj1 = Aig_Or(aig_manager, pTemp = pObj1, Aig_Not(pObj2)); 			
			else
				pObj1 = Aig_Or(aig_manager, pTemp = pObj1, pObj2); 
			
			fscanf(fptr, "%d", &tmpVar); 

			#ifdef DEBUG_SKOLEM
			cout << endl << tmpVar << " read\n";
			#endif 
		}

		pCo = Aig_ObjCreateCo(aig_manager, pObj1); //Co for each factor
		//Add pObj1 as fanin to pCo
		
		#ifdef DEBUG_SKOLEM
		cout << endl << "Created factor " << i << endl;
		#endif 
		
		//pOut = Aig_And (aig_manager, pTemp = pOut, pObj1);
	}
	//Add pOut as fanin to pO
	//Aig_ObjPatchFanin0(aig_manager, pO, pOut);

	Aig_ManCleanup(aig_manager);
	Aig_ManCheck(aig_manager);
	//Aig_ManDumpBlif (pMan, "t.blif", NULL, NULL);
	//Aig_ManShow (pMan, 0, NULL);

	cout << endl << numClauses << " factors created\n";
	
	// Note that we still need to do as done in 
	// obtainFactorsAndVariablesToEliminatFromHWMCCFile

	// reading the factors
	Aig_Obj_t* factorObj;
	i = 0;
    	Aig_ManForEachCo(aig_manager, factorObj, i )
    	{
		assert(factorObj != NULL);
		Aig_Obj_t* Fanin0_factorObj = Aig_ObjChild0(factorObj);		 
		// Note that it is important to use Aig_ObjChild0 here
		// Earlier Aig_ObjFanin0 was used; but Aig_ObjFanin0 regularizes the dag,
		// Aig_ObjChild0 does not regularize the dag		

		assert(Fanin0_factorObj != NULL);
		Factors.insert(Fanin0_factorObj);
    	}

        // Let's get the IDs of the variables
	Aig_Obj_t* variable_obj;
	vector<int> variable_ids;
	i = 0;
	Aig_ManForEachCi(aig_manager, variable_obj, i )
	{
		int Id = Aig_ObjId(variable_obj); // no need to apply Aig_Regular() as variable_obj is CI
		variable_ids.push_back(Id);

		string variable_name = 	variable_names[i];	
		
		Ci_name_to_Ci_object_map.insert(make_pair(variable_name, variable_obj));
		initial_Ci_name_to_Ci_object_map.insert(make_pair(variable_name, variable_obj));
	}

	// Let's create the variable_id ---> variable_name map

	assert(variable_ids.size() == variable_names.size());	
	for(int i = 0; i < variable_ids.size(); i++)
	{
		Ci_id_to_Ci_name_map.insert(make_pair(variable_ids[i], variable_names[i]));
		initial_Ci_id_to_Ci_name_map.insert(make_pair(variable_ids[i], variable_names[i]));
	}

	#ifdef DEBUG_SKOLEM
	cout << endl << "Ci_id_to_Ci_name_map" << endl;
	for(map<int, string>::iterator map_it = Ci_id_to_Ci_name_map.begin(); map_it != Ci_id_to_Ci_name_map.end(); map_it++)
	{
		cout << map_it->first << "\t" << map_it->second << endl;
	}
	#endif

	cout << endl << "Reading the Qdimacs file finished\n";

}




void andFlattening(Aig_Obj_t* root, set<Aig_Obj_t*> &Factors)
{
	assert(root != NULL);
	vector<Aig_Obj_t*> roots_of_conjunction;

	if(!Aig_IsComplement(root) && root->Type == AIG_OBJ_AND)
	{
		roots_of_conjunction.push_back(root);
	}
	else
	{
		Factors.insert(root);	
	}
    	
	while(roots_of_conjunction.size() > 0)
	{
		root = roots_of_conjunction[0];
		roots_of_conjunction.erase(roots_of_conjunction.begin());

		Aig_Obj_t* child1 = Aig_ObjChild0(root);
		assert(child1 != NULL);
		if(!Aig_IsComplement(child1) && child1->Type == AIG_OBJ_AND)
		{
			roots_of_conjunction.push_back(child1);
		}
		else
		{
			Factors.insert(child1);	
		}	

		Aig_Obj_t* child2 = Aig_ObjChild1(root);
		assert(child2 != NULL);
		if(!Aig_IsComplement(child2) && child2->Type == AIG_OBJ_AND)
		{
			roots_of_conjunction.push_back(child2);
		}
		else
		{
			Factors.insert(child2);	
		}
	}
}


void readSkolemFunctionsAndGetTheirSizes(ABC* abcObj, Abc_Frame_t* abcFrame, Aig_Man_t* &aig_manager, int &total_size, int &number_of_vars, int &max_size, float &avg_size)
{
	cout << "\nreadSkolemFunctionsAndGetTheirSizes called\n";

	assert(benchmark_name != "");

	string command;

	bool avoid_simplification = true;
	if(avoid_simplification)
	{
		command = "read " + benchmark_name + ";";
	}
	else
	{
		command = "read " + benchmark_name + ";" + initCommand;
	}
	
	#ifdef DEBUG_SKOLEM
	cout << command << endl;
	#endif

	if (abcObj->comExecute(abcFrame, command))
    	{
	 	cout << "cannot execute " << command << endl;
		assert(false);
	}

	cout << "\nbenchmark read\n";
	//assert(false);

	#ifdef DEBUG_SKOLEM //Printing original circuit
	command = "write skolem.v;";
	cout << command << endl;
		
	if (abcObj->comExecute(abcFrame, command))
	{
		cout << "cannot execute command " << command << endl;
		assert(false);
	}
	#endif	

	Abc_Ntk_t* skolem_functions = abcFrame->pNtkCur;
	//skolem_functions = Abc_NtkDup(skolem_functions); trying to avoid blow-up

	aig_manager = Abc_NtkToDar(skolem_functions, 0, 0);

	cout << "\ntransition function converted to aig_manager\n";

	// transition function converted to aig_manager	

	// reading the Skolem functions
	total_size = 0;
	number_of_vars = 1;
	max_size = 0;
	
	Aig_Obj_t* skolemObj;
	int i = 0;
	Aig_ManForEachCo(aig_manager, skolemObj, i )
    	{
		assert(skolemObj != NULL);
		Aig_Obj_t* Fanin0_skolemObj = Aig_ObjChild0(skolemObj);	
		assert(Fanin0_skolemObj != NULL);
		
		int Fanin0_skolemObj_size = computeSize(Fanin0_skolemObj, aig_manager);
		cout << "\nSize of Skolem function_" << number_of_vars << " is " << Fanin0_skolemObj_size;

		total_size = total_size + Fanin0_skolemObj_size;
		cout << "\nTotal Skolem function size is " << total_size;

		if(Fanin0_skolemObj_size > max_size)
		{
			max_size = Fanin0_skolemObj_size;
		}
		cout << "\nMax Skolem function size is " << max_size << endl;

		number_of_vars++;
    	}

	number_of_vars--;

	avg_size = (float)total_size/(float)number_of_vars;

	cout << "\ntotal_size = " << total_size << "\tnumber_of_vars = " << number_of_vars << "\tmax_size = "<< max_size <<"\tavg_size = " << avg_size << endl;
}




void getFactorsThroughTsietinUptoThreshold(Aig_Man_t* aig_manager, Aig_Obj_t* formula, set<Aig_Obj_t*> &factors, vector<string> &tsietin_variables, bool collect_exact_skolem_functions, map<string, Aig_Obj_t*> &tsietin_variable_to_object_map)
{
	//Ideally wanted t_HashTable<int, Aig_Obj_t*> tsietin_label_table; but there's some
	// problem with this hash_table declaration

	#ifdef DEBUG_SKOLEM
		cout << "\nSize of original formula to be decomposed = " << computeSize(formula, aig_manager) << endl;
	#endif

	map<int, Aig_Obj_t*> tsietin_label_table;
	int tsietin_count = 1;
	
	Aig_Obj_t* root_tsietin_variable = getFactorsThroughTsietinUptoThresholdRecursive(aig_manager, formula, factors, tsietin_label_table, tsietin_count, tsietin_variables, collect_exact_skolem_functions, tsietin_variable_to_object_map);
	assert(root_tsietin_variable != NULL);
	
	if(Aig_IsComplement(formula))
	{
		factors.insert(createNot(root_tsietin_variable, aig_manager));
	}
	else
	{
		factors.insert(root_tsietin_variable);
	}

	number_of_tsietin_variables = tsietin_count - 1;
		
}

Aig_Obj_t* getFactorsThroughTsietinUptoThresholdRecursive(Aig_Man_t* aig_manager, Aig_Obj_t* formula, set<Aig_Obj_t*> &factors,map<int, Aig_Obj_t*>  &tsietin_label_table, int &tsietin_count, vector<string> &tsietin_variables, bool collect_exact_skolem_functions, map<string, Aig_Obj_t*> &tsietin_variable_to_object_map)
{
	formula = Aig_Regular(formula);
	int key = Aig_ObjId(formula);

	#ifdef DEBUG_SKOLEM
		cout << "\nformula = " << formula << "\tkey = " << key << endl;
	#endif

	map<int, Aig_Obj_t*>::iterator LabelTable_it = tsietin_label_table.find(key);
	if (LabelTable_it != tsietin_label_table.end()) // label exists already, i.e. traversed already
	{
		#ifdef DEBUG_SKOLEM
			cout << "\nExists in hashtable\n";
		#endif

		return LabelTable_it->second;
	}
	else
	{
		if(formula->Type == AIG_OBJ_AND && computeSize(formula, aig_manager) > threshold_for_tsietin_encoding)// child_1 \wedge child_2 encountered with size > 
		{
			#ifdef DEBUG_SKOLEM
				cout << "\nAIG_OBJ_AND encountered with size more than " << threshold_for_tsietin_encoding << "\n";
			#endif

			// new AND node encountered; need to create new variable
			// representing the AND node
			Aig_Obj_t* tsietin_variable_object = Aig_ObjCreateCi(aig_manager);	
			assert(tsietin_variable_object != NULL);
			
			char tsietin_count_char[100];
			sprintf(tsietin_count_char, "%d", tsietin_count);
			string tsietin_count_string(tsietin_count_char);
			string tsietin_object_string = "tsietin_";
			tsietin_object_string += tsietin_count_string;
			tsietin_count++;

			if(number_of_components_generated > 0)//useful when this function is used in graph decomposition
			{
				char component_count_char[100];
				sprintf(component_count_char, "%d", number_of_components_generated);
				string component_count_string(component_count_char);

				tsietin_object_string += "_";
				tsietin_object_string += component_count_string;
			}			

			tsietin_variables.push_back(tsietin_object_string);

			int tsietin_object_id = Aig_ObjId(tsietin_variable_object); 
			Ci_id_to_Ci_name_map.insert(make_pair(tsietin_object_id, tsietin_object_string));
			Ci_name_to_Ci_number_map.insert(make_pair(tsietin_object_string, number_of_Cis));	
			number_of_Cis++;

			tsietin_variable_to_object_map.insert(make_pair(tsietin_object_string, tsietin_variable_object)); // this helps when the function is used in graph decomposition

			tsietin_label_table.insert(make_pair(key, tsietin_variable_object));
			// variable representing the node created

			Aig_Obj_t* child_1_object = getFactorsThroughTsietinUptoThresholdRecursive(aig_manager, Aig_ObjChild0(formula), factors, tsietin_label_table, tsietin_count, tsietin_variables, collect_exact_skolem_functions, tsietin_variable_to_object_map);
			assert(child_1_object != NULL);

			Aig_Obj_t* child_2_object = getFactorsThroughTsietinUptoThresholdRecursive(aig_manager, Aig_ObjChild1(formula), factors, tsietin_label_table, tsietin_count, tsietin_variables, collect_exact_skolem_functions, tsietin_variable_to_object_map);
			assert(child_2_object != NULL);

			#ifdef DEBUG_SKOLEM
				cout << "\nCreating factors for the new conjunction " << tsietin_variable_object << "(" << child_1_object << "," << child_2_object <<")\n";
			#endif

			getNewTsietinFactors(aig_manager, tsietin_variable_object, child_1_object, child_2_object, Aig_ObjFaninC0(formula), Aig_ObjFaninC1(formula), factors); 

			if(collect_exact_skolem_functions)
			{
				collectExactSkolemFunctionForTsietinVariable(aig_manager, tsietin_object_string, child_1_object, child_2_object, Aig_ObjFaninC0(formula), Aig_ObjFaninC1(formula));			
			}

			return tsietin_variable_object;
						
		}
		else if(formula->Type == AIG_OBJ_AND && computeSize(formula, aig_manager) <= threshold_for_tsietin_encoding)// child_1 \wedge child_2 encountered with size <= threshold_for_tsietin_encoding
		{
			#ifdef DEBUG_SKOLEM
				cout << "\nAIG_OBJ_AND encountered with size less than or equal to " << threshold_for_tsietin_encoding << endl;
			#endif

			// new AND node encountered but with size less than ; need to create new variable
			// representing the AND node
			Aig_Obj_t* tsietin_variable_object = Aig_ObjCreateCi(aig_manager);	
			assert(tsietin_variable_object != NULL);
			
			char tsietin_count_char[100];
			sprintf(tsietin_count_char, "%d", tsietin_count);
			string tsietin_count_string(tsietin_count_char);
			string tsietin_object_string = "tsietin_";
			tsietin_object_string += tsietin_count_string;
			tsietin_count++;
		
			if(number_of_components_generated > 0)//useful when this function is used in graph decomposition
			{
				char component_count_char[100];
				sprintf(component_count_char, "%d", number_of_components_generated);
				string component_count_string(component_count_char);

				tsietin_object_string += "_";
				tsietin_object_string += component_count_string;
			}

			tsietin_variables.push_back(tsietin_object_string);

			int tsietin_object_id = Aig_ObjId(tsietin_variable_object); 
			Ci_id_to_Ci_name_map.insert(make_pair(tsietin_object_id, tsietin_object_string));
			Ci_name_to_Ci_number_map.insert(make_pair(tsietin_object_string, number_of_Cis));	
			number_of_Cis++;

			tsietin_variable_to_object_map.insert(make_pair(tsietin_object_string, tsietin_variable_object)); // this helps when the function is used in graph decomposition

			tsietin_label_table.insert(make_pair(key, tsietin_variable_object));
			// variable representing the node created

			#ifdef DEBUG_SKOLEM
				cout << "\nMaking a new leaf level factor " << tsietin_variable_object <<"\n";
			#endif

			Aig_Obj_t* leaf_factor = createEquivalence(tsietin_variable_object, formula,  aig_manager);
			assert(leaf_factor != NULL);
			factors.insert(leaf_factor);

			if(collect_exact_skolem_functions)
			{
				tsietin_variable_to_exact_skolem_function_map.insert(make_pair(tsietin_object_string, formula));			
			}

			return tsietin_variable_object;
						
		}
		else if(formula->Type == AIG_OBJ_CI) //CI encountered
		{
			#ifdef DEBUG_SKOLEM
				cout << "\nAIG_OBJ_CI encountered\n";
			#endif
			
			tsietin_label_table.insert(make_pair(key, formula));
			return formula;
			
		}
		else if(formula->Type == AIG_OBJ_CONST1) // 1 encountered
		{
			#ifdef DEBUG_SKOLEM
				cout << "\nAIG_OBJ_CONST1 encountered\n";
			#endif

			tsietin_label_table.insert(make_pair(key, formula));
			return formula;			
		}		
		else if(formula->Type == AIG_OBJ_CO) //CO encountered
		{
			#ifdef DEBUG_SKOLEM
				cout << "\nAIG_OBJ_CO encountered\n";
			#endif
			assert(false);
			
		}
		else
		{
			cout << "\nUnknown formula->Type encountered in helper.cpp::getFactorsThroughTsietinUptoThresholdRecursive\n";		
			assert(false);
		}
	} // if(!label exists already) ends here
}//function ends here				



void obtainArbitraryBooleanProblemInstance(ABC* abcObj, Abc_Frame_t* abcFrame, Aig_Obj_t* &arbitrary_boolean_formula, Aig_Man_t* &aig_manager, list<string> &VariablesToEliminate)
{
	assert(benchmark_name != "");

	string command = "read " + benchmark_name + ";" + initCommand;

	#ifdef DEBUG_SKOLEM
	cout << command << endl;
	#endif

	if (abcObj->comExecute(abcFrame, command))
    	{
	 	cout << "cannot execute " << command << endl;
		assert(false);
	}

	Abc_Ntk_t* transition_function = abcFrame->pNtkCur;
	transition_function = Abc_NtkDup(transition_function);

	set<string> VariablesToEliminate_Set(VariablesToEliminate.begin(), VariablesToEliminate.end());

	// Let's get all the variable names and
	// Ci_name_to_Ci_number_map
	Abc_Obj_t* tempInputObj;
	int j = 0;
	vector<string> variable_names;
	Abc_NtkForEachCi(transition_function, tempInputObj, j)
	{
		string variable_name = Abc_ObjName(tempInputObj);
		variable_names.push_back(variable_name);

		Ci_name_to_Ci_number_map.insert(make_pair(variable_name, j));

		number_of_Cis++;				
	} 

	// Let's split the transition_function into factors

	aig_manager = Abc_NtkToDar(transition_function, 0, 0);
	// transition function converted to aig_manager	

	// reading the factors
	Aig_Obj_t* factorObj;
    	int i = 0;
	set<Aig_Obj_t*> Factors;

	Aig_ManForEachPoSeq(aig_manager, factorObj, i )
    	{
		assert(factorObj != NULL);

		Aig_Obj_t* Fanin0_factorObj = Aig_ObjChild0(factorObj);		 
		// Note that it is important to use Aig_ObjChild0 here
		// Earlier Aig_ObjFanin0 was used; but Aig_ObjFanin0 regularizes the dag,
		// Aig_ObjChild0 does not regularize the dag		

		assert(Fanin0_factorObj != NULL);

		Factors.insert(Fanin0_factorObj);
    	}

	// conjoing the Factors to get arbitrary_boolean_formula

	arbitrary_boolean_formula = createAnd(Factors, aig_manager);
	assert(arbitrary_boolean_formula != NULL);

	// Let's get the IDs of the variables
	Aig_Obj_t* ciObj;
	vector<int> variable_ids;
	i = 0;
	Aig_ManForEachCi(aig_manager, ciObj, i )
	{
		int Id = Aig_ObjId(ciObj); // no need to apply Aig_Regular() as ciObj is CI
		variable_ids.push_back(Id);

		string variable_name = 	variable_names[i];	
		if(VariablesToEliminate_Set.find(variable_name) != VariablesToEliminate_Set.end())
		// variable_name is an input; it is a Ci to be eliminated
		{
			Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.insert(make_pair(variable_name, ciObj));
		}

		Ci_name_to_Ci_object_map.insert(make_pair(variable_name, ciObj));
	}

	// Let's create the variable_id ---> variable_name map

	assert(variable_ids.size() == variable_names.size());	
	for(int i = 0; i < variable_ids.size(); i++)
	{
		Ci_id_to_Ci_name_map.insert(make_pair(variable_ids[i], variable_names[i]));
	}
}


void showNodeWithPolarity(call_type polarity, Aig_Obj_t* formula)
{
	if(polarity == original)
	{
		cout << formula;
	}
	else
	{
		cout << "~ " << formula;
	}
}


void fixOrderOfEliminationForArbitraryBooleanFormula(list<string> &VariablesToEliminate, Aig_Obj_t* arbitrary_boolean_formula, Aig_Man_t* aig_manager)
{
	struct timeval ordering_step_start_ms, ordering_step_finish_ms;
	gettimeofday (&ordering_step_start_ms, NULL); 

	if(order_of_elimination_of_variables == 0)// alphabetical
	{
		#ifdef DEBUG_SKOLEM
		writeFormulaToFile(aig_manager, arbitrary_boolean_formula, "arbitrary_boolean_formula", ".v", 0, 0);	
		#endif

		// Let's fix the variables to be eliminated
		set<string> Local_VariablesToEliminate_Set; // All input variables
		copy(VariablesToEliminate.begin(), VariablesToEliminate.end(), inserter(Local_VariablesToEliminate_Set, Local_VariablesToEliminate_Set.begin()));

		set<string> Support_arbitrary_boolean_formula; // All variables in support
		computeSupport(arbitrary_boolean_formula, Support_arbitrary_boolean_formula, aig_manager);

		set_intersection(Local_VariablesToEliminate_Set.begin(), Local_VariablesToEliminate_Set.end(), Support_arbitrary_boolean_formula.begin(), Support_arbitrary_boolean_formula.end(),inserter(Global_VariablesToEliminate_Set, Global_VariablesToEliminate_Set.begin())); // we set the Global_VariablesToEliminate_Set as the input variables that are present in the support

		// set the variables to be eliminated in that order
		VariablesToEliminate.clear();		
		// push back the variables in VariablesToEliminate
		for(set<string>::iterator Global_VariablesToEliminate_Set_it = 	Global_VariablesToEliminate_Set.begin(); Global_VariablesToEliminate_Set_it != 	Global_VariablesToEliminate_Set.end(); Global_VariablesToEliminate_Set_it++)
		{
			string varible_to_eliminate = *Global_VariablesToEliminate_Set_it;
			VariablesToEliminate.push_back(varible_to_eliminate);
		}		

		
		Global_VariablesToEliminate_Set.clear();

		#ifdef DEBUG_SKOLEM
		cout << endl << "VariablesToEliminate" << endl;
		showList(VariablesToEliminate);	
		#endif
			
	}
	else if(order_of_elimination_of_variables == 1 || order_of_elimination_of_variables == 5)// least-occuring variable first or most-occuring variable first
	{
		#ifdef DEBUG_SKOLEM
		writeFormulaToFile(aig_manager, arbitrary_boolean_formula, "arbitrary_boolean_formula", ".v", 0, 0);	
		#endif

		// Let's fix the variables to be eliminated
		set<string> Local_VariablesToEliminate_Set; // All input variables
		copy(VariablesToEliminate.begin(), VariablesToEliminate.end(), inserter(Local_VariablesToEliminate_Set, Local_VariablesToEliminate_Set.begin()));

		set<string> Support_arbitrary_boolean_formula; // All variables in support
		computeSupport(arbitrary_boolean_formula, Support_arbitrary_boolean_formula, aig_manager);

		set_intersection(Local_VariablesToEliminate_Set.begin(), Local_VariablesToEliminate_Set.end(), Support_arbitrary_boolean_formula.begin(), Support_arbitrary_boolean_formula.end(),inserter(Global_VariablesToEliminate_Set, Global_VariablesToEliminate_Set.begin())); // we set the Global_VariablesToEliminate_Set as the input variables that are present in the support

		map<string, int> number_of_occurrences_of_variables_to_be_eliminated;
		computeNumberOfNodesInWhichEachInputOccurs(arbitrary_boolean_formula, aig_manager, number_of_occurrences_of_variables_to_be_eliminated, true);

		map<int, set<string> > number_of_occurrences_to_variables_map;
		for(map<string, int>::iterator number_of_occurrences_of_variables_to_be_eliminated_it = number_of_occurrences_of_variables_to_be_eliminated.begin(); number_of_occurrences_of_variables_to_be_eliminated_it != number_of_occurrences_of_variables_to_be_eliminated.end(); number_of_occurrences_of_variables_to_be_eliminated_it++)
		{
			string variable_to_eliminate_occurring = number_of_occurrences_of_variables_to_be_eliminated_it->first;
			int number_of_occurrences = number_of_occurrences_of_variables_to_be_eliminated_it->second;
			
			map<int, set<string> >::iterator number_of_occurrences_to_variables_map_it =  number_of_occurrences_to_variables_map.find(number_of_occurrences);
			if(number_of_occurrences_to_variables_map_it == number_of_occurrences_to_variables_map.end()) 	
			{
				set<string> variables_to_eliminate_occurring;
				variables_to_eliminate_occurring.insert(variable_to_eliminate_occurring);

				number_of_occurrences_to_variables_map.insert(make_pair(number_of_occurrences, variables_to_eliminate_occurring));			
			}
			else
			{
				(number_of_occurrences_to_variables_map_it->second).insert(variable_to_eliminate_occurring);
			}
		}
		
		// set the variables to be eliminated in that order
		Global_VariablesToEliminate_Set.clear();
		VariablesToEliminate.clear();		
		// push back the variables in VariablesToEliminate

		for(map<int, set<string> >::iterator number_of_occurrences_to_variables_map_it = number_of_occurrences_to_variables_map.begin(); number_of_occurrences_to_variables_map_it != number_of_occurrences_to_variables_map.end(); number_of_occurrences_to_variables_map_it++)
		{
			int number_of_occurrences = number_of_occurrences_to_variables_map_it->first;
			set<string> variables_to_eliminate_occurring = number_of_occurrences_to_variables_map_it->second;

			for(set<string>::iterator variables_to_eliminate_occurring_it = variables_to_eliminate_occurring.begin(); variables_to_eliminate_occurring_it != variables_to_eliminate_occurring.end(); variables_to_eliminate_occurring_it++)
			{
				VariablesToEliminate.push_back(*variables_to_eliminate_occurring_it);	
			}
		}

		if(order_of_elimination_of_variables == 5) //most-occurring-first
		{
			VariablesToEliminate.reverse();
		}
		
		#ifdef DEBUG_SKOLEM
		cout << endl << "VariablesToEliminate" << endl;
		showList(VariablesToEliminate);		
		#endif
	}
	else if(order_of_elimination_of_variables == 6 || order_of_elimination_of_variables == 7)// smallest/biggest cofactor-1 first
	{
		#ifdef DEBUG_SKOLEM
		writeFormulaToFile(aig_manager, arbitrary_boolean_formula, "arbitrary_boolean_formula", ".v", 0, 0);	
		#endif

		// Let's fix the variables to be eliminated
		set<string> Local_VariablesToEliminate_Set; // All input variables
		copy(VariablesToEliminate.begin(), VariablesToEliminate.end(), inserter(Local_VariablesToEliminate_Set, Local_VariablesToEliminate_Set.begin()));

		set<string> Support_arbitrary_boolean_formula; // All variables in support
		computeSupport(arbitrary_boolean_formula, Support_arbitrary_boolean_formula, aig_manager);

		set_intersection(Local_VariablesToEliminate_Set.begin(), Local_VariablesToEliminate_Set.end(), Support_arbitrary_boolean_formula.begin(), Support_arbitrary_boolean_formula.end(),inserter(Global_VariablesToEliminate_Set, Global_VariablesToEliminate_Set.begin())); // we set the Global_VariablesToEliminate_Set as the input variables that are present in the support

		map<string, int> sizes_of_cofactors_of_variables_to_be_eliminated;
		computeSizesOfCofactorsOfVariablesToBeEliminated(arbitrary_boolean_formula, aig_manager, sizes_of_cofactors_of_variables_to_be_eliminated);

		map<int, set<string> > sizes_of_cofactors_to_variables_map;
		for(map<string, int>::iterator sizes_of_cofactors_of_variables_to_be_eliminated_it = sizes_of_cofactors_of_variables_to_be_eliminated.begin(); sizes_of_cofactors_of_variables_to_be_eliminated_it != sizes_of_cofactors_of_variables_to_be_eliminated.end(); sizes_of_cofactors_of_variables_to_be_eliminated_it++)
		{
			string variable_to_eliminate_occurring = sizes_of_cofactors_of_variables_to_be_eliminated_it->first;
			int size_of_cofactor = sizes_of_cofactors_of_variables_to_be_eliminated_it->second;
			
			map<int, set<string> >::iterator sizes_of_cofactors_to_variables_map_it =  sizes_of_cofactors_to_variables_map.find(size_of_cofactor);
			if(sizes_of_cofactors_to_variables_map_it == sizes_of_cofactors_to_variables_map.end()) 	
			{
				set<string> variables_to_eliminate_occurring;
				variables_to_eliminate_occurring.insert(variable_to_eliminate_occurring);

				sizes_of_cofactors_to_variables_map.insert(make_pair(size_of_cofactor, variables_to_eliminate_occurring));			
			}
			else
			{
				(sizes_of_cofactors_to_variables_map_it->second).insert(variable_to_eliminate_occurring);
			}
		}
		
		// set the variables to be eliminated in that order
		Global_VariablesToEliminate_Set.clear();
		VariablesToEliminate.clear();		
		// push back the variables in VariablesToEliminate

		for(map<int, set<string> >::iterator sizes_of_cofactors_to_variables_map_it = sizes_of_cofactors_to_variables_map.begin(); sizes_of_cofactors_to_variables_map_it != sizes_of_cofactors_to_variables_map.end(); sizes_of_cofactors_to_variables_map_it++)
		{
			int size_of_cofactor = sizes_of_cofactors_to_variables_map_it->first;
			set<string> variables_to_eliminate_occurring = sizes_of_cofactors_to_variables_map_it->second;

			for(set<string>::iterator variables_to_eliminate_occurring_it = variables_to_eliminate_occurring.begin(); variables_to_eliminate_occurring_it != variables_to_eliminate_occurring.end(); variables_to_eliminate_occurring_it++)
			{
				VariablesToEliminate.push_back(*variables_to_eliminate_occurring_it);	
			}
		}

		if(order_of_elimination_of_variables == 7) //biggest cofactor-1 first
		{
			VariablesToEliminate.reverse();
		}
		
		#ifdef DEBUG_SKOLEM
		cout << endl << "VariablesToEliminate" << endl;
		showList(VariablesToEliminate);		
		#endif
	}
	else if(order_of_elimination_of_variables == 2)// external
	{
		// we should read the order from the given file
		list<string> OrderOfVariableEliminationFromFile;
		obtainOrderOfVariableEliminationFromFile(OrderOfVariableEliminationFromFile);

		#ifdef DEBUG_SKOLEM 
		cout << endl << "OrderOfVariableEliminationFromFile" << endl;
		showList(OrderOfVariableEliminationFromFile);
		#endif

		set<string> Local_VariablesToEliminate_Set; // All input variables
		copy(VariablesToEliminate.begin(), VariablesToEliminate.end(), inserter(Local_VariablesToEliminate_Set, Local_VariablesToEliminate_Set.begin()));


		set<string> Support_arbitrary_boolean_formula; // All variables in support
		computeSupport(arbitrary_boolean_formula, Support_arbitrary_boolean_formula, aig_manager);

		VariablesToEliminate.clear();

		for(list<string>::iterator var_order_it = OrderOfVariableEliminationFromFile.begin(); var_order_it != OrderOfVariableEliminationFromFile.end(); var_order_it++)
		{
			string var_from_order_file = *var_order_it;
			if(Local_VariablesToEliminate_Set.find(var_from_order_file) != Local_VariablesToEliminate_Set.end() && Support_arbitrary_boolean_formula.find(var_from_order_file) != Support_arbitrary_boolean_formula.end()) // this is a var to elim as (1) it is present in file, (2) it is an input variable, and (3) it is present in support of arbitrary_boolean_formula
			{
				VariablesToEliminate.push_back(var_from_order_file);
			}
		}

		//assert(Local_VariablesToEliminate_Set.size() == VariablesToEliminate.size());

		#ifdef DEBUG_SKOLEM
		cout << endl << "VariablesToEliminate" << endl;
		showList(VariablesToEliminate);
		#endif
	}
	else
	{
		cout << "\nUnknown order_of_elimination_of_variables\n";
		assert(false);
	}

	string order_file_name = logfile_prefix;

	if(order_of_elimination_of_variables == 0)
	{
		order_file_name += "lexico_graphic_order.txt";
	}
	else if(order_of_elimination_of_variables == 1)
	{
		order_file_name += "least_occurring_first_order.txt";
	}
	else if(order_of_elimination_of_variables == 2)
	{
		order_file_name += "external_order.txt";		
	}
	else if(order_of_elimination_of_variables == 5)
	{
		order_file_name += "most_occurring_first_order.txt";
	}
	else if(order_of_elimination_of_variables == 6)
	{
		order_file_name += "smallest_cofactor1_first_order.txt";
	}
	else if(order_of_elimination_of_variables == 7)
	{
		order_file_name += "biggest_cofactor1_first_order.txt";
	}
	else
	{
		cout << "\nUnknown order " << order_of_elimination_of_variables << endl;
		assert(false);
	}

	FILE* order_fp = fopen(order_file_name.c_str(), "w+");
	assert(order_fp != NULL);
	printList(VariablesToEliminate, order_fp);
	fclose(order_fp);

	gettimeofday (&ordering_step_finish_ms, NULL);
	total_time_in_ordering_for_arbitrary_boolean_combinations = ordering_step_finish_ms.tv_sec * 1000 + ordering_step_finish_ms.tv_usec / 1000;
	total_time_in_ordering_for_arbitrary_boolean_combinations -= ordering_step_start_ms.tv_sec * 1000 + ordering_step_start_ms.tv_usec / 1000;

	#ifdef DEBUG_SKOLEM 
	cout << endl << "total_time_in_ordering_for_arbitrary_boolean_combinations = " << total_time_in_ordering_for_arbitrary_boolean_combinations << endl;
	#endif

	if(exit_after_order_finding && perform_cegar_on_arbitrary_boolean_formulas && set_most_significant_word_to_zero_in_factorization_benchmarks)
	// In this case, we want to print the arbitrary boolean combination out
	{
		Aig_Man_t* simplified_formula_aig_manager;
		simplified_formula_aig_manager = simplifyUsingConeOfInfluence( aig_manager, Aig_ManCoNum(aig_manager)-1, 1 );
		assert(simplified_formula_aig_manager != NULL);

		set<string> Cis_in_Support; 
		computeSupport(arbitrary_boolean_formula, Cis_in_Support, aig_manager);
		
		string verilog_file = benchmark_name_without_extension;
		verilog_file += "_simplified";
		char pname[100];
		strcpy(pname, verilog_file.c_str());
		simplified_formula_aig_manager->pName = pname;
		
		verilog_file += ".v";
		char verilog_file_char[100];
		strcpy(verilog_file_char, verilog_file.c_str());
	
		writeCombinationalCircuitInVerilog(simplified_formula_aig_manager, verilog_file_char, Cis_in_Support);		
	}
}



void obtainArbitraryBooleanProblemInstanceFromGeneratedBenchmark(ABC* abcObj, Abc_Frame_t* abcFrame, Aig_Obj_t* &arbitrary_boolean_formula, Aig_Man_t* &aig_manager, list<string> &VariablesToEliminate)
{
	assert(benchmark_name != "");

	string command = "read " + benchmark_name + ";" + initCommand;
	
	#ifdef DEBUG_SKOLEM
	cout << command << endl;
	#endif

	if (abcObj->comExecute(abcFrame, command))
    	{
	 	cout << "cannot execute " << command << endl;
		assert(false);
	}

	#ifdef DEBUG_SKOLEM //Printing original circuit
	command = "write ckt.v;";
	cout << command << endl;
		
	if (abcObj->comExecute(abcFrame, command))
	{
		cout << "cannot execute command " << command << endl;
		assert(false);
	}
	#endif	

	Abc_Ntk_t* transition_function = abcFrame->pNtkCur;
	transition_function = Abc_NtkDup(transition_function);

	// Let's get all the variable names and
	// Ci_name_to_Ci_number_map
	Abc_Obj_t* tempInputObj;
	int j = 0;
	vector<string> variable_names;
	Abc_NtkForEachCi(transition_function, tempInputObj, j)
	{
		string variable_name = Abc_ObjName(tempInputObj);
		variable_names.push_back(variable_name);

		Ci_name_to_Ci_number_map.insert(make_pair(variable_name, j));

		number_of_Cis++;				
	} 

	aig_manager = Abc_NtkToDar(transition_function, 0, 0);
	// transition function converted to aig_manager	

	// Get the root_of_conjunction
	assert(Aig_ManCoNum(aig_manager) == 1);
	Aig_Obj_t* CO_aig_manager;
	CO_aig_manager = Aig_ManCo(aig_manager, 0);
	assert(CO_aig_manager != NULL);

	Aig_Obj_t* root_of_conjunction;
	root_of_conjunction = Aig_ObjChild0(CO_aig_manager);	
	assert(root_of_conjunction != NULL);

	arbitrary_boolean_formula = root_of_conjunction;

	// Limiting no: of varsto elim if needed
	Aig_Obj_t* ciObj_temp;
	int k = 0;
	int input_var_count_temp = 0;
	Aig_ManForEachCi(aig_manager, ciObj_temp, k )
	{
		string variable_name = 	variable_names[k];
		if(variable_name[0] == 'i' && variable_name[1] == '_')
			input_var_count_temp++;
		else if(variable_name[0] == 'i') //Added for POPL'17
			input_var_count_temp++;
	}

	if(limit_on_variables_to_eliminate != -1)
	{
		assert(limit_on_variables_to_eliminate >=1 && limit_on_variables_to_eliminate <= 100);
		limit_on_variables_to_eliminate = (input_var_count_temp * limit_on_variables_to_eliminate)/100;
	}

	//cout << "\nlimit_on_variables_to_eliminate = " << limit_on_variables_to_eliminate << endl;

	// Let's get the IDs of the variables
	
	Aig_Obj_t* ciObj;
	vector<int> variable_ids;
	int i = 0;

	int vars_to_elim_limiting_count = 0;
	Aig_ManForEachCi(aig_manager, ciObj, i )
	{
		int Id = Aig_ObjId(ciObj); // no need to apply Aig_Regular() as ciObj is CI
		variable_ids.push_back(Id);

		string variable_name = 	variable_names[i];
		if(variable_name[0] == 'i' && variable_name[1] == '_')
		// variable_name is a Ci to be eliminated
		{
			if(limit_on_variables_to_eliminate == -1 || vars_to_elim_limiting_count < limit_on_variables_to_eliminate)
			{
				VariablesToEliminate.push_back(variable_name);
				Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.insert(make_pair(variable_name, ciObj));
				vars_to_elim_limiting_count++;
			}
		}
		else if(variable_name[0] == 'i') //Added for POPL'17
		// variable_name is a Ci to be eliminated
		{
			if(limit_on_variables_to_eliminate == -1 || vars_to_elim_limiting_count < limit_on_variables_to_eliminate)
			{
				VariablesToEliminate.push_back(variable_name);
				Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.insert(make_pair(variable_name, ciObj));
				vars_to_elim_limiting_count++;
			}
		}

		Ci_name_to_Ci_object_map.insert(make_pair(variable_name, ciObj));
	}

	// Let's create the variable_id ---> variable_name map

	assert(variable_ids.size() == variable_names.size());	
	for(int i = 0; i < variable_ids.size(); i++)
	{
		Ci_id_to_Ci_name_map.insert(make_pair(variable_ids[i], variable_names[i]));
	}	
}

int obtainTreeSizeFromHashTable(Aig_Obj_t* formula)
{
	assert( !Aig_IsComplement(formula) );
	int key = Aig_ObjId(formula);

	t_HashTable<int, int>::iterator TreeSizesOfNodes_it = TreeSizesOfNodes.find(key);
	assert(TreeSizesOfNodes_it != TreeSizesOfNodes.end());

	return TreeSizesOfNodes_it.getValue();
}

void obtainVarsToElimFromHashTable(Aig_Obj_t* formula, set<string> &varstoelim_in_formula)
{
	assert( !Aig_IsComplement(formula) );
	int key = Aig_ObjId(formula);

	t_HashTable<int, set<string> >::iterator VarsToElimOfNodes_it = VarsToElimOfNodes.find(key);
	assert(VarsToElimOfNodes_it != VarsToElimOfNodes.end());

	varstoelim_in_formula = VarsToElimOfNodes_it.getValue();
}

bool chooseToApplyMonoSkolem(Aig_Obj_t* formula)
{
	if(!choose_to_apply_monoskolem_on_smaller_problem_instances) //never choose MonoSkolem
	{
		return false;
	}
	else
	{
		int treesize_of_formula;
		set<string> varstoelim_in_formula;
		int number_of_varstoelim_in_formula;

		treesize_of_formula = obtainTreeSizeFromHashTable(formula);
		obtainVarsToElimFromHashTable(formula, varstoelim_in_formula);	
		number_of_varstoelim_in_formula = varstoelim_in_formula.size();

		#ifdef DEBUG_SKOLEM
		cout << "\nobtainTreeSizeFromHashTable(" << formula << ") = " << treesize_of_formula;
		cout << "\n|obtainVarsToElimFromHashTable(" << formula << ")| = " << number_of_varstoelim_in_formula;
		#endif

		bool use_parameterized_scheme = true;
		if(use_parameterized_scheme)
		{
			if(number_of_varstoelim_in_formula == 0)
			{
				return true;
			}
			else
			{
				int threshold_tree_size_local = threshold_size_mult_two_pow_varstoelim_to_apply_monoskolem/2;
				// even if number_of_varstoelim_in_formula == 1, threshold_tree_size_local * 2^number_of_varstoelim_in_formula is threshold_size_mult_two_pow_varstoelim_to_apply_monoskolem
				int threshold_varstoelim_local = log2(threshold_size_mult_two_pow_varstoelim_to_apply_monoskolem);
				// even if treesize_of_formula == 1, treesize_of_formula * 2^threshold_varstoelim_local is threshold_size_mult_two_pow_varstoelim_to_apply_monoskolem

				#ifdef DEBUG_SKOLEM
				cout << "\nthreshold_tree_size_local == " << threshold_tree_size_local << endl;
				cout << "\nthreshold_varstoelim_local == " << threshold_varstoelim_local << endl;
				#endif

				if(number_of_varstoelim_in_formula > threshold_varstoelim_local || treesize_of_formula > threshold_tree_size_local)
				{
					return false;
				}
				else
				{
					int size_mult_two_pow_varstoelim = treesize_of_formula * pow(2, number_of_varstoelim_in_formula);
					#ifdef DEBUG_SKOLEM
					cout << "\nsize_mult_two_pow_varstoelim == " << size_mult_two_pow_varstoelim << endl;					
					#endif

					if(size_mult_two_pow_varstoelim <= threshold_size_mult_two_pow_varstoelim_to_apply_monoskolem)
					{
						return true;
					} 
					else
					{
						return false;
					}
				}				
			}//if(number_of_varstoelim_in_formula > 0)
		}
		else
		{
		
			if(number_of_varstoelim_in_formula == 0)
			{
				return true;
			}
			else if(number_of_varstoelim_in_formula >= 9 || treesize_of_formula > 4000)
			{
				return false;
			}
			else if(number_of_varstoelim_in_formula == 1 && treesize_of_formula <= 4000)
			{
				return true;
			}
			else if(number_of_varstoelim_in_formula == 2 && treesize_of_formula <= 2000)
			{
				return true;
			}
			else if(number_of_varstoelim_in_formula == 3 && treesize_of_formula <= 1000)
			{
				return true;
			}
			else if(number_of_varstoelim_in_formula == 4 && treesize_of_formula <= 500)
			{
				return true;
			}
			else if(number_of_varstoelim_in_formula == 5 && treesize_of_formula <= 250)
			{
				return true;
			}
			else if(number_of_varstoelim_in_formula == 6 && treesize_of_formula <= 125)
			{
				return true;
			}
			else if(number_of_varstoelim_in_formula == 7 && treesize_of_formula <= 65)
			{
				return true;
			}
			else if(number_of_varstoelim_in_formula == 8 && treesize_of_formula <= 32)
			{
				return true;
			}
			else
			{
				return false;
			}

		}//if(!use_parameterized_scheme)
	}//if(choose_to_apply_monoskolem_on_smaller_problem_instances)
}//function ends here



void findTreeSizeAndVarsToElim(Aig_Obj_t* formula, Aig_Man_t* aig_manager)
{
	#ifdef DETAILED_RECORD_KEEP
	unsigned long long int step_ms;
	struct timeval step_start_ms, step_finish_ms;
	gettimeofday (&step_start_ms, NULL); 	
	#endif 

	assert(formula != NULL);
	formula = Aig_Regular(formula);

	set<string> varstoelim_in_root;
	int treesize_of_root = findTreeSizeAndVarsToElim_Recur(formula, varstoelim_in_root, aig_manager, true);

	#ifdef DETAILED_RECORD_KEEP
	gettimeofday (&step_finish_ms, NULL);
   	step_ms = step_finish_ms.tv_sec * 1000 + step_finish_ms.tv_usec / 1000;
   	step_ms -= step_start_ms.tv_sec * 1000 + step_start_ms.tv_usec / 1000;

	cout << "\ntotal_time_in_dfs_during_preprocessing = " << step_ms << " m.secs\n";
	total_time_in_dfs_during_preprocessing = step_ms;
	#endif

}



int findTreeSizeAndVarsToElim_Recur(Aig_Obj_t* formula, set<string> &varstoelim_in_formula, Aig_Man_t* aig_manager, bool include_only_inputs)
{
	assert(formula != NULL);
	assert(!Aig_IsComplement(formula));

	int key = Aig_ObjId(formula);
	int treesize_of_formula;

	t_HashTable<int, int>::iterator TreeSizesOfNodes_it = TreeSizesOfNodes.find(key);
	if (TreeSizesOfNodes_it != TreeSizesOfNodes.end()) // entry present in HashTable
	{
		t_HashTable<int, set<string> >::iterator VarsToElimOfNodes_it = VarsToElimOfNodes.find(key);
		assert(VarsToElimOfNodes_it != VarsToElimOfNodes.end());
		varstoelim_in_formula = VarsToElimOfNodes_it.getValue();
		
		treesize_of_formula = TreeSizesOfNodes_it.getValue();
	}
	else // No entry in HashTable
	{
		if(formula->Type == AIG_OBJ_CONST1)
		{
			varstoelim_in_formula.clear();
			treesize_of_formula = 1;

			VarsToElimOfNodes[key] = varstoelim_in_formula;
			TreeSizesOfNodes[key] = treesize_of_formula;

			#ifdef DEBUG_SKOLEM
			cout << endl << formula;
			showSet(varstoelim_in_formula, "varstoelim_in_formula");
			cout << "\ntreesize = " << treesize_of_formula << endl;
			#endif
		}
		else if(formula->Type == AIG_OBJ_CI)
		{
			// find the variable
			int Ci_id = key; 
			map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(Ci_id);
			if(Ci_id_to_Ci_name_map_it == Ci_id_to_Ci_name_map.end())
			{
				cout << "\nNo entry for " << Ci_id << " in Ci_id_to_Ci_name_map\n";
				assert(false);
			}
			string Ci_name = Ci_id_to_Ci_name_map_it->second;

			if(include_only_inputs)
			{
				if(Global_VariablesToEliminate_Set.find(Ci_name) != Global_VariablesToEliminate_Set.end())//Ci_name is a variable to eliminate
				{
					varstoelim_in_formula.clear();
					varstoelim_in_formula.insert(Ci_name);				
				}
			}
			else
			{
				varstoelim_in_formula.clear();
				varstoelim_in_formula.insert(Ci_name);	
			}

			treesize_of_formula = 1;

			VarsToElimOfNodes[key] = varstoelim_in_formula;
			TreeSizesOfNodes[key] = treesize_of_formula;

			#ifdef DEBUG_SKOLEM
			cout << endl << formula;
			showSet(varstoelim_in_formula, "varstoelim_in_formula");
			cout << "\ntreesize = " << treesize_of_formula << endl;
			#endif
		}
		else if(formula->Type == AIG_OBJ_AND)// AND encountered
		{
			set<string> varstoelim_in_left;
			set<string> varstoelim_in_right;
			int treesize_of_left;
			int treesize_of_right;

			treesize_of_left = findTreeSizeAndVarsToElim_Recur(Aig_ObjFanin0(formula), varstoelim_in_left, aig_manager, include_only_inputs);
			treesize_of_right = findTreeSizeAndVarsToElim_Recur(Aig_ObjFanin1(formula), varstoelim_in_right, aig_manager, include_only_inputs);
			set_union(varstoelim_in_left.begin(), varstoelim_in_left.end(), varstoelim_in_right.begin(), varstoelim_in_right.end(),inserter(varstoelim_in_formula, varstoelim_in_formula.begin()));
			treesize_of_formula = treesize_of_left + treesize_of_right + 1;

			VarsToElimOfNodes[key] = varstoelim_in_formula;
			TreeSizesOfNodes[key] = treesize_of_formula;

			#ifdef DEBUG_SKOLEM
			cout << endl << formula;
			showSet(varstoelim_in_formula, "varstoelim_in_formula");
			cout << "\ntreesize = " << treesize_of_formula << endl;
			#endif
		}
		else
		{
			cout << "\nUnknown formula->Type encountered in helper.cpp::findTreeSizeAndVarsToElim_Recur\n";		
			assert(false);
		}
	
	}

	return treesize_of_formula;
}


void writeFormulaToFileWithNodeId(Aig_Man_t* aig_manager, Aig_Obj_t* formula, string outfile)
{
	assert(formula != NULL);
	
	FILE* fp = fopen(outfile.c_str(), "w+");
	assert(fp != NULL);

	writeFormulaToFileWithNodeId(aig_manager, formula, fp);
	fclose(fp);
}


void writeFormulaToFileWithNodeId(Aig_Man_t* aig_manager, Aig_Obj_t* formula, FILE* fp)
{
	static t_HashTable<string, int> nodes_encountered;
	writeFormulaToFileWithNodeId(aig_manager, formula, fp, nodes_encountered);
	nodes_encountered.clear();
}



void writeFormulaToFileWithNodeId(Aig_Man_t* aig_manager, Aig_Obj_t* formula, FILE* fp, t_HashTable<string, int> &nodes_encountered)
{
	assert(formula != NULL);

	string key = toString(formula);

	t_HashTable<string, int>::iterator nodes_encountered_it = nodes_encountered.find(key);
	if (nodes_encountered_it != nodes_encountered.end()) // formula traversed already
	{
		return;
	}
	else
	{
		nodes_encountered[key] = 1;

		if(Aig_IsComplement(formula)) // ~ encountered
		{
			Aig_Obj_t* child_1 = Aig_Regular(formula);
			assert(child_1 != NULL);
			
			fprintf(fp, "\n%p: ~ %p", formula, child_1);

			writeFormulaToFileWithNodeId(aig_manager, child_1, fp, nodes_encountered);

		} // if(Aig_IsComplement(formula)) ends here
		else if(formula->Type == AIG_OBJ_CI) //CI encountered
		{
			int Ci_id = Aig_ObjId(formula); 
			map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(Ci_id);
			if(Ci_id_to_Ci_name_map_it == Ci_id_to_Ci_name_map.end())
			{
				cout << "\nNo entry for " << Ci_id << " in Ci_id_to_Ci_name_map\n";
				assert(false);
			}
			string Ci_name = Ci_id_to_Ci_name_map_it->second;			

			fprintf(fp, "\n%p(%d): %s", formula, Ci_id, Ci_name.c_str());
		}
		else if(formula->Type == AIG_OBJ_CO) //CO encountered
		{
			// do nothing
		}
		else if(formula->Type == AIG_OBJ_CONST1) // 1 encountered
		{
			fprintf(fp, "\n%p(%d): true", formula, Aig_ObjId(formula));
		}
		else if(formula->Type == AIG_OBJ_AND)// child_1 \wedge child_2 encountered
		{
			Aig_Obj_t* child_1 = Aig_ObjChild0(formula);
			Aig_Obj_t* child_2 = Aig_ObjChild1(formula);

			assert(child_1 != NULL);
			assert(child_2 != NULL);

			fprintf(fp, "\n%p(%d): & %p %p", formula, Aig_ObjId(formula), child_1, child_2);

			writeFormulaToFileWithNodeId(aig_manager, child_1, fp, nodes_encountered);
			writeFormulaToFileWithNodeId(aig_manager, child_2, fp, nodes_encountered);
		}
		else
		{
			cout << "\nUnknown formula->Type encountered in helper.cpp::writeFormulaToFileWithNodeId\n";		
			assert(false);
		}
	} // if(!label exists already) ends here
}//function ends here	




void purifyFailureCondition(Aig_Man_t* aig_manager)
{
	bool purification_done = true;

	set<Aig_Obj_t*> failure_condition_aig_components;
	Aig_Obj_t* root_of_conjunction = failure_condition_aig;

	assert(root_of_conjunction != NULL);
	vector<Aig_Obj_t*> roots_of_conjunction;

	if(!Aig_IsComplement(root_of_conjunction) && root_of_conjunction->Type == AIG_OBJ_AND)
	{
		roots_of_conjunction.push_back(root_of_conjunction);
	}
	else
	{
		failure_condition_aig_components.insert(root_of_conjunction);	
	}

	
	while(roots_of_conjunction.size() > 0)
	{
		root_of_conjunction = roots_of_conjunction[0];
		roots_of_conjunction.erase(roots_of_conjunction.begin());

		Aig_Obj_t* child1 = Aig_ObjChild0(root_of_conjunction);
		assert(child1 != NULL);
		if(!Aig_IsComplement(child1) && child1->Type == AIG_OBJ_AND)
		{
			roots_of_conjunction.push_back(child1);
		}
		else
		{
			failure_condition_aig_components.insert(child1);	
		}	

		Aig_Obj_t* child2 = Aig_ObjChild1(root_of_conjunction);
		assert(child2 != NULL);
		if(!Aig_IsComplement(child2) && child2->Type == AIG_OBJ_AND)
		{
			roots_of_conjunction.push_back(child2);
		}
		else
		{
			failure_condition_aig_components.insert(child2);	
		}
	}


	set<Aig_Obj_t*> purified_failure_condition_aig_components;
	for(set<Aig_Obj_t*>::iterator failure_condition_aig_components_it = failure_condition_aig_components.begin(); failure_condition_aig_components_it != failure_condition_aig_components.end(); failure_condition_aig_components_it++)
	{
		Aig_Obj_t* failure_condition_aig_component = *failure_condition_aig_components_it;
		Aig_Obj_t* regular_failure_condition_aig_component = Aig_Regular(failure_condition_aig_component);

		if(regular_failure_condition_aig_component->Type == AIG_OBJ_CI)
		{

			int Ci_id = Aig_ObjId(regular_failure_condition_aig_component); 
			map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(Ci_id);
			assert(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end());
			string Ci_name = Ci_id_to_Ci_name_map_it->second;

			if(input_names_in_circuit.find(Ci_name) != input_names_in_circuit.end())//Ci_name is an input
			{
				// do nothing
			}
			else
			{
				purified_failure_condition_aig_components.insert(failure_condition_aig_component);
			}
		
		}
		else // regular_failure_condition_aig_component is a formula
		{
			set<string> component_support;
			computeSupport(regular_failure_condition_aig_component, component_support, aig_manager);

			//showSet(component_support, "component_support");

			set<string> inputs_in_component;
			set_intersection(component_support.begin(), component_support.end(), input_names_in_circuit.begin(), input_names_in_circuit.end(), inserter(inputs_in_component, inputs_in_component.begin()));

			//showSet(inputs_in_component, "inputs_in_component");

			set<string> non_inputs_in_component;
			set_difference(component_support.begin(), component_support.end(), input_names_in_circuit.begin(), input_names_in_circuit.end(), inserter(non_inputs_in_component, non_inputs_in_component.begin()));

			//showSet(non_inputs_in_component, "non_inputs_in_component");

			if(non_inputs_in_component.empty()) // failure_condition_aig_component has only inputs
			{
				// do nothing
			}
			else if(inputs_in_component.empty()) // failure_condition_aig_component has only non-inputs
			{
				purified_failure_condition_aig_components.insert(failure_condition_aig_component);
			}
			else // failure_condition_aig_component has both inputs and non-inputs
			{
				// difficult to purify this way
				purification_done = false;
				purified_failure_condition_aig_components.insert(failure_condition_aig_component);
			}
		}	
	}


	// recreating failure_condition_aig
	
	failure_condition_aig = createAnd(purified_failure_condition_aig_components, aig_manager);
	assert(failure_condition_aig != NULL); 

	if(!purification_done)
	{
		cout << "\nIn purifyFailureCondition: failure_condition_aig is not completely purified\n";
		assert(false);
	}   	
	
}


void computeNumberOfNodesInWhichEachInputOccurs(Aig_Obj_t* formula, Aig_Man_t* aig_manager, map<string, int> &number_of_occurrences_of_variables_to_be_eliminated, bool include_only_inputs)
{
	assert(formula != NULL);
	formula = Aig_Regular(formula);

	set<string> varstoelim_in_root;
	int treesize_of_root = findTreeSizeAndVarsToElim_Recur(formula, varstoelim_in_root, aig_manager, include_only_inputs);
	
	// We now have the varstoelim in each node in the global hashtable VarsToElimOfNodes

	// Let's now create the map number_of_occurrences_of_variables_to_be_eliminated from 
	// the hashtable VarsToElimOfNodes
	Vec_Ptr_t* aig_nodes = Aig_Nodes(aig_manager, formula);
		
	int j = 0;
	Aig_Obj_t* node;
	Vec_PtrForEachEntry(Aig_Obj_t*, aig_nodes, node, j )  
	{
		assert(node != NULL);
		int node_id = node->Id;

		t_HashTable<int, set<string> >::iterator VarsToElimOfNodes_it = VarsToElimOfNodes.find(node_id);
		assert(VarsToElimOfNodes_it != VarsToElimOfNodes.end());
		set<string> varstoelim_in_node;

		varstoelim_in_node = VarsToElimOfNodes_it.getValue();	

		#ifdef DEBUG_SKOLEM
		cout << "\nnode_id = " << node_id;
		showSet(varstoelim_in_node, "varstoelim_in_node");
		#endif

		for(set<string>::iterator vars_it = varstoelim_in_node.begin(); vars_it != varstoelim_in_node.end(); vars_it++)
		{
			string vartoelim_in_node = *vars_it;
			map<string, int>::iterator number_of_occurrences_of_variables_to_be_eliminated_it = number_of_occurrences_of_variables_to_be_eliminated.find(vartoelim_in_node);
			if(number_of_occurrences_of_variables_to_be_eliminated_it == number_of_occurrences_of_variables_to_be_eliminated.end())
			{
				number_of_occurrences_of_variables_to_be_eliminated.insert(make_pair(vartoelim_in_node, 1));
			}
			else
			{
				number_of_occurrences_of_variables_to_be_eliminated_it->second = number_of_occurrences_of_variables_to_be_eliminated_it->second + 1;
			}
		}
	}

	#ifdef DEBUG_SKOLEM
	cout << "\nnumber_of_occurrences_of_variables_to_be_eliminated\n";
	for(map<string, int>::iterator number_of_occurrences_of_variables_to_be_eliminated_it = number_of_occurrences_of_variables_to_be_eliminated.begin(); number_of_occurrences_of_variables_to_be_eliminated_it != number_of_occurrences_of_variables_to_be_eliminated.end(); number_of_occurrences_of_variables_to_be_eliminated_it++)
	{
		cout << endl << number_of_occurrences_of_variables_to_be_eliminated_it->first << "\t" << number_of_occurrences_of_variables_to_be_eliminated_it->second;	
	}
	cout << endl;
	#endif
			
}


void Aig_Nodes_rec( Aig_Man_t * p, Aig_Obj_t * pObj, Vec_Ptr_t * vNodes )
{
    if ( Aig_ObjIsTravIdCurrent(p, pObj) )
        return;
    Aig_ObjSetTravIdCurrent(p, pObj);
    if ( Aig_ObjIsConst1(pObj) )
        return;
    if ( Aig_ObjIsCi(pObj) )
    {
        Vec_PtrPush( vNodes, pObj );
        return;
    }
    assert( Aig_ObjIsNode(pObj) || Aig_ObjIsBuf(pObj) );
    Aig_Nodes_rec( p, Aig_ObjFanin0(pObj), vNodes );
    if ( Aig_ObjFanin1(pObj) )
        Aig_Nodes_rec( p, Aig_ObjFanin1(pObj), vNodes );
    Vec_PtrPush( vNodes, pObj );
}



Vec_Ptr_t * Aig_Nodes( Aig_Man_t * p, Aig_Obj_t * pObj )
{
    Vec_Ptr_t * vNodes;
    assert( !Aig_IsComplement(pObj) );
    assert( !Aig_ObjIsCo(pObj) );
    Aig_ManIncrementTravId( p );
    vNodes = Vec_PtrAlloc( 100 );
    Aig_Nodes_rec( p, pObj, vNodes );
    return vNodes;
}


void computeSizesOfCofactorsOfVariablesToBeEliminated(Aig_Obj_t* formula, Aig_Man_t* aig_manager, map<string, int> &sizes_of_cofactors_of_variables_to_be_eliminated)
{
	for(set<string>::iterator Global_VariablesToEliminate_Set_it = 	Global_VariablesToEliminate_Set.begin(); Global_VariablesToEliminate_Set_it != 	Global_VariablesToEliminate_Set.end(); Global_VariablesToEliminate_Set_it++)
	{
		string varible_to_eliminate = *Global_VariablesToEliminate_Set_it;

		Aig_Obj_t* FormulaToSubstitute;
		FormulaToSubstitute = createTrue(aig_manager); 
		assert(FormulaToSubstitute != NULL);

		Aig_Obj_t* ReplacedFormula = ReplaceLeafByExpression(formula, varible_to_eliminate, FormulaToSubstitute, aig_manager); 
		assert(ReplacedFormula != NULL);

		int ReplacedFormula_size = computeSize(ReplacedFormula, aig_manager);

		sizes_of_cofactors_of_variables_to_be_eliminated.insert(make_pair(varible_to_eliminate, ReplacedFormula_size));
	}

	#ifdef DEBUG_SKOLEM
	cout << "\nsizes_of_cofactors_of_variables_to_be_eliminated\n";
	for(map<string, int>::iterator sizes_of_cofactors_of_variables_to_be_eliminated_it = sizes_of_cofactors_of_variables_to_be_eliminated.begin(); sizes_of_cofactors_of_variables_to_be_eliminated_it != sizes_of_cofactors_of_variables_to_be_eliminated.end(); sizes_of_cofactors_of_variables_to_be_eliminated_it++)
	{
		cout << endl << sizes_of_cofactors_of_variables_to_be_eliminated_it->first << "\t" << sizes_of_cofactors_of_variables_to_be_eliminated_it->second;	
	}
	cout << endl;
	#endif
}




void obtainArbitraryBooleanProblemInstanceFromFactorizationBenchmark(ABC* abcObj, Abc_Frame_t* abcFrame, Aig_Obj_t* &arbitrary_boolean_formula, Aig_Man_t* &aig_manager, list<string> &VariablesToEliminate)
{
	assert(benchmark_name != "");

	string command = "read " + benchmark_name + ";" + initCommand;
	
	#ifdef DEBUG_SKOLEM
	cout << command << endl;
	#endif

	if (abcObj->comExecute(abcFrame, command))
    	{
	 	cout << "cannot execute " << command << endl;
		assert(false);
	}

	#ifdef DEBUG_SKOLEM //Printing original circuit
	command = "write ckt.v;";
	cout << command << endl;
		
	if (abcObj->comExecute(abcFrame, command))
	{
		cout << "cannot execute command " << command << endl;
		assert(false);
	}
	#endif	

	Abc_Ntk_t* transition_function = abcFrame->pNtkCur;
	transition_function = Abc_NtkDup(transition_function);

	// Let's get all the variable names and
	// Ci_name_to_Ci_number_map
	Abc_Obj_t* tempInputObj;
	int j = 0;
	vector<string> variable_names;
	Abc_NtkForEachCi(transition_function, tempInputObj, j)
	{
		string variable_name = Abc_ObjName(tempInputObj);
		variable_names.push_back(variable_name);

		Ci_name_to_Ci_number_map.insert(make_pair(variable_name, j));

		number_of_Cis++;				
	} 

	aig_manager = Abc_NtkToDar(transition_function, 0, 0);
	// transition function converted to aig_manager	

	// Get the root_of_conjunction
	assert(Aig_ManCoNum(aig_manager) == 1);
	Aig_Obj_t* CO_aig_manager;
	CO_aig_manager = Aig_ManCo(aig_manager, 0);
	assert(CO_aig_manager != NULL);

	Aig_Obj_t* root_of_conjunction;
	root_of_conjunction = Aig_ObjChild0(CO_aig_manager);	
	assert(root_of_conjunction != NULL);

	arbitrary_boolean_formula = root_of_conjunction;

		
	//Let's get the IDs of the variables
	
	Aig_Obj_t* ciObj;
	vector<int> variable_ids;
	int i = 0;

	Aig_ManForEachCi(aig_manager, ciObj, i )
	{
		int Id = Aig_ObjId(ciObj); // no need to apply Aig_Regular() as ciObj is CI
		variable_ids.push_back(Id);

		string variable_name = 	variable_names[i];
		if(variable_name[0] == 'x' || variable_name[0] == 'y')
		// variable_name is a Ci to be eliminated
		{
			VariablesToEliminate.push_back(variable_name);
			Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.insert(make_pair(variable_name, ciObj));			
		}
		else if( variable_name[0] == 'i' && (variable_name[1] == '1' || variable_name[1] == '2' ))
		// variable_name is a Ci to be eliminated
		{
			VariablesToEliminate.push_back(variable_name);
			Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.insert(make_pair(variable_name, ciObj));			
		}

		Ci_name_to_Ci_object_map.insert(make_pair(variable_name, ciObj));
	}

	// Let's create the variable_id ---> variable_name map

	assert(variable_ids.size() == variable_names.size());	
	for(int i = 0; i < variable_ids.size(); i++)
	{
		Ci_id_to_Ci_name_map.insert(make_pair(variable_ids[i], variable_names[i]));
	}	

	if(set_most_significant_word_to_zero_in_factorization_benchmarks)
	{
		simplifyBySettingLeastSignificantWordToZero(aig_manager, arbitrary_boolean_formula, VariablesToEliminate);
		
		Aig_Obj_t* changed_arbitrary_boolean_formula_CO = Aig_ObjCreateCo(aig_manager, arbitrary_boolean_formula);
		assert(changed_arbitrary_boolean_formula_CO != NULL);	

		intermediate_cos_created.insert(CO_aig_manager);//This is no longer needed
	}
	

	#ifdef DEBUG_SKOLEM
	writeFormulaToFile(aig_manager, arbitrary_boolean_formula, "arbitrary_input_bool_formula", ".v", 0, 0);	
	cout << endl << "VariablesToEliminate" << endl; 
	showList(VariablesToEliminate);
	cout << endl;
	#endif	
}



// return 2 ^ number
unsigned long long int findPower(unsigned long long int number)
{
	unsigned long long int count = 0;
	unsigned long long int value = 1;
	while(count<number) 
	{
		count=count+1; 
		value=value*2;
	}
	return value;
}



// Function to convert a decimal number into binary format
string convertDecimalToBitvectorWithProperWidth(unsigned long long int dec, int Width)
{
	string str = integerToBinaryString(dec);
	int NoOfZeros = Width - str.length();

	string bv;
	for(int i=0; i<NoOfZeros; i++)
	{
		bv += "0";
	}
 
	bv += str;
	return bv;
}

// Function to convert a decimal number into a binary string
string integerToBinaryString(unsigned long long int i)
{
    if(i==0)
        return "0";
    string bin_str="";
    unsigned long long int j=i;
    while(j!=0)
    {
        if(j%2 == 0)
            bin_str = bin_str + "0";
        else
            bin_str = bin_str + "1";
        j = j / 2;
    }
    string str="";
    //Reversing the binary string to bring it to final format
    for(int k=bin_str.size()-1;k>=0;k--)
        str += bin_str[k];
    return str;
}


string getVariablenameAndVariableindexFromArrayReference(string var_to_elim, int &var_index)
{
	int idx = var_to_elim.find("[");
	string var_name = var_to_elim.substr(0, idx);
	string temp = var_to_elim.substr(idx+1);
	
	idx = temp.find("]");
        string var_index_string = temp.substr(0, idx);
        var_index = atoi(var_index_string.c_str());
	
	return var_name;
}


unsigned long long int binaryMapToNumber(map<int, bool> &bit_map)
{
	unsigned long long int number = 0;
	unsigned long long int exponent = 0;

	for(map<int, bool>::reverse_iterator bit_map_rit = bit_map.rbegin(); bit_map_rit != bit_map.rend(); ++bit_map_rit)
	{
		if(bit_map_rit->second)
		{
			unsigned long long int element;
			element = findPower(exponent);
			number = number + element;
		}
	
		exponent++;	
	}

	return number;
}


bool evaluateFormulaOfCi_Efficient(Aig_Obj_t* formula, map<string, bool> &variable_to_value_map)
{
	t_HashTable<int, bool> evaluationHashTable;
	bool value = evaluateFormulaOfCi_Efficient_DFS(Aig_Regular(formula), variable_to_value_map, evaluationHashTable);
	
	if(Aig_IsComplement(formula))
	{
		value = !value;
	}

	return value;
}


bool evaluateFormulaOfCi_Efficient_With_Given_HashTable(Aig_Obj_t* formula, map<string, bool> &variable_to_value_map, t_HashTable<int, bool> &evaluationHashTable)
{
	bool value = evaluateFormulaOfCi_Efficient_DFS(Aig_Regular(formula), variable_to_value_map, evaluationHashTable);
	
	if(Aig_IsComplement(formula))
	{
		value = !value;
	}

	return value;
}


bool evaluateFormulaOfCi_Efficient_DFS(Aig_Obj_t* formula, map<string, bool> &variable_to_value_map, t_HashTable<int, bool> &evaluationHashTable)
{
	assert(formula != NULL);
	assert( !Aig_IsComplement(formula) );

	int key = Aig_ObjId(formula);

	t_HashTable<int, bool>::iterator evaluationHashTable_it = evaluationHashTable.find(key);
	if (evaluationHashTable_it != evaluationHashTable.end()) // traversed already
	{
		return evaluationHashTable_it.getValue();;
	}
	else
	{
		bool node_value;

		if(formula->Type == AIG_OBJ_AND)// child_1 \wedge child_2 encountered
		{
			bool child_1_value = evaluateFormulaOfCi_Efficient_DFS(Aig_ObjFanin0(formula), variable_to_value_map, evaluationHashTable);
			bool child_2_value = evaluateFormulaOfCi_Efficient_DFS(Aig_ObjFanin1(formula), variable_to_value_map, evaluationHashTable);
			
			if(Aig_ObjFaninC0(formula))
			{
				child_1_value = !child_1_value;
			}

			if(Aig_ObjFaninC1(formula))
			{
				child_2_value = !child_2_value;
			}

			node_value = child_1_value && child_2_value;
		}
		else if(formula->Type == AIG_OBJ_CI) //CI encountered
		{
			map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(key);
			assert(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end());
			string Ci_name = Ci_id_to_Ci_name_map_it->second;

			#ifdef DEBUG_SKOLEM
				//cout << endl << Ci_name << " encountered in evaluation\n";
			#endif	

			map<string, bool>::iterator variable_to_value_map_it = variable_to_value_map.find(Ci_name);
			if(variable_to_value_map_it == variable_to_value_map.end())
			{
				cout << endl << Ci_name << " encountered in evaluation with no entry in variable_to_value_map\n";
				assert(false);
			}
			node_value = variable_to_value_map_it->second;

		}
		else if(formula->Type == AIG_OBJ_CONST1) // 1 encountered
		{
			node_value = true;
		}
		else
		{
			cout << "\nError inside function evaluateFormulaOfCi_Efficient_DFS! Unknown formula->Type " << formula->Type << " encountered\n";		
			assert(false);
		}

		evaluationHashTable[key] = node_value;

		return node_value;
	} // if(!traversed already) ends here
}



void simplifyBySettingLeastSignificantWordToZero(Aig_Man_t* aig_manager, Aig_Obj_t* &arbitrary_boolean_formula, list<string> &VariablesToEliminate)
{
	int number_of_x_y_variables = VariablesToEliminate.size();// no: of x variables + y variables		
	assert(number_of_x_y_variables % 2 == 0); // no: of x variables + y variables is even 
	int bits = number_of_x_y_variables/2;
	int number_of_zero_bits = bits/2;	

	set<string> zero_bits;
	for(list<string>::iterator it = VariablesToEliminate.begin(); it != VariablesToEliminate.end(); it++)
	{
		string var_to_elim = *it;
	
		string var_name;
		int var_index;
		var_name = getVariablenameAndVariableindexFromArrayReference(var_to_elim, var_index);
		

		if(var_index < number_of_zero_bits) // this is a zero bit
		{
			zero_bits.insert(var_to_elim);
		}
		
	}

	for(set<string>::iterator it = zero_bits.begin(); it != zero_bits.end(); it++)
	{
		string var_to_elim = *it;

		cout << "\nset " << var_to_elim << " to zero";

		VariablesToEliminate.remove(var_to_elim);

		Aig_Obj_t* FormulaToSubstitute = createFalse(aig_manager); 
		arbitrary_boolean_formula = ReplaceLeafByExpression(arbitrary_boolean_formula, var_to_elim, FormulaToSubstitute, aig_manager);
	}
}



void writeCombinationalCircuitInVerilog( Aig_Man_t * p, char * pFileName, set<string> &Cis_in_Support)
{
    map<Aig_Obj_t*, string> node_name_map;

    FILE * pFile;
    Vec_Ptr_t * vNodes;
    Aig_Obj_t * pObj, * pObjLi, * pObjLo, * pConst1 = NULL;
    int i;
    if ( Aig_ManCoNum(p) == 0 )
    {
        assert(false);
    }
    // check if constant is used
    Aig_ManForEachCo( p, pObj, i )
        if ( Aig_ObjIsConst1(Aig_ObjFanin0(pObj)) )
            pConst1 = Aig_ManConst1(p);
    // collect nodes in the DFS order
    vNodes = Aig_ManDfs( p, 1 );

    // assign IDs to objects
    char node_count_char[100];
    sprintf(node_count_char, "%d", 1);
    string node_count_string(node_count_char);
    string node_string = "c_";
    node_string += node_count_string;
    node_name_map.insert(make_pair(Aig_ManConst1(p), node_string));
	
    Aig_ManForEachCi( p, pObj, i )
	{
	string node_string;

	int Ci_id = Aig_ObjId(pObj);
	map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(Ci_id);
	assert(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end());
	string Ci_name = Ci_id_to_Ci_name_map_it->second;
	node_string = Ci_name;

	node_name_map.insert(make_pair(pObj, node_string));
	}

    int Counter = 1; 
    Aig_ManForEachCo( p, pObj, i )
	{
	char node_count_char[100];
	sprintf(node_count_char, "%d", Counter);
	string node_count_string(node_count_char);
	string node_string = "o_";
	node_string += node_count_string;
	node_name_map.insert(make_pair(pObj, node_string));
	Counter++;
	}    

    Counter = 1;   
    Vec_PtrForEachEntry( Aig_Obj_t *, vNodes, pObj, i )
	{
	char node_count_char[100];
	sprintf(node_count_char, "%d", Counter);
	string node_count_string(node_count_char);
	string node_string = "n_";
	node_string += node_count_string;
	node_name_map.insert(make_pair(pObj, node_string));
	Counter++;
	}
    
    // write the file
    pFile = fopen( pFileName, "w" );
    fprintf( pFile, "// Verilog file written by procedure writeCombinationalCircuitInVerilog\n//Skolem functions to be generated for i_ variables\n" );
//    fprintf( pFile, "// http://www.eecs.berkeley.edu/~alanmi/abc/\n" );
    if ( Aig_ManRegNum(p) )
        fprintf( pFile, "module %s ( clock", p->pName? p->pName: "test" );
    else
        fprintf( pFile, "module %s (", p->pName? p->pName: "test" );
    Aig_ManForEachPiSeq( p, pObj, i )
	{
	      string Ci_name_to_be_written = node_name_map[pObj];
	      if(Cis_in_Support.find(Ci_name_to_be_written) != Cis_in_Support.end())
	      {
  	      	fprintf( pFile, "%s %s", ((Aig_ManRegNum(p) || i)? ",":""), node_name_map[pObj].c_str() );
	      }
	}
    Aig_ManForEachPoSeq( p, pObj, i )
        fprintf( pFile, ", %s", node_name_map[pObj].c_str() );
    fprintf( pFile, " );\n" );

    // write PIs
    if ( Aig_ManRegNum(p) )
        fprintf( pFile, "input clock;\n" );
    Aig_ManForEachPiSeq( p, pObj, i )
	{
		string Ci_name_to_be_written = node_name_map[pObj];
	      	if(Cis_in_Support.find(Ci_name_to_be_written) != Cis_in_Support.end())
	      	{
        		fprintf( pFile, "input %s;\n", node_name_map[pObj].c_str() );
		}
	}
    // write POs
    Aig_ManForEachPoSeq( p, pObj, i )
        fprintf( pFile, "output %s;\n", node_name_map[pObj].c_str() );
    // write latches
    if ( Aig_ManRegNum(p) )
    {
    Aig_ManForEachLiLoSeq( p, pObjLi, pObjLo, i )
        fprintf( pFile, "reg %s;\n", node_name_map[pObjLo].c_str());
    Aig_ManForEachLiLoSeq( p, pObjLi, pObjLo, i )
        fprintf( pFile, "wire %s;\n", node_name_map[pObjLi].c_str() );
    }
    // write nodes
    Vec_PtrForEachEntry( Aig_Obj_t *, vNodes, pObj, i )
        fprintf( pFile, "wire %s;\n", node_name_map[pObj].c_str() );
    if ( pConst1 )
        fprintf( pFile, "wire %s;\n", node_name_map[pConst1].c_str());
    // write nodes
    if ( pConst1 )
        fprintf( pFile, "assign %s = 1\'b1;\n", node_name_map[pConst1].c_str() );
    Vec_PtrForEachEntry( Aig_Obj_t *, vNodes, pObj, i )
    {
        fprintf( pFile, "assign %s = %s%s & %s%s;\n", 
            node_name_map[pObj].c_str(),
            !Aig_ObjFaninC0(pObj) ? " " : "~", node_name_map[Aig_ObjFanin0(pObj)].c_str(), 
            !Aig_ObjFaninC1(pObj) ? " " : "~", node_name_map[Aig_ObjFanin1(pObj)].c_str()
            );
    }
    // write POs
    Aig_ManForEachPoSeq( p, pObj, i )
    {
        fprintf( pFile, "assign %s = %s%s;\n", 
            node_name_map[pObj].c_str(),
            !Aig_ObjFaninC0(pObj) ? " " : "~", node_name_map[Aig_ObjFanin0(pObj)].c_str() );
    }
    if ( Aig_ManRegNum(p) )
    {
        Aig_ManForEachLiLoSeq( p, pObjLi, pObjLo, i )
        {
            fprintf( pFile, "assign %s = %s%s;\n", 
                node_name_map[pObjLi].c_str(),
                !Aig_ObjFaninC0(pObjLi) ? " " : "~", node_name_map[Aig_ObjFanin0(pObjLi)].c_str() );
        }
    }

    // write initial state
    if ( Aig_ManRegNum(p) )
    {
        Aig_ManForEachLiLoSeq( p, pObjLi, pObjLo, i )
            fprintf( pFile, "always @ (posedge clock) begin %s <= %s; end\n", 
                 node_name_map[pObjLo].c_str(),
                 node_name_map[pObjLi].c_str() );
        Aig_ManForEachLiLoSeq( p, pObjLi, pObjLo, i )
            fprintf( pFile, "initial begin %s <= 1\'b0; end\n", 
                 node_name_map[pObjLo].c_str() );
    }

    fprintf( pFile, "endmodule\n\n" );
    fclose( pFile );
    Vec_PtrFree( vNodes );
}


void startGlobalTimer_In_Cluster(time_t external_cluster_global_time_out)
{
	cluster_global_time_out = external_cluster_global_time_out;

	time_t cluster_present_time;
	time(&cluster_present_time);
 	cluster_global_time_out_start = cluster_present_time;

 	cluster_global_time_out_enabled = true; 

 	cluster_global_timed_out = false; 

	if(avoid_cluster_global_time_out_at_top_node)
	{
		//assert(!Aig_IsComplement(input_arbitrary_boolean_formula));
		// Implemented for disjunction

		// presently timing-out ONLY at all lower nodes is implemented
		// only when the top-node is conjunction
	}	
}


bool checkGlobalTimeOut_In_Cluster()
{
	if(!cluster_global_time_out_enabled) // time_out mode is disabled
	{
		return false;
	}

	if(cluster_global_timed_out) // already timed out. No need to check
	{
		return true;
	}

	assert(cluster_global_time_out_start != 0);

	time_t cluster_present_time, cluster_duration;
	time(&cluster_present_time);
	cluster_duration = cluster_present_time - cluster_global_time_out_start;

	if(cluster_duration >= cluster_global_time_out)
	{
		return true;
	}
	else
	{
		return false;
	}
}


bool checkIfResultsAreTimedOut_In_Cluster()
{
	// just check for time-out
	if(cluster_global_time_out_enabled && cluster_global_timed_out)
	{
		return true;
	}
	else
	{
		return false;
	}
}


void disableTimeOut_In_Cluster()
{
	cluster_global_time_out_enabled = false;
}


void convertToRsynthQDimacs(Aig_Obj_t* CO_aig_manager, set<string> &ex_quantifiers, Aig_Man_t* aig_manager, string cnf_file, string output_variables_file)
{
	bool include_tsietin_variables = include_tsietin_variables_in_rsynth_qdimacs_generation;
	Vec_Int_t * vVarMap;

	#ifdef DEBUG_SKOLEM
	showSet(ex_quantifiers, "ex_quantifiers");
	#endif

	assert(CO_aig_manager != NULL);
	Aig_Obj_t* formula;
	formula = Aig_ObjChild0(CO_aig_manager);	
	assert(formula != NULL);

	FILE *pFile = fopen( cnf_file.c_str(), "w" );
	assert(pFile != NULL);
	fprintf( pFile, "c .nnodes 80\n" );
	
	Cnf_Dat_t * pCnf = Cnf_Derive( aig_manager, Aig_ManCoNum(aig_manager) );
	        
	map<string, int> variable_cnfid_map;
	list<int> tseitin_cnfids;
		
	Aig_Obj_t * pObj;
	int i;
	int nvars_in_file = 0;
	int number_of_tseitin_variables = 0;
	vVarMap = Vec_IntStart( pCnf->nVars );
        // create variable_cnfid_map
        Aig_ManForEachCi( aig_manager, pObj, i )
	{
		int Ci_id = pObj->Id;

		map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(Ci_id);
		assert(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end());
		string Ci_name = Ci_id_to_Ci_name_map_it->second;

		int Cnf_id = (pCnf->pVarNums[Ci_id])+1;
		
		#ifdef DEBUG_SKOLEM
		cout << "\nCi_id = " << Ci_id << "\tCi_name = " << Ci_name << "\tCnf_id = " << Cnf_id << endl;
		#endif

		variable_cnfid_map.insert(make_pair(Ci_name, Cnf_id));

		Vec_IntWriteEntry( vVarMap, pCnf->pVarNums[Ci_id], 1 );

		nvars_in_file++;		
	}

	if(include_tsietin_variables)
	{
	        // set nvars_in_file properly
	        nvars_in_file = 0;
		//collect the temporary variables in tseitin_cnfids
	        int i, Entry;
	        Vec_IntForEachEntry( vVarMap, Entry, i )
	       {
		 	if ( Entry == 1)
			{
		          // do nothing
		          nvars_in_file++;
			}
			else if(i != 0)//To account for the fact that cnf-id 1 is not there
			{
		        	tseitin_cnfids.push_back(i);

				#ifdef DEBUG_SKOLEM
				cout << endl << i << " inserted into tseitin_cnfids";
				#endif	
			
				nvars_in_file++;
				number_of_tseitin_variables++;
			}
	       }//for each vector entry				
	}//if(include_tsietin_variables)

	fprintf( pFile, "c .nvars %d\n", nvars_in_file);

	// Let's fix the variables to be eliminated
	set<string> Support_formula; // All variables in support
	computeSupport(formula, Support_formula, aig_manager);
	int nsuppvars_in_file;

        if(include_tsietin_variables)
	  {
	    nsuppvars_in_file = Support_formula.size() + number_of_tseitin_variables;
	  }
	else
	  {
	    nsuppvars_in_file = Support_formula.size();
	  }

	fprintf( pFile, "c .nsuppvars %d\n", nsuppvars_in_file);
	
	set<string> ex_quantifiers_in_support; // All ex_quantifiers in support to be eliminated
	set_intersection(ex_quantifiers.begin(), ex_quantifiers.end(), Support_formula.begin(), Support_formula.end(),inserter(ex_quantifiers_in_support, ex_quantifiers_in_support.begin())); 
	
	// Read the order of variable elimination
	// Decide the ordering
	list<int> output_variable_ids;
	list<string> order_of_variables;
	list<int> tseitin_variable_ids;

	if(order_of_elimination_of_variables == 2)
	{
		// We should read the order from the given file
		list<string> OrderOfVariableEliminationFromFile;
		obtainOrderOfVariableEliminationFromFile(OrderOfVariableEliminationFromFile);	

	
		for(set<string>::iterator it = Support_formula.begin(); it != Support_formula.end(); it++)
		{
			if(ex_quantifiers_in_support.find(*it) == ex_quantifiers_in_support.end())//input variable 
			{
				order_of_variables.push_back(*it);
			}
		}
		for(list<string>::iterator it = OrderOfVariableEliminationFromFile.begin(); it != OrderOfVariableEliminationFromFile.end(); it++)
		{
			if(ex_quantifiers_in_support.find(*it) != ex_quantifiers_in_support.end())//output variable
			{
				order_of_variables.push_back(*it);
			}
		}
	}
	else if(order_of_elimination_of_variables == 1)
	{
		map<string, int> number_of_occurrences_of_variables;
		computeNumberOfNodesInWhichEachInputOccurs(formula, aig_manager, number_of_occurrences_of_variables, false);

		map<int, set<string> > number_of_occurrences_to_variables_map;
		for(map<string, int>::iterator number_of_occurrences_of_variables_it = number_of_occurrences_of_variables.begin(); number_of_occurrences_of_variables_it != number_of_occurrences_of_variables.end(); number_of_occurrences_of_variables_it++)
		{
			string variable_occurring = number_of_occurrences_of_variables_it->first;
			int number_of_occurrences = number_of_occurrences_of_variables_it->second;
			
			map<int, set<string> >::iterator number_of_occurrences_to_variables_map_it =  number_of_occurrences_to_variables_map.find(number_of_occurrences);
			if(number_of_occurrences_to_variables_map_it == number_of_occurrences_to_variables_map.end()) 	
			{
				set<string> variables_occurring;
				variables_occurring.insert(variable_occurring);

				number_of_occurrences_to_variables_map.insert(make_pair(number_of_occurrences, variables_occurring));			
			}
			else
			{
				(number_of_occurrences_to_variables_map_it->second).insert(variable_occurring);
			}
		}

		for(map<int, set<string> >::iterator number_of_occurrences_to_variables_map_it = number_of_occurrences_to_variables_map.begin(); number_of_occurrences_to_variables_map_it != number_of_occurrences_to_variables_map.end(); number_of_occurrences_to_variables_map_it++)
		{
			int number_of_occurrences = number_of_occurrences_to_variables_map_it->first;
			set<string> variables_occurring = number_of_occurrences_to_variables_map_it->second;

			for(set<string>::iterator variables_occurring_it = variables_occurring.begin(); variables_occurring_it != variables_occurring.end(); variables_occurring_it++)
			{
				order_of_variables.push_back(*variables_occurring_it);	
			}
		}
	}
	else
	{
		assert(false);
	}
		
	
	#ifdef DEBUG_SKOLEM
	cout << "\norder_of_variables\n";
	showList(order_of_variables);
	#endif

	fprintf( pFile, "c .ids  ");
	int variable_id = 0;
	for(list<string>::iterator it = order_of_variables.begin(); it != order_of_variables.end(); it++)
	{
		fprintf( pFile, "%d ", variable_id);
		
		if(ex_quantifiers_in_support.find(*it) != ex_quantifiers_in_support.end())//output variable
		{
			output_variable_ids.push_back(variable_id);
		}

		#ifdef DEBUG_SKOLEM
		cout << *it << "\t" << variable_id << endl;
		#endif

		variable_id++;		
	}

	if(include_tsietin_variables)
	{
		for(int i = 0; i < number_of_tseitin_variables; i++)
		{
			fprintf( pFile, "%d ", variable_id);
			tseitin_variable_ids.push_back(variable_id);
			variable_id++;	
		}
	}

	fprintf( pFile, "\n");

	#ifdef DEBUG_SKOLEM
	cout << "\nTotal number of variables = " << order_of_variables.size();
	cout << "\nNumber of output variables = " << output_variable_ids.size();
	#endif

	fprintf( pFile, "c .cnfids  ");
	for(list<string>::iterator it = order_of_variables.begin(); it != order_of_variables.end(); it++)
	{
		string variable = *it;
		map<string, int>::iterator variable_cnfid_map_it = variable_cnfid_map.find(variable);
		assert(variable_cnfid_map_it != variable_cnfid_map.end());	
		fprintf( pFile, "%d ", variable_cnfid_map_it->second);
	}

	if(include_tsietin_variables)
	{
		for(list<int>::iterator tseitin_cnfids_it = tseitin_cnfids.begin(); tseitin_cnfids_it != tseitin_cnfids.end(); tseitin_cnfids_it++)
		{
			fprintf( pFile, "%d ", (*tseitin_cnfids_it)+1);
		}	
	}

	fprintf( pFile, "\n");

	fprintf( pFile, "c .nroots 1\n");

	int rootLit = toLitCond( pCnf->pVarNums[CO_aig_manager->Id], 0 );
	int rootId = (rootLit & 1)? -(rootLit >> 1)-1 : (rootLit >> 1)+1;

	fprintf( pFile, "c .rootids %d\n", rootId);

        // write CNF in to file
	int * pLit, * pStop, VarId;
   		
	fprintf( pFile, "p cnf %d %d\n", pCnf->nVars, pCnf->nClauses+1 );
	
	for ( i = 0; i < pCnf->nClauses; i++ )
	{
		for ( pLit = pCnf->pClauses[i], pStop = pCnf->pClauses[i+1]; pLit < pStop; pLit++ )
		    fprintf( pFile, "%d ", (*pLit & 1)? -(*pLit >> 1)-1 : (*pLit >> 1)+1);
		fprintf( pFile, "0\n" );
	}
	
	fprintf( pFile, "%d 0\n", rootId);
	fprintf( pFile, "\n" );
	fclose( pFile );
	cout << "\nCNF formula written into file " << cnf_file << endl;

	FILE *varFile = fopen( output_variables_file.c_str(), "w" );
	assert(varFile != NULL);
	for(list<int>::iterator it = output_variable_ids.begin(); it != output_variable_ids.end(); it++)
	{
		fprintf( varFile, "%d\n", *it);
	}
	if(include_tsietin_variables)
	{
		for(list<int>::iterator it = tseitin_variable_ids.begin(); it != tseitin_variable_ids.end(); it++)
		{
			fprintf( varFile, "%d\n", *it);
		}	
	}
	fclose(varFile);
	cout << "Ouput variables written into file " << output_variables_file << endl;	
        
	Cnf_DataFree( pCnf );
        

}


int stringToInteger(string s)
{
    //returns 0 if the string is empty
    //Put a check to see whether input string is valid, i.e. does not contain alphabet chars
    for (int i = 0; i < s.size(); i++)
    {
        if (isalpha(s[i]))
        {
            //cerr<<"Invalid string in stringToInteger:"<<s<<endl;
            return -1;
        }
    }
    return atoi(s.c_str());
}




void Aig_Concurrent_Compose_rec( Aig_Man_t * p, Aig_Obj_t * pObj, vector<Aig_Obj_t*> &pFuncVector, vector<Aig_Obj_t*> &pVarVector)
{
    assert( pFuncVector.size() == pVarVector.size() );
    assert( !Aig_IsComplement(pObj) );

    if ( Aig_ObjIsMarkA(pObj) )
        return;
    if ( Aig_ObjIsConst1(pObj))
    {
        pObj->pData = pObj;
        return;
    }
    if ( Aig_ObjIsCi(pObj) )
    {
	for(int i = 0; i < pVarVector.size(); i++)
	{
		Aig_Obj_t* pVar = pVarVector[i];
		Aig_Obj_t* pFunc = pFuncVector[i];

		if( pObj == pVar )
		{
			pObj->pData = pFunc;
			return;
		}
	}
				
        pObj->pData = pObj;
        return;
    }

    Aig_Concurrent_Compose_rec( p, Aig_ObjFanin0(pObj), pFuncVector, pVarVector ); 
    Aig_Concurrent_Compose_rec( p, Aig_ObjFanin1(pObj), pFuncVector, pVarVector );

    pObj->pData = Aig_And( p, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    assert( !Aig_ObjIsMarkA(pObj) ); // loop detection
    Aig_ObjSetMarkA( pObj );
}




Aig_Obj_t * Aig_Concurrent_Compose( Aig_Man_t * p, Aig_Obj_t * pRoot, vector<Aig_Obj_t*> &pFuncVector, vector<int> &iVarVector )
{
    vector<Aig_Obj_t*> pVarVector;
    for(int i = 0; i < iVarVector.size(); i++)
    {
	int iVar = iVarVector[i];
	if ( iVar >= Aig_ManCiNum(p) )
    	{
        	printf( "Aig_Compose(): The PI variable %d is not defined.\n", iVar );
        	return NULL;
    	}
	Aig_Obj_t* pVar = Aig_ManCi(p, iVar);
	pVarVector.push_back(pVar);
    }

    // recursively perform composition
    Aig_Concurrent_Compose_rec( p, Aig_Regular(pRoot), pFuncVector, pVarVector );
    // clear the markings
    Aig_ConeUnmark_rec( Aig_Regular(pRoot) );
    return Aig_NotCond( (Aig_Obj_t *)Aig_Regular(pRoot)->pData, Aig_IsComplement(pRoot) );
}



Aig_Obj_t* ReplaceLeavesByExpressionsConcurrently(Aig_Man_t* aig_manager, Aig_Obj_t* OriginalFormula, map<string, Aig_Obj_t*> &replacement_map)
{
	// sanity checks
	assert(OriginalFormula != NULL);

	vector<Aig_Obj_t*> pFuncVector;
	vector<int> iVarVector;

	// First let's find the ci_index of each var_to_replace
	for(map<string, Aig_Obj_t*>::iterator replacement_map_it = replacement_map.begin(); replacement_map_it != replacement_map.end(); replacement_map_it++)
	{
		string var_to_replace = replacement_map_it->first;
		map<string, int>::iterator Ci_name_to_Ci_number_map_it = Ci_name_to_Ci_number_map.find(var_to_replace);

		if(Ci_name_to_Ci_number_map_it == Ci_name_to_Ci_number_map.end())
		{
			cout <<"\nNo entry for " << var_to_replace << " in Ci_name_to_Ci_number_map\n";
			assert(Ci_name_to_Ci_number_map_it != Ci_name_to_Ci_number_map.end());
		}

		int aig_variable_index = Ci_name_to_Ci_number_map_it->second;

		iVarVector.push_back(aig_variable_index);
		pFuncVector.push_back(replacement_map_it->second);
	}
	
	// Let's compose
	Aig_Obj_t* ComposedFormula = Aig_Concurrent_Compose( aig_manager, OriginalFormula, pFuncVector, iVarVector );
	assert(ComposedFormula != NULL);
	
	return ComposedFormula;
}



Abc_Ntk_t* obtainNetworkFromFragmentOfAIGWithIdNamesWithMultipleEntriesInCOListAllowed(Aig_Man_t * pMan, map<int, string> &idName, int number_of_interested_cos)
{
    Vec_Ptr_t * vNodes;
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pObjNew;
    Aig_Obj_t * pObj, * pObjLo, * pObjLi;
    int i;
    assert(pMan->nAsserts == 0);
    // perform strashing
    pNtkNew = Abc_NtkAlloc(ABC_NTK_STRASH, ABC_FUNC_AIG, 1);
    pNtkNew->nConstrs = pMan->nConstrs;
    // duplicate the name and the spec
    pNtkNew->pName = Extra_UtilStrsav(pMan->pName);
    pNtkNew->pSpec = Extra_UtilStrsav(pMan->pSpec);
    Aig_ManConst1(pMan)->pData = Abc_AigConst1(pNtkNew);

    set<int> Interested_COs;

    int total_index = 0;
    Aig_ManForEachCo(pMan, pObj, i)
    {
	#ifdef DEBUG_SKOLEM 
	cout << endl << "i = " << i << "\tpObj->Id = " << pObj->Id;
	#endif
	total_index++;
    }

    int index_of_first_interested_co = total_index - number_of_interested_cos;

    #ifdef DEBUG_SKOLEM 
    cout << endl << "total_index = " << total_index;
    cout << "\tindex_of_first_interested_co = " << index_of_first_interested_co << endl;
    #endif

    // create PIs
    Aig_ManForEachPiSeq(pMan, pObj, i)
    {
	if(idName.find(pObj->Id) != idName.end()) // interested PI
	{
		pObjNew = Abc_NtkCreatePi(pNtkNew);

		#ifdef DEBUG_SKOLEM 
		cout << endl << "Interested PI: ";
		cout << "pObj->Id = " << pObj->Id;
		cout << "\tidName[pObj->Id] = " << idName[pObj->Id];
		#endif

		Abc_ObjAssignName(pObjNew, (char*) idName[pObj->Id].c_str(), NULL);
		pObj->pData = pObjNew;
	}
    }
 
    // create POs    
    Aig_ManForEachCo(pMan, pObj, i)
    {
	#ifdef DEBUG_SKOLEM 
	cout << endl << "i = " << i << "\tpObj->Id = " << pObj->Id;
	#endif

	if(i < index_of_first_interested_co)
	{
		continue;
	}
        else if(idName.find(pObj->Id) != idName.end() && Interested_COs.find(pObj->Id) == Interested_COs.end()) // interested PO
	{
		pObjNew = Abc_NtkCreatePo(pNtkNew);

		#ifdef DEBUG_SKOLEM 
		cout << endl << "Interested CO: ";
		cout << "pObj->Id = " << pObj->Id;
		cout << "\tidName[pObj->Id] = " << idName[pObj->Id];
		cout << "\tpObjNew->Id = " << pObjNew->Id;
		#endif

		Abc_ObjAssignName(pObjNew, (char*) idName[pObj->Id].c_str(), NULL);
		pObj->pData = pObjNew;

		Interested_COs.insert(pObj->Id);

		#ifdef DEBUG_SKOLEM 
		showSet(Interested_COs, "Interested_COs");
		#endif
	}
	else
	{
		cout << "\nUnallowed CO encountered in obtainNetworkFromFragmentOfAIGWithIdNamesWithMultipleEntriesInCOListAllowed!\n";
		assert(false);
	}
    }

    // create as many latches as there are registers in the manager
    Aig_ManForEachLiLoSeq(pMan, pObjLi, pObjLo, i)
    {
        pObjNew = Abc_NtkCreateLatch(pNtkNew);
        pObjLi->pData = Abc_NtkCreateBi(pNtkNew);
        pObjLo->pData = Abc_NtkCreateBo(pNtkNew);
        Abc_ObjAddFanin(pObjNew, (Abc_Obj_t *) pObjLi->pData);
        Abc_ObjAddFanin((Abc_Obj_t *) pObjLo->pData, pObjNew);
        Abc_LatchSetInit0(pObjNew);
    }

    // rebuild the AIG
    vNodes = Aig_ManDfs_Fragment(pMan, 1, Interested_COs);

    Vec_PtrForEachEntry(Aig_Obj_t *, vNodes, pObj, i)
    if (Aig_ObjIsBuf(pObj))
        pObj->pData = (Abc_Obj_t *) Aig_ObjChild0Copy(pObj);
    else
        pObj->pData = Abc_AigAnd((Abc_Aig_t *) pNtkNew->pManFunc, (Abc_Obj_t *) Aig_ObjChild0Copy(pObj), (Abc_Obj_t *) Aig_ObjChild1Copy(pObj));
    Vec_PtrFree(vNodes);

    
    // connect the PO nodes
    #ifdef DEBUG_SKOLEM 
    cout << endl << "connecting the PO nodes " << endl;
    #endif

    int po_index = 0;
    set<int> Interested_COs_Considered;

    Aig_ManForEachCo(pMan, pObj, i)
    {
	#ifdef DEBUG_SKOLEM 
	cout << endl << "i = " << i << endl;
	#endif

	if(i < index_of_first_interested_co)
	{
		continue;
	}
	else if(idName.find(pObj->Id) != idName.end() && Interested_COs_Considered.find(pObj->Id) == Interested_COs_Considered.end()) // interested CO
	{
		#ifdef DEBUG_SKOLEM 
		cout << endl << "pObj->Id = " << pObj->Id;
		cout << "\tidName[pObj->Id] = " << idName[pObj->Id];
		#endif

        	pObjNew = (Abc_Obj_t *) Aig_ObjChild0Copy(pObj);
        	Abc_ObjAddFanin(Abc_NtkPo(pNtkNew, po_index), pObjNew);	
		po_index++;	

		#ifdef DEBUG_SKOLEM 
		cout << endl << "po added" << endl;
		#endif

		Interested_COs_Considered.insert(pObj->Id);
	}
	else
	{
		cout << "\nUnallowed CO encountered in obtainNetworkFromFragmentOfAIGWithIdNamesWithMultipleEntriesInCOListAllowed!\n";
		assert(false);
	}
    }

    // check the resulting AIG
    if (!Abc_NtkCheck(pNtkNew))
        cout << "obtainNetworkFromFragmentOfAIGWithIdNamesWithMultipleEntriesInCOListAllowed: Network check has failed.\n";
    return pNtkNew;
}



Aig_Obj_t* simplifyAIGUsingFraiging(Aig_Man_t* source_manager, Aig_Obj_t* source_aig)
{
	Aig_Obj_t* source_CO = Aig_ObjCreateCo( source_manager, source_aig ); 
	assert(source_CO != NULL);

	Aig_Man_t* coi_manager;
	coi_manager = simplifyUsingConeOfInfluence_DirectlyOnCO_WithLesserAssertions( source_manager, source_CO, 0 );
	assert(coi_manager != NULL);

	Aig_Man_t* fraig_manager;
	fraig_manager = simplifyUsingFraiging( coi_manager );
	assert(fraig_manager != NULL);

	int CiNum_source_manager = Aig_ManCiNum( source_manager );
	
	assert(Aig_ManCoNum(fraig_manager) == 1);
	Aig_Obj_t* CO_fraig_manager;
	CO_fraig_manager = Aig_ManCo(fraig_manager, 0);
	assert(CO_fraig_manager != NULL);	

	Aig_Obj_t* fraiged_aig;
	fraiged_aig = Aig_Transfer(fraig_manager, source_manager, Aig_ObjChild0(CO_fraig_manager), CiNum_source_manager );
	assert(fraiged_aig != NULL);

	return fraiged_aig;
}


Aig_Man_t * simplifyUsingConeOfInfluence_DirectlyOnCO_WithLesserAssertions( Aig_Man_t * p, Aig_Obj_t * CO_selected, int fAddRegs )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i;
    //assert( Aig_ManRegNum(p) > 0 );
    //assert( iPoNum < Aig_ManCoNum(p)-Aig_ManRegNum(p) );
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    // create the PIs
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachCi( p, pObj, i )
        pObj->pData = Aig_ObjCreateCi( pNew );
    // set registers
    pNew->nRegs    = fAddRegs? p->nRegs : 0;
    pNew->nTruePis = fAddRegs? p->nTruePis : p->nTruePis + p->nRegs;
    pNew->nTruePos = 1;
    // duplicate internal nodes
    Aig_ManForEachNode( p, pObj, i )
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    // create the PO
    pObj = CO_selected;
    Aig_ObjCreateCo( pNew, Aig_ObjChild0Copy(pObj) );
    // create register inputs with MUXes
    if ( fAddRegs )
    {
        Aig_ManForEachLiSeq( p, pObj, i )
            Aig_ObjCreateCo( pNew, Aig_ObjChild0Copy(pObj) );
    }
    Aig_ManCleanup( pNew );
    return pNew;
}




bool getIncrementAsCNF_AddToSolver_and_CallSolver_With_Assumptions(Aig_Man_t* aig_manager, Aig_Obj_t* increment, map<string, int> &Model, unsigned long long int &cnf_time, int &formula_size, unsigned long long int &simplification_time, vector<Aig_Obj_t*> &positive_assumptions_in_exactness_check, vector<Aig_Obj_t*>  &negative_assumptions_in_exactness_check, sat_solver* pSat_for_incremental_solving, t_HashTable<int, int> & IncrementalLabelTable, int &IncrementalLabelCount, map<string, int> &Ci_name_to_Ci_label_map, map<int, string> &Ci_label_to_Ci_name_map)
{
	// Add the clauses from increment (unless it is NULL) to the solver pSat_for_incremental_solving
	simplification_time = 0;
	times_in_aig_simplification_in_cegar.push_back(simplification_time);
	
	assert(increment != NULL);

	// increment is an internal node
	// connect increment to a CO, increment_CO
	// to avoid unauthorized cleanup

	Aig_Obj_t* increment_CO = Aig_ObjCreateCo( aig_manager, increment );
	assert(increment_CO != NULL);
	intermediate_cos_created.insert(increment_CO);
	
	formula_size = computeSize(increment, aig_manager);
	sizes_of_exactness_formulae_in_cegar.push_back(formula_size);

	//cout << "\nformula_size = " << formula_size << endl;

	// Setting number of variables and showing details

	#ifdef DEBUG_SKOLEM
		cout << "\nSetting nvars to " << formula_size + IncrementalLabelCount << endl;
	#endif

	sat_solver_setnvars(pSat_for_incremental_solving, formula_size + IncrementalLabelCount );// SAT-solver specific code

	#ifdef DEBUG_SKOLEM
		showSolverStatus(pSat_for_incremental_solving);// SAT-solver specific code
		cout << "\nAdding clauses from increment to sat-solver\n";
	#endif
	
	struct timeval cnf_start_ms, cnf_finish_ms;
	gettimeofday (&cnf_start_ms, NULL);

	
	//cout << "\nAdding clauses from increment to sat-solver\n";

	getIncrementAsCNF_and_AddToSolver(aig_manager, increment, pSat_for_incremental_solving, IncrementalLabelTable, IncrementalLabelCount, Ci_name_to_Ci_label_map, Ci_label_to_Ci_name_map);

	//cout << "\nClauses added to sat-solver\n";

	#ifdef DEBUG_SKOLEM
		cout << "\nClauses added to sat-solver\n";
		showSolverStatus(pSat_for_incremental_solving); // SAT-solver specific code
	#endif
		
	gettimeofday (&cnf_finish_ms, NULL);
	cnf_time = cnf_finish_ms.tv_sec * 1000 + cnf_finish_ms.tv_usec / 1000;
	cnf_time -= cnf_start_ms.tv_sec * 1000 + cnf_start_ms.tv_usec / 1000;
	times_in_cnf_generation_in_cegar.push_back(cnf_time);

	// Check if the present set of clauses gives satisfiable under
	// positive_assumptions_in_exactness_check and negative_assumptions_in_exactness_check
	
	
	unsigned long long int solver_ms;
	struct timeval solver_start_ms, solver_finish_ms;
	gettimeofday (&solver_start_ms, NULL); 

	//cout << "\nCalling the sat-solver\n";

	bool return_value;
	
	int trivially_unsat = 1;

	if(apply_solver_simplify_in_incremental_sat)
	{
		//cout << "\nApplying simplification of CNF\n";
		trivially_unsat = sat_solver_simplify(pSat_for_incremental_solving); // SAT-solver specific code
	}

	if(trivially_unsat == 0)
	{
		//cout << "\nFormula is trivially unsat\n";
		Model.clear();
		return_value = false;
	}
	else
	{
		#ifdef DEBUG_SKOLEM
			cout << "\nCreating assumptions\n";
		#endif
		// Create assumptions
		Vec_Int_t *    vAssumptions;
		vAssumptions = Vec_IntAlloc( positive_assumptions_in_exactness_check.size() + negative_assumptions_in_exactness_check.size() );

		// for positive assumptions
		#ifdef DEBUG_SKOLEM
			cout << "\nPositive assumptions\n";
		#endif
		for(int assumption_it = 0; assumption_it < positive_assumptions_in_exactness_check.size(); assumption_it++)
		{
			Aig_Obj_t* assumption_obj = positive_assumptions_in_exactness_check[assumption_it];
			int assumption_obj_id = Aig_ObjId(assumption_obj); 

			map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(assumption_obj_id);
			assert(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end());
			string assumption_name = Ci_id_to_Ci_name_map_it->second;			

			map<string, int>::iterator Ci_name_to_Ci_label_map_it = Ci_name_to_Ci_label_map.find(assumption_name);
			if(Ci_name_to_Ci_label_map_it == Ci_name_to_Ci_label_map.end()) // assumption_name is not 
			// present in the clauses with pSat_for_incremental_solving (may be due to simplifications)
			{
				// do nothing
			}
			else
			{
				int assumption_label = Ci_name_to_Ci_label_map_it->second;
				int assumption_lit = toLitCond( assumption_label, 0 );
				Vec_IntPush( vAssumptions, assumption_lit );

				#ifdef DEBUG_SKOLEM
					cout << "\nname = " << assumption_name << "\tlabel = " << assumption_label << "\tlit = " << assumption_lit;
				#endif
			}			
		}
		
		// for negative assumptions
		#ifdef DEBUG_SKOLEM
			cout << "\nNegative assumptions\n";
		#endif
		for(int assumption_it = 0; assumption_it < negative_assumptions_in_exactness_check.size(); assumption_it++)
		{
			Aig_Obj_t* assumption_obj = negative_assumptions_in_exactness_check[assumption_it];
			int assumption_obj_id = Aig_ObjId(assumption_obj); 

			map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(assumption_obj_id);
			assert(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end());
			string assumption_name = Ci_id_to_Ci_name_map_it->second;			

			map<string, int>::iterator Ci_name_to_Ci_label_map_it = Ci_name_to_Ci_label_map.find(assumption_name);
			if(Ci_name_to_Ci_label_map_it == Ci_name_to_Ci_label_map.end()) // assumption_name is not 
			// present in the clauses with pSat_for_incremental_solving (may be due to simplifications)
			{
				// do nothing
			}
			else
			{
				int assumption_label = Ci_name_to_Ci_label_map_it->second;
				int assumption_lit = toLitCond( assumption_label, 1 );
				Vec_IntPush( vAssumptions, assumption_lit );

				#ifdef DEBUG_SKOLEM
					cout << "\nname = " << assumption_name << "\tlabel = " << assumption_label << "\tlit = " << assumption_lit;
				#endif
			}			
		}

		
		// Note that vAssumptions now has list of literals. Each literal 
		// represented by an integer. 
	
		if(perform_cegar_on_arbitrary_boolean_formulas && cluster_global_time_out_enabled)
		// This is a case where we are finding Skolem functions for arbitrary Boolean formulas and 
		// we would like to have a graceful time-out. This is the only case where we set time-out
		// with sat_solver_solve
		{
			time_t present_machine_time;
			time(&present_machine_time);

			time_t elapsed_machine_time;
			elapsed_machine_time = present_machine_time - cluster_global_time_out_start;
		
			time_t remaining_machine_time;
			remaining_machine_time = cluster_global_time_out - elapsed_machine_time;

			abctime sat_solver_timeout_time = (((abctime)remaining_machine_time) * CLOCKS_PER_SEC) + Abc_Clock();	
			sat_solver_set_runtime_limit(pSat_for_incremental_solving, sat_solver_timeout_time); // SAT-solver specific code

			#ifdef DEBUG_SKOLEM
			cout << "\nsat_solver_set_runtime_limit called with abctime = " << sat_solver_timeout_time <<" ,i.e., remaining_machine_time = " << remaining_machine_time << endl;
			#endif
		}
		
		#ifdef DEBUG_SKOLEM
			pSat_for_incremental_solving->verbosity = 2; // SAT-solver specific code
		#endif

		// call sat_solver_solve under assumptions

		//cout << "\nsat_solver_solve called\n";

		#ifdef DEBUG_SKOLEM
			cout << "\ncall sat_solver_solve under assumptions\n";
			showSolverStatus(pSat_for_incremental_solving); // SAT-solver specific code
		#endif

		int status = sat_solver_solve( pSat_for_incremental_solving, Vec_IntArray(vAssumptions), Vec_IntArray(vAssumptions) + Vec_IntSize(vAssumptions), (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 ); // SAT-solver specific code to solve the CNF under these assumptions

		#ifdef DEBUG_SKOLEM
			cout << "\nsat_solver_solve called under assumptions\n";
			showSolverStatus(pSat_for_incremental_solving); // SAT-solver specific code
		#endif

		if ( status == l_False )
		{
			//cout << "\nFormula is unsat\n";
			Model.clear();
			return_value = false;
		}
		else if ( status == l_True )
		{
			//cout << "\nFormula is sat; get the model\n";  

			// get the model

			/* Get the array of labels of CIs ordered as per Ci_name_to_Ci_label_map */
			Vec_Int_t * vCiIds = collectPiSatNums(Ci_name_to_Ci_label_map);

			/* Get the model from sat-solver ordered as per Ci_name_to_Ci_label_map */
			int * pModel = Sat_SolverGetModel( pSat_for_incremental_solving, vCiIds->pArray, vCiIds->nSize ); // SAT-solver specific code to extract the model
			
			int model_location = 0;
			for(map<string, int>::iterator Ci_name_to_Ci_label_map_it = Ci_name_to_Ci_label_map.begin(); Ci_name_to_Ci_label_map_it != Ci_name_to_Ci_label_map.end(); Ci_name_to_Ci_label_map_it++)
			{
				string Ci_name = Ci_name_to_Ci_label_map_it->first;
				int Ci_value = pModel[model_location];

				#ifdef DEBUG_SKOLEM
					cout << "\nCi name = " << Ci_name << "\tCi value = " << Ci_value;
				#endif

				Model.insert(make_pair(Ci_name, Ci_value));
				model_location++;
			}

			return_value = true; 
		
			free(pModel);	//Added by SS
			Vec_IntFree(vCiIds); //Added by SS          
		}
		else
		{
			assert( status == l_Undef );

			if(perform_cegar_on_arbitrary_boolean_formulas && cluster_global_time_out_enabled)
			{
				#ifdef DEBUG_SKOLEM
				cout << "\nWarning!!Time-out inside SAT solver\n";
				#endif
				cluster_global_timed_out = true; // cluster_global_timed_out flag set
				return_value = true; // it can be anything!! will be caught by the caller!
			}
			else
			{
				cout << "\nUnknown value " << status <<" returned from solver inside helper.cc::isExactnessCheckSatisfiable\n";
				assert(false);
			}
		}
		
		Vec_IntFree(vAssumptions); //Added by SS
	
	}// else of if(trivially_unsat == 0) ends here

	//cout << "\nSat-solver called\n";

	gettimeofday (&solver_finish_ms, NULL);
	solver_ms = solver_finish_ms.tv_sec * 1000 + solver_finish_ms.tv_usec / 1000;
	solver_ms -= solver_start_ms.tv_sec * 1000 + solver_start_ms.tv_usec / 1000;
	//cout << "\ninternal solver finished in " << solver_ms << " milliseconds\n";
	times_in_sat_solving_in_cegar.push_back(solver_ms);

	total_time_in_sat_solving_in_cegar = total_time_in_sat_solving_in_cegar + solver_ms;

	if(return_value)
	{
		total_time_in_true_sat_solving_in_cegar = total_time_in_true_sat_solving_in_cegar + solver_ms;
	}
	else
	{
		total_time_in_false_sat_solving_in_cegar = total_time_in_false_sat_solving_in_cegar + solver_ms;
	}

	return return_value;	
}




void getIncrementAsCNF_and_AddToSolver(Aig_Man_t* aig_manager, Aig_Obj_t* increment, sat_solver* pSat_for_incremental_solving, t_HashTable<int, int> & IncrementalLabelTable, int &IncrementalLabelCount, map<string, int> &Ci_name_to_Ci_label_map, map<int, string> &Ci_label_to_Ci_name_map)
{
	// Add the clauses from increment to the solver pSat_for_incremental_solving
	assert(increment != NULL);

	#ifdef DEBUG_SKOLEM
		cout << "\ngetIncrementAsCNF_and_AddToSolver_Internal called\n";
	#endif

	int increment_label = getIncrementAsCNF_and_AddToSolver_Internal(aig_manager, increment, pSat_for_incremental_solving, IncrementalLabelTable, IncrementalLabelCount, Ci_name_to_Ci_label_map, Ci_label_to_Ci_name_map);

	#ifdef DEBUG_SKOLEM
		cout << "\nroot encountered\n";
	#endif

	#ifdef DEBUG_SKOLEM
		cout << "\nAdding clauses for (" << Aig_IsComplement(increment) << " " << increment_label << ")" << endl;
	#endif

	// assert that the root node is true/false; for this add increment_label with approporiate sign

	lit increment_clause[1];
    	int solver_status;
    	assert( increment_label >= 0 );

    	increment_clause[0] = toLitCond( increment_label, Aig_IsComplement(increment) );

	#ifdef DEBUG_SKOLEM
		cout << increment_clause[0] << " 0\n";
	#endif

    	solver_status = sat_solver_addclause( pSat_for_incremental_solving, increment_clause, increment_clause + 1 );// SAT-solver specific code to add a new clause to SAT solver's data-structure
    	assert(solver_status);		
}


int getIncrementAsCNF_and_AddToSolver_Internal(Aig_Man_t* aig_manager, Aig_Obj_t* formula, sat_solver* pSat_for_incremental_solving, t_HashTable<int, int> & IncrementalLabelTable, int &IncrementalLabelCount, map<string, int> &Ci_name_to_Ci_label_map, map<int, string> &Ci_label_to_Ci_name_map)
{
	formula = Aig_Regular(formula);
	int key = Aig_ObjId(formula);

	#ifdef DEBUG_SKOLEM
		//cout << "\nformula = " << formula << "\tkey = " << key << endl;
	#endif

	t_HashTable<int, int>::iterator LabelTable_it = IncrementalLabelTable.find(key);
	if (LabelTable_it != IncrementalLabelTable.end()) // label exists already, i.e. traversed already
	{
		#ifdef DEBUG_SKOLEM
			//cout << "\nExists in hashtable\n";
		#endif

		return LabelTable_it.getValue();;
	}
	else
	{
		int node_label = IncrementalLabelCount;
		IncrementalLabelTable[key] = IncrementalLabelCount;
		IncrementalLabelCount++;

		if(formula->Type == AIG_OBJ_AND)// child_1 \wedge child_2 encountered
		{
			#ifdef DEBUG_SKOLEM
				//cout << "\nAIG_OBJ_AND encountered\n";
			#endif

			int child_1_label = getIncrementAsCNF_and_AddToSolver_Internal(aig_manager, Aig_ObjChild0(formula), pSat_for_incremental_solving, IncrementalLabelTable, IncrementalLabelCount, Ci_name_to_Ci_label_map, Ci_label_to_Ci_name_map);
			int child_2_label = getIncrementAsCNF_and_AddToSolver_Internal(aig_manager, Aig_ObjChild1(formula), pSat_for_incremental_solving, IncrementalLabelTable, IncrementalLabelCount, Ci_name_to_Ci_label_map, Ci_label_to_Ci_name_map);

			#ifdef DEBUG_SKOLEM
				cout << "\nAdding clauses for (" << node_label << ", " << Aig_ObjFaninC0(formula) << " " << child_1_label << ", " << Aig_ObjFaninC1(formula) << " " << child_2_label << ")" << endl;
			#endif

			lit increment_clause[3];
			int solver_status;

			increment_clause[0] = toLitCond( node_label, 1 );
			increment_clause[1] = toLitCond( child_1_label,  Aig_ObjFaninC0(formula));

			#ifdef DEBUG_SKOLEM
				cout << increment_clause[0] << " " << increment_clause[1] << " 0\n"; 
			#endif
			
			solver_status = sat_solver_addclause( pSat_for_incremental_solving, increment_clause,  increment_clause+ 2 );// SAT-solver specific code to add a new clause to SAT solver's data-structure
			assert(solver_status);

			
			increment_clause[0] = toLitCond( node_label, 1 );
			increment_clause[1] = toLitCond( child_2_label, Aig_ObjFaninC1(formula) );

			#ifdef DEBUG_SKOLEM
				cout << increment_clause[0] << " " << increment_clause[1] << " 0\n"; 
			#endif

			solver_status = sat_solver_addclause( pSat_for_incremental_solving, increment_clause, increment_clause + 2 );// SAT-solver specific code to add a new clause to SAT solver's data-structure
			assert(solver_status);

			increment_clause[0] = toLitCond( node_label, 0 );
			increment_clause[1] = toLitCond( child_1_label, !Aig_ObjFaninC0(formula) );
			increment_clause[2] = toLitCond( child_2_label, !Aig_ObjFaninC1(formula) );

			#ifdef DEBUG_SKOLEM
				cout << increment_clause[0] << " " << increment_clause[1] << " " << increment_clause[2] << " 0\n"; 
			#endif

			solver_status = sat_solver_addclause( pSat_for_incremental_solving, increment_clause, increment_clause + 3 );// SAT-solver specific code to add a new clause to SAT solver's data-structure
			assert(solver_status);
		
		}
		else if(formula->Type == AIG_OBJ_CI) //CI encountered
		{
			#ifdef DEBUG_SKOLEM
				//cout << "\nAIG_OBJ_CI encountered\n";
			#endif

			map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(key);
			assert(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end());
			string Ci_name = Ci_id_to_Ci_name_map_it->second;

			#ifdef DEBUG_SKOLEM
				//cout << "\nCi_name = " << Ci_name << endl;
			#endif			

			Ci_name_to_Ci_label_map.insert(make_pair(Ci_name, node_label));
			Ci_label_to_Ci_name_map.insert(make_pair(node_label, Ci_name));
		}
		else if(formula->Type == AIG_OBJ_CONST1) // 1 encountered
		{
			#ifdef DEBUG_SKOLEM
				//cout << "\nAIG_OBJ_CONST1 encountered\n";
			#endif

			#ifdef DEBUG_SKOLEM
				cout << "\nAdding clauses for (" << node_label << ")" << endl;
			#endif
		
			lit node_clause[1];
    			int solver_status;
    			assert( node_label >= 0 );

    			node_clause[0] = toLitCond( node_label, 0 );

			#ifdef DEBUG_SKOLEM
				cout << node_clause[0] << " 0\n";
			#endif

    			solver_status = sat_solver_addclause( pSat_for_incremental_solving, node_clause, node_clause + 1 );// SAT-solver specific code to add a new clause to SAT solver's data-structure
    			assert(solver_status);			
		}		
		else if(formula->Type == AIG_OBJ_CO) //CO encountered
		{
			#ifdef DEBUG_SKOLEM
				//cout << "\nAIG_OBJ_CO encountered\n";
			#endif

			// do nothing
		}
		else
		{
			cout << "\nUnknown formula->Type encountered in helper.cpp::getIncrementAsCNF_and_AddToSolver_Internal\n";		
			assert(false);
		}

		return node_label;

	} // if(!label exists already) ends here

}//function ends here				



void obtainVariableEliminationBenchmark(ABC* abcObj, Abc_Frame_t* abcFrame, Aig_Obj_t* &arbitrary_boolean_formula, set<Aig_Obj_t*> &Factors, Aig_Man_t* &aig_manager, list<string> &VariablesToEliminate)
{
	assert(benchmark_name != "");

	string command = "read " + benchmark_name + ";" + initCommand;
	
	#ifdef DEBUG_SKOLEM
	cout << command << endl;
	#endif

	if (abcObj->comExecute(abcFrame, command))
    	{
	 	cout << "cannot execute " << command << endl;
		assert(false);
	}

	#ifdef DEBUG_SKOLEM //Printing original circuit
	command = "write ckt.v;";
	cout << command << endl;
		
	if (abcObj->comExecute(abcFrame, command))
	{
		cout << "cannot execute command " << command << endl;
		assert(false);
	}
	#endif	

	Abc_Ntk_t* transition_function = abcFrame->pNtkCur;
	transition_function = Abc_NtkDup(transition_function);
	set<string> VariablesToEliminate_Set(VariablesToEliminate.begin(), VariablesToEliminate.end());
	
	// Let's get all the variable names and
	// Ci_name_to_Ci_number_map
	Abc_Obj_t* tempInputObj;
	int j = 0;
	vector<string> variable_names;
	Abc_NtkForEachCi(transition_function, tempInputObj, j)
	{
		string variable_name = Abc_ObjName(tempInputObj);
		variable_names.push_back(variable_name);

		Ci_name_to_Ci_number_map.insert(make_pair(variable_name, j));

		number_of_Cis++;				
	} 

	aig_manager = Abc_NtkToDar(transition_function, 0, 0);
	// transition function converted to aig_manager	

	assert(Aig_ManCoNum(aig_manager) == 1);
	Aig_Obj_t* CO_aig_manager;
	CO_aig_manager = Aig_ManCo(aig_manager, 0);
	assert(CO_aig_manager != NULL);

	Aig_Obj_t* root_of_conjunction;
	root_of_conjunction = Aig_ObjChild0(CO_aig_manager);	
	assert(root_of_conjunction != NULL);

	if(perform_cegar_on_arbitrary_boolean_formulas)
	{
		arbitrary_boolean_formula = root_of_conjunction;
	}
	else // do AND-flattening to get the Factors
	{
		vector<Aig_Obj_t*> roots_of_conjunction;

		if(!Aig_IsComplement(root_of_conjunction) && root_of_conjunction->Type == AIG_OBJ_AND)
		{
			roots_of_conjunction.push_back(root_of_conjunction);
		}
		else
		{
			Factors.insert(root_of_conjunction);	
		}
	    	

		while(roots_of_conjunction.size() > 0)
		{
			root_of_conjunction = roots_of_conjunction[0];
			roots_of_conjunction.erase(roots_of_conjunction.begin());

			Aig_Obj_t* child1 = Aig_ObjChild0(root_of_conjunction);
			assert(child1 != NULL);
			if(!Aig_IsComplement(child1) && child1->Type == AIG_OBJ_AND)
			{
				roots_of_conjunction.push_back(child1);
			}
			else
			{
				Factors.insert(child1);	
			}	

			Aig_Obj_t* child2 = Aig_ObjChild1(root_of_conjunction);
			assert(child2 != NULL);
			if(!Aig_IsComplement(child2) && child2->Type == AIG_OBJ_AND)
			{
				roots_of_conjunction.push_back(child2);
			}
			else
			{
				Factors.insert(child2);	
			}
		}
	}



	// Let's get the IDs of the variables
	
	Aig_Obj_t* ciObj;
	vector<int> variable_ids;
	int i = 0;
	Aig_ManForEachCi(aig_manager, ciObj, i )
	{
		int Id = Aig_ObjId(ciObj); // no need to apply Aig_Regular() as ciObj is CI
		variable_ids.push_back(Id);

		string variable_name = 	variable_names[i];
		if(VariablesToEliminate_Set.find(variable_name) != VariablesToEliminate_Set.end())
		// variable_name is an input; it is a Ci to be eliminated
		{
			Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.insert(make_pair(variable_name, ciObj));
		}

		Ci_name_to_Ci_object_map.insert(make_pair(variable_name, ciObj));		
	}

	// Let's create the variable_id ---> variable_name map

	assert(variable_ids.size() == variable_names.size());	
	for(int i = 0; i < variable_ids.size(); i++)
	{
		Ci_id_to_Ci_name_map.insert(make_pair(variable_ids[i], variable_names[i]));
	}
}


void writeCombinationalCircuitInVerilog( Aig_Man_t * p, char * pFileName, vector<string> &Ci_name_list, vector<string> &Co_name_list)
{
    map<Aig_Obj_t*, string> node_name_map;

    FILE * pFile;
    Vec_Ptr_t * vNodes;
    Aig_Obj_t * pObj, * pObjLi, * pObjLo, * pConst1 = NULL;
    int i;
    if ( Aig_ManCoNum(p) == 0 )
    {
        assert(false);
    }
    // check if constant is used
    Aig_ManForEachCo( p, pObj, i )
        if ( Aig_ObjIsConst1(Aig_ObjFanin0(pObj)) )
            pConst1 = Aig_ManConst1(p);
    // collect nodes in the DFS order
    vNodes = Aig_ManDfs( p, 1 );

    // assign IDs to objects
    char node_count_char[100];
    sprintf(node_count_char, "%d", 1);
    string node_count_string(node_count_char);
    string node_string = "c_";
    node_string += node_count_string;
    node_name_map.insert(make_pair(Aig_ManConst1(p), node_string));
	
    Aig_ManForEachCi( p, pObj, i )
	{
	string node_string;
	node_string = Ci_name_list[i];
	node_name_map.insert(make_pair(pObj, node_string));
	}

    Aig_ManForEachCo( p, pObj, i )
	{
	string node_string;
	node_string = Co_name_list[i];
	node_name_map.insert(make_pair(pObj, node_string));
	}    

    int Counter = 1;   
    Vec_PtrForEachEntry( Aig_Obj_t *, vNodes, pObj, i )
	{
	char node_count_char[100];
	sprintf(node_count_char, "%d", Counter);
	string node_count_string(node_count_char);
	string node_string = "wire_";
	node_string += node_count_string;
	node_name_map.insert(make_pair(pObj, node_string));
	Counter++;
	}
    
    // write the file
    pFile = fopen( pFileName, "w" );
    fprintf( pFile, "// Skolem functions generated\n" );
//    fprintf( pFile, "// http://www.eecs.berkeley.edu/~alanmi/abc/\n" );
    if ( Aig_ManRegNum(p) )
        fprintf( pFile, "module %s ( clock", p->pName? p->pName: "test" );
    else
        fprintf( pFile, "module %s (", p->pName? p->pName: "test" );
    Aig_ManForEachPiSeq( p, pObj, i )
	{
	      string Ci_name_to_be_written = node_name_map[pObj];
	      fprintf( pFile, "%s %s", ((Aig_ManRegNum(p) || i)? ",":""), node_name_map[pObj].c_str() );
	}

    if(Aig_ManCiNum(p) == 0) // No Pi's
    {	
	    Aig_ManForEachPoSeq( p, pObj, i )
	       {
		if(i == 0)
			fprintf( pFile, "%s", node_name_map[pObj].c_str() );
		else
			fprintf( pFile, ", %s", node_name_map[pObj].c_str() );
               }
    }
    else // there are Pi's
    {
	  Aig_ManForEachPoSeq( p, pObj, i )
		fprintf( pFile, ", %s", node_name_map[pObj].c_str() );
    }
    fprintf( pFile, " );\n" );

    // write PIs
    if ( Aig_ManRegNum(p) )
        fprintf( pFile, "input clock;\n" );
    Aig_ManForEachPiSeq( p, pObj, i )
	{
		string Ci_name_to_be_written = node_name_map[pObj];
       		fprintf( pFile, "input %s;\n", node_name_map[pObj].c_str() );
	}
    // write POs
    Aig_ManForEachPoSeq( p, pObj, i )
        fprintf( pFile, "output %s;\n", node_name_map[pObj].c_str() );
    // write latches
    if ( Aig_ManRegNum(p) )
    {
    Aig_ManForEachLiLoSeq( p, pObjLi, pObjLo, i )
        fprintf( pFile, "reg %s;\n", node_name_map[pObjLo].c_str());
    Aig_ManForEachLiLoSeq( p, pObjLi, pObjLo, i )
        fprintf( pFile, "wire %s;\n", node_name_map[pObjLi].c_str() );
    }
    // write nodes
    Vec_PtrForEachEntry( Aig_Obj_t *, vNodes, pObj, i )
        fprintf( pFile, "wire %s;\n", node_name_map[pObj].c_str() );
    if ( pConst1 )
        fprintf( pFile, "wire %s;\n", node_name_map[pConst1].c_str());
    // write nodes
    if ( pConst1 )
        fprintf( pFile, "assign %s = 1\'b1;\n", node_name_map[pConst1].c_str() );
    Vec_PtrForEachEntry( Aig_Obj_t *, vNodes, pObj, i )
    {
        fprintf( pFile, "assign %s = %s%s & %s%s;\n", 
            node_name_map[pObj].c_str(),
            !Aig_ObjFaninC0(pObj) ? " " : "~", node_name_map[Aig_ObjFanin0(pObj)].c_str(), 
            !Aig_ObjFaninC1(pObj) ? " " : "~", node_name_map[Aig_ObjFanin1(pObj)].c_str()
            );
    }
    // write POs
    Aig_ManForEachPoSeq( p, pObj, i )
    {
        fprintf( pFile, "assign %s = %s%s;\n", 
            node_name_map[pObj].c_str(),
            !Aig_ObjFaninC0(pObj) ? " " : "~", node_name_map[Aig_ObjFanin0(pObj)].c_str() );
    }
    if ( Aig_ManRegNum(p) )
    {
        Aig_ManForEachLiLoSeq( p, pObjLi, pObjLo, i )
        {
            fprintf( pFile, "assign %s = %s%s;\n", 
                node_name_map[pObjLi].c_str(),
                !Aig_ObjFaninC0(pObjLi) ? " " : "~", node_name_map[Aig_ObjFanin0(pObjLi)].c_str() );
        }
    }

    // write initial state
    if ( Aig_ManRegNum(p) )
    {
        Aig_ManForEachLiLoSeq( p, pObjLi, pObjLo, i )
            fprintf( pFile, "always @ (posedge clock) begin %s <= %s; end\n", 
                 node_name_map[pObjLo].c_str(),
                 node_name_map[pObjLi].c_str() );
        Aig_ManForEachLiLoSeq( p, pObjLi, pObjLo, i )
            fprintf( pFile, "initial begin %s <= 1\'b0; end\n", 
                 node_name_map[pObjLo].c_str() );
    }

    fprintf( pFile, "endmodule\n\n" );
    fclose( pFile );
    Vec_PtrFree( vNodes );
}

