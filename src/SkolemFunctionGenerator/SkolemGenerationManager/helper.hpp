/***************************************************************************
FileName : helper.hpp

SystemName: ParSyn : Parallel Boolean Funciton Synthesis Tool/ Parallel Skolem Function Generation Tool.

Description: This file is header file for helper.cpp

Copyright (C) 2017  Shetal Shah and Ajith John 

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
************************************************************/

#ifndef HELPER_HPP

#define	HELPER_HPP
#include "AbcApi.hpp"
#include "HashTable_WithStandardKeys.h"
#include "undr_graph.hpp"

#include <iostream>
#include <set>
#include <list>
#include <sys/time.h>

#include <sys/resource.h>
#include <unistd.h>
#include <math.h>

using namespace std;
#define HWMCC_BENCHMARK
#define COI
#undef COI
#undef HWMCC_BENCHMARK
#define DEBUG
//#undef DEBUG

// Added by Ajith John starts here

//#define DEBUG_SKOLEM // Debug option for functions added by Ajith John (this should be commented except in detailed debugging)

//#define SH_DEBUG_SKOLEM // Debug option from Shetal Shah for the parallel version (this should be commented except in detailed debugging)

//#define DEBUG_COMPOSE // Debug option for Dinesh's functions (this should be commented except in debugging Dinesh's functions)

#define RECORD_KEEP // For recording details for experiments (this should be there always)

#define DETAILED_RECORD_KEEP // For detailed recording of details for experiments (this should be there always)

#define ANALYZE_CEGAR // For detailed analysis of CEGAR (this should be there always)

//#define PERFORM_SIZE_COMPUTATIONS_IN_PAR // For enabling code for size computations inside RECORD_KEEP/DETAILED_RECORD_KEEP/ANALYZE_CEGAR when doing in the parallel case (this should be commented while trying in parallel mode as otherwise size computation time can be considerable)

//#define ADDITIONAL_ASSERTION_CHECKS_INSIDE_CEGAR // Option to put additional (costly) assertions inside cegar (this should be commented except in debugging of CEGAR loop) 

//#define DEBUG_CEGAR // Debug option for functions added for CEGAR (this should be commented except in debugging of CEGAR loop)

//#define PRINT_SKOLEM_FUNCTIONS // For printing the skolem functions and original transition relation  (this should be commented except in debugging)

//#define PRINT_VERY_DETAILED_RECORDS_ON_SCREEN // For printing the fine details of skolem function generation on screen  (this should be commented except in debugging)

//#define PRINT_SKOLEM_FUNCTIONS_IN_INTERPOLATION // For printing the skolem functions in interpolation (this should be commented except in debugging)


// Added by Ajith John for parallel implementation

//#define DEBUG_PAR // Debug option for parallel version (this should be commented except in detailed debugging of the parallel version)

//#define ENABLE_FILE_PRINTING_IN_DEBUG_PAR // When DEBUG_PAR is on, enable printing the details to files (this should be commented except in detailed debugging of the parallel version)


// Added by Ajith John for limiting usage details

#define LIMITED_USAGE


// Other #defines...

#define rand0to1 (((double) rand())/((double) RAND_MAX)) // for random number generation

// Added by Ajith John ends here

//keys for the names to be stored in map
const string PREFEDGE = "pref_"; /// prefix key for storing preferred edge circuit in map
const string UNCOVEDGE = "E_"; /// prefix key for storing uncovered edge circuit in map
const string INPUTVEC =  "G_"; /// prefix key for storing input function circuit in map
const string COMPONENT = "C_"; /// prefix key for storing component circuit in map 

//name of PIs,Latch inputs,latchoutputs 
const string PREFPREFIX = "zzp"; /// This prefix is for the primary inputs of the circuit.
const string UNCOVPREFIX = "zze"; /// This prefix is for initial unco
const string LATCHPREFIX = "LATCHIN_"; /// This prefix is for the latch inputs of the circuit.
const string LATCHOUTPREFIX = "LATCHOUT_"; ///This prefix is for the latch outputs, i.e., next state vars.
const string TEMPPREFIX = "TEMP_"; /// This is temp prefix used while renaming inputs/outputs
const string EXTRA_LATCH = "extra_latch"; /// extra_latch added for hwmcc 12 benchmarks, used for debugging.
const string CIRCUITOUTPREFIX = "PRIMARYOUT_"; ///This prefix is for the circuit outputs

//############################################
//CONFIG OPTIONS


 extern string pathValue ;
 extern string circuitValue ;
 extern int numOfComponents;
 extern int badStateDepth;
 extern string nodeCommand;
 
 
//############################################
static string MYCONFIGFILENAME = "configFile"; /// config file name for reading options.
const string UNINTERPRETED_FUNCTION_PREFIX = "f"; /// prefix of uninterpreted functions
//############CONFIG OPTIONS FOR SKOLEM FUNCTION GENERATION###########

 extern set<string> factor_file_names; 
 extern string variables_to_eliminate_file_name; 
 extern string initCommand; 
 extern string benchmark_type;
 extern string benchmark_name;
 extern string machine;
 extern string problem_kind;
 extern int minimum_size_to_apply_nodeCommand;

 extern string benchmark_name_without_extension;
 extern string extension_of_benchmark;
 extern int maximum_index_to_eliminate;
 extern bool apply_cone_before_simplifications;
 extern bool use_simplified_tr;
 extern int order_of_elimination_of_variables;
 extern bool disable_factorization;
 extern bool disable_factorization_inside_factorized_code;
 extern int number_of_variables_eliminated;
 extern bool perform_reverse_substitution;
 extern bool print_factor_graph;
 
 extern bool perform_cofactor_based_quantifier_elimination_along_with_skolem_function_generation;
 extern bool use_bad_in_perform_cofactor_based_quantifier_elimination_along_with_skolem_function_generation;
 
 extern bool compute_generic_skolem_function_parameters;
 extern int uniformity_condition_counter;
 
 extern string variable_order_file_name;
 // Declarations for timeout
 extern time_t time_out;
 extern time_t time_out_start;
 extern bool time_out_enabled; // timeout will happen only if this variable is true
 extern bool timed_out;

 extern bool exit_after_order_finding;
 extern bool exit_after_factor_graph_generation;
 extern bool exit_after_finding_abstract_skolem_functions;
// Declarations for timeout ends here
//####################################################################
//####################################################################

 // options for analysing compose
 extern unsigned long long int first_level_cache_hits;  
 extern unsigned long long int first_level_cache_misses;
 extern unsigned long long int second_level_cache_hits;  
 extern unsigned long long int second_level_cache_misses;
 extern unsigned long long int leaf_cases;  
 extern unsigned long long int node_cases;
 extern unsigned long long int no_recreation_cases;  
 extern unsigned long long int recreation_cases;

//####################################################################
//####################################################################

 // data to plot
 extern unsigned long long int sum_of_number_of_factors_containing_variable;  
 extern unsigned long long int sum_of_skolem_function_sizes;
 extern unsigned long long int total_number_of_compose_operations;  
 extern unsigned long long int total_time_in_compose_operations;
 extern unsigned long long int total_time_in_alpha_combined;
 extern unsigned long long int total_time_in_delta_part;
 extern unsigned long long int total_time_in_correction_part;
 extern unsigned long long int total_time_in_delta_combined;
 extern unsigned long long int total_time_in_next_factor;
 extern unsigned long long int sum_of_skolem_function_sizes_after_reverse_substitution;
 extern list<int> skolem_function_sizes_after_reverse_substitution;
 extern unsigned long long int total_time_in_ordering;
 extern unsigned long long int total_of_skyline_sizes_in_least_cost_ordering;
 extern unsigned long long int total_time_in_compute_size;
 extern unsigned long long int total_time_in_compute_support;
 extern unsigned long long int total_time_in_generator_initialization;
 extern int sum_of_numbers_of_affecting_factors;

 extern int max_factor_size;
 extern int min_factor_size;
 extern int max_factor_varstoelim_size;
 extern int min_factor_varstoelim_size;

 extern int number_of_boolean_operations_for_variable;
 extern unsigned long long int BooleanOpTime;
 extern int number_of_support_operations_for_variable;

 extern int total_number_of_compose_operations_in_initial_skolem_function_generation;
 extern unsigned long long int total_ComposeTime_in_initial_skolem_function_generation;
 extern int total_number_of_boolean_operations_in_initial_skolem_function_generation;
 extern unsigned long long int total_BooleanOpTime_in_initial_skolem_function_generation;
 extern int total_number_of_support_operations_in_initial_skolem_function_generation;
 extern unsigned long long int total_FactorFindingTime_in_initial_skolem_function_generation;
 extern int size_of_quantified_result_in_bdd_like_scheme;

//####################################################################

//########################################################################

// declarations for least cost first ordering
 extern map<int, set<string> > factor_graph_factors_to_vars_map;
 extern map<string, set<int> > factor_graph_vars_to_factors_map;
 extern map<int, string > factor_graph_factors_to_topvars_map;
 extern set<string > topvars;

 // declarations for scc finding
 extern map<string, int > factor_graph_vars_to_sccnos_map;
 extern map<int, set<string> > factor_graph_sccnos_to_sccs_map;

 // declarations for skyline finding
 extern map<string, int > vars_to_eqclassnos_map;
 extern map<int, set<string> > eqclassnos_to_eqclasses_map;

 extern list<string> ordered_vars_to_elim;
 extern set<string> unordered_vars_to_elim;

 extern map<int, int> factor_to_costs_map;
 extern map<int, int> skolemfunctions_to_costs_map;
 extern map<int, int> deltas_to_costs_map;

//#########################################################################

//########################################################################

// declarations for proving correctness

 extern bool prove_correctness_of_skolem_functions_using_qbf_solving; 
 extern bool prove_correctness_of_skolem_functions_of_conjunctions;
 extern string qbf_solver_to_use;
//#########################################################################

//########################################################################

// declarations for scope reduction inside factorized approach

 extern set<int> top_factors_considered;
//#########################################################################
//#########################################################################

// declarations to interface with AIG Manager

 extern Aig_Obj_t* aig_bad_set;
 extern map<int, string> Ci_id_to_Ci_name_map; // used in many functions
 extern map<string, int> Ci_name_to_Ci_number_map; // used in ReplaceLeafByExpression
 extern map<string, Aig_Obj_t*> Ci_to_eliminate_name_to_Ci_to_eliminate_object_map; // used in checkIfSkolemFunctionsAreExact
 extern map<int, Aig_Obj_t*> B_i_index_to_B_i_object_map; // used in checkIfSkolemFunctionsAreExact
 extern map<string, Aig_Obj_t*> connection_string_to_connection_object_map;

 extern map<string, Aig_Obj_t*> Ci_name_to_Ci_object_map; // used in checkIfSkolemFunctionsAreExact
 extern map<int, Aig_Obj_t*> Ci_to_eliminate_renamed_to_Ci_to_eliminate_renamed_object_map; // used in checkIfSkolemFunctionsAreExact 
 extern map<string, Aig_Obj_t*> Ci_to_eliminate_renamed_name_to_Ci_to_eliminate_renamed_object_map; // used in createUniformityConditionDag
  
//#########################################################################

 // declarations to perform CEGAR style skolem function generation

 extern bool enable_cegar;
 extern int cegar_iteration_number;
 extern Aig_Obj_t* disjunction_of_bad_symbols;
 extern Aig_Obj_t* conjunction_of_factors;
 extern Aig_Obj_t* renamed_conjunction_of_factors;
 extern Aig_Obj_t* B_equivalence_part;
 extern int number_of_Cis; 
 extern t_HashTable<string, int> LabelTable;
 extern int LabelCount;
 extern map<string, int> Ci_name_to_Ci_label_mapForGetCNF; 
 extern map<int, string> Ci_label_to_Ci_name_mapForGetCNF; 
 extern int number_of_variables_in_renamed_conjunction_of_factors;
 extern unsigned long long int total_time_in_smt_solver;
 extern string solver;
 extern bool apply_global_simplifications_before_each_iteration;
 extern t_HashTable<string, bool> EvaluationTable;
 extern int refinement_strategy;
 extern map<int, set<int> > sensitivity_list; 
 extern map<int, set<int> > dependency_list; 
 extern string kind_of_global_simplifications;
 extern bool reevaluation_using_solver;
 extern bool use_interpolant_as_skolem_function;
 extern int size_of_alpha_in_interpolant_computation_for_variable;
 extern int size_of_beta_in_interpolant_computation_for_variable;
 extern unsigned long long int time_in_interpolant_computation_for_variable;
 extern unsigned long long int total_time_in_interpolant_computation;

 extern map<int, set<string> > connections_starting_at_skolem_function; 
 extern map<int, set<string> > connections_ending_at_skolem_function; 
 extern int maximum_length_of_connection_in_connection_based_scheme;
 extern int number_of_connections_in_connection_based_scheme;
 extern int number_of_connections_updated_in_iteration_in_connection_based_scheme;
 extern bool apply_optimization_on_connection_finding;
 extern map<int, map<int, int> > values_of_variables_from_bad_to_var;
 extern map<int, map<int, int> > values_of_variables_from_var;
 extern map<string, int> values_of_Y_variables;

 // declarations to perform incremental solving 
 extern map<int, int> Z_variable_counter; 
 extern map<string, int> I_variable_counter;
 extern map<string, Aig_Obj_t*> temporary_variable_for_incremental_solving_to_object_map;
 extern bool apply_solver_simplify_in_incremental_sat;

 extern sat_solver* pSat_for_exactness_check; 
 extern t_HashTable<int, int> IncrementalLabelTableForExactnessCheck;
 extern int IncrementalLabelCountForExactnessCheck;
 extern map<string, int> Ci_name_to_Ci_label_mapForExactnessCheck; 
 extern map<int, string> Ci_label_to_Ci_name_mapForExactnessCheck; 

 extern sat_solver* pSat_for_mismatch_check; 
 extern t_HashTable<int, int> IncrementalLabelTableForMismatchCheck;
 extern int IncrementalLabelCountForMismatchCheck;
 extern map<string, int> Ci_name_to_Ci_label_mapForMismatchCheck; 
 extern map<int, string> Ci_label_to_Ci_name_mapForMismatchCheck; 

 extern bool incremental_solver_for_mismatch_check_initialized;
 extern bool apply_incremental_solving_for_mismatch_check;

 // the following are for debugging 
 extern map<int, Aig_Obj_t*> BetaCombineds; // var to elim index ---> gamma combined
 extern map<int, Aig_Obj_t*> AlphaOrGammaCombineds; // var to elim index ---> alpha or gamma combined
 extern map<int, Aig_Obj_t*> GammaDisjunctions;
 extern map<int, Aig_Obj_t*> DeltaDisjunctions;
 extern vector<Aig_Obj_t*> DeltasForSpecificVariable;
 // for debugging ends here

 // data collected
 extern unsigned long long int total_time_in_initial_abstraction_generation_in_cegar;
 extern unsigned long long int total_time_in_cegar_loops_in_cegar;
 extern unsigned long long int total_time_in_connection_substitution_in_cegar;
 extern unsigned long long int total_time_in_reverse_substitution_in_cegar;

 extern unsigned long long int size_computation_time_in_initialization;
 extern unsigned long long int size_computation_time_in_initial_abstraction_generation_in_cegar;
 extern unsigned long long int size_computation_time_in_cegar_loops_in_cegar;
 extern unsigned long long int size_computation_time_in_connection_substitution_in_cegar;
 extern unsigned long long int size_computation_time_in_reverse_substitution_in_cegar;

 extern unsigned long long int total_time_in_exactness_checking_in_cegar;
 extern unsigned long long int total_time_in_x_new_recompution_in_cegar;
 extern unsigned long long int total_time_in_reevaluation_in_cegar;
 extern int number_of_exactness_checking_in_cegar;
 extern int number_of_x_new_recompution_in_cegar;
 extern int number_of_reevaluation_in_cegar;

 // sum of the above four should give the total time
 extern list<int> sizes_of_exactness_formulae_in_cegar;
 extern list<unsigned long long int> times_in_cnf_generation_in_cegar;
 extern list<unsigned long long int> times_in_sat_solving_in_cegar;
 extern unsigned long long int total_time_in_true_sat_solving_in_cegar;
 extern unsigned long long int total_time_in_false_sat_solving_in_cegar;
 extern unsigned long long int total_time_in_sat_solving_in_cegar;
 extern list<unsigned long long int> times_in_aig_simplification_in_cegar;

 // for additional assertion checking inside cegar
 extern int maximum_bad_location_from_counterexample_in_this_iteration;

 // for using generic Skolem functions inside CEGAR
 extern bool use_disjunction_of_bads_in_mu_based_scheme_in_cegar;
 extern bool use_initial_cannot_be_zero_in_psi_in_mu_based_scheme_in_cegar;

 extern int cannot_be_one_count;
 extern int cannot_be_zero_count;
 extern map<string, Aig_Obj_t*> cannot_be_string_to_cannot_be_object_map;
 extern map<Aig_Obj_t*, Aig_Obj_t*> cannot_be_object_to_cannot_be_dag_map;
 extern map<int, set<Aig_Obj_t*> > cannot_be_one_set;
 extern map<int, set<Aig_Obj_t*> > cannot_be_zero_set;
 extern map<int, Aig_Obj_t*> initial_cannot_be_zero_dags;
 extern map<int, Aig_Obj_t*> initial_cannot_be_zero_objects;
 extern int size_of_conjunction_of_factors;
 extern list<int> sizes_of_cannot_be_one_elements_of_variable;
 extern list<int> sizes_of_cannot_be_zero_elements_of_variable;
 extern int number_of_components_generated;
 extern int cegar_iteration_for_correction_index;
 extern set<string> variables_not_quantified;
 extern set<string> original_variables;
 extern set<string> variables_quantified;
 extern unsigned long long int total_time_in_mu_evaluation_in_cegar;
 extern bool select_cannot_be_elements_based_on_supports;
 extern bool avoid_y_variables_in_select_cannot_be_elements_based_on_supports;
 extern bool refine_all_locations_in_cegar;
 extern bool use_interpolants_in_cegar;
 extern unsigned long long int total_time_in_interpolant_computation_in_cegar;
 extern bool use_dontcare_optimization_in_cegar;
 extern unsigned long long int total_time_in_dontcare_optimization_in_cegar;
 extern map<int, int> D_variable_counter; // for incremental solving
 extern map<int, int> S_variable_counter; // for incremental solving
 extern int InitialSkolemFunctionSizeBeforeOptimization; // size of initial skolem function before don't care optimization
 extern bool use_refinement_from_bottom_in_mu_based_scheme_with_optimizations_in_cegar;
 extern bool use_incremental_solving_for_generalization_in_mu_based_scheme_with_optimizations_in_cegar;
 extern unsigned long long int total_time_in_generalization_in_mu_based_scheme_with_optimizations_in_cegar;

 extern sat_solver* pSat_for_generalization_check; 
 extern t_HashTable<int, int> IncrementalLabelTableForGeneralizationCheck;
 extern int IncrementalLabelCountForGeneralizationCheck;
 extern map<string, int> Ci_name_to_Ci_label_mapForGeneralizationCheck; 
 extern map<int, string> Ci_label_to_Ci_name_mapForGeneralizationCheck; 
 extern bool incremental_solver_for_generalization_check_initialized;

 extern bool simplify_sat_calls_in_use_mu_based_scheme_with_optimizations_in_cegar;
 extern bool drop_free_factors;

 extern bool use_incremental_sat_solving_in_mu_based_scheme_with_optimizations_in_cegar;
 extern map<int, int> Y_variable_counter; // for incremental solving
 extern map<int, Aig_Obj_t*> N_i_index_to_N_i_object_map; 
 extern map<int, set<int> > bads_to_exclude; 

 // declarations for component generation
 extern unsigned long long int cumulative_time_in_compute_size;

 // declarations for benchmark generation
 extern bool generate_graph_decomposition_benchmarks;

 // declarations for LOGGING
 extern string logfile_prefix;

 // Declarations for memoryout
 extern int memory_out;

 // Declarations for bloqqer
 extern bool use_bloqqer;
 extern bool skip_satisfiability_check_before_bloqqer;
 extern bool exit_after_generating_qdimacs;

 // To limit variables to eliminate
 extern int limit_on_variables_to_eliminate;

 // To select skolem function in Jiang's method
 extern string skolem_function_type_in_jiang;

 extern bool accumulate_formulae_in_cbzero_in_cegar;

 // options for unifying CEGAR methods
 extern bool use_assumptions_in_unified_cegar;
 extern bool use_bads_in_unified_cegar;
 extern bool use_cbzero_in_unified_cegar;
 extern int assumptions_flag;
 extern Aig_Obj_t* use_bads_in_unified_cegar_aig;
 extern Aig_Obj_t* use_cbzero_in_unified_cegar_aig;
 extern bool allow_intermediate_generic_sat_calls;
 extern bool compute_initial_bads_from_cbs;


 // declarations for performing graph decomposition
 extern bool write_component_as_sequential_circuit;
 extern bool write_component_in_file;
 extern string component_generation_strategy;
 extern bool use_uncovered_edge_with_preferred_edge;
 extern int failure_condition_location;
 extern Aig_Obj_t* failure_condition_aig;
 extern set<string> input_names_in_circuit;
 extern int component_number_to_be_generated;
 extern bool generate_specific_component;
 extern bool purify_failure_condition;
 extern bool apply_tsietin_encoding_before_calling_cegarskolem_inside_graph_decomposition;
 extern bool apply_global_time_outs_in_component_generation;
 extern bool apply_fraiging_in_graph_decomposition;
 extern bool conjoin_negfail_with_failfxi_to_get_preferred_edges;


 // declarations for performing tsietin encoding on benchmarks
 extern bool apply_tsietin_encoding_on_benchmarks;
 extern int number_of_tsietin_variables;
 extern map<string, Aig_Obj_t*> tsietin_variable_to_exact_skolem_function_map;
 extern bool apply_tsietin_encoding_on_benchmarks_but_dont_push_tsietin_variables_up_in_order;
 extern bool obtain_tsietin_variables_in_bfs_order;
 extern int threshold_for_tsietin_encoding;


 // declarations supporting game benchmarks 
 extern string original_logfile_prefix; 
 extern string original_benchmark_name;
 extern map<int, string> initial_Ci_id_to_Ci_name_map; 
 extern map<string, int> initial_Ci_name_to_Ci_number_map; 
 extern map<string, Aig_Obj_t*> initial_Ci_name_to_Ci_object_map; 
 extern int initial_number_of_Cis;


 // declarations for generation of satisfiable benchmarks
 extern bool generate_satisfiable_benchmarks;
 extern int limit_on_number_of_extra_conjuncts;
 extern bool make_variable_to_skolem_function_map_complex;
 extern string function_to_make_variable_to_skolem_function_map_complex;
 extern bool make_alternate_entries_toggle_in_initial_variable_to_skolem_function_map;
 extern bool extend_tsietin_encoding_to_extra_part;
 extern bool make_initial_variable_to_skolem_function_map_a_formula;


 // declarations to existentially quantified Tseitin variables during benchmark generation
 // Note that this is applicable when GENERATE-SATISFIABLE-BENCHMARKS=false. 
 // If GENERATE-SATISFIABLE-BENCHMARKS=true, then  Tseitin variables are existentially quantified
 // always
 extern bool existentially_quantify_tseitin_variables_in_benchmark_generation;


 // to fix the number of clauses/factor in qdimacs benchmark
 extern int number_of_clauses_per_factor_in_qdimacs_benchmark;

 // for skolem function generation from arbitrary Boolean formulas using CegarSkolem
 extern bool perform_cegar_on_arbitrary_boolean_formulas;
 typedef enum{negated, original} call_type;
 extern map<string, vector<Aig_Obj_t*> > R0_map; // maps NNF node of given polarity to r0's of variables to eliminate
 extern map<string, vector<Aig_Obj_t*> > R1_map; // maps NNF node of given polarity to r1's of variables to eliminate
 extern list<string> Global_VariablesToEliminate; // Global copy of list of variables to eliminate
 extern set<string> Global_VariablesToEliminate_Set; // Global copy of set of variables to eliminate
 extern set<string> Global_VariablesToRemain_Set; // Global copy of set of variables to remain
 extern Aig_Obj_t* input_arbitrary_boolean_formula; // copy of arbitrary_boolean_formula given as input
 extern bool prove_correctness_of_skolem_functions_of_arbitrary_boolean_formula; // for proving correctness
 extern bool prove_correctness_of_skolem_functions_of_arbitrary_boolean_formula_detailed_check;
 extern int number_of_cegarskolem_calls_on_arbitrary_boolean_formulas;
 extern int number_of_monoskolem_calls_on_arbitrary_boolean_formulas;
 extern int number_of_disjunctions_on_arbitrary_boolean_formulas; 
 extern int number_of_conjunctions_on_arbitrary_boolean_formulas;
 extern list<int> skolem_function_sizes_before_reverse_substitution;
 extern unsigned long long int total_time_in_reverse_substitution_on_arbitrary_boolean_formulas;
 extern unsigned long long int total_time_in_callconjunction;
 extern unsigned long long int total_time_in_calldisjunction;
 extern unsigned long long int total_time_in_callmonolithic;
 extern unsigned long long int total_time_in_cegarskolem;
 extern int min_skolem_function_size_after_reverse_substitution;
 extern int max_skolem_function_size_after_reverse_substitution;
 extern int min_skolem_function_size_before_reverse_substitution;
 extern int max_skolem_function_size_before_reverse_substitution;
 extern int total_number_of_cegar_iterations_in_cegarskolem;
 extern int max_number_of_cegar_iterations_in_cegarskolem;
 extern int min_number_of_cegar_iterations_in_cegarskolem;
 extern bool mask_printing_cegar_details; 
 extern int depth_from_root_in_cegarskolem_call_on_arbitrary_boolean_formulas;
 extern bool generate_benchmarks_for_arbitrary_boolean_combinations;
 extern unsigned long long int total_time_in_ordering_for_arbitrary_boolean_combinations;


 extern sat_solver* pSat_for_proving_correctness; 
 extern t_HashTable<int, int> IncrementalLabelTableForProvingCorrectness;
 extern int IncrementalLabelCountForProvingCorrectness;
 extern map<string, int> Ci_name_to_Ci_label_mapForProvingCorrectness; 
 extern map<int, string> Ci_label_to_Ci_name_mapForProvingCorrectness; 
 extern bool incremental_solver_for_proving_correctness_initialized;

 extern bool use_for_qbf_satisfiability;

 extern bool choose_to_apply_monoskolem_on_smaller_problem_instances;
 extern t_HashTable<int, int> TreeSizesOfNodes;
 extern t_HashTable<int, set<string> > VarsToElimOfNodes;
 extern unsigned long long int total_time_in_dfs_during_preprocessing;
 extern int threshold_size_mult_two_pow_varstoelim_to_apply_monoskolem;

 extern bool mask_printing_details_file; 

 // options added during submission to POPL'17
 extern bool generate_all_counterexamples_from_sat_call;
 extern unsigned long long int cumulative_time_in_true_sat_solving_in_cegar;
 extern unsigned long long int cumulative_time_in_false_sat_solving_in_cegar;
 extern unsigned long long int cumulative_time_in_sat_solving_in_cegar;
 extern unsigned long long int total_time_in_simulation_to_replace_sat_in_cegar;
 extern unsigned long long int cumulative_time_in_simulation_to_replace_sat_in_cegar;
 extern bool avoid_sat_call_in_functional_forms;
 extern bool internal_flag_to_avoid_sat_call_in_functional_forms;
 extern int number_of_simulations_before_sat_call_in_functional_forms;
 extern unsigned long long int total_time_in_function_evaluation_to_replace_sat_in_cegar_in_functional_forms;
 extern bool cleanup_after_each_step_in_arbitrary_boolean_combinations;
 extern set<Aig_Obj_t*> intermediate_cos_created;
 extern set<Aig_Obj_t*> intermediate_cis_created;
 extern set<Aig_Obj_t*> r1r0_cos_created;
 extern bool set_most_significant_word_to_zero_in_factorization_benchmarks;
 extern time_t cluster_global_time_out;
 extern time_t cluster_global_time_out_start;
 extern bool cluster_global_time_out_enabled;
 extern bool cluster_global_timed_out;
 extern bool avoid_cluster_global_time_out_at_top_node;
 extern bool factorizedskolem_applied_on_disjunction;
 extern bool use_rsynth;
 extern bool perform_interractive_solving_on_arbitrary_boolean_formulas;
 extern string skf_gen_algorithm;
 extern bool include_tsietin_variables_in_rsynth_qdimacs_generation;
 extern string bdd_ordering_in_rsynth;

 // Declarations to make interface with SAT solver clean
 extern bool use_generic_sat_solver_interface;
 extern string sat_solver_used_in_cegar;
 extern bool prove_correctness_of_skolem_functions; 

 // For Ocan's inputs
 extern bool negate_input_boolean_formula;
//#########################################################################


inline string toString(void* t) {
    static char buffer[50];
    sprintf(buffer, "%p", t);
    return string(buffer);
}


/**
 * Change names of ONLY outputs of network Ntk by adding suffix to their names
 * @param Ntk
 */
void changeNamesbyAddingSuffix(Abc_Ntk_t* &Ntk);

/**
 * changes the names of the primary inputs of circuit with prefix "zzp_"
 * @param c1
 * @param namePrefix
 * @param removePos
 */
void changeNamesAndRemovePos(Abc_Ntk_t*& c1,string namePrefix,int removePos);
/**
 * Rename  the latch inputs of the circuit with LATCHIN_ prefix 
 * @param c1
 * @return 
 */
string renameLatches(Abc_Ntk_t*& c1);

/**
 * Renames the primary inputs of the circuit with LATCHIN_ prefix
 * @param not_of_bad
 */
void renameBadStateInputs(Abc_Ntk_t*& not_of_bad);

/**
 * helper method during renaming.
 * changes names of the PIs of the ckt either with TEMP_ prefix or with newName(passed as an argument)
 * @param copyOfC1
 * @param newName
 */
void changeNamesToTempForPIs(Abc_Ntk_t*& copyOfC1,const string & newName = "");

/**
 * renames only the primary input of the original sequential circuit.
 * Ignores PI names starting with LATCHIN_ prefix as they are latch inputs
 * @param copyOfC1
 * @param newName
 */
void changeNamesToTempForOnlyPIs(Abc_Ntk_t*& copyOfC1,const string & newName = "");

/**
 * changes the name of the given object with TEMP_ prefix or with name passed as an argument.
 * @param prefObj
 * @param name
 * @param suffixCount
 * @return 
 */
string changeNameToTempOfObj(Abc_Obj_t*& prefObj, string name = "",int suffixCount=0);

/**
 * Get number of the given object from the given network 
 * @param 
 * @param 
 * @return 
 */
int getNumberOfObject(Abc_Obj_t*&,Abc_Ntk_t*);

/**
 * given integer to string
 * @param i
 * @return 
 */
string IntegerToString(int i);
/**
 * given string to integer
 * @param str
 * @return 
 */
int StringToInteger(string str);

/**
 * get last Pi number of the circuit c1 with prefix as "name".
 * @param c1
 * @param name
 * @return 
 */
int getLastPinumByprefix(Abc_Ntk_t* c1,string name);
/**
 * get PI by name from network pNtk
 * @param pNtk
 * @param name
 * @return 
 */
Abc_Obj_t* getPIObjByName(Abc_Ntk_t*& pNtk,const string &name);
/**
 * get PO obj with the given prefix
 * @param pNtk
 * @param prefix
 * @return 
 */
Abc_Obj_t* getPOObjByPrefix(Abc_Ntk_t* pNtk,const string &prefix);

/**
 *     NOT used
 * @param c1
 * @return 
 */
Abc_Obj_t* getPiObjWithHighestSuffix(Abc_Ntk_t* &c1);

/**
 * Deletes all the networks in the given map
 * @param mapOfNetworks
 */
void  DeleteNetworksInMap(map<string,Abc_Ntk_t*> &mapOfNetworks);


/**
 * Delete a network from the map with given name
 * @param name
 * @param mapOfNetworks
 * @return 
 */
bool  DeleteNetworkByNameFromMap(const string &name,map<string,Abc_Ntk_t*> & mapOfNetworks);
/**
 * Removes white space from string s
 * @param s
 */
void trimString(string & s);

/**
 * parses and reads the configuration option file i.e.,configFile
 */
void readFileAndInitializeConfigVars();

/**
 * set the value for the config option
 * @param name
 * @param value
 */
void setOption(const string & name,const string &value);

/**
 *    NOT USED. 
 * Implemented for testing
 * @param c1
 * @return 
 */

int deleteAllPiNamesWithBad(Abc_Ntk_t *& c1);

/**
 * prints all the primary inputs of the given networks on the STDOUT.
 * @param 
 */
void printPIs(Abc_Ntk_t*);


/**
 * parses and reads the configuration option file i.e. configFile 
 * (variant of readFileAndInitializeConfigVars for skolem function generation)
 */
void readConfigFile();


/* Function to show the usage */
void usage();


/**
 * reads the command line arguments
 */
void readCommandLineArguments(int argc, char** argv);


/**
 * set the value for the config options 
 * (variant of setOption for skolem function generation)
 * @param name
 * @param value
 */
void setArgument(const string & name, const string &value);




/* read the list of file names containing the factor files */ 
void updateFactorFileNames(string &factor_file_name_list);


/**
 * reads the variables to be eliminated from a file
 * @param variables to be eliminated read
 */
void obtainVariablesToEliminate(list<string> &VariablesToEliminate);



/**
 * writes the given Boolean formula to the given file
 * @param abc object
 * @param abc fame object
 * @param formula to be written
 * @param file where the formula is to be written
 */
void writeFormulaToFile(ABC* abcObj, Abc_Frame_t* abcFrame, Abc_Ntk_t* formula, string outfile);




/* variants of the functions working on map<int, int> */
void insertIntoOneDimensionalMatrix(map<int, int> &Matrix, int rows, int location, int entry, bool delete_existing);
int searchOneDimensionalMatrix(map<int, int> &Matrix, int rows, int location);


/**
 * insert entry var_name --> var_index into var_name_to_var_index_map
 * @param var_name_to_var_index_map
 * @param var_name
 * @param var_index
 */
void insertIntoVarNameToVarIndexMap(map<string, int> &var_name_to_var_index_map, string &var_name, int var_index);



/**
 * return entry at location var_name in var_name_to_var_index_map; 
 * returns -1 if there's no entry (this happens when the variable is not a variable to be eliminated)
 * @param var_name_to_var_index_map
 * @param var_name
 */
int searchVarNameToVarIndexMap(map<string, int> &var_name_to_var_index_map, string &var_name);



/**
 * insert entry var_index --> var_name into var_index_to_var_name_map
 * @param var_index_to_var_name_map
 * @param var_index
 * @param var_name
 */
void insertIntoVarIndexToVarNameMap(map<int, string> &var_index_to_var_name_map, int var_index, string &var_name);



/**
 * return entry at location var_index in var_index_to_var_name_map; assertion failure if there's no entry
 * @param var_index_to_var_name_map
 * @param var_index
 */
string searchVarIndexToVarNameMap(map<int, string> &var_index_to_var_name_map, int var_index);



/**
 * Displays a set of strings on screen
 * @param set of strings
 * @param name of the set
 */
void showSet(set<string> &string_set, string who_am_i);
void showSet(set<string> &string_set); //variant



/**
 * Prints a set of strings in a file
 * @param set of strings
 * @param name of the set
 * @param file pointer
 */
void printSet(set<string> &string_set, string who_am_i, FILE* fptr);
void printSet(set<int> &int_set, string who_am_i, FILE* fptr);



/**
 * Prints a list of strings in a file
 * @param list of strings
 * @param file pointer
 */
void printList(list<string> &string_list, FILE* fptr);



/**
 * Prints a list of strings on screen
 * @param list of strings
 */
void showList(list<string> &string_list);
void showList(list<int> &integer_list, string who_am_i);



/**
 * Displays a set of integers on screen
 * @param set of integers
 * @param name of the set
 */
void showSet(set<int> &integer_set, string who_am_i);
void showSet(set<int> &integer_set); // variant



/* Returns true if the global variable "time_out mode" is true and time out has happened; returns false otherwise */
bool checkTimeOut();



/* reads the oder of elimination of variables provided in a file */
void obtainOrderOfVariableEliminationFromFile(list<string> &OrderOfVariableEliminationFromFile);




/*
 Version of obtainFactorsAndVariablesToEliminatFromHWMCCFile
 that returns factors as set<Aig_Obj_t*> and gets aig_manager
 */
void obtainFactorsAndVariablesToEliminatFromHWMCCFile(ABC* abcObj, Abc_Frame_t* abcFrame, set<Aig_Obj_t*> &Factors, list<string> &VariablesToEliminate, Aig_Man_t* &aig_manager);


void obtainFactorsAndVariablesToEliminatFromHWMCCFile(ABC* abcObj, Abc_Frame_t* abcFrame, set<Aig_Obj_t*> &Factors, set<Aig_Obj_t*> &RHS_of_Factors, list<string> &VariablesToEliminate, map<Aig_Obj_t*, Aig_Obj_t*> &Output_Object_to_RHS_of_Factors, map<Aig_Obj_t*, Aig_Obj_t*> &Output_Object_to_RHS_of_PrimaryOutputs, Aig_Man_t* &aig_manager);


void obtainFactorsAndVariablesToEliminatFromHWMCCFile(ABC* abcObj, Abc_Frame_t* abcFrame, set<Aig_Obj_t*> &Factors, map<string, Aig_Obj_t*> &Output_String_to_RHS_of_Factors, list<string> &VariablesToEliminate, Aig_Man_t* &aig_manager);

void obtainFactors(ABC* abcObj, Abc_Frame_t* abcFrame, set<Aig_Obj_t*> &Factors, Aig_Man_t* &aig_manager, list<string> &VariablesToEliminate);

void obtainFactorsAndVariablesToEliminateFromGeneratedBenchmark(ABC* abcObj, Abc_Frame_t* abcFrame, set<Aig_Obj_t*> &Factors, Aig_Man_t* &aig_manager, list<string> &VariablesToEliminate);


/* Versions of insertIntoOneDimensionalMatrix and searchOneDimensionalMatrix
working on Aig_Obj_t* */
void insertIntoOneDimensionalMatrix(map<int, Aig_Obj_t*> &Matrix, int rows, int location, Aig_Obj_t* entry, bool delete_existing);
Aig_Obj_t* searchOneDimensionalMatrix(map<int, Aig_Obj_t*> &Matrix, int rows, int location);


/* Versions of writeFormulaToFile
working on Aig_Obj_t* */
void writeFormulaToFile(Aig_Man_t* aig_manager, Aig_Obj_t* formula, string outfile);
void writeFormulaToFile(Aig_Man_t* aig_manager, Aig_Obj_t* formula, string type_of_formula, string file_type, int row_index, int column_index);
void writeFormulaToFile(Aig_Man_t* aig_manager, Aig_Obj_t* formula, FILE* fp);
void writeFormulaToFile(Aig_Man_t* aig_manager, Aig_Obj_t* formula, FILE* fp, t_HashTable<string, int> &nodes_encountered);



/* Versions of create functions 
working on Aig_Obj_t* */
Aig_Obj_t* createNot(Aig_Obj_t* child, Aig_Man_t* aig_manager);
Aig_Obj_t* createOr(set<Aig_Obj_t*> &Circuits, Aig_Man_t* aig_manager);
Aig_Obj_t* createOr(Aig_Obj_t* child1, Aig_Obj_t* child2, Aig_Man_t* aig_manager);
Aig_Obj_t* createAnd(set<Aig_Obj_t*> &Circuits, Aig_Man_t* aig_manager);
Aig_Obj_t* createAnd(Aig_Obj_t* child1, Aig_Obj_t* child2, Aig_Man_t* aig_manager);
Aig_Obj_t* createFalse(Aig_Man_t* aig_manager);
Aig_Obj_t* createTrue(Aig_Man_t* aig_manager);
Aig_Obj_t* createEquivalence(Aig_Obj_t* child1, Aig_Obj_t* child2, Aig_Man_t* aig_manager);
Aig_Obj_t* createExor(Aig_Obj_t* child1, Aig_Obj_t* child2, Aig_Man_t* aig_manager);
Aig_Obj_t* createIte(Aig_Obj_t* condition, Aig_Obj_t* true_branch, Aig_Obj_t* false_branch, Aig_Man_t* aig_manager);
Aig_Obj_t* createImplication(Aig_Obj_t* antecedent, Aig_Obj_t* consequent, Aig_Man_t* aig_manager);


/* APIs working on Aig_Obj_t* as indicated by their names */
void computeSupport(Aig_Obj_t* formula, set<string> &support, Aig_Man_t* aig_manager);
Aig_Obj_t* ReplaceLeafByExpression(Aig_Obj_t* OriginalFormula, string var_to_replace, Aig_Obj_t* FormulaToSubstitute, Aig_Man_t* aig_manager);
int computeSize(Aig_Obj_t* formula, Aig_Man_t* aig_manager);


/* APIs working on Aig_Obj_t* for interfacing with sat-solver as indicated by their names 
 returns true and model in Model if sat; returns false if unsat */
bool isSat(Aig_Man_t* aig_manager, Aig_Obj_t* formula, map<string, int> &Model, unsigned long long int &cnf_time, int &formula_size, unsigned long long int &simplification_time);



/* Function to obtain CNF of a formula represented as Aig_Obj* using DFS */
/* The function finds the CNF of formula and appends it in the paramter CNF;
   Returns the label of the node; 
   The label_count and label_table used are global parameters */
int getCNF(Aig_Man_t* aig_manager, Aig_Obj_t* formula, vector< vector<int> > &CNF);



/* Given a CI, this function inserts the CI into LabelTable */
void insertCIIntoLabelTable(Aig_Obj_t* formula);



/* Function to write the CNF_1 followed by CNF_2 to a given file */
void writeCNFToFile(vector< vector<int> > &CNF_1, vector< vector<int> > &CNF_2, int number_of_variables, int number_of_clauses, string filename);



/* Function to give CNF written in cnf_filename to SAT-solver and return
   0 : if unsat
   1 : if sat with Model: Ci_name --> value */
bool giveCNFFiletoSATSolverAndQueryForSatisfiability(string cnf_filename, map<string, int> &Model);



/* Display functions */
void displayModelFromSATSolver(map<string, int> &Model);
void showCNF(vector< vector<int> > &CNF);
void writeCombinationalCircuitInVerilog( Aig_Man_t * p, int number_of_variables_to_eliminate, int original_no_of_cis, int no_of_cis_with_f_variables, int total_no_of_cis, char * pFileName, bool print_tseitin_variable_as_input );
void writeCombinationalCircuitInVerilog( Aig_Man_t * p, char * pFileName, set<string> &Cis_in_Support); //uses Ci_id_to_Ci_name_map for name finding

/* for fraiging */
Aig_Man_t * simplifyUsingFraiging( Aig_Man_t * pManAig );



/* Function to show a map on screen */
void showMap(map<int, set<int> > &integer_map, string whoami);
void showMap(map<int, set<string> > &string_map, string whoami);
void showMap(map<string, Aig_Obj_t*> &replacement_map, string whoami, Aig_Man_t* aig_manager, map<string, int> &var_name_to_var_index_map);
void showMap(map<int, Aig_Obj_t*> &replacement_map, string whoami, Aig_Man_t* aig_manager, map<string, int> &var_name_to_var_index_map);
void showVariableWiseValueMap();
void showMap(map<int, int> &replacement_map, string whoami);
void showMap(map<int, string> &my_map, string whoami);
void showYMap();


/* Function to print a map on file */
void printMap(map<int, int> &replacement_map, string whoami, FILE *fp);
void printYMap(FILE *fp);


/* Function to show a vector on screen */
void showVector(vector<int> &integer_vector, string who_am_i);



/* for cone of influence reduction */
Aig_Man_t * simplifyUsingConeOfInfluence( Aig_Man_t * p, int iPoNum, int fAddRegs );




/* for interpolation */
Aig_Obj_t* Interpolate(Aig_Man_t *aig_manager, Aig_Obj_t* alpha, Aig_Obj_t* beta);
Aig_Man_t * Aig_ManInterpolation( Aig_Man_t * pManOn, Aig_Man_t * pManOff, int fRelation, int fVerbose );
int sat_solver_store_change_last( sat_solver * s );



/* for incremental sat-solving */
bool isExactnessCheckSatisfiable(Aig_Man_t* aig_manager, Aig_Obj_t* increment, map<string, int> &Model, unsigned long long int &cnf_time, int &formula_size, unsigned long long int &simplification_time, vector<Aig_Obj_t*> &positive_assumptions_in_exactness_check, vector<Aig_Obj_t*>  &negative_assumptions_in_exactness_check, sat_solver* pSat_for_incremental_solving, t_HashTable<int, int> & IncrementalLabelTable, int &IncrementalLabelCount, map<string, int> &Ci_name_to_Ci_label_map, map<int, string> &Ci_label_to_Ci_name_map);

void addIncrementToExactnessCheck(Aig_Man_t* aig_manager, Aig_Obj_t* increment, sat_solver* pSat_for_incremental_solving, t_HashTable<int, int> & IncrementalLabelTable, int &IncrementalLabelCount, map<string, int> &Ci_name_to_Ci_label_map, map<int, string> &Ci_label_to_Ci_name_map);

void showSolverStatus(sat_solver* pSat_for_incremental_solving);

Vec_Int_t * collectPiSatNums(map<string, int> &Ci_name_to_Ci_label_map);

int addCNF(Aig_Man_t* aig_manager, Aig_Obj_t* formula, sat_solver* pSat_for_incremental_solving, t_HashTable<int, int> & IncrementalLabelTable, int &IncrementalLabelCount, map<string, int> &Ci_name_to_Ci_label_map, map<int, string> &Ci_label_to_Ci_name_map);

/* for unsat core finding */
void unsatCore(Aig_Man_t* aig_manager, Aig_Obj_t* formula, set<Aig_Obj_t*> &positive_variables, set<Aig_Obj_t*> &negative_variables, set<string> &variables_in_unsat_core);



/**
 * reads factors and variables to be eliminated from a qdimacs file
 */
void obtainFactorsAndVariablesToEliminatFromQdimacsFile(ABC* abcObj, Abc_Frame_t* abcFrame, set<Aig_Obj_t*> &Factors, Aig_Man_t* &aig_manager, list<string> &VariablesToEliminate);



/* for proving correctness */
bool checkEquivalenceUsingQBFSolver(Aig_Obj_t* quantifier_eliminated_formula, Aig_Obj_t* quantified_formula, list<string> &quantifiers, Aig_Man_t* aig_manager);
bool isQbfSat(Aig_Obj_t* quantifier_eliminated_formula, Aig_Obj_t* quantified_formula, list<string> &quantifiers, Aig_Man_t* aig_manager);


/* for FVS finding */
void FVS(UndrGraph &g, UndrGraph &g_copy, set<int> &fvs);
void findOrderOfNodes(UndrGraph &g, set<int> &fvs, list<int> &variable_order);
void obtainFactorGraphBasedOrdering(map<Aig_Obj_t*, set<string> > &VarsToElim_in_Supports_of_Factors, set<string> &Final_VariablesToEliminate_Set, list<string> &VariablesToEliminate);


/* Functions for CEGAR with generic form of Skolem functions */
void show_cannot_be_string_to_cannot_be_object_map();
void show_cannot_be_object_to_cannot_be_dag_map();
void showCannotBeSets();


/* Functions for don't-care-optimizations */
Abc_Ntk_t* obtainNetworkFromAIGWithIdNames(Aig_Man_t * pMan, map<int, string> &idName, string single_po_name);
Aig_Obj_t* performDontCareOptimization(Aig_Man_t *aig_manager, Aig_Obj_t* should_be_one, Aig_Obj_t* dont_care);

void testDontCareOptimization(ABC* abcObj, Abc_Frame_t* abcFrame);
int dontCareOptimization( Abc_Ntk_t * pNtk, Mfs_Par_t * pPars );
//void Abc_NtkMfsPowerResub( Mfs_Man_t * p, Mfs_Par_t * pPars);
int Abc_NtkMfsResub( Mfs_Man_t * p, Abc_Obj_t * pNode );
int Abc_NtkMfsNode( Mfs_Man_t * p, Abc_Obj_t * pNode );
int Abc_WinNode(Mfs_Man_t * p, Abc_Obj_t *pNode);
//Hop_Obj_t * Bdc_FunCopyHop( Bdc_Fun_t * pObj );
Hop_Obj_t * Abc_NodeIfNodeResyn( Bdc_Man_t * p, Hop_Man_t * pHop, Hop_Obj_t * pRoot, int nVars, Vec_Int_t * vTruth, unsigned * puCare, float dProb );
void Abc_NtkBidecResyn( Abc_Ntk_t * pNtk, int fVerbose );


void convertToQDimacs(Aig_Obj_t* formula, set<string> &ex_quantifiers, Aig_Man_t* aig_manager, string qdimacs_file);


/* Functions for getting factors through Tsietin's encoding */
void getFactorsThroughTsietin(Aig_Man_t* aig_manager, Aig_Obj_t* formula, set<Aig_Obj_t*> &factors, vector<string> &tsietin_variables);

Aig_Obj_t* getFactorsThroughTsietinRecursive(Aig_Man_t* aig_manager, Aig_Obj_t* formula, set<Aig_Obj_t*> &factors, map<int, Aig_Obj_t*> &tsietin_label_table, int &tsietin_count, vector<string> &tsietin_variables);

void getNewTsietinFactors(Aig_Man_t* aig_manager, Aig_Obj_t* tsietin_variable_object, Aig_Obj_t* child_1_object, Aig_Obj_t* child_2_object, int child_1_complemented, int child_2_complemented, set<Aig_Obj_t*> &factors);

void obtainFactorsThroughTsietinAndVariablesToEliminateFromGeneratedBenchmark(ABC* abcObj, Abc_Frame_t* abcFrame, set<Aig_Obj_t*> &Factors, Aig_Man_t* &aig_manager, list<string> &VariablesToEliminate);

void obtainFactorsThroughTsietin(ABC* abcObj, Abc_Frame_t* abcFrame, set<Aig_Obj_t*> &Factors, Aig_Man_t* &aig_manager, list<string> &VariablesToEliminate);

void pushTsietinVariablesUpInOrder(list<string> &VariablesToEliminate);

void collectExactSkolemFunctionForTsietinVariable(Aig_Man_t* aig_manager, string tsietin_object_string, Aig_Obj_t* child_1_object, Aig_Obj_t* child_2_object, int child_1_complemented, int child_2_complemented);

void getFactorsThroughTsietinInTopologicalManner(Aig_Man_t* aig_manager, Aig_Obj_t* formula, set<Aig_Obj_t*> &factors, vector<string> &tsietin_variables);

void labelNodesByTsietinVariables(Aig_Man_t* aig_manager, Aig_Obj_t* formula, map<int, Aig_Obj_t*>  &tsietin_label_table, int &tsietin_count, vector<string> &tsietin_variables);

Aig_Obj_t* getFactorsThroughTsietinRecursiveWithLabeledNodes(Aig_Man_t* aig_manager, Aig_Obj_t* formula, set<Aig_Obj_t*> &factors, map<int, Aig_Obj_t*>  &tsietin_label_table, t_HashTable<int, bool> &visited);

bool compare_tsietin(const string& first, const string& second);

void obtainNodesInTopologicalOrder(Aig_Man_t* aig_manager, Aig_Obj_t* formula, stack<Aig_Obj_t*> &topo_stack, t_HashTable<int, bool> &visited);

void getFactorsThroughTsietinUptoThreshold(Aig_Man_t* aig_manager, Aig_Obj_t* formula, set<Aig_Obj_t*> &factors, vector<string> &tsietin_variables, bool collect_exact_skolem_functions, map<string, Aig_Obj_t*> &tsietin_variable_to_object_map);

Aig_Obj_t* getFactorsThroughTsietinUptoThresholdRecursive(Aig_Man_t* aig_manager, Aig_Obj_t* formula, set<Aig_Obj_t*> &factors,map<int, Aig_Obj_t*>  &tsietin_label_table, int &tsietin_count, vector<string> &tsietin_variables, bool collect_exact_skolem_functions, map<string, Aig_Obj_t*> &tsietin_variable_to_object_map);

/* Functions for printing as a sequential circuit */
void Aig_ManDfs_Fragment_rec( Aig_Man_t * p, Aig_Obj_t * pObj, Vec_Ptr_t * vNodes );
Vec_Ptr_t * Aig_ManDfs_Fragment( Aig_Man_t * p, int fNodesOnly, set<int> &Interested_POs);
Abc_Ntk_t* obtainNetworkFromFragmentOfAIGWithIdNames(Aig_Man_t * pMan, map<int, string> &idName);
void Abc_NtkMakeSequential( Abc_Ntk_t * pNtk, int nLatchesToAdd );
string renameLatchesAndOutputs(Abc_Ntk_t*& c1, int number_of_latches_in_original_circuit);
Abc_Ntk_t* obtainNetworkFromFragmentOfAIGWithIdNamesWithMultipleEntriesInCOListAllowed(Aig_Man_t * pMan, map<int, string> &idName, int number_of_interested_cos);


/* Functions for supporting game benchmarks */
void obtainFactorsAndVariablesToEliminatFromGameQdimacsFile(ABC* abcObj, Abc_Frame_t* abcFrame, set<Aig_Obj_t*> &Factors, Aig_Man_t* &aig_manager, vector< list<string> > &VariablesToEliminate, char &TypeOfInnerQuantifier);

void andFlattening(Aig_Obj_t* root, set<Aig_Obj_t*> &Factors);


/* Functions to read Skolem functions supplied by external tools */
void readSkolemFunctionsAndGetTheirSizes(ABC* abcObj, Abc_Frame_t* abcFrame, Aig_Man_t* &aig_manager, int &total_size, int &number_of_vars, int &max_size, float &avg_size);


/* Functions to apply on arbitrary boolean combinations */
void obtainArbitraryBooleanProblemInstance(ABC* abcObj, Abc_Frame_t* abcFrame, Aig_Obj_t* &arbitrary_boolean_formula, Aig_Man_t* &aig_manager, list<string> &VariablesToEliminate);

void showNodeWithPolarity(call_type polarity, Aig_Obj_t* formula);

void fixOrderOfEliminationForArbitraryBooleanFormula(list<string> &VariablesToEliminate, Aig_Obj_t* arbitrary_boolean_formula, Aig_Man_t* aig_manager);

void obtainArbitraryBooleanProblemInstanceFromGeneratedBenchmark(ABC* abcObj, Abc_Frame_t* abcFrame, Aig_Obj_t* &arbitrary_boolean_formula, Aig_Man_t* &aig_manager, list<string> &VariablesToEliminate);


void findTreeSizeAndVarsToElim(Aig_Obj_t* formula, Aig_Man_t* aig_manager);

int findTreeSizeAndVarsToElim_Recur(Aig_Obj_t* formula, set<string> &varstoelim_in_formula, Aig_Man_t* aig_manager, bool include_only_inputs);

int obtainTreeSizeFromHashTable(Aig_Obj_t* formula);

void obtainVarsToElimFromHashTable(Aig_Obj_t* formula, set<string> &varstoelim_in_formula);

bool chooseToApplyMonoSkolem(Aig_Obj_t* formula);

void computeNumberOfNodesInWhichEachInputOccurs(Aig_Obj_t* formula, Aig_Man_t* aig_manager, map<string, int> &number_of_occurrences_of_variables_to_be_eliminated, bool include_only_inputs);

void Aig_Nodes_rec( Aig_Man_t * p, Aig_Obj_t * pObj, Vec_Ptr_t * vNodes );

Vec_Ptr_t * Aig_Nodes( Aig_Man_t * p, Aig_Obj_t * pObj );

void computeSizesOfCofactorsOfVariablesToBeEliminated(Aig_Obj_t* formula, Aig_Man_t* aig_manager, map<string, int> &sizes_of_cofactors_of_variables_to_be_eliminated);


/* Functions for deployment in parallel machines */
void writeFormulaToFileWithNodeId(Aig_Man_t* aig_manager, Aig_Obj_t* formula, string outfile);

void writeFormulaToFileWithNodeId(Aig_Man_t* aig_manager, Aig_Obj_t* formula, FILE* fp);

void writeFormulaToFileWithNodeId(Aig_Man_t* aig_manager, Aig_Obj_t* formula, FILE* fp, t_HashTable<string, int> &nodes_encountered);


/* Functions for use in graph decomposition */
void purifyFailureCondition(Aig_Man_t* aig_manager);


/* Functions for applying on factorization benchmarks */
void obtainArbitraryBooleanProblemInstanceFromFactorizationBenchmark(ABC* abcObj, Abc_Frame_t* abcFrame, Aig_Obj_t* &arbitrary_boolean_formula, Aig_Man_t* &aig_manager, list<string> &VariablesToEliminate);


// Functions to improve the sequential/parallel implementation on arbitrary boolean combinations
unsigned long long int findPower(unsigned long long int number);
string convertDecimalToBitvectorWithProperWidth(unsigned long long int dec, int Width);
string integerToBinaryString(unsigned long long int i);
string getVariablenameAndVariableindexFromArrayReference(string var_to_elim, int &var_index);
unsigned long long int binaryMapToNumber(map<int, bool> &bit_map);


// This function is a more efficient implementation of AIGBasedSkolem::evaluateFormulaOfCi
// Please use this in future. AIGBasedSkolem::evaluateFormulaOfCi is kept to avoid change in old code. 
bool evaluateFormulaOfCi_Efficient(Aig_Obj_t* formula, map<string, bool> &variable_to_value_map);
bool evaluateFormulaOfCi_Efficient_With_Given_HashTable(Aig_Obj_t* formula, map<string, bool> &variable_to_value_map, t_HashTable<int, bool> &evaluationHashTable);
bool evaluateFormulaOfCi_Efficient_DFS(Aig_Obj_t* formula, map<string, bool> &variable_to_value_map, t_HashTable<int, bool> &evaluationHashTable);



// Function to simplify factorization benchmark by setting the most significant word to zero
void simplifyBySettingLeastSignificantWordToZero(Aig_Man_t* aig_manager, Aig_Obj_t* &arbitrary_boolean_formula, list<string> &VariablesToEliminate);



// Functions for global time-out in cluster
void startGlobalTimer_In_Cluster(time_t external_cluster_global_time_out);
bool checkGlobalTimeOut_In_Cluster();
bool checkIfResultsAreTimedOut_In_Cluster();
void disableTimeOut_In_Cluster();



// Functions for conversion to RSynth's DIMACS format
void convertToRsynthQDimacs(Aig_Obj_t* CO_aig_manager, set<string> &ex_quantifiers, Aig_Man_t* aig_manager, string cnf_file, string output_variables_file);


// Functions needed for generator
int stringToInteger(string s);



// Functions for concurrent compose
// Eg: Let we have a \wedge b and in replacement_map [a --> b, b --> c]
// One by one compose will give b first and then c as the answer
// concurrent compose will give b \wedge c 
void Aig_Concurrent_Compose_rec( Aig_Man_t * p, Aig_Obj_t * pObj, vector<Aig_Obj_t*> &pFuncVector, vector<Aig_Obj_t*> &pVarVector);
Aig_Obj_t * Aig_Concurrent_Compose( Aig_Man_t * p, Aig_Obj_t * pRoot, vector<Aig_Obj_t*> &pFuncVector, vector<int> &iVarVector );
Aig_Obj_t* ReplaceLeavesByExpressionsConcurrently(Aig_Man_t* aig_manager, Aig_Obj_t* OriginalFormula, map<string, Aig_Obj_t*> &replacement_map);



// Functions for simplifying AIGs
Aig_Obj_t* simplifyAIGUsingFraiging(Aig_Man_t* source_manager, Aig_Obj_t* source_aig);
Aig_Man_t * simplifyUsingConeOfInfluence_DirectlyOnCO_WithLesserAssertions( Aig_Man_t * p, Aig_Obj_t * CO_selected, int fAddRegs );




// Functions for cleaning up the interface with SAT-solvers
bool getIncrementAsCNF_AddToSolver_and_CallSolver_With_Assumptions(Aig_Man_t* aig_manager, Aig_Obj_t* increment, map<string, int> &Model, unsigned long long int &cnf_time, int &formula_size, unsigned long long int &simplification_time, vector<Aig_Obj_t*> &positive_assumptions_in_exactness_check, vector<Aig_Obj_t*>  &negative_assumptions_in_exactness_check, sat_solver* pSat_for_incremental_solving, t_HashTable<int, int> & IncrementalLabelTable, int &IncrementalLabelCount, map<string, int> &Ci_name_to_Ci_label_map, map<int, string> &Ci_label_to_Ci_name_map);

void getIncrementAsCNF_and_AddToSolver(Aig_Man_t* aig_manager, Aig_Obj_t* increment, sat_solver* pSat_for_incremental_solving, t_HashTable<int, int> & IncrementalLabelTable, int &IncrementalLabelCount, map<string, int> &Ci_name_to_Ci_label_map, map<int, string> &Ci_label_to_Ci_name_map);

int getIncrementAsCNF_and_AddToSolver_Internal(Aig_Man_t* aig_manager, Aig_Obj_t* formula, sat_solver* pSat_for_incremental_solving, t_HashTable<int, int> & IncrementalLabelTable, int &IncrementalLabelCount, map<string, int> &Ci_name_to_Ci_label_map, map<int, string> &Ci_label_to_Ci_name_map);


// Functions for cleaning up the command-line options
void setInternalOptions();

void obtainVariableEliminationBenchmark(ABC* abcObj, Abc_Frame_t* abcFrame, Aig_Obj_t* &arbitrary_boolean_formula, set<Aig_Obj_t*> &Factors, Aig_Man_t* &aig_manager, list<string> &VariablesToEliminate);

void limited_usage();

void basic_usage();

// Functions for outputting Skolem functions in files
void writeCombinationalCircuitInVerilog( Aig_Man_t * p, char * pFileName, vector<string> &Ci_name_list, vector<string> &Co_name_list);


#endif	/* HELPER_HPP */

