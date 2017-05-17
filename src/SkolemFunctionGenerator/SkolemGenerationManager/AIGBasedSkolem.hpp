/***************************************************************************
FileName : AIGBasedSkolem.h

SystemName: ParSyn : Parallel Boolean Funciton Synthesis Tool/ Parallel Skolem Function Generation Tool.

Description: This file is header file for AIGBasedSkolem.cpp

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

#ifndef AIGBASEDSKOLEM_HPP
#define	AIGBASEDSKOLEM_HPP

#include "helper.hpp"
#include "HashTable_WithStandardKeys.h"
#include <vector>
#include <iostream>
#include <assert.h>
#include <limits.h>
#include <sys/time.h>
#include <algorithm>

using namespace std;

class AIGBasedSkolem
{
public:
	// pointer to aig manager
	Aig_Man_t* pub_aig_manager;

    	int number_of_factors; // number of factors in the original problem
	int number_of_vars_to_elim; // number of variables to eliminate in the original problem
	

	// GLOBAL MATRICES AND SETS

	// maps are created between names of variables to be eliminated and their indices. 
	map<string, int> var_name_to_var_index_map; // name --> index map
	map<int, string> var_index_to_var_name_map; // index --> name map

	// matrix storing factors
	map<int, Aig_Obj_t*> FactorMatrix; // factor index ---> factor

	// matrix storing the skolem functions
 	map<int, Aig_Obj_t*> SkolemFunctions; // var to elim index ---> skolem function 
		

	// matrix storing the alpha-combined's
	map<int, Aig_Obj_t*> AlphaCombineds; // var to elim index ---> alpha combined

	
	
	// Following are used when CEGAR is enabled
	map<int, Aig_Obj_t*> BadSets; // var to elim index ---> bad set

	// VARIABLE-SPECIFIC MATRICES AND SETS 
	// THESE ARE CLEANED AFTER FINDING SKOLEM-FUNCTION FOR THE VARIABLE

	set<int> FactorsWithVariable;

	// Matrices storing alpha, beta, gamma, delta, and cofactors
	// Note that the negations of cofactors are not required as the 
	// AIG for negation is obtained by just flipping the pointer
	map<int, Aig_Obj_t*> CofactorOneMatrix; // factor index ---> co-factor 1
	map<int, Aig_Obj_t*> CofactorZeroMatrix; // factor index ---> co-factor 0
	map<int, Aig_Obj_t*> AlphaMatrix; // factor index ---> alpha
	map<int, Aig_Obj_t*> BetaMatrix; // factor index ---> beta
	map<int, Aig_Obj_t*> GammaMatrix; // factor index ---> gamma
	map<int, Aig_Obj_t*> DeltaMatrix; // factor index ---> delta
		

	// GLOBAL MATRICES AND SETS FOR RECORD-KEEPING
	#ifdef RECORD_KEEP
	map<int, int> original_factor_sizes; // sizes of original factors
	map<int, int> abstracted_factor_sizes; // sizes of factors after abstraction - replacement by UFs
	map<int, int> original_factor_support_sizes; // sizes of supports of original factors
	map<int, int> original_factor_varstoelim_sizes; // number of variables to eliminate in original factors
	int original_support_size; // size of support of factor_1 \wedge ... \wedge factor_n

	int NumberOfFactors; // number of factors containing the var to elim
	int SkylineSize; // size of skyline
	unsigned long long int SkolemFunctionGenTime; // time to generate skolem function
	unsigned long long int AlphaCombGenTime; // time to generate alpha combined
	unsigned long long int SkylineGenTime; // time to generate skyline
	unsigned long long int DeltaPartGenTime; // time to generate delta part
	unsigned long long int DeltaCombGenTime; // time to generate delta combined
	unsigned long long int NextFactorGenTime; // time to generate next factor
	unsigned long long int CorrectionPartGenTime; // time to generate correction part
	int SkolemFunctionSize; // size of skolem function
        int AlphaPartSize; // size of alpha \or gamma part
        int DeltaPartSize; // size of delta part
        int DeltaCombinedSize; // size of delta combined
	int CorrectionPartSize; // size of correction part
	int number_of_compose_operations_for_variable;
	#endif

	list<int> FactorsAffectingSkolemFunction; // list of factors which affect the skolem function of the variable
	list<int> sizes_of_factors_affecting_variable; // sizes of factors which affect the skolem function of the variable
	list<int> sizes_of_conflict_conjuncts_affecting_variable; // sizes of conjunctions of conflicts which affect the skolem function of the variable
	list<int> sizes_of_cofactors_affecting_variable; // sizes of cofactors which affect the skolem function of the variable
	unsigned long long int total_time_in_ordering_for_the_variable; // ordering time for the present variable

	#ifdef DETAILED_RECORD_KEEP
	list<int> sizes_of_factors_with_variable;
	unsigned long long int ComposeTime; // total time consumed in compose
	unsigned long long int FactorFindingTime; // total time consumed in support-finding
	set<int> PreviousFactorsWithVariable; // factors with variable for the variable just eliminated
	#endif


	// Constructor, desctructor
 	AIGBasedSkolem(Aig_Man_t* aig_manager);
	AIGBasedSkolem(Abc_Ntk_t* Original_Abc_Network, Aig_Man_t* ext_aig_manager, int rank, int order_from_master, char* order_file_from_master, char* variable_file_from_master, int debug_level, int milking_cex_on, set<string> &non_occuring_variables_to_eliminate, list<string> &order_of_elimination); // Added for implementation in cluster
    	~AIGBasedSkolem(); 
	static AIGBasedSkolem* AIGBasedSkolem_instance;
  	static AIGBasedSkolem* getInstance(Aig_Man_t* aig_manager);

	/**
 	* The factorized skolem function generator
 	* @param factors
 	* @param variables to be eliminated
	*/
	void factorizedSkolemFunctionGenerator(set<Aig_Obj_t*> &Factors, list<string> &VariablesToEliminate);  


	/**
 	* Initializes the fields of AIGBasedSkolem class and
	* Decides the order in which variables are to be eliminated 
 	* @param factors
 	* @param variables to be eliminated
	*/
	void initializeFactorizedSkolemFunctionGenerator(set<Aig_Obj_t*> &Factors, list<string> &VariablesToEliminate);



	/**
 	* Computes the set of factors with the given variable in support
 	* @param index of the variable to be eliminated
	*/	
	void findFactorsWithVariable(int var_to_elim_index);



	/**
 	* Computes alpha at location [var_to_elim_index][factor_index]
 	* @param index of the variable to be eliminated
        * @param index of the factor
	*/
	Aig_Obj_t* computeAlpha(int var_to_elim_index, int factor_index);


	/**
 	* Computes beta at location [var_to_elim_index][factor_index]
 	* @param index of the variable to be eliminated
        * @param index of the factor
	*/
	Aig_Obj_t* computeBeta(int var_to_elim_index, int factor_index);


	/**
 	* Computes gamma at location [var_to_elim_index][factor_index]
 	* @param index of the variable to be eliminated
        * @param index of the factor
	*/
	Aig_Obj_t* computeGamma(int var_to_elim_index, int factor_index);


	/**
 	* Computes delta at location [var_to_elim_index][factor_index]
 	* @param index of the variable to be eliminated
        * @param index of the factor
	*/
	Aig_Obj_t* computeDelta(int var_to_elim_index, int factor_index);


	/**
 	* Computes cofactor-1 at location [var_to_elim_index][factor_index]
	* Takes (computes) factor at location [var_to_elim_index][factor_index], and
	* replaces occurences of variable at var_to_elim_index by 1. 
 	* @param index of the variable to be eliminated
        * @param index of the factor
	*/
	Aig_Obj_t* computeCofactorOne(int var_to_elim_index, int factor_index);
	

	/**
 	* Computes the negation of cofactor-1 at location [var_to_elim_index][factor_index]
	* Takes (computes) cofactor-1 at location [var_to_elim_index][factor_index], and negates it.
 	* @param index of the variable to be eliminated
        * @param index of the factor
	*/	
	Aig_Obj_t* computeNegatedCofactorOne(int var_to_elim_index, int factor_index);


	/**
 	* Computes cofactor-0 at location [var_to_elim_index][factor_index]
	* Takes (computes) factor at location [var_to_elim_index][factor_index], and
	* replaces occurences of variable at var_to_elim_index by 0. 
 	* @param index of the variable to be eliminated
        * @param index of the factor
	*/
	Aig_Obj_t* computeCofactorZero(int var_to_elim_index, int factor_index);


	/**
 	* Computes the negation of cofactor-0 at location [var_to_elim_index][factor_index]
	* Takes (computes) cofactor-0 at location [var_to_elim_index][factor_index], and negates it.
 	* @param index of the variable to be eliminated
        * @param index of the factor
	*/	
	Aig_Obj_t* computeNegatedCofactorZero(int var_to_elim_index, int factor_index);



	/**
 	* Checks if a formula is free of a variable
	* @param formula
        * @param index of variable
	* post-conditions: return value = true if formula is free of a variable; false otherwise
	* Note that the circuit pointed to by formula is not changed by this function 
	*/
	bool formulaFreeOfVariable(Aig_Obj_t* formula, int var_index);



	/**
 	* replaces the occurences of a variable in a formula by another formula
	* @param original formula
 	* @param index of the variable to be replaced
        * @param formula to substitute in place of the variable
	* post-conditions: 1) return value = The result of replacing the occurences of the variable in OriginalFormula by FormulaToSubstitute
	*/
	Aig_Obj_t* replaceVariableByFormula(Aig_Obj_t* OriginalFormula, int var_index_to_replace, Aig_Obj_t* FormulaToSubstitute);



	/**
 	* replaces the occurences of each variable in map by corresponding formula
	* @param original formula
 	* @param replacement map
	* post-conditions: 1) return value = The result of replacing the occurences of the variables in OriginalFormula as per replacement_map
	*/
	Aig_Obj_t* replaceVariablesByFormulas(Aig_Obj_t* OriginalFormula, map<int, Aig_Obj_t*> &replacement_map);




	/**
 	* replaces the occurences of a variable in a formula by constant_to_substitute
	* @param original formula
 	* @param index of the variable to be replaced
        * @param constant to substitute in place of the variable
	* post-conditions: 1) return value = The result of replacing the occurences of the variable in OriginalFormula by constant_to_substitute
	*/
	Aig_Obj_t* replaceVariableByConstant(Aig_Obj_t* OriginalFormula, int var_index_to_replace, int constant_to_substitute);





	/**
 	* replaces the occurences of each variable in map by corresponding constant
	* @param original formula
 	* @param replacement map
	* post-conditions: 1) return value = The result of replacing the occurences of the variables in OriginalFormula as per replacement_map
	*/
	Aig_Obj_t* replaceVariablesByConstants(Aig_Obj_t* OriginalFormula, map<int, int> &replacement_map);




	/* Clears the variable-specific data-structures
	*/	
	void clearVariableSpecificDataStructures();




	
	/* performs reverse-substitution of skolem functions after their 
	   generation to make them order-independent 
        */
	void performReverseSubstitutionOfSkolemFunctions();



	/**
 	* Computes alpha combined \vee gamma combined for a given variable
 	* @param index of the variable to be eliminated
	*/
	Aig_Obj_t* computeAlphaCombinedOrGammaCombined(int var_to_elim_index);




	/* function to print the factor graph */
	void printFactorGraph(set<string> &Final_VariablesToEliminate_Set);




	/* function to print the factor graph as .dat file */
	void printFactorGraphAsData(set<string> &Final_VariablesToEliminate_Set);


	/* Replacement functions */
	Aig_Obj_t* replaceVariablesByFormulas(Aig_Obj_t* OriginalFormula, map<string, Aig_Obj_t*> &replacement_map);
	Aig_Obj_t* replaceVariableByFormula(Aig_Obj_t* OriginalFormula, string var_to_replace, Aig_Obj_t* FormulaToSubstitute);

	

	/* functions for MonoSkolem */
	Aig_Obj_t* computeSkolemFunctionUsingBadSet(int var_to_elim_index, Aig_Obj_t* &cofactor_one_of_bad_set);
	void updateFactorsWithoutComposition(int var_to_elim_index);
	void updateFactorsUsingQuantifierEliminatedResult(int var_to_elim_index, Aig_Obj_t* quantifier_eliminated_result);
	Aig_Obj_t* computeQuantifierEliminatedResultUsingSkolemFunction(int var_to_elim_index, Aig_Obj_t* skolem_function);
	Aig_Obj_t* computeCofactorOneOrNegCofactorZero(int var_to_elim_index);


	/* Functions for Interpolant-based MonoSkolem */
	Aig_Obj_t* computeBetaCombined(int var_to_elim_index);
	Aig_Obj_t* computeSkolemFunctionAsInterpolant(int var_to_elim_index);
	Aig_Obj_t* computeAlphaCombined(int var_to_elim_index);

	
	/* Functions for benchmark generation */
	void benchmarkGeneration(set<Aig_Obj_t*> &transition_function_factors, map<string, Aig_Obj_t*> &output_string_to_transition_function_parts, list<string> &VariablesToEliminate);



	/* Functions for graph decomposition */
	int graphDecomposition(set<Aig_Obj_t*> &transition_function_factors, set<Aig_Obj_t*> &transition_function_parts, list<string> &VariablesToEliminate, map<Aig_Obj_t*, Aig_Obj_t*> &Output_Object_to_RHS_of_Factors, map<Aig_Obj_t*, Aig_Obj_t*> &Output_Object_to_RHS_of_PrimaryOutputs, ABC* abcObj, Abc_Frame_t* abcFrame);
	void obtainSkolemFunctionsInGraphDecomposition(set<Aig_Obj_t*> &uncovered_edges_factors, list<string> &VariablesToEliminate, map<string, Aig_Obj_t*> &variable_to_skolem_function_map, int iterations_of_loop);
	void clearAllDataStructures();
	Aig_Obj_t* generateComponent(Aig_Obj_t* transition_function, map<string, Aig_Obj_t*> &variable_to_skolem_function_map);
	Aig_Obj_t* generateCoveredEdges(set<Aig_Obj_t*> &transition_function_parts, map<string, Aig_Obj_t*> &variable_to_skolem_function_map);
	Aig_Obj_t* obtainEdgeToFailStates(Aig_Obj_t* failure_condition_aig, map<Aig_Obj_t*, Aig_Obj_t*> &Output_Object_to_RHS_of_PrimaryOutputs);
	void optimizeReplacementMap(map<string, Aig_Obj_t*> &replacement_map, Aig_Obj_t* source_formula, map<string, Aig_Obj_t*> &optimized_replacement_map);
	void showReplacementMap(map<string, Aig_Obj_t*> &replacement_map, string whoami);
	void showReplacementMap(map<string, Aig_Obj_t*> &replacement_map, string whoami, int call_count);
	Aig_Obj_t* findNewPartInFailureConditionDagUsingUnrolling(int &number_of_state_elements, map<int, string> &idName, list<string> &output_names, map<string, Aig_Obj_t*> &output_name_to_replaced_factor, map<Aig_Obj_t*, Aig_Obj_t*> &Output_Object_to_RHS_of_PrimaryOutputs, map<string, Aig_Obj_t*> &variable_to_skolem_function_map, int iterations_of_loop, ABC* abcObj, Abc_Frame_t* abcFrame);


	/* Functions for CegarSkolem */
	void initializeCEGAR_using_ABC();
	string obtainZVariableString(int var_to_elim_index, int z_i_count);
	Aig_Obj_t* obtainObjectOfTemporaryVariableForIncrementalSolving(string temporary_variable_string);
	Aig_Obj_t* obtainExistingObjectOfTemporaryVariableForIncrementalSolving(string temporary_variable_string);
	void removeTemporaryVariablesFromModel(map<string, int> &Model_of_ExactnessCheck);
	void allocateStringAndObjectToCannotBeDag(int kind_of_cannot_be, Aig_Obj_t* cannot_be_dag, string &cannot_be_string, Aig_Obj_t* &cannot_be_object);
	Aig_Obj_t* obtain_initial_mu(int origin, map<Aig_Obj_t*, int> &cannot_be_object_to_value_map, int &number_of_cannot_be_one_elements, int &number_of_cannot_be_zero_elements, int &size_of_initial_mu);
	Aig_Obj_t* obtain_disjunction_of_true_cannot_be_zero_dags(int destination, map<Aig_Obj_t*, int> &cannot_be_object_to_value_map, Aig_Obj_t* cofactor_of_mu, int &number_of_cannot_be_zero_elements_that_are_true_selected);
	Aig_Obj_t* obtain_disjunction_of_true_cannot_be_one_dags(int destination, map<Aig_Obj_t*, int> &cannot_be_object_to_value_map, Aig_Obj_t* cofactor_of_mu, int &number_of_cannot_be_one_elements_that_are_true_selected);
	void show_present_refinement_hint(map<int, Aig_Obj_t*> &Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX, map<int, Aig_Obj_t*> &Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX);
	Aig_Obj_t* computeInitialSkolemFunctionsBadSetsAndCannotBeSets(int var_to_elim_index);
	void refineSkolemFunctions_using_Mu_Based_Scheme_With_Optimizations(int correction_index, map<string, int> &Model_of_ExactnessCheck, map<int, Aig_Obj_t*> &Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX, map<int, Aig_Obj_t*> &Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX);
	bool evaluateMu(Aig_Obj_t* mu, map<int, int> &XValues, map<string, int> &YValues, int destination, int value_at_destination);
	Aig_Obj_t* createSkolemFunction_In_Mu_Based_Scheme_With_Optimizations(int destination);
	Aig_Obj_t* optimizeCannotBeOneDagThroughInterpolation(Aig_Obj_t* original_cannot_be_one_dag, int destination);
	Aig_Obj_t* createDontCarePart_In_Mu_Based_Scheme_With_Optimizations(int destination);
	Aig_Obj_t* obtainExtraCannotBeOneDagAtDestination(map<int, int> &XValues, map<string, int> &YValues, int destination, int &number_of_variables_dropped_in_generalization);
	void obtainGeneralizedModelByIncrementalSolvingInObtainingExtraCannotBeOneDagAtDestination(map<int, int> &XValues, map<string, int> &YValues, int destination, set<string> &variables_avoided);
	bool checkIfSkolemFunctionAtGivenIndexIsExact_using_Mu_Based_Scheme_With_Optimizations_With_Unified_Code_And_Incremental_Solving(int correction_index, map<string, int> &Model_of_ExactnessCheck, map<int, Aig_Obj_t*> &Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX, map<int, Aig_Obj_t*> &Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX, list<string> &VariablesToEliminate);
	void obtainAssumptionsInExactnessCheck_using_Generic_Skolem_Functions_With_Unified_Code_And_Incremental_Solving(int correction_index, vector<Aig_Obj_t*> &positive_assumptions_in_exactness_check, vector<Aig_Obj_t*> &negative_assumptions_in_exactness_check);
	bool obtainValueOfCi(string variable, map<string, bool> &variable_to_value_map);
	// A more efficient implementation of AIGBasedSkolem::evaluateFormulaOfCi is evaluateFormulaOfCi_Efficient
	// in helper.cpp. Please use that in future. This function is kept to avoid change in old code.
	bool evaluateFormulaOfCi(Aig_Obj_t* formula, map<string, bool> &variable_to_value_map);
	bool evaluateFormulaOfCi_DFS(Aig_Obj_t* formula, map<string, bool> &variable_to_value_map);	
	

	/* For skolem function generation using Bloqqer */
	void skolemFunctionGeneratorUsingBloqqer(set<Aig_Obj_t*> &Factors_new, list<string> &VariablesToEliminate);


	/* Functions for supporting game benchmarks */
	void generateSkolemFunctionsForGameBenchmarks(set<Aig_Obj_t*> &original_factors, vector< list<string> > &VariablesToEliminateForGameBenchmarks, char TypeOfInnerQuantifier);
	void obtainSkolemFunctionsInGameBenchmarks(set<Aig_Obj_t*> &Factors, list<string> &VariablesToEliminate, map<string, Aig_Obj_t*> &variable_to_skolem_function_map, int quantifier_block, char TypeOfQuantifier);
	void recreateCiMaps(list<string> &VariablesToEliminate);


	/* Functions to generate satisfiable benchmarks */
	void satisfiableBenchmarkGeneration(set<Aig_Obj_t*> &transition_function_factors, map<string, Aig_Obj_t*> &output_string_to_transition_function_parts, list<string> &VariablesToEliminate);



	/* Functions to apply on arbitrary boolean combinations */
	void callMonoSkolem(call_type original_polarity, Aig_Obj_t* original_formula, call_type polarity, Aig_Obj_t* formula, int depth_from_root);
	void computeCannotBeSetsInsideMonolithic(int var_to_elim_index);
	void insertIntoR0HashTable(call_type polarity, Aig_Obj_t* formula, vector<Aig_Obj_t*> &list_of_r0s);
	void insertIntoR1HashTable(call_type polarity, Aig_Obj_t* formula, vector<Aig_Obj_t*> &list_of_r1s);
	void callCegarSkolem(call_type original_polarity, Aig_Obj_t* original_formula, call_type polarity, Aig_Obj_t* formula, int depth_from_root);
	bool obtainFromR0HashTable(call_type polarity, Aig_Obj_t* formula, vector<Aig_Obj_t*> &list_of_r0s);
	bool obtainFromR1HashTable(call_type polarity, Aig_Obj_t* formula, vector<Aig_Obj_t*> &list_of_r1s);
	Aig_Obj_t* computeInitialSkolemFunctionsAndCannotBeSetsFromHashTableEntries(int var_to_elim_index, int location_of_var_to_elim, map<int, vector<Aig_Obj_t*> > &factor_index_to_list_of_r0s_map, map<int, vector<Aig_Obj_t*> > &factor_index_to_list_of_r1s_map);
	void callDisjunction(call_type original_polarity, Aig_Obj_t* original_formula, call_type polarity, Aig_Obj_t* formula, int depth_from_root);
	void Skolem(call_type original_polarity, Aig_Obj_t* original_formula, int depth_from_root);
	bool existsInR0HashTable(call_type polarity, Aig_Obj_t* formula);
	bool existsInR1HashTable(call_type polarity, Aig_Obj_t* formula);
	void callSkolem(Aig_Obj_t* formula);
	int findLocationOfVariableInGlobalVariablesToEliminate(string var_to_elim);
	void performReverseSubstitutionOfSkolemFunctions(vector<Aig_Obj_t*> &skolem_functions_of_formula);
	void setParametersToDefaults();
	void getR1R0ForFreeVariablesInConjunction(Aig_Obj_t* formula, map<string, Aig_Obj_t*> &map_of_r1s, map<string, Aig_Obj_t*> &map_of_r0s);
	void getEntryFromR0HashTable(call_type original_polarity, Aig_Obj_t* original_formula, vector<Aig_Obj_t*> &list_of_r0s);
	void getEntryFromR1HashTable(call_type original_polarity, Aig_Obj_t* original_formula, vector<Aig_Obj_t*> &list_of_r1s);
	void arbitraryBooleanBenchmarkGeneration(set<Aig_Obj_t*> &transition_function_factors, map<string, Aig_Obj_t*> &output_string_to_transition_function_parts, list<string> &VariablesToEliminate);
	void setParametersOfSeqCegarToDefaults();
	void cleanupDatastructuresAndSetParametersOfSeqCegarToDefaults();


	// Functions for parallel implementation
	void Skolem_In_Cluster(int original_polarity_as_int, Aig_Obj_t* original_formula, int depth_from_root, vector<Aig_Obj_t*> &list_of_r1s, vector<Aig_Obj_t*> &list_of_r0s, int rank, bool top_level_block, bool prove_correctness_at_top_level_block, bool &r1r0s_computed_are_exact);
	void GetFromHashTable_In_Cluster(int original_polarity_as_int, Aig_Obj_t* original_formula, vector<Aig_Obj_t*> &list_of_r1s, vector<Aig_Obj_t*> &list_of_r0s, int rank);
	void SetInHashTable_In_Cluster(int original_polarity_as_int, Aig_Obj_t* original_formula, vector<Aig_Obj_t*> &list_of_r1s, vector<Aig_Obj_t*> &list_of_r0s, int rank);
	void showListOfAigNodes(vector<Aig_Obj_t*> &list_of_r, string whoami);
	void printHashTableOperation_Across_ClusterNodes(call_type polarity, Aig_Obj_t* formula, vector<Aig_Obj_t*> &list_of_r1s, vector<Aig_Obj_t*> &list_of_r0s, bool set_operation, int rank);
	void printCallDetails_Across_ClusterNodes(call_type polarity, Aig_Obj_t* formula, string function_name, int rank);
	void attachCallDetailsInFile(call_type polarity, Aig_Obj_t* formula, string function_name);


	// Functions to improve the sequential/parallel implementation on arbitrary boolean combinations
	bool checkIfSkolemFunctionAtGivenIndexIsExact_using_Simulation(int correction_index, map<string, int> &Model_of_ExactnessCheck, map<int, Aig_Obj_t*> &Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX, map<int, Aig_Obj_t*> &Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX, list<string> &VariablesToEliminate, int number_of_solutions_generated_with_same_y);
	bool checkSatisfiabilityOfFunctionUsingSimulation(map<string, int> &Model_of_ExactnessCheck, map<int, Aig_Obj_t*> &Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX, list<string> &VariablesToEliminate);
	Aig_Obj_t* createSkolemFunction_In_Mu_Based_Scheme_With_Optimizations_With_Optional_ICb0(int destination);
	bool checkIfSkolemFunctionAtGivenIndexIsExact_using_Mu_Based_Scheme_With_Optimizations_For_Functional_Forms(int cegar_iteration_number, int correction_index, map<string, int> &Model_of_ExactnessCheck, map<int, Aig_Obj_t*> &Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX, map<int, Aig_Obj_t*> &Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX, list<string> &VariablesToEliminate);
	bool checkSatisfiabilityOfFunctionInFunctionalForms(map<string, int> &Model_of_ExactnessCheck);
	void cleanupAfterEachStepInArbitraryBooleanCombinations(string step_name);
	void cleanupMemoryInProcessor_In_Cluster(int rank);
	void getR1R0ForFreeVariablesInDisjunction(Aig_Obj_t* formula, map<string, Aig_Obj_t*> &map_of_r1s, map<string, Aig_Obj_t*> &map_of_r0s);
	Aig_Obj_t* computeInitialSkolemFunctionsAndCannotBeSetsFromHashTableEntriesForDisjunction(int var_to_elim_index, int location_of_var_to_elim, map<int, vector<Aig_Obj_t*> > &factor_index_to_list_of_r0s_map, map<int, vector<Aig_Obj_t*> > &factor_index_to_list_of_r1s_map);


	/* For skolem function generation using Rsynth */
	void skolemFunctionGeneratorUsingRsynth(list<string> &VariablesToEliminate);


	// Functions for formula solving
	void callInterractiveSolver(Aig_Obj_t* formula);
	void interractiveSolver(Aig_Obj_t* formula, list<string> &VariablesToEliminate, set<string> &VariablesToRemain, vector<Aig_Obj_t*> &list_of_initial_r1s, vector<Aig_Obj_t*> &list_of_initial_r0s);
	void getYValuesFromUser(map<string, int> &YValues);
	void giveXValuesToUser(list<string> &VariablesToEliminate, map<string, int> &Model_of_ExactnessCheck);
	bool checkIfEpsilonIsSat_For_Given_Y_using_Simulation(Aig_Obj_t* formula, map<string, int> &YValues, map<string, int> &Model_of_ExactnessCheck, int last_refined_location);
	bool checkIfSkolemFunctionsObtainedAreCorrect(Aig_Obj_t* formula, list<string> &VariablesToEliminate_Order, vector<Aig_Obj_t*> &skolem_functions_of_formula);
	
};

#endif	/* AIGBASEDSKOLEM_HPP */

