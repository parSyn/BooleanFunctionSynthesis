/***************************************************************************
FileName : main.cc

SystemName: ParSyn : Parallel Boolean Funciton Synthesis Tool/ Parallel Skolem Function Generation Tool.

Authors: Shetal Shah and Ajith John 
 
Affliation: IIT Bombay

Description: main file for the sequential versions of Skolem function generation algorithms
************************************************************/

#include<iostream>
#include<vector>
#include<stdio.h>
#include<algorithm>
#include<cstdlib>
#include<iterator>
#include<exception>
#include<fstream>
#include <string.h>
#include <functional>
#include <cassert>
#include <sys/time.h>
using namespace std;
#include "HashTable_WithStandardKeys.h"
//#include "Generator.hpp"
#include "AIGBasedSkolem.hpp"



int main(int argc, char *argv[])
{  
  int return_value = 0; //return_value is important only in a few cases
  
#ifdef DEBUG_SKOLEM
  cout << "Staring Project..." << endl;
#endif

  clock_t start_clock, end_clock;
  start_clock = clock();

  bool input_from_command_line = true;
  if(input_from_command_line) 
    {
      // read the command-line args and set the configuration options appropriately
      //cout << "Reading the command-line args and setting the configuration options appropriately..." << endl;		
      readCommandLineArguments(argc, argv); 

    }
  else
    {    
      // read the confguration file and set the configuration options appropriately
      //cout << "Reading the confguration file and setting the configuration options appropriately..." << endl;
      readConfigFile(); 
    }

  ABC* abcObj;
  abcObj = ABC::getSingleton();
  assert(abcObj != NULL);		
    
  Abc_Frame_t* abcFrame = abcObj->getAbcFrame();
  assert(abcFrame != NULL);

  Aig_Obj_t* arbitrary_boolean_formula;
  set<Aig_Obj_t*> Factors;
  list<string> VariablesToEliminate;
  set<Aig_Obj_t*> RHS_of_Factors;
  map<string, Aig_Obj_t*> Output_String_to_RHS_of_Factors;
  map<Aig_Obj_t*, Aig_Obj_t*> Output_Object_to_RHS_of_Factors;
  map<Aig_Obj_t*, Aig_Obj_t*> Output_Object_to_RHS_of_PrimaryOutputs;

  vector< list<string> > VariablesToEliminateForGameBenchmarks;
  char TypeOfInnerQuantifier;

  int external_skolem_total_size;
  int external_skolem_number_of_vars;
  int external_skolem_max_size;
  float external_skolem_avg_size;			

  Aig_Man_t* aig_manager;

  //cout << "Reading the benchmark..." << endl;	

  if(extension_of_benchmark == "qdimacs")
  {
  	assert(problem_kind == "variable_elimination");

  	obtainFactorsAndVariablesToEliminatFromQdimacsFile(abcObj, abcFrame, Factors, aig_manager, VariablesToEliminate);	
      	
  }
  else if(extension_of_benchmark == "aig" || extension_of_benchmark == "v")
  {
  	if(problem_kind == "graph_decomposition")
	{
		obtainFactorsAndVariablesToEliminatFromHWMCCFile(abcObj, abcFrame, Factors, RHS_of_Factors, VariablesToEliminate, Output_Object_to_RHS_of_Factors, Output_Object_to_RHS_of_PrimaryOutputs, aig_manager);
	}
	else if(problem_kind == "benchmark_generation")
	{
		obtainFactorsAndVariablesToEliminatFromHWMCCFile(abcObj, abcFrame, Factors, Output_String_to_RHS_of_Factors, VariablesToEliminate, aig_manager);	
	}
	else if(problem_kind == "print_stats")
	{
		readSkolemFunctionsAndGetTheirSizes(abcObj, abcFrame, aig_manager, external_skolem_total_size,  external_skolem_number_of_vars, external_skolem_max_size, external_skolem_avg_size);	
	} 
	else if(problem_kind == "variable_elimination")
	{
		obtainVariablesToEliminate(VariablesToEliminate);
		obtainVariableEliminationBenchmark(abcObj, abcFrame, arbitrary_boolean_formula, Factors, aig_manager, VariablesToEliminate);
	} 
	else
	{
		cout <<"\nUnknown PROBLEM-KIND " << problem_kind << " \n";
		assert(false);
	}
  }
  else
  {
	cout <<"\nInput with extension " << extension_of_benchmark << " is not supported\n";
	assert(false);	
  }

    
  AIGBasedSkolem* AIGBasedSkolemObj = new AIGBasedSkolem(aig_manager);
  assert(AIGBasedSkolemObj != NULL);

  // set the logfile_prefix
  logfile_prefix = benchmark_name_without_extension;
  if(use_bloqqer)
    {
      logfile_prefix += "_bloqqer_";
    }
  else if(use_rsynth)
    {
      logfile_prefix += "_rsynth_";
    }
  else if(problem_kind == "print_stats")
    {
      logfile_prefix += "_externalskolem_";	
    }
  else if(perform_cegar_on_arbitrary_boolean_formulas || perform_interractive_solving_on_arbitrary_boolean_formulas)
    {
      logfile_prefix += "_arbitraryboolean_";	
    }
  else if(enable_cegar)
    {
      logfile_prefix += "_cegar";

      if(use_assumptions_in_unified_cegar)
       {
	      logfile_prefix += "_optimized";
       }
      else
	{
	   logfile_prefix += "_unoptimized";
	}
				
      if(use_bads_in_unified_cegar)
	 {
	     logfile_prefix += "_withbads";
	 }
      else
	   {
	     logfile_prefix += "_withnegf";
	   }


	 if(accumulate_formulae_in_cbzero_in_cegar)
	    {
	      logfile_prefix += "_withaccumulate_";
	    }
	  else
	    {
	      logfile_prefix += "_noaccumulate_";
	    }
    }
  else
    {
      logfile_prefix += "_monolithic";	
      logfile_prefix += "_compositionqe";

      if(use_interpolant_as_skolem_function)
	{
	  logfile_prefix += "_interpolantskf";
	}
      else
	{
	  logfile_prefix += "_cofactorskf";
	}
				
      if(skolem_function_type_in_jiang == "cofactorone")
	{
	  logfile_prefix += "_cofactorone_";
	}
      else
	{
	  logfile_prefix += "_bothcofactors_";
	}
    }
			

#ifdef RECORD_KEEP
  unsigned long long int total_duration_ms;
  struct timeval total_start_ms, total_finish_ms;
  gettimeofday (&total_start_ms, NULL); 

  string record_file;
  record_file = logfile_prefix;
  record_file += "skolem_function_generation_details.txt";
  FILE* record_fp = fopen(record_file.c_str(), "a+");
  assert(record_fp != NULL);
  fprintf(record_fp, "\n\n\n\n");
  fprintf(record_fp, "benchmark type = %s\n", benchmark_type.c_str()); 
  fprintf(record_fp, "benchmark name = %s\n", benchmark_name.c_str()); 
  fprintf(record_fp, "problem = %s\n", problem_kind.c_str()); 
  fprintf(record_fp, "machine = %s\n", machine.c_str());
  fclose(record_fp);
#endif
			
  if(time_out_enabled)
    {
      time_t elim_start_time;
      time(&elim_start_time);
      time_out_start = elim_start_time;
    }

  if(problem_kind == "benchmark_generation")
    {
      // to generate benchmarks of the component generation problem at arbitrary Boolean level
      if(generate_benchmarks_for_arbitrary_boolean_combinations)
	{
	  AIGBasedSkolemObj->arbitraryBooleanBenchmarkGeneration(Factors, Output_String_to_RHS_of_Factors, VariablesToEliminate);
	}
      // to generate benchmarks of the component generation problem
      else if(generate_satisfiable_benchmarks)
	{
	  AIGBasedSkolemObj->satisfiableBenchmarkGeneration(Factors, Output_String_to_RHS_of_Factors, VariablesToEliminate);
	}
      else
	{
	  AIGBasedSkolemObj->benchmarkGeneration(Factors, Output_String_to_RHS_of_Factors, VariablesToEliminate);
	}
    }
  else if(problem_kind == "graph_decomposition")
    {
      // graph decomposition on HMWMCC benchmarks

      // Skolem function generation is done inside graph decomposition
      // It can be either monolithic or factorized depending on 'disable_factorization'
      
	return_value = AIGBasedSkolemObj->graphDecomposition(Factors, RHS_of_Factors, VariablesToEliminate, Output_Object_to_RHS_of_Factors, Output_Object_to_RHS_of_PrimaryOutputs, abcObj, abcFrame);
      				
      //cout << "\nComponent generation successful\n";		
      //cout << "\nreturn_value = " << return_value << endl;
    }  
  else if(problem_kind == "print_stats")
    {
      #ifdef RECORD_KEEP
      string plot_file;
      plot_file = logfile_prefix; 
      plot_file += "skolem_function_generation_details_to_plot.txt";
      FILE* plot_fp = fopen(plot_file.c_str(), "a+");
      assert(plot_fp != NULL);
      fprintf(plot_fp, "\n%s\t%s\t%s\t%d\t%d\t%d\t%f", benchmark_type.c_str(), benchmark_name.c_str(), machine.c_str(), external_skolem_total_size,  external_skolem_number_of_vars, external_skolem_max_size, external_skolem_avg_size);
      fclose(plot_fp);
      #endif
    }
  // problem_kind == "variable_elimination"
  else if(perform_cegar_on_arbitrary_boolean_formulas)
    {
        if(cluster_global_time_out_enabled)//for graceful time-out
	{	
	  time_t elim_start_time;
	  time(&elim_start_time);
	  cluster_global_time_out_start = elim_start_time;
	}

      fixOrderOfEliminationForArbitraryBooleanFormula(VariablesToEliminate, arbitrary_boolean_formula, aig_manager);

      Global_VariablesToEliminate = VariablesToEliminate;
      copy(Global_VariablesToEliminate.begin(), Global_VariablesToEliminate.end(), inserter(Global_VariablesToEliminate_Set, Global_VariablesToEliminate_Set.begin()));

      set<string> support_arbitrary_boolean_formula;
      computeSupport(arbitrary_boolean_formula, support_arbitrary_boolean_formula, aig_manager);
      set_difference(support_arbitrary_boolean_formula.begin(), support_arbitrary_boolean_formula.end(), Global_VariablesToEliminate_Set.begin(), Global_VariablesToEliminate_Set.end(),inserter(Global_VariablesToRemain_Set, Global_VariablesToRemain_Set.begin()));

      input_arbitrary_boolean_formula = arbitrary_boolean_formula;

      if(!exit_after_order_finding)
	{
	  bool test_with_skolem_in_cluster = false;
	  if(test_with_skolem_in_cluster)
	  {
		vector<Aig_Obj_t*> list_of_r1s_temp;
		vector<Aig_Obj_t*> list_of_r0s_temp;
		bool r1r0s_computed_are_exact_temp;
		generate_all_counterexamples_from_sat_call = false;
		
		AIGBasedSkolemObj->Skolem_In_Cluster(0, arbitrary_boolean_formula, 0, list_of_r1s_temp, list_of_r0s_temp, 0, true, false, r1r0s_computed_are_exact_temp);	
          }
	  else
	  {
		AIGBasedSkolemObj->callSkolem(arbitrary_boolean_formula);	
          }
	}
    }  
  else if(use_bloqqer) // use bloqqer
    {
      AIGBasedSkolemObj->skolemFunctionGeneratorUsingBloqqer(Factors, VariablesToEliminate);			
				
    }
  else if(use_rsynth) // use rsynth
    {

      AIGBasedSkolemObj->skolemFunctionGeneratorUsingRsynth(VariablesToEliminate);	
	
    }  
  else // use factorized approach -- CegarSkolem or MonoSkolem invoked as per parameters
    {
      AIGBasedSkolemObj->factorizedSkolemFunctionGenerator(Factors, VariablesToEliminate);
    }

  if(time_out_enabled && timed_out)
    {
      cout << "\nTime-out from skolem-function generator\n";
    }

     
  end_clock = clock();
  //Write results to a dat file - this is for easy plotting of results.	
  string datfileName(benchmark_name);
  datfileName = datfileName.substr(datfileName.find_last_of("/") + 1);  //Get the file name;
  datfileName.erase(datfileName.find ("."), string::npos); //This contains the code for the raw file name;
  datfileName.append(".dat"); //This contains the code for the raw file name;
  ofstream mydatfile;
  mydatfile.open ((const char*) datfileName.c_str(), std::ios::app);
  mydatfile << benchmark_name << " " << ((double) (end_clock - start_clock)/CLOCKS_PER_SEC) << endl;
  mydatfile.close();

  // printing the statitics
#ifdef RECORD_KEEP
  gettimeofday (&total_finish_ms, NULL);
  total_duration_ms = total_finish_ms.tv_sec * 1000 + total_finish_ms.tv_usec / 1000;
  total_duration_ms -= total_start_ms.tv_sec * 1000 + total_start_ms.tv_usec / 1000;

  if(problem_kind == "variable_elimination") // for the graph_decomposition case,
    // there are multiple calls to variable_elimination and total_time_in_compute_size is reset
    // to zero after each call
    {
      total_duration_ms = total_duration_ms - total_time_in_compute_size;
    }
  else if(problem_kind == "graph_decomposition")// for graph_decomposition; substract the cumulative time spent in size computation
    {
      total_duration_ms = total_duration_ms - cumulative_time_in_compute_size;
    }
  else
    {
      // do nothing
    }

  string order_string_to_print;
  if(order_of_elimination_of_variables == 0)
    {
      order_string_to_print = "alphabetical";	
    }
  else if(order_of_elimination_of_variables == 1)
    {
      order_string_to_print = "least-occurring-first";	
    }
  else if(order_of_elimination_of_variables == 3)
    {
      order_string_to_print = "factor-graph-based";	
    }
  else if(order_of_elimination_of_variables == 2)
    {
      order_string_to_print = "externally-supplied";	
    }
  else if(order_of_elimination_of_variables == 4)
    {
      order_string_to_print = "reverse-factor-graph-based";	
    }
  else if(order_of_elimination_of_variables == 5)
    {
      order_string_to_print = "most-occurring-first";	
    }
  else if(order_of_elimination_of_variables == 6)
    {
      order_string_to_print = "smallest-cofactor1-first";	
    }
  else if(order_of_elimination_of_variables == 7)
    {
      order_string_to_print = "biggest-cofactor1-first";	
    }

  string algorithm_string;
  if(enable_cegar)
    {
      algorithm_string = "cegar";

      if(use_assumptions_in_unified_cegar)
	    {
	      algorithm_string += "_optimized";
	    }
      else
	    {
	      algorithm_string += "_unoptimized";
	    }
				
      if(use_bads_in_unified_cegar)
	    {
	      algorithm_string += "_withbads";
	    }
      else
	    {
	      algorithm_string += "_withnegf";
	    }


      if(accumulate_formulae_in_cbzero_in_cegar)
	    {
	      algorithm_string += "_withaccumulate";
	    }
       else
	    {
	      algorithm_string += "_noaccumulate";
	    }
    }
  else
    {
      algorithm_string = "monolithic";	
      algorithm_string += "_compositionqe";

      if(use_interpolant_as_skolem_function)
	{
	  algorithm_string += "_interpolantskf";
	}
      else
	{
	  algorithm_string += "_cofactorskf";
	}

      if(skolem_function_type_in_jiang == "cofactorone")
	{
	  algorithm_string += "_cofactorone";
	}
      else
	{
	  algorithm_string += "_bothcofactors";
	}
    }
				
  record_file = logfile_prefix;
  record_file += "skolem_function_generation_details.txt";
  record_fp = fopen(record_file.c_str(), "a+");
  assert(record_fp != NULL);		
				
				
  if(problem_kind == "graph_decomposition")
    {
      fprintf(record_fp, "\n\n\ntotal-time-in-component-generation-without-size-computation-time = %llu milliseconds\nsize-computation-time = %llu\nnumber of components generated = %d\n", total_duration_ms, cumulative_time_in_compute_size, number_of_components_generated);
    }
  else if(problem_kind == "variable_elimination")
    {
      if(perform_cegar_on_arbitrary_boolean_formulas)
	{
	  if(time_out_enabled && timed_out)
	    {
	      total_duration_ms = time_out * 1000;
	    }
				
	  fprintf(record_fp, "\n\n\nnumber of cegarskolem calls = %d\nnumber of monoskolem calls = %d\nnumber of find_skolem_disjunction calls = %d\nnumber of find_skolem_conjunction calls = %d\nordering-used = %s\ntotal-time-in-reverse-substitution-without-size-computation-time = %llu millisecond\n\ntotal-time-without-size-computation-time = %llu milliseconds\n", number_of_cegarskolem_calls_on_arbitrary_boolean_formulas, number_of_monoskolem_calls_on_arbitrary_boolean_formulas, number_of_disjunctions_on_arbitrary_boolean_formulas, number_of_conjunctions_on_arbitrary_boolean_formulas, order_string_to_print.c_str(), total_time_in_reverse_substitution_on_arbitrary_boolean_formulas, total_duration_ms);

	  fprintf(record_fp, "\ntime in monoskolem calls = %llu\ntime in find_skolem_disjunction calls = %llu\ntime in find_skolem_conjunction calls = %llu\n", total_time_in_callmonolithic, total_time_in_calldisjunction, total_time_in_callconjunction);

	  fprintf(record_fp, "\ntotal time in true sat calls inside cegar = %llu\ntotal time in false sat calls inside cegar = %llu\ntotal time in sat calls inside cegar = %llu\ntotal time in simulation to replace sat inside cegar in milking counterexamples = %llu\ntotal time in simulation to replace sat inside cegar by making use of functional form = %llu\n", cumulative_time_in_true_sat_solving_in_cegar, cumulative_time_in_false_sat_solving_in_cegar, cumulative_time_in_sat_solving_in_cegar, cumulative_time_in_simulation_to_replace_sat_in_cegar, total_time_in_function_evaluation_to_replace_sat_in_cegar_in_functional_forms);
		
	}
      else if(enable_cegar)
	{
	   fprintf(record_fp, "\n\n\ntotal-time-in-evaluation-of-mu = %llu milliseconds\ntotal-time-in-interpolant-computation-in-cegar = %llu milliseconds\ntotal-time-in-dont-care-optimization-in-cegar = %llu milliseconds\ntotal-time-in-generalization-in-refinement-from-bottom-in-cegar = %llu milliseconds\ntotal-time-in-initial-abstraction-generation-without-size-computation-time = %llu milliseconds\ntotal-time-in-cegar-loops-without-size-computation-time = %llu milliseconds\ntotal-time-in-reverse-substitution-without-size-computation-time = %llu milliseconds\nsolver-used = %s\nnumber-of-cegar-iterations = %d\n\ntotal-time-without-size-computation-time = %llu milliseconds\n", total_time_in_mu_evaluation_in_cegar, total_time_in_interpolant_computation_in_cegar, total_time_in_dontcare_optimization_in_cegar, total_time_in_generalization_in_mu_based_scheme_with_optimizations_in_cegar, total_time_in_initial_abstraction_generation_in_cegar, total_time_in_cegar_loops_in_cegar, total_time_in_reverse_substitution_in_cegar, solver.c_str(), cegar_iteration_number, total_duration_ms);	   
					
	}
      else
	{
	  fprintf(record_fp, "\ntotal-time-in-initial-skolem-function-generation-without-size-computation-time = %llu milliseconds\ntotal-time-in-reverse-substitution-without-size-computation-time = %llu milliseconds\ntotal-time-without-size-computation-time = %llu milliseconds\ntotal-time-in-interpolant-computation = %llu", total_time_in_initial_abstraction_generation_in_cegar, total_time_in_reverse_substitution_in_cegar, total_duration_ms, total_time_in_interpolant_computation);

	  fprintf(record_fp, "\n\nalgorithm-used = %s\nordering-used = %s\ntotal time in ordering = %llu milliseconds\ntotal time in compute-size = %llu\ntotal time in compute-support = %llu\ntotal time in initialization of skolem function generator-without-size-computation-time = %llu\ntotal time in sat solving = %llu\nsolver used = %s\nnumber of cegar iterations = %d", algorithm_string.c_str(), order_string_to_print.c_str(), total_time_in_ordering, total_time_in_compute_size, total_time_in_compute_support, total_time_in_generator_initialization, total_time_in_smt_solver, solver.c_str(), cegar_iteration_number);

	  fprintf(record_fp, "\n\nCompose Details:\nHit_1 = %llu\nMiss_1 = %llu\nHit_2 = %llu\nMiss_2 = %llu\nLeaves = %llu\nNon-leaves = %llu\nNo-create-expr = %llu\nCreate-expr = %llu\nCreate-expr/Miss_2 = %f", first_level_cache_hits, first_level_cache_misses, second_level_cache_hits, second_level_cache_misses, leaf_cases, node_cases, no_recreation_cases, recreation_cases, (float)recreation_cases/(float)second_level_cache_misses);

	  fprintf(record_fp, "\n\nsize_computation_time_in_initialization = %llu milliseconds\nsize_computation_time_in_initial_abstraction_generation_in_cegar = %llu milliseconds\nsize_computation_time_in_reverse_substitution_in_cegar = %llu milliseconds\nsize_computation_time_in_cegar_loops_in_cegar = %llu milliseconds\nsize_computation_time_in_connection_substitution_in_cegar = %llu milliseconds\ntotal_time_in_compute_size = %llu milliseconds", size_computation_time_in_initialization, size_computation_time_in_initial_abstraction_generation_in_cegar, size_computation_time_in_reverse_substitution_in_cegar, size_computation_time_in_cegar_loops_in_cegar, size_computation_time_in_connection_substitution_in_cegar, total_time_in_compute_size);
	}


      if(perform_cegar_on_arbitrary_boolean_formulas)
	{
	  fprintf(record_fp, "\nskolem-function-sizes-before-reverse-substitution = ");
	  for(list<int>::iterator sfs_it = skolem_function_sizes_before_reverse_substitution.begin(); sfs_it != skolem_function_sizes_before_reverse_substitution.end(); sfs_it++)
	    {
	      fprintf(record_fp, "%d, ", *sfs_it);
	    }

	  fprintf(record_fp, "\n\nskolem-function-sizes-after-reverse-substitution = ");
	  for(list<int>::iterator sfs_it = skolem_function_sizes_after_reverse_substitution.begin(); sfs_it != skolem_function_sizes_after_reverse_substitution.end(); sfs_it++)
	    {
	      fprintf(record_fp, "%d, ", *sfs_it);
	    }	
		
	}
      else if(enable_cegar && perform_reverse_substitution)
	{
	  fprintf(record_fp, "\nnumber-of-composes-in-reverse-substitution = %d", AIGBasedSkolemObj->number_of_compose_operations_for_variable);
	  fprintf(record_fp, "\nfinal-skolem-function-sizes = ");
	  for(list<int>::iterator sfs_it = skolem_function_sizes_after_reverse_substitution.begin(); sfs_it != skolem_function_sizes_after_reverse_substitution.end(); sfs_it++)
	    {
	      fprintf(record_fp, "%d, ", *sfs_it);
	    }
	}
      else if(perform_reverse_substitution)
	{
	  fprintf(record_fp, "\ncompose-in-reverse-substitution = %d", AIGBasedSkolemObj->number_of_compose_operations_for_variable);
	  fprintf(record_fp, "\ntime-in-reverse-substitution = %llu", AIGBasedSkolemObj->ComposeTime);
	  fprintf(record_fp, "\nfinal-skolem-function-sizes = ");
	  for(list<int>::iterator sfs_it = skolem_function_sizes_after_reverse_substitution.begin(); sfs_it != skolem_function_sizes_after_reverse_substitution.end(); sfs_it++)
	    {
	      fprintf(record_fp, "%llu, ", *sfs_it);
	    }
	}
      else
	{
	  fprintf(record_fp, "\ncompose-in-reverse-substitution = -");
	  fprintf(record_fp, "\ntime-in-reverse-substitution = -");
	  fprintf(record_fp, "\nfinal-skolem-function-sizes = -");
	}
    }//else if(problem_kind == "variable_elimination") ends here
  else
    {
      // do nothing
    }

  fclose(record_fp);


  if(perform_cegar_on_arbitrary_boolean_formulas)
    {
      string plot_file;
      plot_file = logfile_prefix; 
      plot_file += "skolem_function_generation_details_to_plot.txt";
      FILE* plot_fp = fopen(plot_file.c_str(), "a+");
      assert(plot_fp != NULL);

      if(time_out_enabled && timed_out)
	{
	  fprintf(plot_fp, "-\t-\t-\t-\t-\t-\t");
	}
      else
	{
	  fprintf(plot_fp, "%f\t%d\t%d\t%f\t%d\t%d\t", (float)sum_of_skolem_function_sizes/(float)(Global_VariablesToEliminate_Set.size()), max_skolem_function_size_before_reverse_substitution, min_skolem_function_size_before_reverse_substitution, sum_of_skolem_function_sizes_after_reverse_substitution/(float)(Global_VariablesToEliminate_Set.size()), max_skolem_function_size_after_reverse_substitution, min_skolem_function_size_after_reverse_substitution);
	}

      fprintf(plot_fp, "%f\t%d\t%d\t", (float)total_number_of_cegar_iterations_in_cegarskolem/(float)(number_of_cegarskolem_calls_on_arbitrary_boolean_formulas), max_number_of_cegar_iterations_in_cegarskolem, min_number_of_cegar_iterations_in_cegarskolem);

      fprintf(plot_fp, "%d\t%d\t%d\t%d\t", number_of_monoskolem_calls_on_arbitrary_boolean_formulas, number_of_conjunctions_on_arbitrary_boolean_formulas, number_of_disjunctions_on_arbitrary_boolean_formulas, number_of_cegarskolem_calls_on_arbitrary_boolean_formulas);

      if(time_out_enabled && timed_out)
	{
	  fprintf(plot_fp, ">%d\t-\t-\t-\t-\t-\t-\n", time_out*1000);
	}
      else
	{
	  fprintf(plot_fp, "%llu\t%llu\t%llu\t%llu\t%llu\t%llu\t%llu\n", total_duration_ms, total_time_in_ordering_for_arbitrary_boolean_combinations, total_time_in_callmonolithic, total_time_in_callconjunction, total_time_in_calldisjunction, total_time_in_cegarskolem, total_time_in_reverse_substitution_on_arbitrary_boolean_formulas);
	}

      fclose(plot_fp);
    }
  else if(!use_rsynth && !use_bloqqer && problem_kind != "print_stats")
    {
				
      string plot_file;
      plot_file = logfile_prefix; 
      plot_file += "skolem_function_generation_details_to_plot.txt";
      FILE* plot_fp = fopen(plot_file.c_str(), "a+");
      assert(plot_fp != NULL);

      if(time_out_enabled && timed_out)
       {
	      if(enable_cegar)
		{
		  fprintf(plot_fp, "\t-\t%f", (float)sum_of_number_of_factors_containing_variable/(float)(number_of_variables_eliminated));
		}
	      else
		{
		  fprintf(plot_fp, "\t%f\t%f", (float)sum_of_number_of_factors_containing_variable/(float)(number_of_variables_eliminated), (float)sum_of_skolem_function_sizes/(float)(number_of_variables_eliminated));
		}
	}
	else
	{
	      fprintf(plot_fp, "\t%f\t%f", (float)sum_of_number_of_factors_containing_variable/(float)(AIGBasedSkolemObj->number_of_vars_to_elim), (float)sum_of_skolem_function_sizes/(float)(AIGBasedSkolemObj->number_of_vars_to_elim));						
	}
					

      if(time_out_enabled && timed_out)
	{
	  fprintf(plot_fp, "\t%llu\t", time_out*1000);
	}
      else
	{
	  fprintf(plot_fp, "\t%llu\t", total_duration_ms);
	}

				
      if(time_out_enabled && timed_out)
	{
	  //fprintf(plot_fp, "-\t-\t%s\t%llu\t%llu\t%llu\t%f\t", order_string_to_print.c_str(), total_time_in_ordering, total_time_in_compute_size, total_time_in_ordering+total_time_in_compute_size, (float)sum_of_numbers_of_affecting_factors/(float)(number_of_variables_eliminated));
	  fprintf(plot_fp, "%d\t-\t-\t%s\t%llu\t", cegar_iteration_number, order_string_to_print.c_str(), total_time_in_ordering);
	}
      else if(!perform_reverse_substitution)
	{
	  //fprintf(plot_fp, "-\t-\t%s\t%llu\t%llu\t%llu\t%f\t", order_string_to_print.c_str(), total_time_in_ordering, total_time_in_compute_size, total_time_in_ordering+total_time_in_compute_size, (float)sum_of_numbers_of_affecting_factors/(float)(AIGBasedSkolemObj->number_of_vars_to_elim));
	  fprintf(plot_fp, "%d\t-\t-\t%s\t%llu\t", cegar_iteration_number, order_string_to_print.c_str(), total_time_in_ordering);
	}
      else
	{
	  //fprintf(plot_fp, "%llu\t%f\t%s\t%llu\t%llu\t%llu\t%f\t", AIGBasedSkolemObj->ComposeTime, (float)sum_of_skolem_function_sizes_after_reverse_substitution/(float)(AIGBasedSkolemObj->number_of_vars_to_elim), order_string_to_print.c_str(), total_time_in_ordering, total_time_in_compute_size, total_time_in_ordering+total_time_in_compute_size, (float)sum_of_numbers_of_affecting_factors/(float)(AIGBasedSkolemObj->number_of_vars_to_elim));
	  fprintf(plot_fp, "%d\t%llu\t%f\t%s\t%llu\t", cegar_iteration_number, total_time_in_reverse_substitution_in_cegar, (float)sum_of_skolem_function_sizes_after_reverse_substitution/(float)(AIGBasedSkolemObj->number_of_vars_to_elim), order_string_to_print.c_str(), total_time_in_ordering);
	}

				
      if(enable_cegar)
	{
	  fprintf(plot_fp, "%llu\t%llu\t%llu\t%llu\t%llu\t%llu\t%llu\t%llu\t%llu\n", total_time_in_mu_evaluation_in_cegar, total_time_in_interpolant_computation_in_cegar, total_time_in_dontcare_optimization_in_cegar, total_time_in_generalization_in_mu_based_scheme_with_optimizations_in_cegar, total_time_in_initial_abstraction_generation_in_cegar, total_time_in_cegar_loops_in_cegar, total_time_in_sat_solving_in_cegar, total_time_in_true_sat_solving_in_cegar, total_time_in_false_sat_solving_in_cegar);
	}
      else
	{
	  fprintf(plot_fp, "%llu\t%llu\t%llu\t%llu\t%llu\t%llu\t%llu\t%llu\t%llu\n", total_time_in_mu_evaluation_in_cegar, total_time_in_interpolant_computation, total_time_in_dontcare_optimization_in_cegar, total_time_in_generalization_in_mu_based_scheme_with_optimizations_in_cegar, total_time_in_initial_abstraction_generation_in_cegar, total_time_in_cegar_loops_in_cegar, total_time_in_sat_solving_in_cegar, total_time_in_true_sat_solving_in_cegar, total_time_in_false_sat_solving_in_cegar);
	}

				
      fclose(plot_fp);

    }
#endif

#ifdef DEBUG_SKOLEM
  string map_file_name = "Ci_id_to_Ci_name_map.txt";
  FILE* map_fp = fopen(map_file_name.c_str(), "w+");
  assert(map_fp != NULL);

  for(map<int, string>::iterator map_it = Ci_id_to_Ci_name_map.begin(); map_it != Ci_id_to_Ci_name_map.end(); map_it++)
    {
      fprintf(map_fp, "\n%d\t%s\n", map_it->first, (map_it->second).c_str());	
    }
  fclose(map_fp);

  map_file_name = "Ci_name_to_Ci_number_map.txt";
  map_fp = fopen(map_file_name.c_str(), "w+");
  assert(map_fp != NULL);

  for(map<string, int>::iterator map_it = Ci_name_to_Ci_number_map.begin(); map_it != Ci_name_to_Ci_number_map.end(); map_it++)
    {
      fprintf(map_fp, "\n%s\t%d\n", (map_it->first).c_str(), map_it->second);	
    }
  fclose(map_fp);

  map_file_name = "Ci_name_to_Ci_label_map.txt";
  map_fp = fopen(map_file_name.c_str(), "w+");
  assert(map_fp != NULL);

  for(map<string, int>::iterator map_it = Ci_name_to_Ci_label_mapForGetCNF.begin(); map_it != Ci_name_to_Ci_label_mapForGetCNF.end(); map_it++)
    {
      fprintf(map_fp, "\n%s\t%d\n", (map_it->first).c_str(), map_it->second);	
    }
  fclose(map_fp);
  //char dump_file[100];
  //strcpy(dump_file, "dump.v");
  //Aig_ManDumpVerilog( aig_manager, dump_file );

  Aig_ManShow(aig_manager, 0, NULL); 
#endif
   
  //cout<< "\nEnd of TEST"<<endl;
  return return_value;

}
