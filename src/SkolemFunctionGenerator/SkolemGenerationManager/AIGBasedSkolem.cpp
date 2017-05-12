/***************************************************************************
FileName : AIGBasedSkolem.cc

SystemName: ParSyn : Parallel Boolean Funciton Synthesis Tool/ Parallel Skolem Function Generation Tool.

Authors: Shetal Shah, Ajith John
 
Affliation: IIT Bombay

Description: The file contains the code to synthesize boolean functions in sequential - specifically it contains the code for implementation of different Skolem function generation algorithms on a single processor
************************************************************/

#include "AIGBasedSkolem.hpp"


/**
 * Initializes pub_aig_manager
 * @param em
 */
AIGBasedSkolem::AIGBasedSkolem(Aig_Man_t* aig_manager)
{
	if (AIGBasedSkolem_instance != NULL) 
	{
    		cerr << "Error in AIGBasedSkolem::AIGBasedSkolem: Attempt to create multiple copies of AIGBasedSkolem" << endl;
    		cerr << "There should be only one copy of AIGBasedSkolem" << endl;
    		assert(0);
  	}

	pub_aig_manager = aig_manager;	
}



AIGBasedSkolem::~AIGBasedSkolem()
{
}


AIGBasedSkolem* AIGBasedSkolem::AIGBasedSkolem_instance = NULL;


AIGBasedSkolem* AIGBasedSkolem::getInstance(Aig_Man_t* aig_manager)
{
	if(AIGBasedSkolem_instance == NULL)
	{
		try
		{
			AIGBasedSkolem_instance = new AIGBasedSkolem(aig_manager);
		}
		catch(bad_alloc&) 
		{
		      cerr << "Memory allocation failure in AIGBasedSkolem::getInstance" << endl;
      		      assert(0);
    		}
  	}

	return AIGBasedSkolem_instance;
}


void AIGBasedSkolem::initializeFactorizedSkolemFunctionGenerator(set<Aig_Obj_t*> &Factors_new, list<string> &VariablesToEliminate)
{
	set<string> VariablesToEliminate_Set(VariablesToEliminate.begin(), VariablesToEliminate.end());
	set<Aig_Obj_t*> Factors;	
	if(drop_free_factors)
	{
		for(set<Aig_Obj_t*>::iterator factor_it = Factors_new.begin(); factor_it != Factors_new.end(); factor_it++)
		{
			Aig_Obj_t* factor = *factor_it;
			assert(factor != NULL);		

			set<string> support_factor;
			computeSupport(factor, support_factor, pub_aig_manager); 

			set<string> varstoelim_in_support_factor;
			set_intersection(support_factor.begin(), support_factor.end(), VariablesToEliminate_Set.begin(), VariablesToEliminate_Set.end(), inserter(varstoelim_in_support_factor, varstoelim_in_support_factor.begin()));

			if(!varstoelim_in_support_factor.empty())
			{
				Factors.insert(factor);
			}
		}//for
	}//if(drop_free_factors) ends here
	else
	{
		Factors = Factors_new;
	}
	// Let's first remove the free factors

	// Let's now 1) Remove variables which are not occuring in the factors
	// from the set of variables to be eliminated, and
	// 2) Insert the factors into FactorMatrix

	set<string> support;
	set<string> Final_VariablesToEliminate_Set;
	number_of_factors = Factors.size();

	// insert factors into FactorMatrix[1...number_of_factors]
	int factor_index = 1; // varies from 1 to number_of_factors
	
	#ifdef DEBUG_CEGAR
	string support_file_name = logfile_prefix;
	support_file_name += "support.txt";
	FILE* support_fp = fopen(support_file_name.c_str(), "w");
	assert(support_fp != NULL);
	printSet(VariablesToEliminate_Set, "Original_VariablesToEliminate_Set", support_fp);
	#endif

	map<string, int> VarsToElim_To_Factors_Map;
	map<Aig_Obj_t*, set<string> > VarsToElim_in_Supports_of_Factors;

	for(set<Aig_Obj_t*>::iterator factor_it = Factors.begin(); factor_it != Factors.end(); factor_it++)
	{
		Aig_Obj_t* factor = *factor_it;
		assert(factor != NULL);		

		set<string> support_factor;

		computeSupport(factor, support_factor, pub_aig_manager); // AIG Manager API Call

		int support_size = support_factor.size();
		original_factor_support_sizes.insert(make_pair(factor_index, support_size));

		copy(support_factor.begin(), support_factor.end(), inserter(support, support.end()));

		set<string> varstoelim_in_support_factor;
		set_intersection(support_factor.begin(), support_factor.end(), VariablesToEliminate_Set.begin(), VariablesToEliminate_Set.end(), inserter(varstoelim_in_support_factor, varstoelim_in_support_factor.begin()));
		int varstoelim_in_support_factor_size = varstoelim_in_support_factor.size();
		original_factor_varstoelim_sizes.insert(make_pair(factor_index, varstoelim_in_support_factor_size)); 
						
		int factor_size = computeSize(factor, pub_aig_manager); // AIG Manager API Call

		original_factor_sizes.insert(make_pair(factor_index, factor_size));	

		copy(varstoelim_in_support_factor.begin(), varstoelim_in_support_factor.end(), inserter(Final_VariablesToEliminate_Set, Final_VariablesToEliminate_Set.end()));

		for(set<string>::iterator varstoelim_it = varstoelim_in_support_factor.begin(); varstoelim_it != varstoelim_in_support_factor.end(); varstoelim_it++)
		{
			string variable_to_eliminate = *varstoelim_it;
			map<string, int>::iterator VarsToElim_To_Factors_Map_it = VarsToElim_To_Factors_Map.find(variable_to_eliminate);
			if(VarsToElim_To_Factors_Map_it == VarsToElim_To_Factors_Map.end()) 
			// variable_to_eliminate occuring for the first time
			{
				VarsToElim_To_Factors_Map.insert(make_pair(variable_to_eliminate, 1));
			}
			else
			{
				(VarsToElim_To_Factors_Map_it->second)++;
			}
		} 
		
		#ifdef DEBUG_CEGAR
		fprintf(support_fp,"\nfactor_%d\n",factor_index);
		cout << endl;
		printSet(support_factor, "support_factor", support_fp);
		cout << endl;
		printSet(varstoelim_in_support_factor, "varstoelim_in_support_factor", support_fp);
		cout << endl;		
		#endif	
		
		insertIntoOneDimensionalMatrix(FactorMatrix, number_of_factors, factor_index, factor, false);

		#ifdef RECORD_KEEP
		abstracted_factor_sizes.insert(make_pair(factor_index, factor_size));
		#endif
		

		if(order_of_elimination_of_variables == 3 || order_of_elimination_of_variables == 4)
		{	
			VarsToElim_in_Supports_of_Factors.insert(make_pair(factor, varstoelim_in_support_factor));
		}
						
		factor_index++;
	}

	original_support_size = support.size();	

	set_difference(support.begin(), support.end(), Final_VariablesToEliminate_Set.begin(), Final_VariablesToEliminate_Set.end(), inserter(variables_not_quantified, variables_not_quantified.begin()));
	original_variables = support;
	variables_quantified = Final_VariablesToEliminate_Set;
	
	
	#ifdef DEBUG_CEGAR
	printSet(support, "support", support_fp);
	printSet(Final_VariablesToEliminate_Set, "Final_VariablesToEliminate_Set", support_fp);
	printSet(variables_not_quantified, "variables_not_quantified", support_fp);
	printSet(variables_quantified, "variables_quantified", support_fp);
	fclose(support_fp);
	#endif

	#ifdef DETAILED_RECORD_KEEP
	struct timeval ordering_start_ms, ordering_finish_ms;
	gettimeofday (&ordering_start_ms, NULL); 
	#endif

	if(!mask_printing_cegar_details)
	{
		cout << "\nFinding the order of elimination of variables\n";
	}

	if(perform_cegar_on_arbitrary_boolean_formulas)
	{
		assert(order_of_elimination_of_variables == 0 || order_of_elimination_of_variables == 1 || order_of_elimination_of_variables == 2 || order_of_elimination_of_variables == 5 || order_of_elimination_of_variables == 6 || order_of_elimination_of_variables == 7);
	
		VariablesToEliminate.clear();
		for(list<string>::iterator list_it = Global_VariablesToEliminate.begin(); list_it != 		Global_VariablesToEliminate.end(); list_it++)
		{
			string var_to_elim_from_global_list = *list_it;
			if(Final_VariablesToEliminate_Set.find(var_to_elim_from_global_list) != Final_VariablesToEliminate_Set.end())//this is a variable to eliminate
			{
				VariablesToEliminate.push_back(var_to_elim_from_global_list);
			}
		}
		
	}
        else if(order_of_elimination_of_variables == 1) // least-factor-first order
	{
		map<int, set<string> > Factors_To_VarsToElim_Map;
		for(map<string, int>::iterator VarsToElim_To_Factors_Map_it = VarsToElim_To_Factors_Map.begin(); VarsToElim_To_Factors_Map_it != VarsToElim_To_Factors_Map.end(); VarsToElim_To_Factors_Map_it++)
		{
			string variable_to_eliminate = VarsToElim_To_Factors_Map_it->first;
			int number_of_factors_with_variable_to_eliminate = VarsToElim_To_Factors_Map_it->second;

			//cout << endl << variable_to_eliminate << "\t" << number_of_factors_with_variable_to_eliminate << endl;

			map<int, set<string> >::iterator Factors_To_VarsToElim_Map_it = Factors_To_VarsToElim_Map.find(number_of_factors_with_variable_to_eliminate);
			if(Factors_To_VarsToElim_Map_it == Factors_To_VarsToElim_Map.end())
			{
				set<string> variables_with_factor_count;
				variables_with_factor_count.insert(variable_to_eliminate);
				Factors_To_VarsToElim_Map.insert(make_pair(number_of_factors_with_variable_to_eliminate, variables_with_factor_count));
			}
			else
			{
				(Factors_To_VarsToElim_Map_it->second).insert(variable_to_eliminate);
			}
		}

		VariablesToEliminate.clear();
		for(map<int, set<string> >::iterator Factors_To_VarsToElim_Map_it = Factors_To_VarsToElim_Map.begin(); Factors_To_VarsToElim_Map_it != Factors_To_VarsToElim_Map.end(); Factors_To_VarsToElim_Map_it++)
		{
			//cout << endl << "factor_count = " << Factors_To_VarsToElim_Map_it->first <<"\tvariables = ";

			set<string> variables_with_factor_count = Factors_To_VarsToElim_Map_it->second;
			for(set<string>::iterator variable_it = variables_with_factor_count.begin(); variable_it != variables_with_factor_count.end(); variable_it++)
			{
				//cout << *variable_it << ", ";
				VariablesToEliminate.push_back(*variable_it);
			}
		}			
	}
	else if(order_of_elimination_of_variables == 2) // from external file
	{
		// we should read the order from the given file
		list<string> OrderOfVariableEliminationFromFile;
		obtainOrderOfVariableEliminationFromFile(OrderOfVariableEliminationFromFile);

		#ifdef DEBUG_SKOLEM 
		cout << endl << "OrderOfVariableEliminationFromFile" << endl;
		showList(OrderOfVariableEliminationFromFile);
		#endif

		VariablesToEliminate.clear();

		for(list<string>::iterator var_order_it = OrderOfVariableEliminationFromFile.begin(); var_order_it != OrderOfVariableEliminationFromFile.end(); var_order_it++)
		{
			string var_from_order_file = *var_order_it;
			if(Final_VariablesToEliminate_Set.find(var_from_order_file) != Final_VariablesToEliminate_Set.end()) // this is a var to elim
			{
				VariablesToEliminate.push_back(var_from_order_file);
			}
		}

		#ifdef DEBUG_SKOLEM 
		cout << endl << "VariablesToEliminate" << endl;
		showList(VariablesToEliminate);
		#endif
	}
	else if(order_of_elimination_of_variables == 0) // lexico-graphic order
	{
		VariablesToEliminate.clear();
		copy(Final_VariablesToEliminate_Set.begin(), Final_VariablesToEliminate_Set.end(), inserter(VariablesToEliminate, VariablesToEliminate.end()));
	}
	else if(order_of_elimination_of_variables == 3) // factor-graph-based order
	{
		VariablesToEliminate.clear();
		obtainFactorGraphBasedOrdering(VarsToElim_in_Supports_of_Factors, Final_VariablesToEliminate_Set, VariablesToEliminate);
	}
	else if(order_of_elimination_of_variables == 4) // reverse factor-graph-based order
	{
		VariablesToEliminate.clear();
		obtainFactorGraphBasedOrdering(VarsToElim_in_Supports_of_Factors, Final_VariablesToEliminate_Set, VariablesToEliminate);
		VariablesToEliminate.reverse();
	}
	else
	{
		cout << "\nUnknown order " << order_of_elimination_of_variables << endl;
		assert(false);
	}

	if(apply_tsietin_encoding_on_benchmarks)
	{
		assert(order_of_elimination_of_variables == 1);//Presently implemented
		// only for order_of_elimination_of_variables == 1
		pushTsietinVariablesUpInOrder(VariablesToEliminate);
	}

	#ifdef DETAILED_RECORD_KEEP
	gettimeofday (&ordering_finish_ms, NULL);
	total_time_in_ordering = ordering_finish_ms.tv_sec * 1000 + ordering_finish_ms.tv_usec / 1000;
   	total_time_in_ordering -= ordering_start_ms.tv_sec * 1000 + ordering_start_ms.tv_usec / 1000; 	
	#endif

	number_of_vars_to_elim = VariablesToEliminate.size();

	if(!mask_printing_cegar_details)
	{
		cout << "\nOrder of elimination of variables found\n";
	}

	#ifdef DETAILED_RECORD_KEEP
	if(!perform_cegar_on_arbitrary_boolean_formulas)
	{

		string order_file_name = logfile_prefix;

		if(order_of_elimination_of_variables == 0)
		{
			order_file_name += "lexico_graphic_order.txt";
		}
		else if(order_of_elimination_of_variables == 1)
		{
			order_file_name += "least_factor_first_order.txt";
		}
		else if(order_of_elimination_of_variables == 2)
		{
			order_file_name += "external_order.txt";
		}
		else if(order_of_elimination_of_variables == 3)
		{
			order_file_name += "factor_graph_based_order.txt";		
		}
		else if(order_of_elimination_of_variables == 4)
		{
			order_file_name += "reverse_factor_graph_based_order.txt";	
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

	}
	#endif

	if(exit_after_order_finding)
	{
		return;
	}


	#ifdef DEBUG_SKOLEM
	cout << "number_of_factors = " << number_of_factors << endl;
	cout << "number_of_vars_to_elim = " << number_of_vars_to_elim << endl;
	#endif	

	// create the var_name_to_var_index_map and var_index_to_var_name_map
	int var_index = 1;
	for(list<string>::iterator list_it = VariablesToEliminate.begin(); list_it != VariablesToEliminate.end(); list_it++)
	{
		insertIntoVarNameToVarIndexMap(var_name_to_var_index_map, *list_it, var_index);
		insertIntoVarIndexToVarNameMap(var_index_to_var_name_map, var_index, *list_it);

		#ifdef DEBUG_SKOLEM
		cout << "(" << *list_it << ", " << var_index << ") inserted into maps "<< endl;
		#endif	

		var_index++;
	}


	if(enable_cegar)
	{
		if(factorizedskolem_applied_on_disjunction)
		{
			conjunction_of_factors = createNot(createAnd(Factors, pub_aig_manager), pub_aig_manager);
			// we have ~(f1 \wedge f2) here
		}
		else
		{
			conjunction_of_factors = createAnd(Factors, pub_aig_manager);
		}

		Aig_Obj_t* conjunction_of_factors_CO = Aig_ObjCreateCo( pub_aig_manager, conjunction_of_factors ); // to aviod unwanted cleanup of conjunction_of_factors
		assert(conjunction_of_factors_CO != NULL);
		intermediate_cos_created.insert(conjunction_of_factors_CO);

		// Note that BadSets[1] = false
		Aig_Obj_t* bad_set_1 = createFalse(pub_aig_manager);
		assert(bad_set_1 != NULL);
		Aig_Obj_t* bad_set_1_CO = Aig_ObjCreateCo( pub_aig_manager, bad_set_1 ); // to aviod 
		// unwanted cleanup of bad_set_1
		assert(bad_set_1_CO != NULL);
		intermediate_cos_created.insert(bad_set_1_CO);

		#ifdef DEBUG_SKOLEM
		cout << "\nbad_set_1 computed\n";
		writeFormulaToFile(pub_aig_manager, bad_set_1, "bad_set", ".v", 1, cegar_iteration_number);	
		#endif

		// Enter into matrix
		insertIntoOneDimensionalMatrix(BadSets, number_of_vars_to_elim, 1, bad_set_1, false);			

	}
	else 
	{
		aig_bad_set = createFalse(pub_aig_manager);	// AIG Manager API Call			
	}
	
	

	if(print_factor_graph)
	{
		if(false)
		{
			printFactorGraphAsData(Final_VariablesToEliminate_Set);
		}
		else
		{
			cout << "\nPrinting the factor graph in dot format\n";

			printFactorGraph(Final_VariablesToEliminate_Set);
		}
	}

	if(exit_after_factor_graph_generation)
	{
		return;
	}


	if(enable_cegar)
	{
		if(use_bads_in_unified_cegar)
		{
			assert(use_cbzero_in_unified_cegar);

			use_bads_in_unified_cegar_aig = createTrue(pub_aig_manager);
			use_cbzero_in_unified_cegar_aig = createTrue(pub_aig_manager);
		}
		else
		{
			assert(!use_cbzero_in_unified_cegar);

			use_bads_in_unified_cegar_aig = createFalse(pub_aig_manager);
			use_cbzero_in_unified_cegar_aig = createFalse(pub_aig_manager);
		}

		Aig_Obj_t* use_bads_in_unified_cegar_aig_CO = Aig_ObjCreateCo(pub_aig_manager,  use_bads_in_unified_cegar_aig); 
		assert(use_bads_in_unified_cegar_aig_CO != NULL);
		intermediate_cos_created.insert(use_bads_in_unified_cegar_aig_CO);

		Aig_Obj_t* use_cbzero_in_unified_cegar_aig_CO = Aig_ObjCreateCo(pub_aig_manager,  use_cbzero_in_unified_cegar_aig); 
		assert(use_cbzero_in_unified_cegar_aig_CO != NULL);
		intermediate_cos_created.insert(use_cbzero_in_unified_cegar_aig_CO);

		if(use_assumptions_in_unified_cegar)
		{
			assumptions_flag = 1;
		}
		else
		{
			assumptions_flag = 0;
		}
		
	}
	

	#ifdef RECORD_KEEP
		string record_file;
		record_file = logfile_prefix;
		record_file += "skolem_function_generation_details.txt";
		FILE* record_fp = fopen(record_file.c_str(), "a+");
		assert(record_fp != NULL);

		if(perform_cegar_on_arbitrary_boolean_formulas && !mask_printing_details_file)
		{
			fprintf(record_fp, "\n\nDetails of CegarSkolem Call#:%d (Depth from root = %d)\n\n", number_of_cegarskolem_calls_on_arbitrary_boolean_formulas, depth_from_root_in_cegarskolem_call_on_arbitrary_boolean_formulas); 
		}

		if(!mask_printing_details_file)
		{
			fprintf(record_fp, "number of factors = %d\n", number_of_factors); 
			fprintf(record_fp, "number of variables to eliminate = %d\n", number_of_vars_to_elim); 

			// print details of original factors
			fprintf(record_fp, "number of variables = %d\n", original_support_size);
		}

		if(!mask_printing_cegar_details)
		{
			fprintf(record_fp, "\naig sizes of factors = ");
		}

		unsigned long long int total_of_factor_sizes = 0;
		unsigned long long int total_of_abstracted_factor_sizes = 0;
		unsigned long long int total_of_factor_support_sizes = 0;
		unsigned long long int total_of_factor_varstoelim_sizes = 0;
		unsigned long long int total_of_skyline_sizes = 0;
		
		for(map<int, int>::iterator original_factor_sizes_it = original_factor_sizes.begin(); original_factor_sizes_it != original_factor_sizes.end(); original_factor_sizes_it++)
		{
			if(!mask_printing_cegar_details)
			{
				fprintf(record_fp, "%d, ", original_factor_sizes_it->second);
			}

			total_of_factor_sizes = total_of_factor_sizes + original_factor_sizes_it->second;

			if(max_factor_size == -1)
			{
				max_factor_size = original_factor_sizes_it->second;
				min_factor_size = original_factor_sizes_it->second;
			}
			else if(original_factor_sizes_it->second > max_factor_size)
			{
				max_factor_size = original_factor_sizes_it->second;
			}
			else if(original_factor_sizes_it->second < min_factor_size)
			{
				min_factor_size = original_factor_sizes_it->second;
			}			
		} 

		if(!mask_printing_cegar_details)
		{
			fprintf(record_fp, "\n\n");
		}

		/*fprintf(record_fp, "A_f = ");
		for(map<int, int>::iterator abstracted_factor_sizes_it = abstracted_factor_sizes.begin(); abstracted_factor_sizes_it != abstracted_factor_sizes.end(); abstracted_factor_sizes_it++)
		{
			fprintf(record_fp, "%d, ", abstracted_factor_sizes_it->second);
			total_of_abstracted_factor_sizes = total_of_abstracted_factor_sizes + abstracted_factor_sizes_it->second;
		} 
		fprintf(record_fp, "\n\n");*/
		
		if(!mask_printing_cegar_details)
		{
			fprintf(record_fp, "variables in factors = ");
		}

		for(map<int, int>::iterator original_factor_support_sizes_it = original_factor_support_sizes.begin(); original_factor_support_sizes_it != original_factor_support_sizes.end(); original_factor_support_sizes_it++)
		{
			if(!mask_printing_cegar_details)
			{
			fprintf(record_fp, "%d, ", original_factor_support_sizes_it->second);
			}

			total_of_factor_support_sizes = total_of_factor_support_sizes + original_factor_support_sizes_it->second;
		} 

		if(!mask_printing_cegar_details)
		{
			fprintf(record_fp, "\n\n");
			fprintf(record_fp, "variables to eliminate in factors = ");
		}

		for(map<int, int>::iterator original_factor_varstoelim_sizes_it = original_factor_varstoelim_sizes.begin(); original_factor_varstoelim_sizes_it != original_factor_varstoelim_sizes.end(); original_factor_varstoelim_sizes_it++)
		{
			if(!mask_printing_cegar_details)
			{
				fprintf(record_fp, "%d, ", original_factor_varstoelim_sizes_it->second);
			}

			total_of_factor_varstoelim_sizes = total_of_factor_varstoelim_sizes + original_factor_varstoelim_sizes_it->second;


			if(max_factor_varstoelim_size == -1)
			{
				max_factor_varstoelim_size = original_factor_varstoelim_sizes_it->second;
				min_factor_varstoelim_size = original_factor_varstoelim_sizes_it->second;
			}
			else if(original_factor_varstoelim_sizes_it->second > max_factor_varstoelim_size)
			{
				max_factor_varstoelim_size = original_factor_varstoelim_sizes_it->second;
			}
			else if(original_factor_varstoelim_sizes_it->second < min_factor_varstoelim_size)
			{
				min_factor_varstoelim_size = original_factor_varstoelim_sizes_it->second;
			}

		} 

		if(!mask_printing_cegar_details)
		{
			fprintf(record_fp, "\n\n");
		}

		number_of_compose_operations_for_variable = 0;
		ComposeTime = 0;
		number_of_boolean_operations_for_variable = 0;
		BooleanOpTime = 0;
		number_of_support_operations_for_variable = 0;
		
		if(!mask_printing_cegar_details)
		{		
			if(enable_cegar)
			{
				if(perform_cegar_on_arbitrary_boolean_formulas)
				{

					#ifdef RECORD_KEEP
						fprintf(record_fp, "i: index of variable to be eliminated\n");
						fprintf(record_fp, "v: name of variable to be eliminated\n");
						fprintf(record_fp, "T_v: Time (in milliseconds) to generate the initial Skolem function for the variable\n");
						fprintf(record_fp, "M_v: Size of the initial Skolem function for the variable before don't-care optimization\n");
						fprintf(record_fp, "N_v: Size of the initial Skolem function for the variable after don't-care optimization\n");
						fprintf(record_fp, "r1_v: Sizes of elements in r1 of variable\n");
						fprintf(record_fp, "r0_v: Sizes of elements in r0 of variable\n");
						fprintf(record_fp, "\n\n");
						fprintf(record_fp, "i\tv\tT_v\tM_v\tN_v\tr1_v\tr0_v\n\n");
					#endif				

				}
				else
				{
					#ifdef RECORD_KEEP
						fprintf(record_fp, "i: index of variable to be eliminated\n");
						fprintf(record_fp, "v: name of variable to be eliminated\n");
						fprintf(record_fp, "F_v: Number of factors with the variable to be eliminated\n");
						fprintf(record_fp, "T_v: Time (in milliseconds) to generate the initial Skolem function for the variable\n");
						fprintf(record_fp, "M_v: Size of the initial Skolem function for the variable before don't-care optimization\n");
						fprintf(record_fp, "N_v: Size of the initial Skolem function for the variable after don't-care optimization\n");
						fprintf(record_fp, "I_v: Indices of factors containing the variable\n");
						fprintf(record_fp, "X_v: Sizes of factors containing the variable\n");
						fprintf(record_fp, "Cb1_v: Sizes of elements in Cb1 of variable\n");
						fprintf(record_fp, "Cb0_v: Sizes of elements in Cb0 of variable\n");
						fprintf(record_fp, "B_v: Size of Bad of variable\n");
						fprintf(record_fp, "\n\n");
						fprintf(record_fp, "i\tv\tF_v\tT_v\tM_v\tN_v\tI_v\tX_v\tCb1_v\tCb0_v\tB_v\n\n");
					#endif
				
				}
			}
			else
			{
				if(use_interpolant_as_skolem_function)
				{
					#ifdef RECORD_KEEP
						fprintf(record_fp, "i: index of variable to be eliminated\n");
						fprintf(record_fp, "v: name of variable to be eliminated\n");
						fprintf(record_fp, "F_v: Number of factors with the variable to be eliminated\n");
						fprintf(record_fp, "T_v: Time (in milliseconds) to eliminate the variable\n");
						fprintf(record_fp, "N_v: Size of the skolem function psi_i = interpolant between alpha_i and beta_i\n");
						fprintf(record_fp, "Q_v: Size of the quantified result q_i = conjunction of factors with variable substituted by skolem function\n");
						fprintf(record_fp, "A_v: Size of alpha_i\n");
						fprintf(record_fp, "B_v: Size of beta_i\n");
						fprintf(record_fp, "I_T: Time consumed in computing interpolant between alpha_i and beta_i\n");
						fprintf(record_fp, "cmp_v: Number of composes in elimination of the variable\n");
						fprintf(record_fp, "cmp_T: Time consumed in composes in elimination of the variable\n");
						fprintf(record_fp, "B_v: Number of boolean operations in elimination of the variable\n");
						fprintf(record_fp, "B_T: Time consumed in boolean operations in elimination of the variable\n");
						fprintf(record_fp, "S_v: Number of support operations in elimination of the variable\n");
						fprintf(record_fp, "S_T: Time consumed in support operations in elimination of the variable\n");
						fprintf(record_fp, "I_v: Indices of factors containing the variable to be eliminated\n");
						fprintf(record_fp, "X_v: Sizes of factors containing the variable to be eliminated\n");
						fprintf(record_fp, "\n\n");
						fprintf(record_fp, "i\tv\tF_v\tT_v\tN_v\tA_v\tB_v\tI_T\tQ_v\tcmp_v\tcmp_T\tB_v\tB_T\tS_v\tS_T\tI_v\tX_v\n\n");
					#endif
				}
				else
				{
					#ifdef RECORD_KEEP
						fprintf(record_fp, "i: index of variable to be eliminated\n");
						fprintf(record_fp, "v: name of variable to be eliminated\n");
						fprintf(record_fp, "F_v: Number of factors with the variable to be eliminated\n");
						fprintf(record_fp, "T_v: Time (in milliseconds) to eliminate the variable\n");
						fprintf(record_fp, "N_v: Size of the skolem function psi_i = conjunction of co-factor-1's of factors\n");
						fprintf(record_fp, "Q_v: Size of the quantified result q_i = (conjunction of co-factor-1's of factors) or (conjunction of co-factor-0's of factors)\n");
						fprintf(record_fp, "cmp_v: Number of composes in elimination of the variable\n");
						fprintf(record_fp, "cmp_T: Time consumed in composes in elimination of the variable\n");
						fprintf(record_fp, "B_v: Number of boolean operations in elimination of the variable\n");
						fprintf(record_fp, "B_T: Time consumed in boolean operations in elimination of the variable\n");
						fprintf(record_fp, "S_v: Number of support operations in elimination of the variable\n");
						fprintf(record_fp, "S_T: Time consumed in support operations in elimination of the variable\n");
						fprintf(record_fp, "I_v: Indices of factors containing the variable to be eliminated\n");
						fprintf(record_fp, "X_v: Sizes of factors containing the variable to be eliminated\n");
						fprintf(record_fp, "\n\n");
						fprintf(record_fp, "i\tv\tF_v\tT_v\tN_v\tQ_v\tcmp_v\tcmp_T\tB_v\tB_T\tS_v\tS_T\tI_v\tX_v\n\n");
					#endif
				}
			}			
		}//if(!mask_printing_cegar_details)

		fclose(record_fp);


		string plot_file;
		plot_file = logfile_prefix;
		plot_file += "skolem_function_generation_details_to_plot.txt";
		FILE* plot_fp = fopen(plot_file.c_str(), "a+");
		assert(plot_fp != NULL);

		if(!perform_cegar_on_arbitrary_boolean_formulas)
		{		
			fprintf(plot_fp, "\n%s\t%s\t%s", benchmark_type.c_str(), benchmark_name.c_str(), machine.c_str());
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

		if(!perform_cegar_on_arbitrary_boolean_formulas)
		{
			fprintf(plot_fp, "\t%s", algorithm_string.c_str());
			fprintf(plot_fp, "\t%d\t%d\t%d", number_of_factors, number_of_vars_to_elim, original_support_size);
		}

		if(conjunction_of_factors == NULL)
		{
			conjunction_of_factors = createAnd(Factors, pub_aig_manager); // AIG Manager API Call
		}
		assert(conjunction_of_factors != NULL);
		size_of_conjunction_of_factors = computeSize(conjunction_of_factors, pub_aig_manager); // AIG Manager API Call	
		if(!perform_cegar_on_arbitrary_boolean_formulas)
		{
			fprintf(plot_fp, "\t%d", size_of_conjunction_of_factors);
		}

		float avg_of_factor_sizes = (float)total_of_factor_sizes/(float)number_of_factors;
		float avg_of_abstracted_factor_sizes = (float)total_of_abstracted_factor_sizes/(float)number_of_factors;
		float avg_of_factor_support_sizes = (float)total_of_factor_support_sizes/(float)number_of_factors;
		float avg_of_factor_varstoelim_sizes = (float)total_of_factor_varstoelim_sizes/(float)number_of_factors;
		float avg_of_skyline_sizes = (float)total_of_skyline_sizes/(float)number_of_vars_to_elim;

		if(!perform_cegar_on_arbitrary_boolean_formulas)
		{
			if(order_of_elimination_of_variables == 3 || order_of_elimination_of_variables == 4)
			{
					fprintf(plot_fp, "\t%f\t%f\t%f", avg_of_factor_sizes, avg_of_factor_support_sizes, avg_of_factor_varstoelim_sizes);
			}
			else
			{
				//fprintf(plot_fp, "\t%f\t%f\t%f\t%f\t%f", avg_of_factor_sizes, avg_of_abstracted_factor_sizes, avg_of_factor_support_sizes, avg_of_factor_varstoelim_sizes, avg_of_skyline_sizes);
					fprintf(plot_fp, "\t%f\t%f\t%f", avg_of_factor_sizes, avg_of_factor_support_sizes, avg_of_factor_varstoelim_sizes);
			}

			fprintf(plot_fp, "\t%d\t%d\t%d\t%d", max_factor_size, min_factor_size, max_factor_varstoelim_size, min_factor_varstoelim_size);
		}

		fclose(plot_fp);

		
	#endif		
}


void AIGBasedSkolem::factorizedSkolemFunctionGenerator(set<Aig_Obj_t*> &Factors, list<string> &VariablesToEliminate)
{
	struct timeval cegar_step_start_ms, cegar_step_finish_ms;
	gettimeofday (&cegar_step_start_ms, NULL); 

	#ifdef DETAILED_RECORD_KEEP
	unsigned long long int step_ms;
	struct timeval step_start_ms, step_finish_ms;
	gettimeofday (&step_start_ms, NULL); 	
	#endif

	initializeFactorizedSkolemFunctionGenerator(Factors, VariablesToEliminate);

	#ifdef DETAILED_RECORD_KEEP
	gettimeofday (&step_finish_ms, NULL);
   	step_ms = step_finish_ms.tv_sec * 1000 + step_finish_ms.tv_usec / 1000;
   	step_ms -= step_start_ms.tv_sec * 1000 + step_start_ms.tv_usec / 1000;
	if(!mask_printing_cegar_details)
	{
		cout << "\ninitializeFactorizedSkolemFunctionGenerator finished in " << step_ms << " milliseconds\n";
	}

	total_time_in_generator_initialization = step_ms;
	#endif

	size_computation_time_in_initialization = total_time_in_compute_size;	
	total_time_in_generator_initialization = total_time_in_generator_initialization - size_computation_time_in_initialization;

	if(!mask_printing_cegar_details)
	{
		cout << "\n#factors = " << number_of_factors << "\t#variables_to_eliminate = " << number_of_vars_to_elim << endl;
	}

	if(exit_after_order_finding || exit_after_factor_graph_generation)
	{
		return;
	}

	if(enable_cegar)
	{
		// Generate initial Skolem functions, bad sets, cannot-be-1 and cannot-be-0 sets
		if(perform_cegar_on_arbitrary_boolean_formulas)
		{
			// Here we already have the initial cannot-be-1 and cannot-be-0 sets
			// Let's take list_of_r0s and list_of_r1s of each factor. 
			// From these lists, construct the r0's and r1's of all variables

			int factor_index = 1;
			map<int, vector<Aig_Obj_t*> > factor_index_to_list_of_r0s_map;
			map<int, vector<Aig_Obj_t*> > factor_index_to_list_of_r1s_map;

			FactorsWithVariable.clear();

			for(set<Aig_Obj_t*>::iterator Factors_it = Factors.begin(); Factors_it != Factors.end(); Factors_it++)
			{
				Aig_Obj_t* given_factor;
				given_factor = *Factors_it;
				assert(given_factor != NULL);

				//#ifdef DEBUG_PAR
				//cout << "\ngiven_factor = " << given_factor << endl;
				//#endif
				
				vector<Aig_Obj_t*> list_of_r0s_of_factor;
				vector<Aig_Obj_t*> list_of_r1s_of_factor;
				call_type factor_polarity;

				if(factorizedskolem_applied_on_disjunction)
				{
					factor_polarity = negated;
				}
				else
				{
					factor_polarity = original;
				}
				
				getEntryFromR0HashTable(factor_polarity, given_factor, list_of_r0s_of_factor);
				getEntryFromR1HashTable(factor_polarity, given_factor, list_of_r1s_of_factor);

				//#ifdef DEBUG_PAR
				//cout << "\nlist_of_r0s_of_factor.size() = " << list_of_r0s_of_factor.size() << endl;
				//cout << "\nlist_of_r1s_of_factor.size() = " << list_of_r1s_of_factor.size() << endl;
				//#endif
				
				factor_index_to_list_of_r0s_map.insert(make_pair(factor_index, list_of_r0s_of_factor));
				factor_index_to_list_of_r1s_map.insert(make_pair(factor_index, list_of_r1s_of_factor));

				FactorsWithVariable.insert(factor_index); // assume that all variables appear in all factors

				factor_index++;
			}//consider each factor ends here

			// We have list_of_r0s and list_of_r1s of each factor now
			// From these lists construct the final r0's, r1's, and skolem functions

			for(list<string>::iterator list_it = VariablesToEliminate.begin(); list_it != VariablesToEliminate.end(); list_it++)
			{
				string var_to_elim = *list_it;
				int var_to_elim_index = searchVarNameToVarIndexMap(var_name_to_var_index_map, var_to_elim);
				assert(var_to_elim_index != -1);

				int location_of_var_to_elim = findLocationOfVariableInGlobalVariablesToEliminate(var_to_elim);

				#ifdef DEBUG_SKOLEM
				cout << "\nvar_to_elim = " << var_to_elim << "\tvar_to_elim_index = " << var_to_elim_index << "\tlocation_of_var_to_elim = " << location_of_var_to_elim << endl;
				#endif

				if(checkTimeOut()) // check for time-out
				{
					cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::factorizedSkolemFunctionGenerator\n";
					timed_out = true; // timed_out flag set
					return;
				}		

				#ifdef DEBUG_SKOLEM
				cout << "\nGetting initial Skolem functions, cannot-be-1 and cannot-be-0 sets of x_" << var_to_elim_index << " from hash tables" << endl;
				#endif

				#ifdef RECORD_KEEP
				unsigned long long int duration_ms;
				struct timeval start_ms, finish_ms;
				gettimeofday (&start_ms, NULL); 
				#endif

				#ifdef DETAILED_RECORD_KEEP
				gettimeofday (&step_start_ms, NULL); 	
				#endif
		
				Aig_Obj_t* skolem_function;
				
				if(factorizedskolem_applied_on_disjunction)
				{

					skolem_function = computeInitialSkolemFunctionsAndCannotBeSetsFromHashTableEntriesForDisjunction(var_to_elim_index, location_of_var_to_elim, factor_index_to_list_of_r0s_map, factor_index_to_list_of_r1s_map);

				}
				else
				{
					skolem_function = computeInitialSkolemFunctionsAndCannotBeSetsFromHashTableEntries(var_to_elim_index, location_of_var_to_elim, factor_index_to_list_of_r0s_map, factor_index_to_list_of_r1s_map);

				}

				if(checkTimeOut()) // check for time-out
				{
					cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::factorizedSkolemFunctionGenerator\n";
					timed_out = true; // timed_out flag set
					return;
				}

				assert(skolem_function != NULL);

				#ifdef DETAILED_RECORD_KEEP
				gettimeofday (&step_finish_ms, NULL);
				step_ms = step_finish_ms.tv_sec * 1000 + step_finish_ms.tv_usec / 1000;
				step_ms -= step_start_ms.tv_sec * 1000 + step_start_ms.tv_usec / 1000;
				if(!mask_printing_cegar_details)
				{
					cout << "\ncomputeInitialSkolemFunctionsAndCannotBeSetsFromHashTableEntries finished in " << step_ms << " milliseconds\n";
				}
				#endif


				#ifdef RECORD_KEEP
				gettimeofday (&finish_ms, NULL);
			   	duration_ms = finish_ms.tv_sec * 1000 + finish_ms.tv_usec / 1000;
			   	duration_ms -= start_ms.tv_sec * 1000 + start_ms.tv_usec / 1000;
				SkolemFunctionGenTime = duration_ms;

				SkolemFunctionSize = computeSize(skolem_function, pub_aig_manager); // AIG Manager API Call	
			   	#endif

				if(!mask_printing_cegar_details)
				{
					cout << "\nabstract skolem_function_" << var_to_elim_index << ", i.e., abstract skolem function for " << var_to_elim << " computed\n";
				}

				#ifdef RECORD_KEEP
				string record_file;
				record_file = logfile_prefix;
				record_file += "skolem_function_generation_details.txt";
				FILE* record_fp = fopen(record_file.c_str(), "a+");
				assert(record_fp != NULL);

				if(!mask_printing_cegar_details)
				{
					fprintf(record_fp, "%d\t%s\t%llu\t%d\t%d\t", var_to_elim_index, var_to_elim.c_str(), SkolemFunctionGenTime, InitialSkolemFunctionSizeBeforeOptimization, SkolemFunctionSize);
				}
							
				for(list<int>::iterator size_it = sizes_of_cannot_be_one_elements_of_variable.begin(); size_it != sizes_of_cannot_be_one_elements_of_variable.end(); size_it++)
				{
					if(!mask_printing_cegar_details)
					{
						fprintf(record_fp, "%d,", *size_it);			
					}
				}		

				if(!mask_printing_cegar_details)
				{
					fprintf(record_fp, "\t");
				}

				sizes_of_cannot_be_one_elements_of_variable.clear();

			
				for(list<int>::iterator size_it = sizes_of_cannot_be_zero_elements_of_variable.begin(); size_it != sizes_of_cannot_be_zero_elements_of_variable.end(); size_it++)
				{
					if(!mask_printing_cegar_details)
					{
						fprintf(record_fp, "%d,", *size_it);			
					}
				}		

				if(!mask_printing_cegar_details)
				{
					fprintf(record_fp, "\t");
				}

				sizes_of_cannot_be_zero_elements_of_variable.clear();

				if(!mask_printing_cegar_details)
				{
					fprintf(record_fp, "\n\n");
				}

				number_of_compose_operations_for_variable = 0;
				ComposeTime = 0;
		
				fclose(record_fp);
				#endif	

				location_of_var_to_elim++;
			}//for ends here			
			
		}
		else // obtain the the initial cannot-be-1 and cannot-be-0 sets
		{

			for(int var_to_elim_index = 1; var_to_elim_index <= number_of_vars_to_elim; var_to_elim_index++)
			{
				if(checkTimeOut()) // check for time-out
				{
					cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::factorizedSkolemFunctionGenerator\n";
					timed_out = true; // timed_out flag set
					return;
				}		

				if(maximum_index_to_eliminate != -1) // to stop computation in between
				{
					if(var_to_elim_index > maximum_index_to_eliminate)
					{
						cout << "\nLet us stop here...\n";
						return;
					}			
				}

				#ifdef DEBUG_SKOLEM
				cout << "\ncomputing initial Skolem functions, bad sets, cannot-be-1 and cannot-be-0 sets of x_" << var_to_elim_index << endl;
				#endif

				#ifdef PRINT_VERY_DETAILED_RECORDS_ON_SCREEN
				cout << "\ncomputing initial Skolem functions, bad sets, cannot-be-1 and cannot-be-0 sets of x_" << var_to_elim_index << endl;
				#endif

				#ifdef RECORD_KEEP
				unsigned long long int duration_ms;
				struct timeval start_ms, finish_ms;
				gettimeofday (&start_ms, NULL); 
				#endif

				#ifdef DETAILED_RECORD_KEEP
				gettimeofday (&step_start_ms, NULL); 	
				#endif

				findFactorsWithVariable(var_to_elim_index);// find the set of factors containing the variable			

				if(checkTimeOut()) // check for time-out
				{
					cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::factorizedSkolemFunctionGenerator\n";
					timed_out = true; // timed_out flag set
					return;
				}

				#ifdef DETAILED_RECORD_KEEP
				gettimeofday (&step_finish_ms, NULL);
				step_ms = step_finish_ms.tv_sec * 1000 + step_finish_ms.tv_usec / 1000;
				step_ms -= step_start_ms.tv_sec * 1000 + step_start_ms.tv_usec / 1000;

				if(!mask_printing_cegar_details)
				{
					cout << "\nfindFactorsWithVariable finished in " << step_ms << " milliseconds\n";
		
					cout << "\nnumber of factors containing the variable = " << FactorsWithVariable.size() << endl; 
				}
			
				NumberOfFactors = FactorsWithVariable.size();
				FactorFindingTime = step_ms;
				#endif

				#ifdef DETAILED_RECORD_KEEP
				gettimeofday (&step_start_ms, NULL); 	
				#endif
		
				Aig_Obj_t* skolem_function = computeInitialSkolemFunctionsBadSetsAndCannotBeSets(var_to_elim_index);

				if(checkTimeOut()) // check for time-out
				{
					cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::computeInitialSkolemFunctionsBadSetsAndCannotBeSets\n";
					timed_out = true; // timed_out flag set
					return;
				}

				assert(skolem_function != NULL);

				#ifdef DETAILED_RECORD_KEEP
				gettimeofday (&step_finish_ms, NULL);
				step_ms = step_finish_ms.tv_sec * 1000 + step_finish_ms.tv_usec / 1000;
				step_ms -= step_start_ms.tv_sec * 1000 + step_start_ms.tv_usec / 1000;


				if(!mask_printing_cegar_details)
				{
					cout << "\ncomputeInitialSkolemFunctionsBadSetsAndCannotBeSets finished in " << step_ms << " milliseconds\n";
				}
				#endif


				#ifdef DETAILED_RECORD_KEEP
				gettimeofday (&step_start_ms, NULL); 	
				#endif
		
				if(var_to_elim_index != number_of_vars_to_elim) // We need to update the factor matrix
				{	
					#ifdef DEBUG_SKOLEM
					cout << "\nupdating factors\n";
					#endif

					updateFactorsWithoutComposition(var_to_elim_index);
				}

				if(checkTimeOut()) // check for time-out
				{
					cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::factorizedSkolemFunctionGenerator\n";
					timed_out = true; // timed_out flag set
					return;
				}

				#ifdef DETAILED_RECORD_KEEP
				gettimeofday (&step_finish_ms, NULL);
				step_ms = step_finish_ms.tv_sec * 1000 + step_finish_ms.tv_usec / 1000;
				step_ms -= step_start_ms.tv_sec * 1000 + step_start_ms.tv_usec / 1000;
				if(!mask_printing_cegar_details)
				{
					cout << "\nupdateFactors finished in " << step_ms << " milliseconds\n";
				}
				NextFactorGenTime = step_ms;
				#endif

				#ifdef DEBUG_SKOLEM
				cout << "\nclearing variable-specific data-structures\n";
				#endif

				#ifdef DETAILED_RECORD_KEEP
				gettimeofday (&step_start_ms, NULL); 	
				#endif
		
				clearVariableSpecificDataStructures();

				#ifdef DETAILED_RECORD_KEEP
				gettimeofday (&step_finish_ms, NULL);
				step_ms = step_finish_ms.tv_sec * 1000 + step_finish_ms.tv_usec / 1000;
				step_ms -= step_start_ms.tv_sec * 1000 + step_start_ms.tv_usec / 1000;
				if(!mask_printing_cegar_details)
				{
					cout << "\nclearVariableSpecificDataStructures finished in " << step_ms << " milliseconds\n";
				}
				#endif

				#ifdef RECORD_KEEP
				gettimeofday (&finish_ms, NULL);
			   	duration_ms = finish_ms.tv_sec * 1000 + finish_ms.tv_usec / 1000;
			   	duration_ms -= start_ms.tv_sec * 1000 + start_ms.tv_usec / 1000;
				SkolemFunctionGenTime = duration_ms;

				SkolemFunctionSize = computeSize(skolem_function, pub_aig_manager); // AIG Manager API Call	
			   	#endif

				string var_to_elim = searchVarIndexToVarNameMap(var_index_to_var_name_map, var_to_elim_index);
				if(!mask_printing_cegar_details)
				{
					cout << "\nabstract skolem_function_" << var_to_elim_index << ", i.e., abstract skolem function for " << var_to_elim << " computed\n";
				}

				#ifdef RECORD_KEEP
				string record_file;
				record_file = logfile_prefix;
				record_file += "skolem_function_generation_details.txt";
				FILE* record_fp = fopen(record_file.c_str(), "a+");
				assert(record_fp != NULL);

				total_of_skyline_sizes_in_least_cost_ordering = 0;
				sum_of_number_of_factors_containing_variable = sum_of_number_of_factors_containing_variable + NumberOfFactors;
				//sum_of_skolem_function_sizes = 0; // we will find this before reverse-substitution
				total_number_of_compose_operations = total_number_of_compose_operations + number_of_compose_operations_for_variable;
				total_time_in_compose_operations = total_time_in_compose_operations + ComposeTime;
				total_time_in_alpha_combined = total_time_in_alpha_combined + AlphaCombGenTime;
				total_time_in_delta_part = total_time_in_delta_part + DeltaPartGenTime;
				total_time_in_delta_combined = total_time_in_delta_combined + DeltaCombGenTime;
				total_time_in_next_factor = total_time_in_next_factor + NextFactorGenTime;
				total_time_in_correction_part = 0;
				number_of_variables_eliminated = var_to_elim_index;
				sum_of_numbers_of_affecting_factors = 0;

				//fprintf(record_fp, "%s\t%d\t%llu\t%d\t%d\t", var_to_elim.c_str(), NumberOfFactors, SkolemFunctionGenTime, SkolemFunctionSize, AlphaPartSize); // more detailed output

				fprintf(record_fp, "%d\t%s\t%d\t%llu\t%d\t%d\t", var_to_elim_index, var_to_elim.c_str(), NumberOfFactors, SkolemFunctionGenTime, InitialSkolemFunctionSizeBeforeOptimization, SkolemFunctionSize);
				if(print_factor_graph)
				{
					string fg_file_name = benchmark_name_without_extension;
					fg_file_name += "_factorized";					
					fg_file_name += "_factor_graph.dat";
					FILE* fg_fp = fopen(fg_file_name.c_str(), "a+");
					assert(fg_fp != NULL);			
					for(list<int>::iterator affect_it = FactorsAffectingSkolemFunction.begin(); affect_it != FactorsAffectingSkolemFunction.end(); affect_it++)
					{
						fprintf(fg_fp, "%d\t%d\n", *affect_it, var_to_elim_index);			
					}				
					fclose(fg_fp);
				}
		
			
				for(set<int>::iterator factor_it = PreviousFactorsWithVariable.begin(); factor_it != PreviousFactorsWithVariable.end(); factor_it++)
				{
					fprintf(record_fp, "%d,", *factor_it);			
				}
				
				fprintf(record_fp, "\t");		
				PreviousFactorsWithVariable.clear();

				for(list<int>::iterator size_it = sizes_of_factors_with_variable.begin(); size_it != sizes_of_factors_with_variable.end(); size_it++)
				{
					fprintf(record_fp, "%d,", *size_it);			
				}		

				fprintf(record_fp, "\t");
				sizes_of_factors_with_variable.clear();


				for(list<int>::iterator size_it = sizes_of_cannot_be_one_elements_of_variable.begin(); size_it != sizes_of_cannot_be_one_elements_of_variable.end(); size_it++)
				{
					fprintf(record_fp, "%d,", *size_it);			
				}		

				fprintf(record_fp, "\t");
				sizes_of_cannot_be_one_elements_of_variable.clear();

			
				for(list<int>::iterator size_it = sizes_of_cannot_be_zero_elements_of_variable.begin(); size_it != sizes_of_cannot_be_zero_elements_of_variable.end(); size_it++)
				{
					fprintf(record_fp, "%d,", *size_it);			
				}		

				fprintf(record_fp, "\t");
				sizes_of_cannot_be_zero_elements_of_variable.clear();

				fprintf(record_fp, "%d\t", CorrectionPartSize);

				fprintf(record_fp, "\n\n");

				number_of_compose_operations_for_variable = 0;
				ComposeTime = 0;
		
				fclose(record_fp);
				#endif	
			}//for ends here

		}//else of if(perform_cegar_on_arbitrary_boolean_formulas) ends here

		gettimeofday (&cegar_step_finish_ms, NULL);
	   	total_time_in_initial_abstraction_generation_in_cegar = cegar_step_finish_ms.tv_sec * 1000 + cegar_step_finish_ms.tv_usec / 1000;
	   	total_time_in_initial_abstraction_generation_in_cegar -= cegar_step_start_ms.tv_sec * 1000 + cegar_step_start_ms.tv_usec / 1000;

		size_computation_time_in_initial_abstraction_generation_in_cegar = total_time_in_compute_size - size_computation_time_in_initialization;	
		total_time_in_initial_abstraction_generation_in_cegar = total_time_in_initial_abstraction_generation_in_cegar - size_computation_time_in_initial_abstraction_generation_in_cegar;

		if(!mask_printing_cegar_details)
		{
		cout << "\ntotal_time_in_initial_abstraction_generation_in_cegar = " << total_time_in_initial_abstraction_generation_in_cegar << " milliseconds\tsize_computation_time_in_initial_abstraction_generation_in_cegar = " << size_computation_time_in_initial_abstraction_generation_in_cegar << " milliseconds\n";
		}

		// We have the initial abstract skolem functions and cannot-be sets here

		#ifdef DEBUG_CEGAR
			showCannotBeSets();
			cout << "\nWe have the initial abstract skolem functions, bad sets, and cannot-be sets, starting CEGAR\n\n";
		#endif

		#ifdef RECORD_KEEP
			string record_file;
			record_file = logfile_prefix;
			record_file += "skolem_function_generation_details.txt";
			FILE* record_fp = fopen(record_file.c_str(), "a+");
			assert(record_fp != NULL);
	
			if(!mask_printing_cegar_details)
			{
				fprintf(record_fp, "\nDetails of CEGAR\n");
			}

			assert(size_of_conjunction_of_factors != 0);

			if(!mask_printing_cegar_details)
			{
				fprintf(record_fp, "\nSize of F(X, Y) = %d\n\nIteration number\tIndex of the variable being refined\tTime details\tRefinement steps\n\nTime details: time to check satisfiability of exactness condition using SAT solver (time spent in cnf generation, time spent in simplification) (size of formula) / time to check if exactness condition is sat using simulation (-,-)(-)\n\nRefinement steps: (x@origin, number of selected elements in Cb1_origin that are true + number of selected elements in Cb0_origin that are true, size of initial mu) (x@location=value, size of new element added to Cb1/Cb0_location, number of selected elements in Cb1/Cb0_location that are true, size of disjunction of selected elements in Cb1/Cb0_location that are true, size of changed mu, size of changed Skolem function before don't care optimization, size of changed Skolem function after don't care optimization, size of component of the new element added to Cb1/Cb0_location from refinement-from-bottom, number of variables avoided through generalization in refinement-from-bottom)...", size_of_conjunction_of_factors);
			}

			fclose(record_fp);
		#endif	

		// CEGAR starting here

		gettimeofday (&cegar_step_start_ms, NULL);

		if(!mask_printing_cegar_details)
		{
			cout << "\nInitializing CEGAR\n";
		}

		if(exit_after_finding_abstract_skolem_functions)
		{
			cout << "\nExiting after finding abstract Skolem functions\n";
		}
		else // CEGAR loop
		{
			if(perform_cegar_on_arbitrary_boolean_formulas)
			{
				if(checkGlobalTimeOut_In_Cluster())
				{
					#ifdef DEBUG_PAR
					cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::factorizedSkolemFunctionGenerator\n";
					#endif
					cluster_global_timed_out = true; // cluster_global_timed_out flag set
					return;
				}	
			}

			initializeCEGAR_using_ABC();

			if(!mask_printing_cegar_details)
			{
				cout << "\nCEGAR initialized\n";
			}
			
			if(use_generic_sat_solver_interface)
			{
				#ifdef DEBUG_SKOLEM
				cout << "\nuse_generic_sat_solver_interface\n";
				#endif

				if(sat_solver_used_in_cegar == "abc")
				{
					pSat_for_exactness_check = sat_solver_new();// SAT-solver specific code
				}
				else // for other SAT solvers
				{
					assert(false);
				}	
			}
			else
			{
				pSat_for_exactness_check = sat_solver_new();
			}

			int correction_index = number_of_vars_to_elim; 

			cegar_iteration_for_correction_index = 0;

			map<string, int> Model_of_ExactnessCheck;
			
			map<int, Aig_Obj_t*> Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX;
			map<int, Aig_Obj_t*> Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX;	

			bool skolem_function_is_exact;

			while(correction_index >= 1)
			{
				#ifdef DEBUG_SKOLEM
				cout << "\nCorrecting Skolem function for x_" << correction_index << endl;
				#endif

				if(perform_cegar_on_arbitrary_boolean_formulas)
				{
					if(checkGlobalTimeOut_In_Cluster())
					{
						#ifdef DEBUG_PAR
						cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::factorizedSkolemFunctionGenerator\n";
						#endif
						cluster_global_timed_out = true; // cluster_global_timed_out flag set
						return;
					}	
				}

				if(checkTimeOut()) // check for time-out
				{
					#ifdef RECORD_KEEP
					record_fp = fopen(record_file.c_str(), "a+");
					assert(record_fp != NULL);
					fprintf(record_fp, "\nTime-out inside function AIGBasedSkolem::factorizedSkolemFunctionGenerator during CEGAR iteration %d\n", cegar_iteration_number);
					fclose(record_fp);
					#endif
	
					cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::factorizedSkolemFunctionGenerator\n";
					timed_out = true; // timed_out flag set
					return;
				}

				#ifdef RECORD_KEEP
					record_fp = fopen(record_file.c_str(), "a+");
					assert(record_fp != NULL);

					if(!mask_printing_cegar_details)
					{
						fprintf(record_fp, "\n\n%d\t%d", cegar_iteration_number, correction_index);	
					}

					fclose(record_fp);
				#endif
		
				Model_of_ExactnessCheck.clear();

				if(internal_flag_to_avoid_sat_call_in_functional_forms)
				{
					skolem_function_is_exact = checkIfSkolemFunctionAtGivenIndexIsExact_using_Mu_Based_Scheme_With_Optimizations_For_Functional_Forms(cegar_iteration_number, correction_index, Model_of_ExactnessCheck, Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX, Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX, VariablesToEliminate);

				}
				else
				{
					clock_t satTime = clock();	//Added by SS
					skolem_function_is_exact = checkIfSkolemFunctionAtGivenIndexIsExact_using_Mu_Based_Scheme_With_Optimizations_With_Unified_Code_And_Incremental_Solving(correction_index, Model_of_ExactnessCheck, Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX, Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX, VariablesToEliminate);	
					//cout << "Time taken in SAT solving " << ((double) (clock() - satTime)/CLOCKS_PER_SEC); //Added by SS

				}
				
			//	if(!mask_printing_cegar_details)
	//Commented by SS
				//{
				//	cout << "\ncegar_iteration_number = " << cegar_iteration_number << ", " << "\tcegar_iteration_for_correction_index = " << cegar_iteration_for_correction_index << "\tcorrection_index = " << correction_index << "\tassumptions_flag = " << assumptions_flag << "\tskolem_function_is_exact = " << skolem_function_is_exact << " finished\n";
			//	}

				#ifdef DEBUG_SKOLEM
					//cout << "\nPress any key to continue...";
					//char c = getchar();
				#endif	

				if(allow_intermediate_generic_sat_calls) // generic sat calls possible in between specific calls
				{
		
					if(skolem_function_is_exact)
					{
						if(assumptions_flag == 0 || assumptions_flag == 2)// no assumptions; skolem functions exact
						{
							#ifdef DEBUG_SKOLEM
								cout << "\nAll skolem functions are exact\n";
							#endif

							break;

						}
						else if(assumptions_flag == 1)// with assumptions; this skolem function is exact
						// let's do a generic check
						{
							#ifdef DEBUG_SKOLEM
								cout << "\nSkolem function at location " << correction_index << " is exact. Let's do a generic check\n";
							#endif

							assumptions_flag = 2;
							cegar_iteration_number++;
							cegar_iteration_for_correction_index++;		
						
						}
					}
					else
					{
						if(assumptions_flag == 0)
						{
							#ifdef DEBUG_SKOLEM
								cout << "\nAll skolem functions are NOT exact\n";
							#endif

							cegar_iteration_number++;
							cegar_iteration_for_correction_index++;
						}
						else if(assumptions_flag == 1)
						{
							#ifdef DEBUG_SKOLEM
								cout << "\nSkolem function at location " << correction_index << " is INEXACT\n";
							#endif
							
							cegar_iteration_number++;
							cegar_iteration_for_correction_index++;
						}
						else if(assumptions_flag == 2)
						{
							#ifdef DEBUG_SKOLEM
								cout << "\nGeneric check fails; Let's go back to specific check for Skolem function at location " << correction_index-1 << " \n";
							#endif
							
							assumptions_flag = 1;
							cegar_iteration_number++;
							correction_index--;
							cegar_iteration_for_correction_index = 0;
						}
						
					}


				}
				else
				{
		
					if(skolem_function_is_exact)
					{
						if(assumptions_flag == 0)// no assumptions; skolem functions exact
						{
							#ifdef DEBUG_SKOLEM
								cout << "\nAll skolem functions are exact\n";
							#endif

							break;
						}
						else if(assumptions_flag == 1)// with assumptions; this skolem function is exact
						{
							#ifdef DEBUG_SKOLEM
								cout << "\nSkolem function at location " << correction_index << " is exact\n";
							#endif

							cegar_iteration_number++;
							correction_index--;
							cegar_iteration_for_correction_index = 0;
						
						}
					}
					else
					{
						if(assumptions_flag == 0)
						{
							#ifdef DEBUG_SKOLEM
								cout << "\nAll skolem functions are NOT exact\n";
							#endif
						}
						else if(assumptions_flag == 1)
						{
							#ifdef DEBUG_SKOLEM
								cout << "\nSkolem function at location " << correction_index << " is INEXACT\n";
							#endif
						}
	
						cegar_iteration_number++;
						cegar_iteration_for_correction_index++;
					}

				}

				if(perform_cegar_on_arbitrary_boolean_formulas)
				{
					if(checkGlobalTimeOut_In_Cluster())
					{
						#ifdef DEBUG_PAR
						cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::factorizedSkolemFunctionGenerator\n";
						#endif
						cluster_global_timed_out = true; // cluster_global_timed_out flag set
						return;
					}	
				}
				
				if(checkTimeOut()) // check for time-out
				{
					#ifdef RECORD_KEEP
					record_fp = fopen(record_file.c_str(), "a+");
					assert(record_fp != NULL);
					fprintf(record_fp, "\nTime-out inside function AIGBasedSkolem::factorizedSkolemFunctionGenerator during CEGAR iteration %d\n", cegar_iteration_number);
					fclose(record_fp);
					#endif
	
					cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::factorizedSkolemFunctionGenerator\n";
					timed_out = true; // timed_out flag set
					return;
				}			
				
				
				Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX.clear();
				Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX.clear();

				if(!skolem_function_is_exact)
				{
					if(generate_all_counterexamples_from_sat_call && cegar_iteration_number > 0 && cegar_iteration_for_correction_index > 0 ) // In other cases SAT call is needed
					{
						#ifdef DEBUG_SKOLEM
						cout << "\nLet's generate maximum counterexamples from this solution!!\n";
						#endif
				
						bool epsilon_is_sat_for_given_y = true;
						int number_of_solutions_generated_with_same_y = 1;

						while(epsilon_is_sat_for_given_y)
						{
							#ifdef DEBUG_SKOLEM
							cout << "\nepsilon_is_sat_for_given_y is true\n";
							#endif

							// from the model of exactness check, obtain the refinement hint to
							// eliminate this counterexample
							refineSkolemFunctions_using_Mu_Based_Scheme_With_Optimizations(correction_index, Model_of_ExactnessCheck, Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX, Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX); 
				
							#ifdef DEBUG_SKOLEM
							cout << "\nCalling checkIfSkolemFunctionAtGivenIndexIsExact_using_Simulation to get new counterexample with the same y\n";
							#endif
		
							// check if epsilon remains satisfiable 
							// after adding this refinement hint
							epsilon_is_sat_for_given_y = checkIfSkolemFunctionAtGivenIndexIsExact_using_Simulation(correction_index, Model_of_ExactnessCheck, Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX, Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX, VariablesToEliminate, number_of_solutions_generated_with_same_y);	

							Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX.clear();
							Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX.clear();

							number_of_solutions_generated_with_same_y++;

							cegar_iteration_number++;
							cegar_iteration_for_correction_index++;
						}

						#ifdef DEBUG_SKOLEM
						cout << "\nepsilon_is_sat_for_given_y is false\n";
						#endif						

					}
					else
					{
						// from the model of exactness check, obtain the refinement hint to
						// eliminate this counterexample
						refineSkolemFunctions_using_Mu_Based_Scheme_With_Optimizations(correction_index, Model_of_ExactnessCheck, Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX, Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX); 
					}

				}//if(!skolem_function_is_exact) ends here

			}//while(correction_index >= 1) ends here

			
			if(use_generic_sat_solver_interface)
			{
				if(sat_solver_used_in_cegar == "abc")
				{
					sat_solver_delete(pSat_for_exactness_check);// SAT-solver specific code
				}
				else // for other SAT solvers
				{
					assert(false);
				}	
			}
			else
			{
				sat_solver_delete(pSat_for_exactness_check);
			}

	
		} // CEGAR loop part ends here
		
		if(!mask_printing_cegar_details)
		{
			cout << "\nexact skolem functions are found\n";
		}
		// exact skolem functions are found

		gettimeofday (&cegar_step_finish_ms, NULL);
	   	total_time_in_cegar_loops_in_cegar = cegar_step_finish_ms.tv_sec * 1000 + cegar_step_finish_ms.tv_usec / 1000;
	   	total_time_in_cegar_loops_in_cegar -= cegar_step_start_ms.tv_sec * 1000 + cegar_step_start_ms.tv_usec / 1000;
		

		size_computation_time_in_cegar_loops_in_cegar = total_time_in_compute_size - size_computation_time_in_initialization - size_computation_time_in_initial_abstraction_generation_in_cegar;	
		total_time_in_cegar_loops_in_cegar = total_time_in_cegar_loops_in_cegar - size_computation_time_in_cegar_loops_in_cegar;

		total_time_in_connection_substitution_in_cegar = 0;
		size_computation_time_in_connection_substitution_in_cegar = 0;			
	
	}//if(enable_cegar) ends here
	else // option for monoskolem
	{				
		for(int var_to_elim_index = 1; var_to_elim_index <= number_of_vars_to_elim; var_to_elim_index++)
		{
			if(checkTimeOut()) // check for time-out
			{
				cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::factorizedSkolemFunctionGenerator\n";
				timed_out = true; // timed_out flag set
				return;
			}		

			if(maximum_index_to_eliminate != -1) // to stop computation in between
			{
				if(var_to_elim_index > maximum_index_to_eliminate)
				{
					#ifdef DEBUG_SKOLEM
					cout << "\nLet us stop here...\n";
					#endif

					return;
				}			
			}

			#ifdef DEBUG_SKOLEM
			cout << "\ncomputing skolem_function_" << var_to_elim_index << endl;
			#endif

			#ifdef PRINT_VERY_DETAILED_RECORDS_ON_SCREEN
			cout << "\ncomputing skolem_function_" << var_to_elim_index << "\n";
			#endif

			#ifdef RECORD_KEEP
			unsigned long long int duration_ms;
			struct timeval start_ms, finish_ms;
			gettimeofday (&start_ms, NULL); 
			#endif

			#ifdef DETAILED_RECORD_KEEP
			gettimeofday (&step_start_ms, NULL); 	
			#endif

			findFactorsWithVariable(var_to_elim_index);// find the set of factors containing the variable			

			if(checkTimeOut()) // check for time-out
			{
				cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::factorizedSkolemFunctionGenerator\n";
				timed_out = true; // timed_out flag set
				return;
			}

			#ifdef DETAILED_RECORD_KEEP
			gettimeofday (&step_finish_ms, NULL);
			step_ms = step_finish_ms.tv_sec * 1000 + step_finish_ms.tv_usec / 1000;
			step_ms -= step_start_ms.tv_sec * 1000 + step_start_ms.tv_usec / 1000;
			//cout << "\nfindFactorsWithVariable finished in " << step_ms << " milliseconds\n";
		
			//cout << "\nnumber of factors containing the variable = " << FactorsWithVariable.size() << endl;

			FactorFindingTime = step_ms;
			#endif

			#ifdef DETAILED_RECORD_KEEP
			gettimeofday (&step_start_ms, NULL); 	
			#endif
		
			Aig_Obj_t* cofactor_one_of_bad_set = NULL;
			Aig_Obj_t* skolem_function;

			if(use_interpolant_as_skolem_function)
			{
				skolem_function = computeSkolemFunctionAsInterpolant(var_to_elim_index);

				// connect to some output to avoid unwanted deletion
				Aig_Obj_t* skolem_function_CO = Aig_ObjCreateCo(pub_aig_manager, skolem_function ); 
				assert(skolem_function_CO != NULL);

				insertIntoOneDimensionalMatrix(SkolemFunctions, number_of_vars_to_elim, var_to_elim_index, skolem_function, false);				
				#ifdef PRINT_SKOLEM_FUNCTIONS
				string skolem_function_file_name = benchmark_name_without_extension;
				skolem_function_file_name += "_skolem_function";
				writeFormulaToFile(pub_aig_manager, skolem_function, skolem_function_file_name, ".v", var_to_elim_index, 0);
				#endif
			}
			else
			{
				skolem_function = computeSkolemFunctionUsingBadSet(var_to_elim_index, cofactor_one_of_bad_set);
			
				// connect to some output to avoid unwanted deletion
				Aig_Obj_t* skolem_function_CO = Aig_ObjCreateCo(pub_aig_manager, skolem_function ); 
				assert(skolem_function_CO != NULL);				

				assert(cofactor_one_of_bad_set != NULL);
			}
			
			if(checkTimeOut()) // check for time-out
			{
				cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::factorizedSkolemFunctionGenerator\n";
				timed_out = true; // timed_out flag set
				return;
			}

			assert(skolem_function != NULL);			

			#ifdef DETAILED_RECORD_KEEP
			gettimeofday (&step_finish_ms, NULL);
			step_ms = step_finish_ms.tv_sec * 1000 + step_finish_ms.tv_usec / 1000;
			step_ms -= step_start_ms.tv_sec * 1000 + step_start_ms.tv_usec / 1000;
			//cout << "\ncomputeSkolemFunctionUsingBadSet finished in " << step_ms << " milliseconds\n";
			#endif

			#ifdef DETAILED_RECORD_KEEP
			gettimeofday (&step_start_ms, NULL); 	
			#endif
			
			#ifdef RECORD_KEEP
			DeltaCombinedSize = -1;
			#endif
			
			if(checkTimeOut()) // check for time-out
			{
				cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::factorizedSkolemFunctionGenerator\n";
				timed_out = true; // timed_out flag set
				return;
			}

			#ifdef DETAILED_RECORD_KEEP
			gettimeofday (&step_finish_ms, NULL);
			step_ms = step_finish_ms.tv_sec * 1000 + step_finish_ms.tv_usec / 1000;
			step_ms -= step_start_ms.tv_sec * 1000 + step_start_ms.tv_usec / 1000;
			//cout << "\nupdateBadSet finished in " << step_ms << " milliseconds\n";
			DeltaCombGenTime = step_ms;
			#endif
			
			#ifdef DETAILED_RECORD_KEEP
			gettimeofday (&step_start_ms, NULL); 	
			#endif
		
			if(var_to_elim_index != number_of_vars_to_elim) // We need to update the factor matrix
			{	
				#ifdef DEBUG_SKOLEM
				cout << "\nupdating factors\n";
				#endif

				Aig_Obj_t* quantifier_eliminated_result;
				quantifier_eliminated_result = computeQuantifierEliminatedResultUsingSkolemFunction(var_to_elim_index, skolem_function);
				assert(quantifier_eliminated_result != NULL);

				// connect to some output to avoid unwanted deletion
				Aig_Obj_t* quantifier_eliminated_result_CO = Aig_ObjCreateCo(pub_aig_manager, quantifier_eliminated_result ); 
				assert(quantifier_eliminated_result_CO != NULL);

				updateFactorsUsingQuantifierEliminatedResult(var_to_elim_index, quantifier_eliminated_result);		
				
			}

			if(checkTimeOut()) // check for time-out
			{
				cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::factorizedSkolemFunctionGenerator\n";
				timed_out = true; // timed_out flag set
				return;
			}

			#ifdef DETAILED_RECORD_KEEP
			gettimeofday (&step_finish_ms, NULL);
			step_ms = step_finish_ms.tv_sec * 1000 + step_finish_ms.tv_usec / 1000;
			step_ms -= step_start_ms.tv_sec * 1000 + step_start_ms.tv_usec / 1000;
			//cout << "\nupdateFactors finished in " << step_ms << " milliseconds\n";
			NextFactorGenTime = step_ms;
			#endif

			#ifdef DEBUG_SKOLEM
			cout << "\nclearing variable-specific data-structures\n";
			#endif

			#ifdef DETAILED_RECORD_KEEP
			gettimeofday (&step_start_ms, NULL); 	
			#endif
		
			clearVariableSpecificDataStructures();

			#ifdef DETAILED_RECORD_KEEP
			gettimeofday (&step_finish_ms, NULL);
			step_ms = step_finish_ms.tv_sec * 1000 + step_finish_ms.tv_usec / 1000;
			step_ms -= step_start_ms.tv_sec * 1000 + step_start_ms.tv_usec / 1000;
			//cout << "\nclearVariableSpecificDataStructures finished in " << step_ms << " milliseconds\n";
			#endif

			#ifdef RECORD_KEEP
			gettimeofday (&finish_ms, NULL);
		   	duration_ms = finish_ms.tv_sec * 1000 + finish_ms.tv_usec / 1000;
		   	duration_ms -= start_ms.tv_sec * 1000 + start_ms.tv_usec / 1000;
			SkolemFunctionGenTime = duration_ms;

			SkolemFunctionSize = computeSize(skolem_function, pub_aig_manager); // AIG Manager API Call	
		   	#endif

			string var_to_elim = searchVarIndexToVarNameMap(var_index_to_var_name_map, var_to_elim_index);
			//cout << "\nskolem_function_" << var_to_elim_index << ", i.e., skolem function for " << var_to_elim << " computed\n";

			#ifdef RECORD_KEEP
			string record_file;
			record_file = logfile_prefix;
			record_file += "skolem_function_generation_details.txt";
			FILE* record_fp = fopen(record_file.c_str(), "a+");
			assert(record_fp != NULL);

			total_of_skyline_sizes_in_least_cost_ordering = 0;
			sum_of_number_of_factors_containing_variable = sum_of_number_of_factors_containing_variable + NumberOfFactors;
			//sum_of_skolem_function_sizes = sum_of_skolem_function_sizes + SkolemFunctionSize; // we will find this before reverse-substitution
			total_number_of_compose_operations = total_number_of_compose_operations + number_of_compose_operations_for_variable;
			total_time_in_compose_operations = total_time_in_compose_operations + ComposeTime;
			total_time_in_alpha_combined = total_time_in_alpha_combined + AlphaCombGenTime;
			total_time_in_delta_part = total_time_in_delta_part + DeltaPartGenTime;
			total_time_in_delta_combined = total_time_in_delta_combined + DeltaCombGenTime;
			total_time_in_next_factor = total_time_in_next_factor + NextFactorGenTime;
			total_time_in_correction_part = 0;
			number_of_variables_eliminated = var_to_elim_index;
			sum_of_numbers_of_affecting_factors = 0;

			total_number_of_boolean_operations_in_initial_skolem_function_generation = total_number_of_boolean_operations_in_initial_skolem_function_generation + number_of_boolean_operations_for_variable;
			total_BooleanOpTime_in_initial_skolem_function_generation = total_BooleanOpTime_in_initial_skolem_function_generation + BooleanOpTime;
			total_number_of_support_operations_in_initial_skolem_function_generation = total_number_of_support_operations_in_initial_skolem_function_generation + number_of_support_operations_for_variable;
			total_FactorFindingTime_in_initial_skolem_function_generation = total_FactorFindingTime_in_initial_skolem_function_generation + FactorFindingTime;

			if(use_interpolant_as_skolem_function)
			{
				fprintf(record_fp, "%d\t%s\t%d\t%llu\t%d\t%d\t%d\t%llu\t%d\t", var_to_elim_index, var_to_elim.c_str(), NumberOfFactors, SkolemFunctionGenTime, SkolemFunctionSize, size_of_alpha_in_interpolant_computation_for_variable, size_of_beta_in_interpolant_computation_for_variable, time_in_interpolant_computation_for_variable, size_of_quantified_result_in_bdd_like_scheme);
			}
			else
			{
				fprintf(record_fp, "%d\t%s\t%d\t%llu\t%d\t%d\t", var_to_elim_index, var_to_elim.c_str(), NumberOfFactors, SkolemFunctionGenTime, SkolemFunctionSize, size_of_quantified_result_in_bdd_like_scheme);	
			}

			if(print_factor_graph)
			{
				string fg_file_name = benchmark_name_without_extension;
				fg_file_name += "_factorized";				
				fg_file_name += "_factor_graph.dat";
				FILE* fg_fp = fopen(fg_file_name.c_str(), "a+");
				assert(fg_fp != NULL);			
				for(list<int>::iterator affect_it = FactorsAffectingSkolemFunction.begin(); affect_it != FactorsAffectingSkolemFunction.end(); affect_it++)
				{
					fprintf(fg_fp, "%d\t%d\n", *affect_it, var_to_elim_index);			
				}				
				fclose(fg_fp);
			}
		
			fprintf(record_fp, "%d\t%llu\t%d\t%llu\t%d\t%llu", number_of_compose_operations_for_variable, ComposeTime, number_of_boolean_operations_for_variable, BooleanOpTime, number_of_support_operations_for_variable, FactorFindingTime);
			fprintf(record_fp, "\t");
			for(set<int>::iterator factor_it = PreviousFactorsWithVariable.begin(); factor_it != PreviousFactorsWithVariable.end(); factor_it++)
			{
				fprintf(record_fp, "%d,", *factor_it);			
			}
				
			fprintf(record_fp, "\t");		
			PreviousFactorsWithVariable.clear();

			for(list<int>::iterator size_it = sizes_of_factors_with_variable.begin(); size_it != sizes_of_factors_with_variable.end(); size_it++)
			{
				fprintf(record_fp, "%d,", *size_it);			
			}		

			fprintf(record_fp, "\t");
			sizes_of_factors_with_variable.clear();

			
			fprintf(record_fp, "\n\n");

			number_of_compose_operations_for_variable = 0;
			ComposeTime = 0;
			number_of_boolean_operations_for_variable = 0;
			BooleanOpTime = 0;
			number_of_support_operations_for_variable = 0;
		
			fclose(record_fp);
			#endif	
		}//for ends here

		gettimeofday (&cegar_step_finish_ms, NULL);
	   	total_time_in_initial_abstraction_generation_in_cegar = cegar_step_finish_ms.tv_sec * 1000 + cegar_step_finish_ms.tv_usec / 1000;
	   	total_time_in_initial_abstraction_generation_in_cegar -= cegar_step_start_ms.tv_sec * 1000 + cegar_step_start_ms.tv_usec / 1000;

		total_time_in_cegar_loops_in_cegar = 0;
		total_time_in_connection_substitution_in_cegar = 0;
		size_computation_time_in_initial_abstraction_generation_in_cegar = total_time_in_compute_size - size_computation_time_in_initialization;

		total_time_in_initial_abstraction_generation_in_cegar = total_time_in_initial_abstraction_generation_in_cegar - 		size_computation_time_in_initial_abstraction_generation_in_cegar;

		size_computation_time_in_cegar_loops_in_cegar = 0;
		size_computation_time_in_connection_substitution_in_cegar = 0;

	} 

	total_number_of_compose_operations_in_initial_skolem_function_generation = total_number_of_compose_operations;
	total_ComposeTime_in_initial_skolem_function_generation = total_time_in_compose_operations;

	if(perform_cegar_on_arbitrary_boolean_formulas)
	{
		string record_file;
		record_file = logfile_prefix;
		record_file += "skolem_function_generation_details.txt";
		FILE* record_fp = fopen(record_file.c_str(), "a+");
		assert(record_fp != NULL);

		if(!mask_printing_details_file)
		{
			fprintf(record_fp, "\n\ntotal-time-in-initial-skolem-function-generation-without-size-computation-time = %llu milliseconds\ntotal-time-in-cegar-loops-without-size-computation-time = %llu\nnumber-of-cegar-iterations = %d\n\n", total_time_in_initial_abstraction_generation_in_cegar, total_time_in_cegar_loops_in_cegar, cegar_iteration_number);
		}

		fclose(record_fp);
	}
	else if(!enable_cegar)
	{
		string record_file;
		record_file = logfile_prefix;
		record_file += "skolem_function_generation_details.txt";
		FILE* record_fp = fopen(record_file.c_str(), "a+");
		assert(record_fp != NULL);

		fprintf(record_fp, "\n\ntotal_number_of_compose_operations_in_initial_skolem_function_generation = %d\ntotal_ComposeTime_in_initial_skolem_function_generation = %llu milliseconds\ntotal_number_of_boolean_operations_in_initial_skolem_function_generation = %d\ntotal_BooleanOpTime_in_initial_skolem_function_generation = %llu milliseconds\ntotal_number_of_support_operations_in_initial_skolem_function_generation = %d\ntotal_FactorFindingTime_in_initial_skolem_function_generation = %llu milliseconds", total_number_of_compose_operations_in_initial_skolem_function_generation, total_ComposeTime_in_initial_skolem_function_generation, total_number_of_boolean_operations_in_initial_skolem_function_generation, total_BooleanOpTime_in_initial_skolem_function_generation, total_number_of_support_operations_in_initial_skolem_function_generation, total_FactorFindingTime_in_initial_skolem_function_generation);

		fprintf(record_fp, "\n\ntotal-time-in-initial-skolem-function-generation-without-size-computation-time = %llu milliseconds\ntotal time in initialization of skolem function generator-without-size-computation-time = %llu\n", total_time_in_initial_abstraction_generation_in_cegar, total_time_in_generator_initialization);

		fclose(record_fp);
	}

	gettimeofday (&cegar_step_start_ms, NULL);

	if(perform_reverse_substitution)
	{
		for(int var_to_elim_index = 1; var_to_elim_index <= number_of_vars_to_elim; var_to_elim_index++)
		{
			Aig_Obj_t* final_skolem_function;
			final_skolem_function = searchOneDimensionalMatrix(SkolemFunctions, number_of_vars_to_elim, var_to_elim_index);
			assert(final_skolem_function != NULL);	

			#ifdef RECORD_KEEP
			int final_skolem_function_size = computeSize(final_skolem_function, pub_aig_manager); // AIG Manager API Call
			sum_of_skolem_function_sizes = sum_of_skolem_function_sizes + final_skolem_function_size;
			#endif
		}

		performReverseSubstitutionOfSkolemFunctions();

		if(checkTimeOut()) // check for time-out
		{
			cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::factorizedSkolemFunctionGenerator\n";
			timed_out = true; // timed_out flag set
			return;
		}
		
		for(int var_to_elim_index = 1; var_to_elim_index <= number_of_vars_to_elim; var_to_elim_index++)
		{
			Aig_Obj_t* final_skolem_function;
			final_skolem_function = searchOneDimensionalMatrix(SkolemFunctions, number_of_vars_to_elim, var_to_elim_index);
			assert(final_skolem_function != NULL);	

			#ifdef RECORD_KEEP
			int final_skolem_function_size = computeSize(final_skolem_function, pub_aig_manager); // AIG Manager API Call

			skolem_function_sizes_after_reverse_substitution.push_back(final_skolem_function_size);
			sum_of_skolem_function_sizes_after_reverse_substitution = sum_of_skolem_function_sizes_after_reverse_substitution + final_skolem_function_size;
			#endif

			#ifdef PRINT_SKOLEM_FUNCTIONS
			string skolem_function_file_name = benchmark_name_without_extension;
			skolem_function_file_name += "_skolem_function_after_reverse_substitution";
			writeFormulaToFile(pub_aig_manager, final_skolem_function, skolem_function_file_name, ".v", var_to_elim_index, 0);
			#endif
		}
	}

	gettimeofday (&cegar_step_finish_ms, NULL);
	total_time_in_reverse_substitution_in_cegar = cegar_step_finish_ms.tv_sec * 1000 + cegar_step_finish_ms.tv_usec / 1000;
	total_time_in_reverse_substitution_in_cegar -= cegar_step_start_ms.tv_sec * 1000 + cegar_step_start_ms.tv_usec / 1000;

	size_computation_time_in_reverse_substitution_in_cegar = total_time_in_compute_size - size_computation_time_in_initial_abstraction_generation_in_cegar - size_computation_time_in_initialization - size_computation_time_in_cegar_loops_in_cegar - size_computation_time_in_connection_substitution_in_cegar;

	total_time_in_reverse_substitution_in_cegar = total_time_in_reverse_substitution_in_cegar - size_computation_time_in_reverse_substitution_in_cegar;


	if(prove_correctness_of_skolem_functions_using_qbf_solving || prove_correctness_of_skolem_functions_of_conjunctions)
	{
		if(conjunction_of_factors == NULL)
		{
			conjunction_of_factors = createAnd(Factors, pub_aig_manager); 
		}
		assert(conjunction_of_factors != NULL);

		map<int, Aig_Obj_t*> skolem_function_replacement_map;
		for(int var_to_elim_index = 1; var_to_elim_index <= number_of_vars_to_elim; var_to_elim_index++)
		{			
			Aig_Obj_t* skolem_function_at_var_to_elim_index;
			skolem_function_at_var_to_elim_index = searchOneDimensionalMatrix(SkolemFunctions, number_of_vars_to_elim, var_to_elim_index);
			assert(skolem_function_at_var_to_elim_index != NULL); 

			skolem_function_replacement_map.insert(make_pair(var_to_elim_index, skolem_function_at_var_to_elim_index));
		}
		assert(skolem_function_replacement_map.size() > 0);

		Aig_Obj_t* result_of_qe_using_skolem_functions;
		result_of_qe_using_skolem_functions = replaceVariablesByFormulas(conjunction_of_factors, skolem_function_replacement_map);	
		assert(result_of_qe_using_skolem_functions != NULL);		
		
		bool formulas_equivalent = checkEquivalenceUsingQBFSolver(result_of_qe_using_skolem_functions, conjunction_of_factors, VariablesToEliminate, pub_aig_manager);

		string record_file;
		record_file = logfile_prefix;
		record_file += "skolem_function_generation_details.txt";
		FILE* record_fp = fopen(record_file.c_str(), "a+");
		assert(record_fp != NULL);

		if(formulas_equivalent)
		{
			if(prove_correctness_of_skolem_functions_of_conjunctions)
			{
				//cout << "~exists X.f => ~f[X --> psi] is valid for any psi\nSkolem functions are exact\n";
				
				cout << "\nSkolem functions are exact\n";
				
				fprintf(record_fp, "\n\nexists X.f(X,Y) => f'(psi,Y) is valid; Skolem functions are exact\n");
			}
			else
			{
				cout << "\nSkolem functions are exact\n";

				fprintf(record_fp, "\n\nexists X.f(X,Y) = f'(psi,Y) is valid; Skolem functions are exact\n");
			}
		}
		else
		{
			cout << "\nSkolem functions are NOT exact\n";

			if(prove_correctness_of_skolem_functions_of_conjunctions)
			{
				fprintf(record_fp, "\n\nexists X.f(X,Y) => f'(psi,Y) is NOT valid; Skolem functions are NOT exact\n");
			}
			else
			{
				fprintf(record_fp, "\n\nexists X.f(X,Y) = f'(psi,Y) is NOT valid; Skolem functions are NOT exact\n");
			}			

		}

		fclose(record_fp);
	
	}//if(prove_correctness_of_skolem_functions_using_qbf_solving) ends here
}



void AIGBasedSkolem::findFactorsWithVariable(int var_to_elim_index)
{
	#ifdef DEBUG_SKOLEM
	cout << "\nfinding factors with variable_" << var_to_elim_index << endl;
	#endif

	#ifdef DEBUG_CEGAR
	cout << "\nFactors\n";
	#endif

	FactorsWithVariable.clear();

	for(int factor_index = 1; factor_index <= number_of_factors; factor_index++)
	{
		Aig_Obj_t* factor = searchOneDimensionalMatrix(FactorMatrix, number_of_factors, factor_index);
		assert(factor != NULL);

		#ifdef DEBUG_SKOLEM
		writeFormulaToFile(pub_aig_manager, factor, "factor", ".v", var_to_elim_index, factor_index);	
		#endif
		
		if(!formulaFreeOfVariable(factor, var_to_elim_index))
		{
			FactorsWithVariable.insert(factor_index);

			#ifdef DETAILED_RECORD_KEEP
			int factor_size = computeSize(factor, pub_aig_manager); // AIG Manager API call

			sizes_of_factors_with_variable.push_back(factor_size);
			#endif

			#ifdef PRINT_VERY_DETAILED_RECORDS_ON_SCREEN
			cout << "\nfactor_ " << factor_index << " of size " << factor_size << " encountered with variable_" << var_to_elim_index << endl;
			#endif
		}

		#ifdef DEBUG_CEGAR
		int factor_size = computeSize(factor, pub_aig_manager); // AIG Manager API call
		cout << "(" << factor_index << ")" << factor_size << "\t";
		#endif
	}

	#ifdef DEBUG_CEGAR
	cout << "\nIndices of factors with variable\n";
	showSet(FactorsWithVariable, "FactorsWithVariable");
	#endif

	#ifdef DEBUG_SKOLEM
	showSet(FactorsWithVariable, "FactorsWithVariable");
	#endif
}



Aig_Obj_t* AIGBasedSkolem::computeAlpha(int var_to_elim_index, int factor_index)
{
	// check if entry already exists in the matrix
	Aig_Obj_t* alpha;
	alpha = searchOneDimensionalMatrix(AlphaMatrix, number_of_factors, factor_index);
	if(alpha != NULL)
	{
		return alpha;
	}
	else
	{
		// hash table miss
		#ifdef PRINT_VERY_DETAILED_RECORDS_ON_SCREEN
		cout << "\nhash table miss in AIGBasedSkolem::computeAlpha(" << var_to_elim_index <<", "<< factor_index <<")\n";
		#endif
		// alpha_i_j = (factor_i_j with var_i = true) \wedge (\neg factor_i_j with var_i = false)

		// compute cofactor_1 = factor_i_j with var_i = true
		Aig_Obj_t* cofactor_1 = computeCofactorOne(var_to_elim_index, factor_index); 
		assert(cofactor_1 != NULL);

		// compute neg_cofactor_0 = not(factor_i_j with var_i = false)
		Aig_Obj_t* neg_cofactor_0 = computeNegatedCofactorZero(var_to_elim_index, factor_index); 
		assert(neg_cofactor_0 != NULL);

		alpha = createAnd(cofactor_1, neg_cofactor_0, pub_aig_manager); // AIG Manager API Call
		assert(alpha != NULL);

		// Enter into matrix
		insertIntoOneDimensionalMatrix(AlphaMatrix, number_of_factors, factor_index, alpha, false);
		
		return alpha;	
	}	
}



Aig_Obj_t* AIGBasedSkolem::computeBeta(int var_to_elim_index, int factor_index)
{
	// check if entry already exists in the matrix
	Aig_Obj_t* beta;
	beta = searchOneDimensionalMatrix(BetaMatrix, number_of_factors, factor_index);
	if(beta != NULL)
	{
		return beta;
	}
	else
	{
		// hash table miss
		#ifdef PRINT_VERY_DETAILED_RECORDS_ON_SCREEN
		cout << "\nhash table miss in AIGBasedSkolem::computeBeta(" << var_to_elim_index <<", "<< factor_index <<")\n";
		#endif
		// beta_i_j = (factor_i_j with var_i = false) \wedge (\neg factor_i_j with var_i = true)

		// compute cofactor_0 = factor_i_j with var_i = false
		Aig_Obj_t* cofactor_0 = computeCofactorZero(var_to_elim_index, factor_index); 
		assert(cofactor_0 != NULL);

		// compute neg_cofactor_1 = not(factor_i_j with var_i = true)
		Aig_Obj_t* neg_cofactor_1 = computeNegatedCofactorOne(var_to_elim_index, factor_index); 
		assert(neg_cofactor_1 != NULL);

		beta = createAnd(cofactor_0, neg_cofactor_1, pub_aig_manager); // AIG Manager API Call
		assert(beta != NULL);
		
		// Enter into matrix
		insertIntoOneDimensionalMatrix(BetaMatrix, number_of_factors, factor_index, beta, false);
		
		return beta;	
	}	
}



Aig_Obj_t* AIGBasedSkolem::computeGamma(int var_to_elim_index, int factor_index)
{
	// check if entry already exists in the matrix
	Aig_Obj_t* gamma;
	gamma = searchOneDimensionalMatrix(GammaMatrix, number_of_factors, factor_index);
	if(gamma != NULL)
	{
		return gamma;
	}
	else
	{
		// hash table miss
		#ifdef PRINT_VERY_DETAILED_RECORDS_ON_SCREEN
		cout << "\nhash table miss in AIGBasedSkolem::computeGamma(" << var_to_elim_index <<", "<< factor_index <<")\n";
		#endif
		// gamma_i_j = (factor_i_j with var_i = false) \wedge (factor_i_j with var_i = true)

		// compute cofactor_0 = factor_i_j with var_i = false
		Aig_Obj_t* cofactor_0 = computeCofactorZero(var_to_elim_index, factor_index); 
		assert(cofactor_0 != NULL);

		// compute cofactor_1 = factor_i_j with var_i = true
		Aig_Obj_t* cofactor_1 = computeCofactorOne(var_to_elim_index, factor_index); 
		assert(cofactor_1 != NULL);

		gamma = createAnd(cofactor_0, cofactor_1, pub_aig_manager); // AIG Manager API Call
		assert(gamma != NULL);
		
		// Enter into matrix
		insertIntoOneDimensionalMatrix(GammaMatrix, number_of_factors, factor_index, gamma, false);
		
		return gamma;	
	}	
}



Aig_Obj_t* AIGBasedSkolem::computeDelta(int var_to_elim_index, int factor_index)
{
	// check if entry already exists in the matrix
	Aig_Obj_t* delta;
	delta = searchOneDimensionalMatrix(DeltaMatrix, number_of_factors, factor_index);
	if(delta != NULL)
	{
		return delta;
	}
	else
	{
		// hash table miss
		#ifdef PRINT_VERY_DETAILED_RECORDS_ON_SCREEN
		cout << "\nhash table miss in AIGBasedSkolem::computeDelta(" << var_to_elim_index <<", "<< factor_index <<")\n";
		#endif
		// delta_i_j = (\neg factor_i_j with var_i = false) \wedge (\neg factor_i_j with var_i = true)

		// compute negated_cofactor_0 = not(factor_i_j with var_i = false)
		Aig_Obj_t* negated_cofactor_0 = computeNegatedCofactorZero(var_to_elim_index, factor_index); 
		assert(negated_cofactor_0 != NULL);

		// compute negated_cofactor_1 = not(factor_i_j with var_i = true)
		Aig_Obj_t* negated_cofactor_1 = computeNegatedCofactorOne(var_to_elim_index, factor_index); 
		assert(negated_cofactor_1 != NULL);

		delta = createAnd(negated_cofactor_0, negated_cofactor_1, pub_aig_manager); // AIG Manager API Call
		assert(delta != NULL);
		
		// Enter into matrix
		insertIntoOneDimensionalMatrix(DeltaMatrix, number_of_factors, factor_index, delta, false);

		return delta;	
	}	
}



Aig_Obj_t* AIGBasedSkolem::computeCofactorOne(int var_to_elim_index, int factor_index)
{
	// check if entry already exists in the matrix
	Aig_Obj_t* cofactor_1;
	cofactor_1 = searchOneDimensionalMatrix(CofactorOneMatrix, number_of_factors, factor_index);
	if(cofactor_1 != NULL)
	{
		return cofactor_1;
	}
	else
	{
		// hash table miss
		#ifdef PRINT_VERY_DETAILED_RECORDS_ON_SCREEN
		cout << "\nhash table miss in AIGBasedSkolem::computeCofactorOne(" << var_to_elim_index <<", "<< factor_index <<")\n";
		#endif
		// compute cofactor_1 = factor_i_j with var_i = true
		Aig_Obj_t* factor = searchOneDimensionalMatrix(FactorMatrix, number_of_factors, factor_index);
		assert(factor != NULL);

		cofactor_1 = replaceVariableByConstant(factor, var_to_elim_index, 1);
		assert(cofactor_1 != NULL);

		// Enter into matrix
		insertIntoOneDimensionalMatrix(CofactorOneMatrix, number_of_factors, factor_index, cofactor_1, false);

		return cofactor_1;	
	}	
}


Aig_Obj_t* AIGBasedSkolem::computeNegatedCofactorOne(int var_to_elim_index, int factor_index)
{
	// compute cofactor_1 
	Aig_Obj_t* cofactor_1 = computeCofactorOne(var_to_elim_index, factor_index);
	assert(cofactor_1 != NULL);

	Aig_Obj_t* neg_cofactor_1 = createNot(cofactor_1, pub_aig_manager); // AIG Manager API Call
	assert(neg_cofactor_1 != NULL);

	return neg_cofactor_1;	
}


Aig_Obj_t* AIGBasedSkolem::computeCofactorZero(int var_to_elim_index, int factor_index)
{
	// check if entry already exists in the matrix
	Aig_Obj_t* cofactor_0;
	cofactor_0 = searchOneDimensionalMatrix(CofactorZeroMatrix, number_of_factors, factor_index);
	if(cofactor_0 != NULL)
	{
		return cofactor_0;
	}
	else
	{
		// hash table miss
		#ifdef PRINT_VERY_DETAILED_RECORDS_ON_SCREEN
		cout << "\nhash table miss in AIGBasedSkolem::computeCofactorZero(" << var_to_elim_index <<", "<< factor_index <<")\n";
		#endif
		// compute cofactor_0 = factor_i_j with var_i = false
		Aig_Obj_t* factor = searchOneDimensionalMatrix(FactorMatrix, number_of_factors, factor_index);
		assert(factor != NULL);

		cofactor_0 = replaceVariableByConstant(factor, var_to_elim_index, 0);		
		assert(cofactor_0 != NULL);

		// Enter into matrix
		insertIntoOneDimensionalMatrix(CofactorZeroMatrix, number_of_factors, factor_index, cofactor_0, false);
		
		return cofactor_0;	
	}	
}



Aig_Obj_t* AIGBasedSkolem::computeNegatedCofactorZero(int var_to_elim_index, int factor_index)
{
	// compute cofactor_0 
	Aig_Obj_t* cofactor_0 = computeCofactorZero(var_to_elim_index, factor_index);
	assert(cofactor_0 != NULL);

	Aig_Obj_t* neg_cofactor_0 = createNot(cofactor_0, pub_aig_manager); // AIG Manager API Call
	assert(neg_cofactor_0 != NULL);

	return neg_cofactor_0;	
}



bool AIGBasedSkolem::formulaFreeOfVariable(Aig_Obj_t* formula, int var_index)
{
	#ifdef DEBUG_SKOLEM
	cout << "\nchecking if formula is free of variable_" << var_index << endl;
	#endif

	// sanity checks
	assert(formula != NULL);
	assert(var_index >= 1);

	// obtain the adress of the variable object
	string var_string = searchVarIndexToVarNameMap(var_index_to_var_name_map, var_index);

	number_of_support_operations_for_variable++;

	set<string> support;
	computeSupport(formula, support, pub_aig_manager);  // AIG Manager API Call
	if(support.find(var_string) == support.end()) // formula is free of var_string
	{
		return true;
	}
	else
	{
		return false;
	}
}



Aig_Obj_t* AIGBasedSkolem::replaceVariableByConstant(Aig_Obj_t* OriginalFormula, int var_index_to_replace, int constant_to_substitute)
{

	#ifdef RECORD_KEEP
	number_of_compose_operations_for_variable++;
	#endif

	#ifdef DETAILED_RECORD_KEEP
	unsigned long long int step_ms;
	struct timeval step_start_ms, step_finish_ms;
	gettimeofday (&step_start_ms, NULL); 	
	#endif

	// sanity checks
	assert(OriginalFormula != NULL);
	assert(var_index_to_replace >= 1);
	assert(constant_to_substitute == 0 || constant_to_substitute == 1);

	Aig_Obj_t* FormulaToSubstitute;
	if(constant_to_substitute == 0) // replace by zero
	{
		FormulaToSubstitute = createFalse(pub_aig_manager); // AIG Manager API Call
	}
	else // replace by one
	{
		FormulaToSubstitute = createTrue(pub_aig_manager); // AIG Manager API Call
	}
	assert(FormulaToSubstitute != NULL);

	string var_to_replace = searchVarIndexToVarNameMap(var_index_to_var_name_map, var_index_to_replace);

	Aig_Obj_t* ReplacedFormula = ReplaceLeafByExpression(OriginalFormula, var_to_replace, FormulaToSubstitute, pub_aig_manager); // AIG Manager API Call
	assert(ReplacedFormula != NULL);
	
	#ifdef DETAILED_RECORD_KEEP
	gettimeofday (&step_finish_ms, NULL);
   	step_ms = step_finish_ms.tv_sec * 1000 + step_finish_ms.tv_usec / 1000;
   	step_ms -= step_start_ms.tv_sec * 1000 + step_start_ms.tv_usec / 1000;

	ComposeTime += step_ms;
	#endif

	#ifdef PRINT_VERY_DETAILED_RECORDS_ON_SCREEN
	cout << "\nreplaceVariableByConstant finished in " << step_ms << " milliseconds\n";
	#endif	

	return ReplacedFormula;	
}




Aig_Obj_t* AIGBasedSkolem::replaceVariableByFormula(Aig_Obj_t* OriginalFormula, int var_index_to_replace, Aig_Obj_t* FormulaToSubstitute)
{

	#ifdef RECORD_KEEP
	number_of_compose_operations_for_variable++;
	#endif

	#ifdef DETAILED_RECORD_KEEP
	unsigned long long int step_ms;
	struct timeval step_start_ms, step_finish_ms;
	gettimeofday (&step_start_ms, NULL);
	#endif

	// sanity checks
	assert(OriginalFormula != NULL);
	assert(var_index_to_replace >= 1);
	assert(FormulaToSubstitute != NULL);

	string var_to_replace = searchVarIndexToVarNameMap(var_index_to_var_name_map, var_index_to_replace);
	
	Aig_Obj_t* ReplacedFormula = ReplaceLeafByExpression(OriginalFormula, var_to_replace, FormulaToSubstitute, pub_aig_manager); // AIG Manager API Call
	assert(ReplacedFormula != NULL);
	
	#ifdef DETAILED_RECORD_KEEP
	gettimeofday (&step_finish_ms, NULL);
   	step_ms = step_finish_ms.tv_sec * 1000 + step_finish_ms.tv_usec / 1000;
   	step_ms -= step_start_ms.tv_sec * 1000 + step_start_ms.tv_usec / 1000;

	ComposeTime += step_ms;
	#endif

	#ifdef PRINT_VERY_DETAILED_RECORDS_ON_SCREEN
	cout << "\nreplaceVariableByFormula finished in " << step_ms << " milliseconds\n";		
	#endif

	return ReplacedFormula;	
}





Aig_Obj_t* AIGBasedSkolem::replaceVariablesByFormulas(Aig_Obj_t* OriginalFormula, map<int, Aig_Obj_t*> &replacement_map)
{
	Aig_Obj_t* original_formula = OriginalFormula;

	for(map<int, Aig_Obj_t*>::iterator map_it = replacement_map.begin(); map_it != replacement_map.end(); map_it++)
	{
		int var_index_to_replace = map_it->first;
		Aig_Obj_t* formula_to_substitute = map_it->second;

		assert(original_formula != NULL);
		assert(formula_to_substitute != NULL);

		Aig_Obj_t* replaced_formula = replaceVariableByFormula(original_formula, var_index_to_replace, formula_to_substitute);

		original_formula = replaced_formula; 
	}

	return original_formula;
}





void AIGBasedSkolem::clearVariableSpecificDataStructures()
{
	#ifdef DETAILED_RECORD_KEEP
	for(set<int>::iterator factor_it = FactorsWithVariable.begin(); factor_it != FactorsWithVariable.end(); factor_it++)
	{
		PreviousFactorsWithVariable.insert(*factor_it);			
	}
	#endif

	FactorsWithVariable.clear();

	CofactorOneMatrix.clear();
	CofactorZeroMatrix.clear();
	AlphaMatrix.clear();
	BetaMatrix.clear();
	GammaMatrix.clear();
	DeltaMatrix.clear();
}



void AIGBasedSkolem::performReverseSubstitutionOfSkolemFunctions()
{
	for(int i = number_of_vars_to_elim; i >= 2; i--)
	{
		if(checkTimeOut()) // check for time-out
		{
			cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::performReverseSubstitutionOfSkolemFunctions()\n";
			timed_out = true; // timed_out flag set
			return;
		}

		Aig_Obj_t* skolem_function_to_substitute;
		skolem_function_to_substitute = searchOneDimensionalMatrix(SkolemFunctions, number_of_vars_to_elim, i);
		assert(skolem_function_to_substitute != NULL);	

		if(!mask_printing_cegar_details)
		{
			cout << "\nReplacing variable_" << i << " by its skolem function in the skolem function for preceding variables" << endl;	
		}

		for(int j = i-1; j >= 1; j--)
		{
			if(checkTimeOut()) // check for time-out
			{
				cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::performReverseSubstitutionOfSkolemFunctions()\n";
				timed_out = true; // timed_out flag set
				return;
			}			
			
			Aig_Obj_t* destination_skolem_function;
			destination_skolem_function = searchOneDimensionalMatrix(SkolemFunctions, number_of_vars_to_elim, j);
			assert(destination_skolem_function != NULL);

			#ifdef PRINT_VERY_DETAILED_RECORDS_ON_SCREEN
			cout << "\nReplacing variable_" << i << " by its skolem function in the skolem function for variable_" << j << endl;
			#endif	

			#ifdef DEBUG_SKOLEM
			writeFormulaToFile(pub_aig_manager, destination_skolem_function, "dest_sk_function", ".v", i, j);	
			#endif
			
			destination_skolem_function = replaceVariableByFormula(destination_skolem_function, i, skolem_function_to_substitute);
			assert(destination_skolem_function != NULL);

			#ifdef DEBUG_SKOLEM
			writeFormulaToFile(pub_aig_manager, destination_skolem_function, "dest_sk_function_rev_subst", ".v", i, j);	
			#endif

			insertIntoOneDimensionalMatrix(SkolemFunctions, number_of_vars_to_elim, j, destination_skolem_function, true);

		}//for ends here
		
	}// for ends here

	#ifdef RECORD_KEEP
	total_time_in_compose_operations = total_time_in_compose_operations + ComposeTime;
	total_number_of_compose_operations = total_number_of_compose_operations + number_of_compose_operations_for_variable;
	#endif
}// function ends here




void AIGBasedSkolem::performReverseSubstitutionOfSkolemFunctions(vector<Aig_Obj_t*> &skolem_functions_of_formula)
{

	vector<string> VariablesToEliminate_Vector;
	for(list<string>::iterator list_it = Global_VariablesToEliminate.begin(); list_it != Global_VariablesToEliminate.end(); list_it++)
	{
		string variable_to_eliminate = *list_it;
		VariablesToEliminate_Vector.push_back(variable_to_eliminate);
	}

	if(VariablesToEliminate_Vector.size() != skolem_functions_of_formula.size())
	{
		cout << "\nVariablesToEliminate_Vector.size() = " << VariablesToEliminate_Vector.size() << endl;
		cout << "\nskolem_functions_of_formula.size() = " << skolem_functions_of_formula.size() << endl;
		assert(false);
	}

	for(int i = skolem_functions_of_formula.size()-1; i >= 1; i--)
	{
		if(checkTimeOut()) // check for time-out
		{
			cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::performReverseSubstitutionOfSkolemFunctions\n";
			timed_out = true; // timed_out flag set
			return;
		}

		string variable_to_eliminate = VariablesToEliminate_Vector[i];

		Aig_Obj_t* skolem_function_to_substitute;
		skolem_function_to_substitute = skolem_functions_of_formula[i];
		assert(skolem_function_to_substitute != NULL);	

		if(!mask_printing_cegar_details)
		{
			cout << "\nReplacing variable_" << i+1 << ", i.e., " << variable_to_eliminate << " by its skolem function in the skolem function for preceding variables" << endl;	
		}

		for(int j = i-1; j >= 0; j--)
		{
			if(checkTimeOut()) // check for time-out
			{
				cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::performReverseSubstitutionOfSkolemFunctions\n";
				timed_out = true; // timed_out flag set
				return;
			}			
			
			Aig_Obj_t* destination_skolem_function;
			destination_skolem_function = skolem_functions_of_formula[j];
			assert(destination_skolem_function != NULL);

			#ifdef PRINT_VERY_DETAILED_RECORDS_ON_SCREEN
			cout << "\nReplacing variable_" << i+1 << ", i.e., " << variable_to_eliminate << " by its skolem function in the skolem function for variable_" << j+1 << endl;
			#endif	

			destination_skolem_function = replaceVariableByFormula(destination_skolem_function, variable_to_eliminate, skolem_function_to_substitute);
			assert(destination_skolem_function != NULL);

			skolem_functions_of_formula[j] = destination_skolem_function;

		}//for ends here
		
	}// for ends here
	
}// function ends here



Aig_Obj_t* AIGBasedSkolem::computeAlphaCombinedOrGammaCombined(int var_to_elim_index)
{
	// Let us compute alpha_combined_{var_to_elim_index}\vee gamma_combined_{var_to_elim_index}
	// Suppose i = var_to_elim_index

	// i.e. we need to compute alpha_combined_{i}\vee gamma_combined_{i}
	// i.e., conjunction of alpha_combined_or_gamma_combined_components
	// Each alpha_combined_or_gamma_combined_component_i_j = co-factor-1_i_j
	set<Aig_Obj_t*> alpha_combined_or_gamma_combined_components; 

	#ifdef DEBUG_SKOLEM
	cout << "\ncomputing components of alpha_combined_or_gamma_combined\n";
	#endif

	#ifdef PRINT_VERY_DETAILED_RECORDS_ON_SCREEN
	cout << "\ncomputing components of alpha_combined_or_gamma_combined\n";
	#endif

	#ifdef RECORD_KEEP
	int number_of_factors_containing_var_to_elim_index = FactorsWithVariable.size();
	#endif

	for(set<int>::iterator factor_it = FactorsWithVariable.begin(); factor_it != FactorsWithVariable.end(); factor_it++)
	{
		int factor_index = *factor_it;

		#ifdef DEBUG_SKOLEM
		cout << "\nfactor_index = " << factor_index << endl;
		#endif

		// Suppose j = factor_index
		// Each alpha_combined_or_gamma_combined_component_i_j = co-factor-1_i_j

		Aig_Obj_t* cofactor_1_i_j;
		cofactor_1_i_j = computeCofactorOne(var_to_elim_index, factor_index); 
		assert(cofactor_1_i_j != NULL);	

		Aig_Obj_t* alpha_combined_or_gamma_combined_component = cofactor_1_i_j;			
				
		#ifdef DEBUG_SKOLEM
		writeFormulaToFile(pub_aig_manager, alpha_combined_or_gamma_combined_component, "alpha_combined_or_gamma_combined_component", ".v", var_to_elim_index, factor_index);		
		cout << "\nalpha_combined_or_gamma_combined_component[" << var_to_elim_index << ", " << factor_index << "] obtained\n";			
		#endif

		#ifdef PRINT_VERY_DETAILED_RECORDS_ON_SCREEN
		cout << "\nalpha_combined_or_gamma_combined_component[" << var_to_elim_index << ", " << factor_index << "] obtained\n";	
		cout << "\nsize of alpha_combined_or_gamma_combined_component[" << var_to_elim_index << ", " << factor_index << "] is: " << computeSize(alpha_combined_or_gamma_combined_component, pub_aig_manager) << endl; 
		#endif
				
		alpha_combined_or_gamma_combined_components.insert(alpha_combined_or_gamma_combined_component);	

		FactorsAffectingSkolemFunction.push_back(factor_index);
						
	}// for each factor ends here

	// recall that alpha_combined_or_gamma_combined = conjunction of alpha_combined_or_gamma_combined_components
	Aig_Obj_t* alpha_combined_or_gamma_combined;				
	if(alpha_combined_or_gamma_combined_components.size() == 0) // we should return true in this case as per the defn. of alpha_combined_or_gamma_combined
	{
		alpha_combined_or_gamma_combined = createTrue(pub_aig_manager); 
		assert(alpha_combined_or_gamma_combined != NULL);
	}
	else
	{
		alpha_combined_or_gamma_combined = createAnd(alpha_combined_or_gamma_combined_components, pub_aig_manager);
		assert(alpha_combined_or_gamma_combined != NULL);
	}

	#ifdef DEBUG_SKOLEM
	writeFormulaToFile(pub_aig_manager, alpha_combined_or_gamma_combined, "alpha_combined_or_gamma_combined", ".v", var_to_elim_index, 0);				
	#endif

	#ifdef RECORD_KEEP
	NumberOfFactors = number_of_factors_containing_var_to_elim_index;
	#endif

	return alpha_combined_or_gamma_combined;		
} // function ends here



void AIGBasedSkolem::printFactorGraph(set<string> &Final_VariablesToEliminate_Set)
{
	string dot_file_name = benchmark_name_without_extension;
	dot_file_name += "_factor_graph.dot";

	fstream file_op(dot_file_name.c_str(),ios::out);
        file_op << "digraph G {" << endl;

	set<string> PrintedVariables;
	
	for(int factor_index = 1; factor_index <= number_of_factors; factor_index++)
	{
		// Suppose j = factor_index
		// first let us obtain factor_1_j
			
		Aig_Obj_t* factor_1_j = searchOneDimensionalMatrix(FactorMatrix, number_of_factors, factor_index);
		assert(factor_1_j != NULL);

		set<string> support;
		computeSupport(factor_1_j, support, pub_aig_manager);

		file_op << "f" << factor_index <<"[shape=square, color=red, label=\""<< "f_"<< factor_index <<"\"];"<<endl;

		for(set<string>::iterator support_it = support.begin(); support_it != support.end(); support_it++)
		{
			string variable = *support_it;
			
			if(Final_VariablesToEliminate_Set.find(variable) != Final_VariablesToEliminate_Set.end()) // this is a variable to be eliminated
			{
				if(PrintedVariables.find(variable) == PrintedVariables.end()) //not already printed
				{
					file_op << variable <<"[color=green, label=\""<< variable <<"\"];"<<endl;
					PrintedVariables.insert(variable);
				}

				file_op << "f" << factor_index << "->" << variable << "[dir=none];" << endl;	
			}
			else // this is a variable to remain
			{
			     // do not do anything
			}
		}		
		
	}//for each factor ends here

	file_op << "}" << endl;
	file_op.close();	
}// function ends here


void AIGBasedSkolem::printFactorGraphAsData(set<string> &Final_VariablesToEliminate_Set)
{
	string dat_file_name = benchmark_name_without_extension;
	dat_file_name += "_factor_graph.dat";

	fstream file_op(dat_file_name.c_str(),ios::out);
        
	for(int factor_index = 1; factor_index <= number_of_factors; factor_index++)
	{
		// Suppose j = factor_index
		// first let us obtain factor_1_j
			
		Aig_Obj_t* factor_1_j = searchOneDimensionalMatrix(FactorMatrix, number_of_factors, factor_index);
		assert(factor_1_j != NULL);

		set<string> support;
		computeSupport(factor_1_j, support, pub_aig_manager);

		for(set<string>::iterator support_it = support.begin(); support_it != support.end(); support_it++)
		{
			string variable = *support_it;
			
			if(Final_VariablesToEliminate_Set.find(variable) != Final_VariablesToEliminate_Set.end()) // this is a variable to be eliminated
			{
				int variable_index = searchVarNameToVarIndexMap(var_name_to_var_index_map, variable);				
				file_op << factor_index <<"\t"<< variable_index << endl;
			}
			else // this is a variable to remain
			{
			     // do not do anything
			}
		}		
		
	}//for each factor ends here

	file_op.close();	
}// function ends here



Aig_Obj_t* AIGBasedSkolem::computeSkolemFunctionUsingBadSet(int var_to_elim_index, Aig_Obj_t* &cofactor_one_of_bad_set)
{
	// skolem function = (conjunction of co-factor-1's of factors with var_to_elim_index) \wedge (cofactor-1 of \neg bad_set)

	#ifdef RECORD_KEEP
	unsigned long long int alpha_duration_ms, delta_duration_ms;
	struct timeval start_ms, finish_ms;
	#endif

	#ifdef RECORD_KEEP
	gettimeofday (&start_ms, NULL); 
	#endif

	// computing alpha_combined_or_gamma_combined{var_to_elim_index}
	#ifdef DEBUG_SKOLEM
	cout << "\ncomputing alpha_combined_or_gamma_combined_" << var_to_elim_index << "\n";
	#endif
		
	Aig_Obj_t* alpha_combined_or_gamma_combined;

	if(skolem_function_type_in_jiang == "cofactorone_or_negcofactorzero")
	{
		alpha_combined_or_gamma_combined = computeCofactorOneOrNegCofactorZero(var_to_elim_index);
	}
	else
	{
		alpha_combined_or_gamma_combined = computeAlphaCombinedOrGammaCombined(var_to_elim_index);
	}
	assert(alpha_combined_or_gamma_combined != NULL);

	if(checkTimeOut()) // check for time-out
	{
		cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::computeSkolemFunction\n";
		timed_out = true; // timed_out flag set
		return NULL;
	}

	#ifdef DEBUG_SKOLEM
	cout << "\nalpha_combined_or_gamma_combined_" << var_to_elim_index << " computed\n";
	#endif

	#ifdef RECORD_KEEP
	gettimeofday (&finish_ms, NULL);
	alpha_duration_ms = finish_ms.tv_sec * 1000 + finish_ms.tv_usec / 1000;
	alpha_duration_ms -= start_ms.tv_sec * 1000 + start_ms.tv_usec / 1000;
	AlphaCombGenTime = alpha_duration_ms;
	#endif

	#ifdef DETAILED_RECORD_KEEP
	//cout << "\ncomputeAlphaCombinedOrGammaCombined finished in " << alpha_duration_ms << "milli seconds\n";
	#endif

	#ifdef PRINT_VERY_DETAILED_RECORDS_ON_SCREEN
	cout << "\nsize of alpha_combined_or_gamma_combined is " << computeSize(alpha_combined_or_gamma_combined, pub_aig_manager) << endl;
	#endif

	#ifdef RECORD_KEEP
	AlphaPartSize = computeSize(alpha_combined_or_gamma_combined, pub_aig_manager);
	#endif
	
	// computing cofactor-1 of bad part
	#ifdef RECORD_KEEP
	gettimeofday (&start_ms, NULL); 
	#endif

	// computing bad_part_{var_to_elim_index}
	#ifdef DEBUG_SKOLEM
	cout << "\ncomputing bad_part_" << var_to_elim_index << "\n";
	#endif

	Aig_Obj_t* bad_part;
	cofactor_one_of_bad_set = aig_bad_set;
	bad_part = createTrue(pub_aig_manager);
	assert(bad_part != NULL);
	
	#ifdef DEBUG_SKOLEM
	cout << "\nbad_part computed\n";
	writeFormulaToFile(pub_aig_manager, bad_part, "bad_part", ".v", var_to_elim_index, 0);
	#endif

	#ifdef RECORD_KEEP
	gettimeofday (&finish_ms, NULL);
	delta_duration_ms = finish_ms.tv_sec * 1000 + finish_ms.tv_usec / 1000;
	delta_duration_ms -= start_ms.tv_sec * 1000 + start_ms.tv_usec / 1000;
	DeltaPartGenTime = delta_duration_ms;
	#endif

	#ifdef DETAILED_RECORD_KEEP
	//cout << "\ncomputing delta part finished in " << delta_duration_ms << "milli seconds\n";
	#endif

	#ifdef PRINT_VERY_DETAILED_RECORDS_ON_SCREEN
	cout << "\nsize of bad_part is " << computeSize(bad_part, pub_aig_manager) << endl;
	#endif

	#ifdef RECORD_KEEP
	DeltaPartSize = computeSize(bad_part, pub_aig_manager);
	#endif
	
        //computing skolem_function

	Aig_Obj_t* skolem_function;	
	// skolem_function = alpha_combined_or_gamma_combined \wedge bad_part
	skolem_function = createAnd(alpha_combined_or_gamma_combined, bad_part, pub_aig_manager);	
	assert(skolem_function != NULL);

	#ifdef DEBUG_SKOLEM
	cout << "\nskolem_function computed\n";	
	#endif

	#ifdef PRINT_SKOLEM_FUNCTIONS
	string skolem_function_file_name = benchmark_name_without_extension;
	skolem_function_file_name += "_skolem_function";
	writeFormulaToFile(pub_aig_manager, skolem_function, skolem_function_file_name, ".v", var_to_elim_index, 0);
	#endif

	// Enter into matrix
	insertIntoOneDimensionalMatrix(SkolemFunctions, number_of_vars_to_elim, var_to_elim_index, skolem_function, false);


	if(perform_cegar_on_arbitrary_boolean_formulas)
	{
		//compute cannot-be-one dag and cannot-be-zero dag
		computeCannotBeSetsInsideMonolithic(var_to_elim_index);				
	}

		
	return skolem_function;		
}


void AIGBasedSkolem::updateFactorsWithoutComposition(int var_to_elim_index)
{
	assert(var_to_elim_index < number_of_vars_to_elim);

	for(set<int>::iterator factor_it = FactorsWithVariable.begin(); factor_it != FactorsWithVariable.end(); factor_it++)
	{
		int factor_index = *factor_it;

		#ifdef DEBUG_SKOLEM
		cout << "\nfactor_index = " << factor_index << endl;
		#endif

		// obtain the existing factor
		Aig_Obj_t* previous_factor;
		previous_factor = searchOneDimensionalMatrix(FactorMatrix, number_of_factors, factor_index);
		assert(previous_factor != NULL);

		#ifdef DEBUG_SKOLEM
		writeFormulaToFile(pub_aig_manager, previous_factor, "factor", ".v", var_to_elim_index, factor_index);	
		#endif

		Aig_Obj_t* delta;
		delta = computeDelta(var_to_elim_index, factor_index); 
		assert(delta != NULL);

		Aig_Obj_t* factor = createNot(delta, pub_aig_manager);
		assert(factor != NULL);
		
		#ifdef DEBUG_SKOLEM
		writeFormulaToFile(pub_aig_manager, factor, "factor", ".v", var_to_elim_index+1, factor_index);	
		#endif

		insertIntoOneDimensionalMatrix(FactorMatrix, number_of_factors, factor_index, factor, true);
	}	
}



void AIGBasedSkolem::updateFactorsUsingQuantifierEliminatedResult(int var_to_elim_index, Aig_Obj_t* quantifier_eliminated_result)
{
	assert(var_to_elim_index < number_of_vars_to_elim);

	int factor_count = 1;

	for(set<int>::iterator factor_it = FactorsWithVariable.begin(); factor_it != FactorsWithVariable.end(); factor_it++)
	{
		int factor_index = *factor_it;

		#ifdef DEBUG_SKOLEM
		cout << "\nfactor_index = " << factor_index << endl;
		#endif

		Aig_Obj_t* factor;		
		if(factor_count == FactorsWithVariable.size())
		{
			factor = quantifier_eliminated_result;
		}
		else
		{
			factor = createTrue(pub_aig_manager);
		}
		assert(factor != NULL);
		
		#ifdef DEBUG_SKOLEM
		writeFormulaToFile(pub_aig_manager, factor, "factor", ".v", var_to_elim_index+1, factor_index);	
		#endif

		insertIntoOneDimensionalMatrix(FactorMatrix, number_of_factors, factor_index, factor, true);

		factor_count++;
	}	
}


Aig_Obj_t* AIGBasedSkolem::computeAlphaCombined(int var_to_elim_index)
{
	// Let us compute alpha_combined_{var_to_elim_index}
	// Suppose i = var_to_elim_index

	// i.e. we need to compute alpha_combined_{i}
	// alpha_combined_{i} = disjunction of alpha_combined_components
	set<Aig_Obj_t*> alpha_combined_components; 

	#ifdef DEBUG_SKOLEM
	cout << "\ncomputing components of alpha_combined\n";
	#endif

	#ifdef PRINT_VERY_DETAILED_RECORDS_ON_SCREEN
	cout << "\ncomputing components of alpha_combined\n";
	#endif

	for(set<int>::iterator factor_it = FactorsWithVariable.begin(); factor_it != FactorsWithVariable.end(); factor_it++)
	{
		int factor_index = *factor_it;

		#ifdef DEBUG_SKOLEM
		cout << "\nfactor_index = " << factor_index << endl;
		#endif

		// Suppose j = factor_index
		// Each alpha_combined_component_i_j is the conjunction of
		// alpha_i_j and all_agree_with_i_j				
		
		Aig_Obj_t* alpha_i_j;
		alpha_i_j = computeAlpha(var_to_elim_index, factor_index); 
		assert(alpha_i_j != NULL);

		#ifdef DEBUG_SKOLEM
		writeFormulaToFile(pub_aig_manager, alpha_i_j, "alpha", ".v", var_to_elim_index, factor_index);	
		#endif
		
		// all_agree_with_i_j = conjunction of all_agree_with_components
		Aig_Obj_t* all_agree_with_i_j;
		set<Aig_Obj_t*> all_agree_with_components; 

		#ifdef DEBUG_SKOLEM
		cout << "\nCreating all_agree_with_i_j" << endl;
		#endif
	
		for(set<int>::iterator agree_it = FactorsWithVariable.begin(); agree_it != FactorsWithVariable.end(); agree_it++)
		{
			int agree_index = *agree_it;

			#ifdef DEBUG_SKOLEM
			cout << "\nagree_index = " << agree_index << endl;
			#endif

			// Suppose k = agree_index

			if(factor_index == agree_index) // j == k; no need to consider
			{
				#ifdef DEBUG_SKOLEM
				cout << "\nfactor_index == agree_index; no need to consider" << endl;
				#endif

				continue;
			}

			#ifdef DEBUG_SKOLEM
			cout << "\nfactor_index != agree_index" << endl;
			#endif

			Aig_Obj_t* alpha_i_k;
			alpha_i_k = computeAlpha(var_to_elim_index, agree_index); 
			assert(alpha_i_k != NULL);
						
			#ifdef DEBUG_SKOLEM
			writeFormulaToFile(pub_aig_manager, alpha_i_k, "alpha", ".v", var_to_elim_index, agree_index);
			#endif

			Aig_Obj_t* gamma_i_k;
			gamma_i_k = computeGamma(var_to_elim_index, agree_index); 
			assert(gamma_i_k != NULL);

			#ifdef DEBUG_SKOLEM
			writeFormulaToFile(pub_aig_manager, gamma_i_k, "gamma", ".v", var_to_elim_index, agree_index);
			#endif

		        Aig_Obj_t* all_agree_with_component = createOr(alpha_i_k, gamma_i_k, pub_aig_manager);
			assert(all_agree_with_component != NULL);

			#ifdef DEBUG_SKOLEM
			writeFormulaToFile(pub_aig_manager, all_agree_with_component, "all_agree_with_component", ".v", var_to_elim_index, agree_index);
			#endif

			all_agree_with_components.insert(all_agree_with_component);						
		} // for each agree factor ends here
		

		// computing all_agree_with_i_j
		// recall that all_agree_with_i_j = conjunction of all_agree_with_components
		if(all_agree_with_components.size() == 0)
		{
			all_agree_with_i_j = NULL;
		
			#ifdef DEBUG_SKOLEM
			cout << "\nall_agree_with_i_j = NULL" << endl;
			#endif
		}
		else
		{
			all_agree_with_i_j = createAnd(all_agree_with_components, pub_aig_manager);
			assert(all_agree_with_i_j != NULL);

			#ifdef DEBUG_SKOLEM
			writeFormulaToFile(pub_aig_manager, all_agree_with_i_j, "all_agree_with_i_j", ".v", var_to_elim_index, factor_index);
			#endif
		}

			
		// recall that alpha_combined_component_i_j is the conjunction of
		// alpha_i_j and all_agree_with_i_j
	
		Aig_Obj_t* alpha_combined_component;
		if(all_agree_with_i_j == NULL)
		{
			alpha_combined_component = alpha_i_j;
		}
		else
		{
			alpha_combined_component = createAnd(alpha_i_j, all_agree_with_i_j, pub_aig_manager);
			assert(alpha_combined_component != NULL);
		}

		#ifdef DEBUG_SKOLEM
		writeFormulaToFile(pub_aig_manager, alpha_combined_component, "alpha_combined_component", ".v", var_to_elim_index, factor_index);		
		cout << "\nalpha_combined_component[" << var_to_elim_index << ", " << factor_index << "] obtained\n";			
		#endif
				
		alpha_combined_components.insert(alpha_combined_component);						
	}// for each factor ends here
		

        // recall that alpha_combined = disjunction of alpha_combined_components
	Aig_Obj_t* alpha_combined;				
	if(alpha_combined_components.size() == 0) // we should return false in this case (as per defn. of alpha)
	{
		alpha_combined = createFalse(pub_aig_manager); 
		assert(alpha_combined != NULL);
	}
	else
	{
		alpha_combined = createOr(alpha_combined_components, pub_aig_manager);
		assert(alpha_combined != NULL);
	}


	#ifdef DEBUG_SKOLEM
	writeFormulaToFile(pub_aig_manager, alpha_combined, "alpha_combined", ".v", var_to_elim_index, 0);				
	#endif

	#ifdef RECORD_KEEP
	NumberOfFactors = FactorsWithVariable.size();
	#endif

	// Enter into matrix
	insertIntoOneDimensionalMatrix(AlphaCombineds, number_of_vars_to_elim, var_to_elim_index, alpha_combined, false);
	
	return alpha_combined;	
		
} // function ends here



void AIGBasedSkolem::initializeCEGAR_using_ABC()
{
	#ifdef DEBUG_SKOLEM
	unsigned long long int step_ms;
	struct timeval step_start_ms, step_finish_ms;
	gettimeofday (&step_start_ms, NULL); 	
	#endif

	// Creating F(X', Y) and (B1\vee ... \vee B_n \vee B_{n+1})

	#ifdef DEBUG_SKOLEM
		cout << "\nObtaining Ci's for X'\n";
	#endif	

	#ifdef DEBUG_SKOLEM
	unsigned long long int sub_step_ms;
	struct timeval sub_step_start_ms, sub_step_finish_ms;
	gettimeofday (&sub_step_start_ms, NULL); 	
	#endif

	vector<Aig_Obj_t*> var_to_elim_renamed_objects;

	for(int var_to_elim_index = 1; var_to_elim_index <= number_of_vars_to_elim; var_to_elim_index++)
	{
		string var_to_elim = searchVarIndexToVarNameMap(var_index_to_var_name_map, var_to_elim_index);
		string var_to_elim_renamed = var_to_elim;
		var_to_elim_renamed += "_new";
		
		Aig_Obj_t* var_to_elim_renamed_obj = Aig_ObjCreateCi(pub_aig_manager);	
		int var_to_elim_renamed_id = Aig_ObjId(var_to_elim_renamed_obj); // no need to apply Aig_Regular() as var_to_elim_renamed_obj is CI
		Ci_id_to_Ci_name_map.insert(make_pair(var_to_elim_renamed_id, var_to_elim_renamed));

		Ci_name_to_Ci_number_map.insert(make_pair(var_to_elim_renamed, number_of_Cis));

		var_to_elim_renamed_objects.push_back(var_to_elim_renamed_obj);

		Ci_to_eliminate_renamed_to_Ci_to_eliminate_renamed_object_map.insert(make_pair(var_to_elim_index, var_to_elim_renamed_obj));
		Ci_to_eliminate_renamed_name_to_Ci_to_eliminate_renamed_object_map.insert(make_pair(var_to_elim_renamed, var_to_elim_renamed_obj));

		number_of_Cis++;
	}

	#ifdef DEBUG_SKOLEM
	gettimeofday (&sub_step_finish_ms, NULL);
   	sub_step_ms = sub_step_finish_ms.tv_sec * 1000 + sub_step_finish_ms.tv_usec / 1000;
   	sub_step_ms -= sub_step_start_ms.tv_sec * 1000 + sub_step_start_ms.tv_usec / 1000;
	cout << "\nObtaining Ci's for X' finished in " << sub_step_ms << " milliseconds\n";
	#endif

	#ifdef DEBUG_SKOLEM
		cout << "\nCi's for X' obtained\n";
	#endif	

	#ifdef DEBUG_SKOLEM
	gettimeofday (&sub_step_start_ms, NULL); 	
	#endif

	set<Aig_Obj_t*> B_i_objects;

	// create B_1,...,B_n

	#ifdef DEBUG_SKOLEM
		cout << "\nObtaining Ci's for Bad's\n";
	#endif			

	for(int bad_location_index = 1; bad_location_index <= number_of_vars_to_elim; bad_location_index++)
	{
		string B_i = "B_";
	
		char bad_count_char[100];
		sprintf(bad_count_char, "%d", bad_location_index);
		string bad_count_string(bad_count_char);
		B_i += bad_count_string;
		
		Aig_Obj_t* B_i_obj = Aig_ObjCreateCi(pub_aig_manager);	
		int B_i_id = Aig_ObjId(B_i_obj); // no need to apply Aig_Regular() as B_i_obj is CI

		Ci_id_to_Ci_name_map.insert(make_pair(B_i_id, B_i));

		Ci_name_to_Ci_number_map.insert(make_pair(B_i, number_of_Cis));

		B_i_index_to_B_i_object_map.insert(make_pair(bad_location_index, B_i_obj));

		B_i_objects.insert(B_i_obj);

		number_of_Cis++;
	}

	#ifdef DEBUG_SKOLEM
		cout << "\nCi's for Bad's obtained\n";
	#endif	
	
	#ifdef DEBUG_SKOLEM
	gettimeofday (&sub_step_finish_ms, NULL);
   	sub_step_ms = sub_step_finish_ms.tv_sec * 1000 + sub_step_finish_ms.tv_usec / 1000;
   	sub_step_ms -= sub_step_start_ms.tv_sec * 1000 + sub_step_start_ms.tv_usec / 1000;
	cout << "\nObtaining Ci's for Bad's finished in " << sub_step_ms << " milliseconds\n";
	#endif

	#ifdef DEBUG_SKOLEM
	gettimeofday (&sub_step_start_ms, NULL); 	
	#endif

	#ifdef DEBUG_SKOLEM
		cout << "\nObtaining F(X', Y)\n";
	#endif

	if(!mask_printing_cegar_details)
	{
		cout << "\nObtaining F(X', Y)\n";	
	}

	renamed_conjunction_of_factors = conjunction_of_factors;

	for(int var_to_elim_index = 1; var_to_elim_index <= number_of_vars_to_elim; var_to_elim_index++)
	{
		#ifdef DEBUG_SKOLEM
			cout << "\nvar_to_elim_index = " << var_to_elim_index << endl;
		#endif

		string var_to_elim = searchVarIndexToVarNameMap(var_index_to_var_name_map, var_to_elim_index);

		#ifdef DEBUG_SKOLEM
			cout << "\nvar_to_elim = " << var_to_elim << endl;
		#endif


		Aig_Obj_t* var_to_elim_renamed_obj = var_to_elim_renamed_objects[var_to_elim_index-1];

		#ifdef DEBUG_SKOLEM
			cout << "\nReplacing "<< var_to_elim << " by renamed object for it\n";
		#endif

		renamed_conjunction_of_factors = ReplaceLeafByExpression(renamed_conjunction_of_factors, var_to_elim, var_to_elim_renamed_obj, pub_aig_manager);
	}

	#ifdef DEBUG_SKOLEM
		cout << "\nF(X', Y) obtained\n";
	#endif

	if(!mask_printing_cegar_details)
	{
		cout << "\nF(X', Y) obtained\n";
	}
	
	#ifdef DEBUG_SKOLEM
	gettimeofday (&sub_step_finish_ms, NULL);
   	sub_step_ms = sub_step_finish_ms.tv_sec * 1000 + sub_step_finish_ms.tv_usec / 1000;
   	sub_step_ms -= sub_step_start_ms.tv_sec * 1000 + sub_step_start_ms.tv_usec / 1000;
	cout << "\nObtaining F(X', Y) finished in " << sub_step_ms << " milliseconds\n";
	#endif

	#ifdef DEBUG_SKOLEM
	gettimeofday (&sub_step_start_ms, NULL); 	
	#endif

	#ifdef DEBUG_SKOLEM
		cout << "\nObtaining disjunction_of_bad_symbols\n";
	#endif


	if(B_i_objects.empty())
	{
		disjunction_of_bad_symbols = createFalse(pub_aig_manager);
	}
	else
	{
		disjunction_of_bad_symbols = createOr(B_i_objects, pub_aig_manager);
	}

	#ifdef DEBUG_SKOLEM
		cout << "\ndisjunction_of_bad_symbols obtained\n";
	#endif

	#ifdef DEBUG_SKOLEM
	string renamed_conjunction_of_factors_file_name = benchmark_name_without_extension;
	renamed_conjunction_of_factors_file_name += "_renamed_conjunction_of_factors";

	cout << "\nrenamed_conjunction_of_factors computed\n";
	
	writeFormulaToFile(pub_aig_manager, renamed_conjunction_of_factors, renamed_conjunction_of_factors_file_name, ".v", 0, 0);
	#endif	

	Aig_Obj_t* renamed_conjunction_of_factors_CO = Aig_ObjCreateCo( pub_aig_manager, renamed_conjunction_of_factors ); // to aviod 
	// unwanted cleanup of renamed_conjunction_of_factors
	assert(renamed_conjunction_of_factors_CO != NULL);
	intermediate_cos_created.insert(renamed_conjunction_of_factors_CO);
	
	
	#ifdef DEBUG_SKOLEM
	string disjunction_of_bad_symbols_file_name = benchmark_name_without_extension;
	disjunction_of_bad_symbols_file_name += "_disjunction_of_bad_symbols";

	cout << "\ndisjunction_of_bad_symbols computed\n";

	writeFormulaToFile(pub_aig_manager, disjunction_of_bad_symbols, disjunction_of_bad_symbols_file_name, ".v", 0, 0);
	#endif

	Aig_Obj_t* disjunction_of_bad_symbols_CO = Aig_ObjCreateCo( pub_aig_manager, disjunction_of_bad_symbols ); // to aviod 
	// unwanted cleanup of disjunction_of_bad_symbols
	assert(disjunction_of_bad_symbols_CO != NULL);	
	intermediate_cos_created.insert(disjunction_of_bad_symbols_CO);

	
	#ifdef DEBUG_SKOLEM
	gettimeofday (&sub_step_finish_ms, NULL);
   	sub_step_ms = sub_step_finish_ms.tv_sec * 1000 + sub_step_finish_ms.tv_usec / 1000;
   	sub_step_ms -= sub_step_start_ms.tv_sec * 1000 + sub_step_start_ms.tv_usec / 1000;
	cout << "\nObtaining disjunction of bads and printing finished in " << sub_step_ms << " milliseconds\n";
	#endif

	#ifdef DEBUG_SKOLEM
	gettimeofday (&sub_step_start_ms, NULL); 	
	#endif
		
	if(perform_cegar_on_arbitrary_boolean_formulas && !use_bads_in_unified_cegar)
	{
		// In arbitrary boolean cases, it is better to avoid this
		// unless it is asked to use bads
		// as it was observed that the following code can be expensive
	}
	else
	{
		#ifdef DEBUG_SKOLEM
		cout << "\ncreating bads_to_exclude\n";
		#endif

		map<int, set<string> > bad_supports; 

		for(int var_to_elim_index = 1; var_to_elim_index <= number_of_vars_to_elim; var_to_elim_index++)
		{
			#ifdef DEBUG_SKOLEM
			cout << "\nvar_to_elim_index = " << var_to_elim_index << endl;
			#endif

			Aig_Obj_t* bad_dag;
			bad_dag = searchOneDimensionalMatrix(BadSets, number_of_vars_to_elim, var_to_elim_index);
			if(bad_dag == NULL)
			{
				cout << "\nbad_dag == NULL\n";
				assert(false);		
			}
			else
			{
				//cout << "\nbad_dag != NULL\n";
			}

			set<string> support_bad_dag;
			computeSupport(bad_dag, support_bad_dag, pub_aig_manager);
			bad_supports.insert(make_pair(var_to_elim_index, support_bad_dag));
		}

		set<string> frozen_support;
		frozen_support = variables_not_quantified;		

		for(int var_to_elim_index = number_of_vars_to_elim-1; var_to_elim_index >= 1; var_to_elim_index--)
		{
			set<int> bads_to_exclude_for_me;

			int last_frozen = var_to_elim_index + 1;

			string var_last_frozen = searchVarIndexToVarNameMap(var_index_to_var_name_map, last_frozen);
			frozen_support.insert(var_last_frozen);
			
			for(int lower_index = number_of_vars_to_elim; lower_index >= last_frozen; lower_index--)
			{
				bads_to_exclude_for_me.insert(lower_index);
			}

			for(int upper_index = last_frozen-1; upper_index >= 1; upper_index--)
			{
				set<string> support_bad_upper_index = bad_supports[upper_index];
			
				set<string> remaining_variables_in_support_bad_upper_index;
				set_difference(support_bad_upper_index.begin(), support_bad_upper_index.end(), frozen_support.begin(), frozen_support.end(), inserter(remaining_variables_in_support_bad_upper_index, remaining_variables_in_support_bad_upper_index.begin()));

				if(remaining_variables_in_support_bad_upper_index.empty())
				{
					bads_to_exclude_for_me.insert(upper_index);
				}
			}//for

			#ifdef DEBUG_SKOLEM
			cout << "\nbads_to_exclude["<< var_to_elim_index << "] is\n";
			showSet(bads_to_exclude_for_me, "bads_to_exclude_for_me");
			#endif

			bads_to_exclude.insert(make_pair(var_to_elim_index, bads_to_exclude_for_me));
		}//for

	}//else of if(perform_cegar_on_arbitrary_boolean_formulas && !use_bads_in_unified_cegar)

	#ifdef DEBUG_SKOLEM
	gettimeofday (&sub_step_finish_ms, NULL);
   	sub_step_ms = sub_step_finish_ms.tv_sec * 1000 + sub_step_finish_ms.tv_usec / 1000;
   	sub_step_ms -= sub_step_start_ms.tv_sec * 1000 + sub_step_start_ms.tv_usec / 1000;
	cout << "\nCreating bads to exclude finished in " << sub_step_ms << " milliseconds\n";
	#endif

	#ifdef DEBUG_SKOLEM
	gettimeofday (&step_finish_ms, NULL);
   	step_ms = step_finish_ms.tv_sec * 1000 + step_finish_ms.tv_usec / 1000;
   	step_ms -= step_start_ms.tv_sec * 1000 + step_start_ms.tv_usec / 1000;
	//if(!mask_printing_cegar_details)
	//{
		cout << "\ninitializeCEGAR_using_ABC finished in " << step_ms << " milliseconds\n";
	//}
	#endif
}//function




bool AIGBasedSkolem::obtainValueOfCi(string variable, map<string, bool> &variable_to_value_map)
{
	map<string, bool>::iterator variable_to_value_map_it = variable_to_value_map.find(variable);
	if(variable_to_value_map_it != variable_to_value_map.end())
	{
		#ifdef DEBUG_SKOLEM
			//cout << endl << "Entry exists for " << variable << " in variable_to_value_map" << endl;
		#endif
		return variable_to_value_map_it->second;
	}
	else
	{
		#ifdef DEBUG_SKOLEM
			cout << endl << "Entry does not exist for " << variable << " in variable_to_value_map" << endl;
		#endif

		// get the formula for variable
		Aig_Obj_t* formula;
		int var_to_elim_index = searchVarNameToVarIndexMap(var_name_to_var_index_map, variable);
		if(var_to_elim_index == -1)
		{
			cout << "\nError in function AIGBasedSkolem::obtainValueOfCi! variable other than connection variable and variable to be eliminated encountered\n";
			assert(false);
		}
		else
		{
			#ifdef DEBUG_SKOLEM
			cout << endl << variable << " is a variable to be eliminated" << endl;
			#endif
			formula = searchOneDimensionalMatrix(SkolemFunctions, number_of_vars_to_elim, var_to_elim_index);				

		}


		assert(formula != NULL);

		#ifdef DEBUG_SKOLEM
			cout << endl << "evaluating formula for " << variable << endl;
		#endif		
		
		bool value = evaluateFormulaOfCi(formula, variable_to_value_map);

		#ifdef DEBUG_SKOLEM
			cout << endl << "formula for " << variable << " evaluated\n";
		#endif		


		variable_to_value_map.insert(make_pair(variable, value));

		return value;		
	}
}



bool AIGBasedSkolem::evaluateFormulaOfCi(Aig_Obj_t* formula, map<string, bool> &variable_to_value_map)
{
	EvaluationTable.clear();
	bool value = evaluateFormulaOfCi_DFS(formula, variable_to_value_map);
	return value;
}



bool AIGBasedSkolem::evaluateFormulaOfCi_DFS(Aig_Obj_t* formula, map<string, bool> &variable_to_value_map)
{
	assert(formula != NULL);

	string key = toString(formula);

	t_HashTable<string, bool>::iterator EvaluationTable_it = EvaluationTable.find(key);
	if (EvaluationTable_it != EvaluationTable.end()) // traversed already
	{
		return EvaluationTable_it.getValue();;
	}
	else
	{
		bool node_value;

		if(Aig_IsComplement(formula)) // ~ encountered
		{
			Aig_Obj_t* child_1 = Aig_Regular(formula);
			assert(child_1 != NULL);
			bool child_1_value = evaluateFormulaOfCi_DFS(child_1, variable_to_value_map);
			node_value = !child_1_value;

		} // if(Aig_IsComplement(formula)) ends here
		else if(formula->Type == AIG_OBJ_CI) //CI encountered
		{
			int Ci_id = Aig_ObjId(formula); 
			map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(Ci_id);
			assert(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end());
			string Ci_name = Ci_id_to_Ci_name_map_it->second;

			#ifdef DEBUG_SKOLEM
				//cout << endl << Ci_name << " encountered in evaluation\n";
			#endif			

			node_value = obtainValueOfCi(Ci_name, variable_to_value_map);
		}
		else if(formula->Type == AIG_OBJ_CO) //CO encountered
		{
			cout << "\nError inside function AIGBasedSkolem::evaluateFormulaOfCi_DFS! CO encountered\n";
			assert(false);
		}
		else if(formula->Type == AIG_OBJ_CONST1) // 1 encountered
		{
			node_value = true;
		}
		else if(formula->Type == AIG_OBJ_AND)// child_1 \wedge child_2 encountered
		{
			Aig_Obj_t* child_1 = Aig_ObjChild0(formula);
			Aig_Obj_t* child_2 = Aig_ObjChild1(formula);

			assert(child_1 != NULL);
			assert(child_2 != NULL);

			bool child_1_value = evaluateFormulaOfCi_DFS(child_1, variable_to_value_map);
			bool child_2_value = evaluateFormulaOfCi_DFS(child_2, variable_to_value_map);
			
			node_value = child_1_value && child_2_value;
		}
		else
		{
			cout << "\nError inside function AIGBasedSkolem::evaluateFormulaOfCi_DFS! Unknown formula->Type " << formula->Type << " encountered\n";		
			assert(false);
		}

		EvaluationTable[key] = node_value;

		return node_value;
	} // if(!traversed already) ends here
}



Aig_Obj_t* AIGBasedSkolem::computeQuantifierEliminatedResultUsingSkolemFunction(int var_to_elim_index, Aig_Obj_t* skolem_function)
{
	assert(skolem_function != NULL);

	// QuantifierEliminatedResult = (conjunction of factors with variable) with variable substituted 
	//				by the skolem function

	set<Aig_Obj_t*> QuantifierEliminatedResult_components; 

	for(set<int>::iterator factor_it = FactorsWithVariable.begin(); factor_it != FactorsWithVariable.end(); factor_it++)
	{
		int factor_index = *factor_it;

		#ifdef DEBUG_SKOLEM
		cout << "\nfactor_index = " << factor_index << endl;
		#endif

		Aig_Obj_t* factor = searchOneDimensionalMatrix(FactorMatrix, number_of_factors, factor_index);
		assert(factor != NULL);

		Aig_Obj_t* QuantifierEliminatedResult_component = replaceVariableByFormula(factor, var_to_elim_index, skolem_function);
		assert(QuantifierEliminatedResult_component != NULL);

		QuantifierEliminatedResult_components.insert(QuantifierEliminatedResult_component);						
	}// for each factor ends here

	
	//cout << "\nCreating QuantifierEliminatedResult" << endl;

	Aig_Obj_t* QuantifierEliminatedResult;				
	if(QuantifierEliminatedResult_components.size() == 0) // we should return true in this case
	{
		QuantifierEliminatedResult = createTrue(pub_aig_manager); 
		assert(QuantifierEliminatedResult != NULL);
	}
	else
	{
		QuantifierEliminatedResult = createAnd(QuantifierEliminatedResult_components, pub_aig_manager);
		assert(QuantifierEliminatedResult != NULL);

	}

	//cout << "\nQuantifierEliminatedResult created" << endl;

	#ifdef DETAILED_RECORD_KEEP
	size_of_quantified_result_in_bdd_like_scheme = computeSize(QuantifierEliminatedResult, pub_aig_manager);
	//cout << "\nSize of QuantifierEliminatedResult is " << size_of_quantified_result_in_bdd_like_scheme << endl;
	#endif


	#ifdef DEBUG_SKOLEM
	writeFormulaToFile(pub_aig_manager, QuantifierEliminatedResult, "QuantifierEliminatedResult", ".v", var_to_elim_index, 0);				
	#endif

	return QuantifierEliminatedResult;	
}


Aig_Obj_t* AIGBasedSkolem::computeBetaCombined(int var_to_elim_index)
{
	// Let us compute beta_combined_{var_to_elim_index}
	// Suppose i = var_to_elim_index

	// i.e. we need to compute beta_combined_{i}
	// beta_combined_{i} = disjunction of beta_combined_components
	set<Aig_Obj_t*> beta_combined_components; 

	#ifdef DEBUG_SKOLEM
	cout << "\ncomputing components of beta_combined\n";
	#endif

	#ifdef PRINT_VERY_DETAILED_RECORDS_ON_SCREEN
	cout << "\ncomputing components of beta_combined\n";
	#endif

	for(set<int>::iterator factor_it = FactorsWithVariable.begin(); factor_it != FactorsWithVariable.end(); factor_it++)
	{
		int factor_index = *factor_it;

		#ifdef DEBUG_SKOLEM
		cout << "\nfactor_index = " << factor_index << endl;
		#endif

		// Suppose j = factor_index
		// Each beta_combined_component_i_j is the conjunction of
		// beta_i_j and all_agree_with_i_j				
		
		Aig_Obj_t* beta_i_j;
		beta_i_j = computeBeta(var_to_elim_index, factor_index); 
		assert(beta_i_j != NULL);

		#ifdef DEBUG_SKOLEM
		writeFormulaToFile(pub_aig_manager, beta_i_j, "beta", ".v", var_to_elim_index, factor_index);	
		#endif
		
		// all_agree_with_i_j = conjunction of all_agree_with_components
		Aig_Obj_t* all_agree_with_i_j;
		set<Aig_Obj_t*> all_agree_with_components; 

		#ifdef DEBUG_SKOLEM
		cout << "\nCreating all_agree_with_i_j" << endl;
		#endif
	
		for(set<int>::iterator agree_it = FactorsWithVariable.begin(); agree_it != FactorsWithVariable.end(); agree_it++)
		{
			int agree_index = *agree_it;

			#ifdef DEBUG_SKOLEM
			cout << "\nagree_index = " << agree_index << endl;
			#endif

			// Suppose k = agree_index

			if(factor_index == agree_index) // j == k; no need to consider
			{
				#ifdef DEBUG_SKOLEM
				cout << "\nfactor_index == agree_index; no need to consider" << endl;
				#endif

				continue;
			}

			#ifdef DEBUG_SKOLEM
			cout << "\nfactor_index != agree_index" << endl;
			#endif

			Aig_Obj_t* beta_i_k;
			beta_i_k = computeBeta(var_to_elim_index, agree_index); 
			assert(beta_i_k != NULL);
						
			#ifdef DEBUG_SKOLEM
			writeFormulaToFile(pub_aig_manager, beta_i_k, "beta", ".v", var_to_elim_index, agree_index);
			#endif

			Aig_Obj_t* gamma_i_k;
			gamma_i_k = computeGamma(var_to_elim_index, agree_index); 
			assert(gamma_i_k != NULL);

			#ifdef DEBUG_SKOLEM
			writeFormulaToFile(pub_aig_manager, gamma_i_k, "gamma", ".v", var_to_elim_index, agree_index);
			#endif

		        Aig_Obj_t* all_agree_with_component = createOr(beta_i_k, gamma_i_k, pub_aig_manager);
			assert(all_agree_with_component != NULL);

			#ifdef DEBUG_SKOLEM
			writeFormulaToFile(pub_aig_manager, all_agree_with_component, "all_agree_with_component", ".v", var_to_elim_index, agree_index);
			#endif

			all_agree_with_components.insert(all_agree_with_component);						
		} // for each agree factor ends here
		

		// computing all_agree_with_i_j
		// recall that all_agree_with_i_j = conjunction of all_agree_with_components
		if(all_agree_with_components.size() == 0)
		{
			all_agree_with_i_j = NULL;
		
			#ifdef DEBUG_SKOLEM
			cout << "\nall_agree_with_i_j = NULL" << endl;
			#endif
		}
		else
		{
			all_agree_with_i_j = createAnd(all_agree_with_components, pub_aig_manager);
			assert(all_agree_with_i_j != NULL);

			#ifdef DEBUG_SKOLEM
			writeFormulaToFile(pub_aig_manager, all_agree_with_i_j, "all_agree_with_i_j", ".v", var_to_elim_index, factor_index);
			#endif
		}

			
		// recall that beta_combined_component_i_j is the conjunction of
		// beta_i_j and all_agree_with_i_j
	
		Aig_Obj_t* beta_combined_component;
		if(all_agree_with_i_j == NULL)
		{
			beta_combined_component = beta_i_j;
		}
		else
		{
			beta_combined_component = createAnd(beta_i_j, all_agree_with_i_j, pub_aig_manager);
			assert(beta_combined_component != NULL);
		}

		#ifdef DEBUG_SKOLEM
		writeFormulaToFile(pub_aig_manager, beta_combined_component, "beta_combined_component", ".v", var_to_elim_index, factor_index);		
		cout << "\nbeta_combined_component[" << var_to_elim_index << ", " << factor_index << "] obtained\n";			
		#endif
				
		beta_combined_components.insert(beta_combined_component);						
	}// for each factor ends here
		

        // recall that beta_combined = disjunction of beta_combined_components
	Aig_Obj_t* beta_combined;				
	if(beta_combined_components.size() == 0) // we should return false in this case (as per defn. of beta)
	{
		beta_combined = createFalse(pub_aig_manager); 
		assert(beta_combined != NULL);
	}
	else
	{
		beta_combined = createOr(beta_combined_components, pub_aig_manager);
		assert(beta_combined != NULL);
	}


	#ifdef DEBUG_SKOLEM
	writeFormulaToFile(pub_aig_manager, beta_combined, "beta_combined", ".v", var_to_elim_index, 0);				
	#endif

	// Enter into matrix
	insertIntoOneDimensionalMatrix(BetaCombineds, number_of_vars_to_elim, var_to_elim_index, beta_combined, false);
	
	return beta_combined;	
		
} // function ends here



Aig_Obj_t* AIGBasedSkolem::computeSkolemFunctionAsInterpolant(int var_to_elim_index)
{
	#ifdef DEBUG_SKOLEM
	cout << "\ncomputing skolem function as interpolant\n";
	#endif
	

	Aig_Obj_t* alpha = computeAlphaCombined(var_to_elim_index);
	assert(alpha != NULL);
	size_of_alpha_in_interpolant_computation_for_variable = computeSize(alpha, pub_aig_manager);
	
	Aig_Obj_t* beta = computeBetaCombined(var_to_elim_index);
	assert(beta != NULL);
	size_of_beta_in_interpolant_computation_for_variable = computeSize(beta, pub_aig_manager);


	unsigned long long int interpolate_ms;
	struct timeval interpolate_start_ms, interpolate_finish_ms;
	gettimeofday (&interpolate_start_ms, NULL); 

	Aig_Obj_t* skolem_function;
	skolem_function = Interpolate(pub_aig_manager, alpha, beta);
	if(skolem_function == NULL)
	{
		cout << "\nInterpolation between alpha and beta fails!!See problem_alpha.v and problem_beta.v\n";
		writeFormulaToFile(pub_aig_manager, alpha, "problem_alpha", ".v", 0, 0);
		writeFormulaToFile(pub_aig_manager, beta, "problem_beta", ".v", 0, 0);
		assert(false);
	}

	gettimeofday (&interpolate_finish_ms, NULL);
   	interpolate_ms = interpolate_finish_ms.tv_sec * 1000 + interpolate_finish_ms.tv_usec / 1000;
   	interpolate_ms -= interpolate_start_ms.tv_sec * 1000 + interpolate_start_ms.tv_usec / 1000;
	cout << "\ncomputeSkolemFunctionAsInterpolant finished in " << interpolate_ms << " milliseconds\n";
	time_in_interpolant_computation_for_variable = interpolate_ms;

	total_time_in_interpolant_computation = total_time_in_interpolant_computation + time_in_interpolant_computation_for_variable;

	#ifdef PRINT_SKOLEM_FUNCTIONS_IN_INTERPOLATION
	writeFormulaToFile(pub_aig_manager, skolem_function, "skolem_function", ".v", var_to_elim_index, 0);
	#endif

	return skolem_function;
}



Aig_Obj_t* AIGBasedSkolem::replaceVariablesByFormulas(Aig_Obj_t* OriginalFormula, map<string, Aig_Obj_t*> &replacement_map)
{
	Aig_Obj_t* original_formula = OriginalFormula;

	for(map<string, Aig_Obj_t*>::iterator map_it = replacement_map.begin(); map_it != replacement_map.end(); map_it++)
	{
		string var_to_replace = map_it->first;
		Aig_Obj_t* formula_to_substitute = map_it->second;

		assert(original_formula != NULL);
		assert(formula_to_substitute != NULL);

		Aig_Obj_t* replaced_formula = replaceVariableByFormula(original_formula, var_to_replace, formula_to_substitute);

		original_formula = replaced_formula; 
	}

	return original_formula;
}


Aig_Obj_t* AIGBasedSkolem::replaceVariableByFormula(Aig_Obj_t* OriginalFormula, string var_to_replace, Aig_Obj_t* FormulaToSubstitute)
{

	#ifdef RECORD_KEEP
	number_of_compose_operations_for_variable++;
	#endif

	#ifdef DETAILED_RECORD_KEEP
	unsigned long long int step_ms;
	struct timeval step_start_ms, step_finish_ms;
	gettimeofday (&step_start_ms, NULL);
	#endif

	// sanity checks
	assert(OriginalFormula != NULL);
	assert(FormulaToSubstitute != NULL);

	Aig_Obj_t* ReplacedFormula = ReplaceLeafByExpression(OriginalFormula, var_to_replace, FormulaToSubstitute, pub_aig_manager); // AIG Manager API Call
	assert(ReplacedFormula != NULL);
	
	#ifdef DETAILED_RECORD_KEEP
	gettimeofday (&step_finish_ms, NULL);
   	step_ms = step_finish_ms.tv_sec * 1000 + step_finish_ms.tv_usec / 1000;
   	step_ms -= step_start_ms.tv_sec * 1000 + step_start_ms.tv_usec / 1000;

	ComposeTime += step_ms;
	#endif

	#ifdef PRINT_VERY_DETAILED_RECORDS_ON_SCREEN
	cout << "\nreplaceVariableByFormula finished in " << step_ms << " milliseconds\n";		
	#endif

	return ReplacedFormula;	
}




string AIGBasedSkolem::obtainZVariableString(int var_to_elim_index, int z_i_count)
{
	// Return the string Z_{var_to_elim_index}_{z_i_count}

	string Z_string = "Z_";

	char var_char[100];
	sprintf(var_char, "%d", var_to_elim_index);
	string var_string(var_char);
	Z_string += var_string;
	Z_string += "_";

	char count_char[100];
	sprintf(count_char, "%d", z_i_count);
	string count_string(count_char);
	Z_string += count_string;

	return Z_string;

}



Aig_Obj_t* AIGBasedSkolem::obtainObjectOfTemporaryVariableForIncrementalSolving(string temporary_variable_string)
{
	// check if object for temporary_variable_string is already existing in temporary_variable_for_incremental_solving_to_object_map
	Aig_Obj_t* temporary_variable_object;
	map<string, Aig_Obj_t*>::iterator temporary_variable_for_incremental_solving_to_object_map_it = temporary_variable_for_incremental_solving_to_object_map.find(temporary_variable_string);

	if(temporary_variable_for_incremental_solving_to_object_map_it != temporary_variable_for_incremental_solving_to_object_map.end()) // object for temporary_variable_string exists
	{
		temporary_variable_object = temporary_variable_for_incremental_solving_to_object_map_it->second;
		assert(temporary_variable_object != NULL);		
	}
	else
	{
		// creating new variable object
		temporary_variable_object = Aig_ObjCreateCi(pub_aig_manager);	
		assert(temporary_variable_object != NULL);

		int temporary_variable_object_id = Aig_ObjId(temporary_variable_object); 
		Ci_id_to_Ci_name_map.insert(make_pair(temporary_variable_object_id, temporary_variable_string));
		Ci_name_to_Ci_number_map.insert(make_pair(temporary_variable_string, number_of_Cis));
		temporary_variable_for_incremental_solving_to_object_map.insert(make_pair(temporary_variable_string, temporary_variable_object));		
					
		number_of_Cis++;
	}

	return temporary_variable_object;
}


Aig_Obj_t* AIGBasedSkolem::obtainExistingObjectOfTemporaryVariableForIncrementalSolving(string temporary_variable_string)
{
	// check if object for temporary_variable_string is already existing in temporary_variable_for_incremental_solving_to_object_map
	Aig_Obj_t* temporary_variable_object;
	map<string, Aig_Obj_t*>::iterator temporary_variable_for_incremental_solving_to_object_map_it = temporary_variable_for_incremental_solving_to_object_map.find(temporary_variable_string);

	if(temporary_variable_for_incremental_solving_to_object_map_it != temporary_variable_for_incremental_solving_to_object_map.end()) // object for temporary_variable_string exists
	{
		temporary_variable_object = temporary_variable_for_incremental_solving_to_object_map_it->second;
		assert(temporary_variable_object != NULL);		
	}
	else
	{
		cout << "\nError in function AIGBasedSkolem::obtainExistingObjectOfTemporaryVariableForIncrementalSolving!! No object exists for " << temporary_variable_string << endl;
		assert(false);
	}

	return temporary_variable_object;
}

	

void AIGBasedSkolem::removeTemporaryVariablesFromModel(map<string, int> &Model_of_ExactnessCheck)
{
	map<string, int> Model_of_ExactnessCheck_Cleaned;
	for(map<string, int>::iterator assignment_it = Model_of_ExactnessCheck.begin(); assignment_it != Model_of_ExactnessCheck.end(); assignment_it++)
	{
		string Ci_name = assignment_it->first;
		int Ci_value = assignment_it->second;

		if(temporary_variable_for_incremental_solving_to_object_map.find(Ci_name) == temporary_variable_for_incremental_solving_to_object_map.end())
		{
			Model_of_ExactnessCheck_Cleaned.insert(make_pair(Ci_name, Ci_value));
		}
	}
	Model_of_ExactnessCheck = Model_of_ExactnessCheck_Cleaned;
}


Aig_Obj_t* AIGBasedSkolem::replaceVariablesByConstants(Aig_Obj_t* OriginalFormula, map<int, int> &replacement_map)
{
	Aig_Obj_t* original_formula = OriginalFormula;

	for(map<int, int>::iterator map_it = replacement_map.begin(); map_it != replacement_map.end(); map_it++)
	{
		int var_index_to_replace = map_it->first;
		int constant_to_substitute = map_it->second;

		assert(original_formula != NULL);
		assert(constant_to_substitute == 0 || constant_to_substitute == 1);

		Aig_Obj_t* replaced_formula = replaceVariableByConstant(original_formula, var_index_to_replace, constant_to_substitute);

		original_formula = replaced_formula; 
	}

	return original_formula;
}



void AIGBasedSkolem::allocateStringAndObjectToCannotBeDag(int kind_of_cannot_be, Aig_Obj_t* cannot_be_dag, string &cannot_be_string, Aig_Obj_t* &cannot_be_object)
{
	// create the cannot_be_string

	if(kind_of_cannot_be == 1)
	{
		cannot_be_string = "sigma_";

		cannot_be_one_count++;

		char count_char[100];
		sprintf(count_char, "%d", cannot_be_one_count);
		string count_string(count_char);
		cannot_be_string += count_string;
	}
	else if(kind_of_cannot_be == 0)
	{
		cannot_be_string = "eta_";

		cannot_be_zero_count++;

		char count_char[100];
		sprintf(count_char, "%d", cannot_be_zero_count);
		string count_string(count_char);
		cannot_be_string += count_string;
	}
	else
	{
		cout << "\nUnknown value " << kind_of_cannot_be << " for kind_of_cannot_be in AIGBasedSkolem::allocateStringAndObjectToCannotBeDag\n";
		assert(false);
	}

	// ensure that cannot_be_object	does not exist
	map<string, Aig_Obj_t*>::iterator cannot_be_string_to_cannot_be_object_map_it = cannot_be_string_to_cannot_be_object_map.find(cannot_be_string);
	assert(cannot_be_string_to_cannot_be_object_map_it == cannot_be_string_to_cannot_be_object_map.end());

	// creating cannot_be_object and allocating cannot_be_string --> cannot_be_object
	cannot_be_object = Aig_ObjCreateCi(pub_aig_manager);	
	assert(cannot_be_object != NULL);

	int cannot_be_object_id = Aig_ObjId(cannot_be_object); 
	Ci_id_to_Ci_name_map.insert(make_pair(cannot_be_object_id, cannot_be_string));
	Ci_name_to_Ci_number_map.insert(make_pair(cannot_be_string, number_of_Cis));
	cannot_be_string_to_cannot_be_object_map.insert(make_pair(cannot_be_string, cannot_be_object));		
	number_of_Cis++;

	// creating cannot_be_object --> cannot_be_dag
	cannot_be_object_to_cannot_be_dag_map.insert(make_pair(cannot_be_object, cannot_be_dag));	
}


Aig_Obj_t* AIGBasedSkolem::obtain_initial_mu(int origin, map<Aig_Obj_t*, int> &cannot_be_object_to_value_map, int &number_of_cannot_be_one_elements_selected, int &number_of_cannot_be_zero_elements_selected, int &size_of_initial_mu)
{
	int number_of_cannot_be_one_elements = 0;
	int number_of_cannot_be_zero_elements = 0;

	set<Aig_Obj_t*> dags_from_cannot_be_one_set;
	set<Aig_Obj_t*> dags_from_cannot_be_zero_set;

	#ifdef ADDITIONAL_ASSERTION_CHECKS_INSIDE_CEGAR
	cout << "\norigin = " << origin << endl; 
	#endif
	
	map<int, set<Aig_Obj_t*> >::iterator cannot_be_one_set_it = cannot_be_one_set.find(origin);
	assert(cannot_be_one_set_it != cannot_be_one_set.end());

	set<Aig_Obj_t*> cannot_be_one_set_of_variable = cannot_be_one_set_it->second;

	int cannot_be_one_set_index = 1;

	for(set<Aig_Obj_t*>::iterator cannot_be_one_set_of_variable_it = cannot_be_one_set_of_variable.begin(); cannot_be_one_set_of_variable_it != cannot_be_one_set_of_variable.end(); cannot_be_one_set_of_variable_it++)
	{
		Aig_Obj_t* cannot_be_one_set_object_of_variable = *cannot_be_one_set_of_variable_it;

		map<Aig_Obj_t*, Aig_Obj_t*>::iterator cannot_be_object_to_cannot_be_dag_map_it = cannot_be_object_to_cannot_be_dag_map.find(cannot_be_one_set_object_of_variable);
		assert(cannot_be_object_to_cannot_be_dag_map_it != cannot_be_object_to_cannot_be_dag_map.end());

		Aig_Obj_t* cannot_be_one_set_dag_of_variable = cannot_be_object_to_cannot_be_dag_map_it->second;

		map<Aig_Obj_t*, int>::iterator cannot_be_object_to_value_map_it = cannot_be_object_to_value_map.find(cannot_be_one_set_object_of_variable);
		assert(cannot_be_object_to_value_map_it != cannot_be_object_to_value_map.end());

		int value_of_cannot_be_one_set_object_of_variable = cannot_be_object_to_value_map_it->second;

		if(value_of_cannot_be_one_set_object_of_variable == 1)
		{
			dags_from_cannot_be_one_set.insert(cannot_be_one_set_dag_of_variable);

			number_of_cannot_be_one_elements++;

			#ifdef ADDITIONAL_ASSERTION_CHECKS_INSIDE_CEGAR
			cout << "\ncannot-be-one element at location " << cannot_be_one_set_index << " of size " << computeSize(cannot_be_one_set_dag_of_variable, pub_aig_manager) << " added into dags_from_cannot_be_one_set\n";
			#endif
		}

		cannot_be_one_set_index++;
	}

	map<int, set<Aig_Obj_t*> >::iterator cannot_be_zero_set_it = cannot_be_zero_set.find(origin);
	assert(cannot_be_zero_set_it != cannot_be_zero_set.end());

	set<Aig_Obj_t*> cannot_be_zero_set_of_variable = cannot_be_zero_set_it->second;

	int cannot_be_zero_set_index = 1;

	for(set<Aig_Obj_t*>::iterator cannot_be_zero_set_of_variable_it = cannot_be_zero_set_of_variable.begin(); cannot_be_zero_set_of_variable_it != cannot_be_zero_set_of_variable.end(); cannot_be_zero_set_of_variable_it++)
	{
		Aig_Obj_t* cannot_be_zero_set_object_of_variable = *cannot_be_zero_set_of_variable_it;

		map<Aig_Obj_t*, Aig_Obj_t*>::iterator cannot_be_object_to_cannot_be_dag_map_it = cannot_be_object_to_cannot_be_dag_map.find(cannot_be_zero_set_object_of_variable);
		assert(cannot_be_object_to_cannot_be_dag_map_it != cannot_be_object_to_cannot_be_dag_map.end());

		Aig_Obj_t* cannot_be_zero_set_dag_of_variable = cannot_be_object_to_cannot_be_dag_map_it->second;

		map<Aig_Obj_t*, int>::iterator cannot_be_object_to_value_map_it = cannot_be_object_to_value_map.find(cannot_be_zero_set_object_of_variable);
		assert(cannot_be_object_to_value_map_it != cannot_be_object_to_value_map.end());

		int value_of_cannot_be_zero_set_object_of_variable = cannot_be_object_to_value_map_it->second;

		if(value_of_cannot_be_zero_set_object_of_variable == 1)
		{
			dags_from_cannot_be_zero_set.insert(cannot_be_zero_set_dag_of_variable);

			number_of_cannot_be_zero_elements++;

			#ifdef ADDITIONAL_ASSERTION_CHECKS_INSIDE_CEGAR
			cout << "\ncannot-be-zero element at location " << cannot_be_zero_set_index << " of size " << computeSize(cannot_be_zero_set_dag_of_variable, pub_aig_manager) << " added into dags_from_cannot_be_zero_set\n";
			#endif
		}

		cannot_be_zero_set_index++;
	}

	assert(!dags_from_cannot_be_one_set.empty());
	assert(!dags_from_cannot_be_zero_set.empty());

	Aig_Obj_t* cannot_be_one_part_of_mu;
	Aig_Obj_t* cannot_be_zero_part_of_mu;

	if(select_cannot_be_elements_based_on_supports)
	{
	    // select only one element from cannot-be one and cannot-be zero sets s.t. support of mu is minimum

		#ifdef DEBUG_SKOLEM
		cout << "\nselecting only one element from cannot-be one and cannot-be zero sets s.t. support of mu is minimum\n";
		#endif		

		// first select the cannot-be-one element with minimum support
		set<Aig_Obj_t*>::iterator dags_from_cannot_be_one_set_it = dags_from_cannot_be_one_set.begin();

		Aig_Obj_t* cannot_be_one_dag_selected = *dags_from_cannot_be_one_set_it;
		set<string> support_of_cannot_be_one_dag_selected;
		set<string> yin_support_of_cannot_be_one_dag_selected;

		if(avoid_y_variables_in_select_cannot_be_elements_based_on_supports)
		{
			set<string> temp_support_of_cannot_be_one_dag_selected;
			computeSupport(cannot_be_one_dag_selected, temp_support_of_cannot_be_one_dag_selected, pub_aig_manager);
			
			set_difference(temp_support_of_cannot_be_one_dag_selected.begin(), temp_support_of_cannot_be_one_dag_selected.end(), variables_not_quantified.begin(), variables_not_quantified.end(),inserter(support_of_cannot_be_one_dag_selected, support_of_cannot_be_one_dag_selected.begin()));
			set_difference(temp_support_of_cannot_be_one_dag_selected.begin(), temp_support_of_cannot_be_one_dag_selected.end(), variables_quantified.begin(), variables_quantified.end(),inserter(yin_support_of_cannot_be_one_dag_selected, yin_support_of_cannot_be_one_dag_selected.begin()));
		}
		else
		{
			computeSupport(cannot_be_one_dag_selected, support_of_cannot_be_one_dag_selected, pub_aig_manager);
		}

		int size_of_support_of_cannot_be_one_dag_selected = support_of_cannot_be_one_dag_selected.size();
		int size_of_yin_support_of_cannot_be_one_dag_selected = yin_support_of_cannot_be_one_dag_selected.size();

		#ifdef DEBUG_SKOLEM
		showSet(support_of_cannot_be_one_dag_selected, "support_of_cannot_be_one_dag_selected");
		showSet(yin_support_of_cannot_be_one_dag_selected, "yin_support_of_cannot_be_one_dag_selected");
		#endif
		
		dags_from_cannot_be_one_set_it++;
		for(;dags_from_cannot_be_one_set_it != dags_from_cannot_be_one_set.end(); dags_from_cannot_be_one_set_it++)
		{
			Aig_Obj_t* cannot_be_one_dag = *dags_from_cannot_be_one_set_it;
			set<string> support_of_cannot_be_one_dag;
			set<string> yin_support_of_cannot_be_one_dag;
			
			if(avoid_y_variables_in_select_cannot_be_elements_based_on_supports)
			{
				set<string> temp_support_of_cannot_be_one_dag;
				computeSupport(cannot_be_one_dag, temp_support_of_cannot_be_one_dag, pub_aig_manager);
			
				set_difference(temp_support_of_cannot_be_one_dag.begin(), temp_support_of_cannot_be_one_dag.end(), variables_not_quantified.begin(), variables_not_quantified.end(),inserter(support_of_cannot_be_one_dag, support_of_cannot_be_one_dag.begin()));
				set_difference(temp_support_of_cannot_be_one_dag.begin(), temp_support_of_cannot_be_one_dag.end(), variables_quantified.begin(), variables_quantified.end(),inserter(yin_support_of_cannot_be_one_dag, yin_support_of_cannot_be_one_dag.begin()));
			}
			else
			{
				computeSupport(cannot_be_one_dag, support_of_cannot_be_one_dag, pub_aig_manager);
			}

			int size_of_support_of_cannot_be_one_dag = support_of_cannot_be_one_dag.size();
			int size_of_yin_support_of_cannot_be_one_dag = yin_support_of_cannot_be_one_dag.size();

			#ifdef DEBUG_SKOLEM
			showSet(support_of_cannot_be_one_dag, "support_of_cannot_be_one_dag");
			showSet(yin_support_of_cannot_be_one_dag, "yin_support_of_cannot_be_one_dag");
			#endif

			if(size_of_support_of_cannot_be_one_dag < size_of_support_of_cannot_be_one_dag_selected || (size_of_support_of_cannot_be_one_dag == size_of_support_of_cannot_be_one_dag_selected && size_of_yin_support_of_cannot_be_one_dag < size_of_yin_support_of_cannot_be_one_dag_selected) )
			{
				cannot_be_one_dag_selected = cannot_be_one_dag;
				support_of_cannot_be_one_dag_selected = support_of_cannot_be_one_dag;
				yin_support_of_cannot_be_one_dag_selected = yin_support_of_cannot_be_one_dag;
				size_of_support_of_cannot_be_one_dag_selected = size_of_support_of_cannot_be_one_dag;
				size_of_yin_support_of_cannot_be_one_dag_selected = size_of_yin_support_of_cannot_be_one_dag;
			}

			#ifdef DEBUG_SKOLEM
			showSet(support_of_cannot_be_one_dag_selected, "support_of_cannot_be_one_dag_selected");
			showSet(yin_support_of_cannot_be_one_dag_selected, "yin_support_of_cannot_be_one_dag_selected");
			#endif
		}

		// now select the cannot-be-zero element with minimum (support \union support of selected cannot-be-one element)
		set<Aig_Obj_t*>::iterator dags_from_cannot_be_zero_set_it = dags_from_cannot_be_zero_set.begin();

		Aig_Obj_t* cannot_be_zero_dag_selected = *dags_from_cannot_be_zero_set_it;
		set<string> support_of_cannot_be_zero_dag_selected;
		set<string> yin_support_of_cannot_be_zero_dag_selected;
	
		if(avoid_y_variables_in_select_cannot_be_elements_based_on_supports)
		{
			set<string> temp_support_of_cannot_be_zero_dag_selected;
			computeSupport(cannot_be_zero_dag_selected, temp_support_of_cannot_be_zero_dag_selected, pub_aig_manager);
			
			set_difference(temp_support_of_cannot_be_zero_dag_selected.begin(), temp_support_of_cannot_be_zero_dag_selected.end(), variables_not_quantified.begin(), variables_not_quantified.end(),inserter(support_of_cannot_be_zero_dag_selected, support_of_cannot_be_zero_dag_selected.begin()));

			set_difference(temp_support_of_cannot_be_zero_dag_selected.begin(), temp_support_of_cannot_be_zero_dag_selected.end(), variables_quantified.begin(), variables_quantified.end(),inserter(yin_support_of_cannot_be_zero_dag_selected, yin_support_of_cannot_be_zero_dag_selected.begin()));
		}
		else
		{
			computeSupport(cannot_be_zero_dag_selected, support_of_cannot_be_zero_dag_selected, pub_aig_manager);
		}

		set<string> union_support_selected;
		set_union(support_of_cannot_be_one_dag_selected.begin(), support_of_cannot_be_one_dag_selected.end(), support_of_cannot_be_zero_dag_selected.begin(), support_of_cannot_be_zero_dag_selected.end(),inserter(union_support_selected, union_support_selected.begin()));	
		int size_of_union_support_selected = union_support_selected.size();

		set<string> yin_union_support_selected;
		set_union(yin_support_of_cannot_be_one_dag_selected.begin(), yin_support_of_cannot_be_one_dag_selected.end(), yin_support_of_cannot_be_zero_dag_selected.begin(), yin_support_of_cannot_be_zero_dag_selected.end(),inserter(yin_union_support_selected, yin_union_support_selected.begin()));	
		int size_of_yin_union_support_selected = yin_union_support_selected.size();

		#ifdef DEBUG_SKOLEM
		showSet(support_of_cannot_be_zero_dag_selected, "support_of_cannot_be_zero_dag_selected");
		showSet(union_support_selected, "union_support_selected");
		showSet(yin_union_support_selected, "yin_union_support_selected");
		#endif
		
		dags_from_cannot_be_zero_set_it++;
		for(;dags_from_cannot_be_zero_set_it != dags_from_cannot_be_zero_set.end(); dags_from_cannot_be_zero_set_it++)
		{
			Aig_Obj_t* cannot_be_zero_dag = *dags_from_cannot_be_zero_set_it;
			set<string> support_of_cannot_be_zero_dag;
			set<string> yin_support_of_cannot_be_zero_dag;

			if(avoid_y_variables_in_select_cannot_be_elements_based_on_supports)
			{
				set<string> temp_support_of_cannot_be_zero_dag;
				computeSupport(cannot_be_zero_dag, temp_support_of_cannot_be_zero_dag, pub_aig_manager);
			
				set_difference(temp_support_of_cannot_be_zero_dag.begin(), temp_support_of_cannot_be_zero_dag.end(), variables_not_quantified.begin(), variables_not_quantified.end(),inserter(support_of_cannot_be_zero_dag, support_of_cannot_be_zero_dag.begin()));
				set_difference(temp_support_of_cannot_be_zero_dag.begin(), temp_support_of_cannot_be_zero_dag.end(), variables_quantified.begin(), variables_quantified.end(),inserter(yin_support_of_cannot_be_zero_dag, yin_support_of_cannot_be_zero_dag.begin()));
			}
			else
			{
				computeSupport(cannot_be_zero_dag, support_of_cannot_be_zero_dag, pub_aig_manager);
			}

			set<string> union_support;
			set_union(support_of_cannot_be_one_dag_selected.begin(), support_of_cannot_be_one_dag_selected.end(), support_of_cannot_be_zero_dag.begin(), support_of_cannot_be_zero_dag.end(),inserter(union_support, union_support.begin()));	
			int size_of_union_support = union_support.size();

			set<string> yin_union_support;
			set_union(yin_support_of_cannot_be_one_dag_selected.begin(), yin_support_of_cannot_be_one_dag_selected.end(), yin_support_of_cannot_be_zero_dag.begin(), yin_support_of_cannot_be_zero_dag.end(),inserter(yin_union_support, yin_union_support.begin()));	
			int size_of_yin_union_support = yin_union_support.size();

			#ifdef DEBUG_SKOLEM
			showSet(support_of_cannot_be_zero_dag, "support_of_cannot_be_zero_dag");
			showSet(union_support, "union_support");
			showSet(yin_union_support, "yin_union_support");
			#endif

			if(size_of_union_support < size_of_union_support_selected || (size_of_union_support == size_of_union_support_selected && size_of_yin_union_support < size_of_yin_union_support_selected) )
			{
				cannot_be_zero_dag_selected = cannot_be_zero_dag;
				support_of_cannot_be_zero_dag_selected = support_of_cannot_be_zero_dag;
				yin_support_of_cannot_be_zero_dag_selected = yin_support_of_cannot_be_zero_dag;
				size_of_union_support_selected = size_of_union_support;
				size_of_yin_union_support_selected = size_of_yin_union_support;
			}

			#ifdef DEBUG_SKOLEM
			showSet(support_of_cannot_be_zero_dag_selected, "support_of_cannot_be_zero_dag_selected");
			showSet(union_support_selected, "union_support_selected");
			showSet(yin_union_support_selected, "yin_union_support_selected");
			#endif
		}

		cannot_be_one_part_of_mu = cannot_be_one_dag_selected;
		cannot_be_zero_part_of_mu = cannot_be_zero_dag_selected;

		number_of_cannot_be_one_elements_selected = 1;
		number_of_cannot_be_zero_elements_selected = 1;	

		#ifdef ADDITIONAL_ASSERTION_CHECKS_INSIDE_CEGAR
		cout << "\nsize of cannot-be-one element selected = " << computeSize(cannot_be_one_dag_selected, pub_aig_manager) << endl;
		cout << "\nsize of cannot-be-zero element selected = " << computeSize(cannot_be_zero_dag_selected, pub_aig_manager) << endl;
		#endif
		
	}
	else //take disjunction of all dags in cannot-be one/zero parts
	{
		cannot_be_one_part_of_mu = createOr(dags_from_cannot_be_one_set, pub_aig_manager);
		cannot_be_zero_part_of_mu = createOr(dags_from_cannot_be_zero_set, pub_aig_manager);

		number_of_cannot_be_one_elements_selected = number_of_cannot_be_one_elements;
		number_of_cannot_be_zero_elements_selected = number_of_cannot_be_zero_elements;	
	}

	assert(cannot_be_one_part_of_mu != NULL);
	assert(cannot_be_zero_part_of_mu != NULL);

	Aig_Obj_t* mu;	
	mu = createAnd(cannot_be_one_part_of_mu, cannot_be_zero_part_of_mu, pub_aig_manager);
	assert(mu != NULL);

	size_of_initial_mu = computeSize(mu, pub_aig_manager);

	return mu;
}


Aig_Obj_t* AIGBasedSkolem::obtain_disjunction_of_true_cannot_be_zero_dags(int destination, map<Aig_Obj_t*, int> &cannot_be_object_to_value_map, Aig_Obj_t* cofactor_of_mu, int &number_of_cannot_be_zero_elements_that_are_true_selected)
{
	int number_of_cannot_be_zero_elements_that_are_true = 0;

	set<Aig_Obj_t*> dags_from_cannot_be_zero_set;

	#ifdef ADDITIONAL_ASSERTION_CHECKS_INSIDE_CEGAR
	cout << "\ndestination = " << destination << endl; 
	#endif
	
	map<int, set<Aig_Obj_t*> >::iterator cannot_be_zero_set_it = cannot_be_zero_set.find(destination);
	assert(cannot_be_zero_set_it != cannot_be_zero_set.end());

	set<Aig_Obj_t*> cannot_be_zero_set_of_variable = cannot_be_zero_set_it->second;

	int cannot_be_zero_set_index = 1;

	for(set<Aig_Obj_t*>::iterator cannot_be_zero_set_of_variable_it = cannot_be_zero_set_of_variable.begin(); cannot_be_zero_set_of_variable_it != cannot_be_zero_set_of_variable.end(); cannot_be_zero_set_of_variable_it++)
	{
		Aig_Obj_t* cannot_be_zero_set_object_of_variable = *cannot_be_zero_set_of_variable_it;

		map<Aig_Obj_t*, Aig_Obj_t*>::iterator cannot_be_object_to_cannot_be_dag_map_it = cannot_be_object_to_cannot_be_dag_map.find(cannot_be_zero_set_object_of_variable);
		assert(cannot_be_object_to_cannot_be_dag_map_it != cannot_be_object_to_cannot_be_dag_map.end());

		Aig_Obj_t* cannot_be_zero_set_dag_of_variable = cannot_be_object_to_cannot_be_dag_map_it->second;

		map<Aig_Obj_t*, int>::iterator cannot_be_object_to_value_map_it = cannot_be_object_to_value_map.find(cannot_be_zero_set_object_of_variable);
		assert(cannot_be_object_to_value_map_it != cannot_be_object_to_value_map.end());

		int value_of_cannot_be_zero_set_object_of_variable = cannot_be_object_to_value_map_it->second;

		if(value_of_cannot_be_zero_set_object_of_variable == 1)
		{
			dags_from_cannot_be_zero_set.insert(cannot_be_zero_set_dag_of_variable);
			
			number_of_cannot_be_zero_elements_that_are_true++;

			#ifdef ADDITIONAL_ASSERTION_CHECKS_INSIDE_CEGAR
			cout << "\ncannot-be-zero element at location " << cannot_be_zero_set_index << " of size " << computeSize(cannot_be_zero_set_dag_of_variable, pub_aig_manager) << " added into dags_from_cannot_be_zero_set\n";
			#endif
		}

		cannot_be_zero_set_index++;
	}

	assert(!dags_from_cannot_be_zero_set.empty());
	Aig_Obj_t* cannot_be_zero_part_of_mu;

	if(select_cannot_be_elements_based_on_supports)
	{
		// select the cannot-be-zero element with minimum (support \union support of cofactor_zero_of_mu)

		set<string> support_of_cofactor_of_mu;	
		set<string> yin_support_of_cofactor_of_mu;	

		if(avoid_y_variables_in_select_cannot_be_elements_based_on_supports)
		{
			set<string> temp_support_of_cofactor_of_mu;
			computeSupport(cofactor_of_mu, temp_support_of_cofactor_of_mu, pub_aig_manager);
		
			set_difference(temp_support_of_cofactor_of_mu.begin(), temp_support_of_cofactor_of_mu.end(), variables_not_quantified.begin(), variables_not_quantified.end(),inserter(support_of_cofactor_of_mu, support_of_cofactor_of_mu.begin()));
			set_difference(temp_support_of_cofactor_of_mu.begin(), temp_support_of_cofactor_of_mu.end(), variables_quantified.begin(), variables_quantified.end(),inserter(yin_support_of_cofactor_of_mu, yin_support_of_cofactor_of_mu.begin()));
		}
		else
		{
			computeSupport(cofactor_of_mu, support_of_cofactor_of_mu, pub_aig_manager);
		}

		set<Aig_Obj_t*>::iterator dags_from_cannot_be_zero_set_it = dags_from_cannot_be_zero_set.begin();
		Aig_Obj_t* cannot_be_zero_dag_selected = *dags_from_cannot_be_zero_set_it;
		set<string> support_of_cannot_be_zero_dag_selected;
		set<string> yin_support_of_cannot_be_zero_dag_selected;

		if(avoid_y_variables_in_select_cannot_be_elements_based_on_supports)
		{
			set<string> temp_support_of_cannot_be_zero_dag_selected;
			computeSupport(cannot_be_zero_dag_selected, temp_support_of_cannot_be_zero_dag_selected, pub_aig_manager);
		
			set_difference(temp_support_of_cannot_be_zero_dag_selected.begin(), temp_support_of_cannot_be_zero_dag_selected.end(), variables_not_quantified.begin(), variables_not_quantified.end(),inserter(support_of_cannot_be_zero_dag_selected, support_of_cannot_be_zero_dag_selected.begin()));
			set_difference(temp_support_of_cannot_be_zero_dag_selected.begin(), temp_support_of_cannot_be_zero_dag_selected.end(), variables_quantified.begin(), variables_quantified.end(),inserter(yin_support_of_cannot_be_zero_dag_selected, yin_support_of_cannot_be_zero_dag_selected.begin()));
		}
		else
		{
			computeSupport(cannot_be_zero_dag_selected, support_of_cannot_be_zero_dag_selected, pub_aig_manager);
		}

		set<string> union_support_selected;
		set_union(support_of_cofactor_of_mu.begin(), support_of_cofactor_of_mu.end(), support_of_cannot_be_zero_dag_selected.begin(), support_of_cannot_be_zero_dag_selected.end(),inserter(union_support_selected, union_support_selected.begin()));	
		int size_of_union_support_selected = union_support_selected.size();

		set<string> yin_union_support_selected;
		set_union(yin_support_of_cofactor_of_mu.begin(), yin_support_of_cofactor_of_mu.end(), yin_support_of_cannot_be_zero_dag_selected.begin(), yin_support_of_cannot_be_zero_dag_selected.end(),inserter(yin_union_support_selected, yin_union_support_selected.begin()));	
		int yin_size_of_union_support_selected = yin_union_support_selected.size();

		#ifdef DEBUG_SKOLEM
		showSet(support_of_cofactor_of_mu, "support_of_cofactor_of_mu");
		showSet(support_of_cannot_be_zero_dag_selected, "support_of_cannot_be_zero_dag_selected");
		showSet(union_support_selected, "union_support_selected");
		showSet(yin_union_support_selected, "yin_union_support_selected");
		#endif
		
		dags_from_cannot_be_zero_set_it++;
		for(;dags_from_cannot_be_zero_set_it != dags_from_cannot_be_zero_set.end(); dags_from_cannot_be_zero_set_it++)
		{
			Aig_Obj_t* cannot_be_zero_dag = *dags_from_cannot_be_zero_set_it;
			set<string> support_of_cannot_be_zero_dag;
			set<string> yin_support_of_cannot_be_zero_dag;

			if(avoid_y_variables_in_select_cannot_be_elements_based_on_supports)
			{
				set<string> temp_support_of_cannot_be_zero_dag;
				computeSupport(cannot_be_zero_dag, temp_support_of_cannot_be_zero_dag, pub_aig_manager);
		
				set_difference(temp_support_of_cannot_be_zero_dag.begin(), temp_support_of_cannot_be_zero_dag.end(), variables_not_quantified.begin(), variables_not_quantified.end(),inserter(support_of_cannot_be_zero_dag, support_of_cannot_be_zero_dag.begin()));

				set_difference(temp_support_of_cannot_be_zero_dag.begin(), temp_support_of_cannot_be_zero_dag.end(), variables_quantified.begin(), variables_quantified.end(),inserter(yin_support_of_cannot_be_zero_dag, yin_support_of_cannot_be_zero_dag.begin()));
			}
			else
			{
				computeSupport(cannot_be_zero_dag, support_of_cannot_be_zero_dag, pub_aig_manager);
			}

			set<string> union_support;
			set_union(support_of_cofactor_of_mu.begin(), support_of_cofactor_of_mu.end(), support_of_cannot_be_zero_dag.begin(), support_of_cannot_be_zero_dag.end(),inserter(union_support, union_support.begin()));	
			int size_of_union_support = union_support.size();

			set<string> yin_union_support;
			set_union(yin_support_of_cofactor_of_mu.begin(), yin_support_of_cofactor_of_mu.end(), yin_support_of_cannot_be_zero_dag.begin(), yin_support_of_cannot_be_zero_dag.end(),inserter(yin_union_support, yin_union_support.begin()));	
			int yin_size_of_union_support = yin_union_support.size();

			#ifdef DEBUG_SKOLEM
			showSet(support_of_cannot_be_zero_dag, "support_of_cannot_be_zero_dag");
			showSet(union_support, "union_support");
			showSet(yin_union_support, "yin_union_support");
			#endif

			if(size_of_union_support < size_of_union_support_selected || (size_of_union_support == size_of_union_support_selected &&  yin_size_of_union_support < yin_size_of_union_support_selected))
			{
				cannot_be_zero_dag_selected = cannot_be_zero_dag;
				support_of_cannot_be_zero_dag_selected = support_of_cannot_be_zero_dag;
				yin_support_of_cannot_be_zero_dag_selected = yin_support_of_cannot_be_zero_dag;
				size_of_union_support_selected = size_of_union_support;
				yin_size_of_union_support_selected = yin_size_of_union_support;
			}

			#ifdef DEBUG_SKOLEM
			showSet(support_of_cannot_be_zero_dag_selected, "support_of_cannot_be_zero_dag_selected");
			showSet(union_support_selected, "union_support_selected");
			showSet(yin_union_support_selected, "yin_union_support_selected");
			#endif
		}

		cannot_be_zero_part_of_mu = cannot_be_zero_dag_selected;
		number_of_cannot_be_zero_elements_that_are_true_selected = 1;

		#ifdef ADDITIONAL_ASSERTION_CHECKS_INSIDE_CEGAR
		cout << "\nsize of cannot-be-zero element selected = " << computeSize(cannot_be_zero_dag_selected, pub_aig_manager) << endl;
		#endif
	}
	else
	{
		cannot_be_zero_part_of_mu = createOr(dags_from_cannot_be_zero_set, pub_aig_manager);
		number_of_cannot_be_zero_elements_that_are_true_selected = number_of_cannot_be_zero_elements_that_are_true;
	}
		
	assert(cannot_be_zero_part_of_mu != NULL);

	return cannot_be_zero_part_of_mu;
}


Aig_Obj_t* AIGBasedSkolem::obtain_disjunction_of_true_cannot_be_one_dags(int destination, map<Aig_Obj_t*, int> &cannot_be_object_to_value_map, Aig_Obj_t* cofactor_of_mu, int &number_of_cannot_be_one_elements_that_are_true_selected)
{
	int number_of_cannot_be_one_elements_that_are_true = 0;

	set<Aig_Obj_t*> dags_from_cannot_be_one_set;

	#ifdef ADDITIONAL_ASSERTION_CHECKS_INSIDE_CEGAR
	cout << "\ndestination = " << destination << endl; 
	#endif
	
	map<int, set<Aig_Obj_t*> >::iterator cannot_be_one_set_it = cannot_be_one_set.find(destination);
	assert(cannot_be_one_set_it != cannot_be_one_set.end());

	set<Aig_Obj_t*> cannot_be_one_set_of_variable = cannot_be_one_set_it->second;

	int cannot_be_one_set_index = 1;

	for(set<Aig_Obj_t*>::iterator cannot_be_one_set_of_variable_it = cannot_be_one_set_of_variable.begin(); cannot_be_one_set_of_variable_it != cannot_be_one_set_of_variable.end(); cannot_be_one_set_of_variable_it++)
	{
		Aig_Obj_t* cannot_be_one_set_object_of_variable = *cannot_be_one_set_of_variable_it;

		map<Aig_Obj_t*, Aig_Obj_t*>::iterator cannot_be_object_to_cannot_be_dag_map_it = cannot_be_object_to_cannot_be_dag_map.find(cannot_be_one_set_object_of_variable);
		assert(cannot_be_object_to_cannot_be_dag_map_it != cannot_be_object_to_cannot_be_dag_map.end());

		Aig_Obj_t* cannot_be_one_set_dag_of_variable = cannot_be_object_to_cannot_be_dag_map_it->second;

		map<Aig_Obj_t*, int>::iterator cannot_be_object_to_value_map_it = cannot_be_object_to_value_map.find(cannot_be_one_set_object_of_variable);
		assert(cannot_be_object_to_value_map_it != cannot_be_object_to_value_map.end());

		int value_of_cannot_be_one_set_object_of_variable = cannot_be_object_to_value_map_it->second;

		if(value_of_cannot_be_one_set_object_of_variable == 1)
		{
			dags_from_cannot_be_one_set.insert(cannot_be_one_set_dag_of_variable);

			number_of_cannot_be_one_elements_that_are_true++;

			#ifdef ADDITIONAL_ASSERTION_CHECKS_INSIDE_CEGAR
			cout << "\ncannot-be-one element at location " << cannot_be_one_set_index << " of size " << computeSize(cannot_be_one_set_dag_of_variable, pub_aig_manager) << " added into dags_from_cannot_be_one_set\n";
			#endif
		}

		cannot_be_one_set_index++;
	}

	assert(!dags_from_cannot_be_one_set.empty());
	Aig_Obj_t* cannot_be_one_part_of_mu;

	if(select_cannot_be_elements_based_on_supports)
	{
		// select the cannot-be-one element with minimum (support \union support of cofacto_of_mu)

		set<string> support_of_cofactor_of_mu;
		set<string> yin_support_of_cofactor_of_mu;
		if(avoid_y_variables_in_select_cannot_be_elements_based_on_supports)
		{
			set<string> temp_support_of_cofactor_of_mu;
			computeSupport(cofactor_of_mu, temp_support_of_cofactor_of_mu, pub_aig_manager);
		
			set_difference(temp_support_of_cofactor_of_mu.begin(), temp_support_of_cofactor_of_mu.end(), variables_not_quantified.begin(), variables_not_quantified.end(),inserter(support_of_cofactor_of_mu, support_of_cofactor_of_mu.begin()));
			set_difference(temp_support_of_cofactor_of_mu.begin(), temp_support_of_cofactor_of_mu.end(), variables_quantified.begin(), variables_quantified.end(),inserter(yin_support_of_cofactor_of_mu, yin_support_of_cofactor_of_mu.begin()));
		}
		else
		{
			computeSupport(cofactor_of_mu, support_of_cofactor_of_mu, pub_aig_manager);
		}	
		
		set<Aig_Obj_t*>::iterator dags_from_cannot_be_one_set_it = dags_from_cannot_be_one_set.begin();
		Aig_Obj_t* cannot_be_one_dag_selected = *dags_from_cannot_be_one_set_it;
		set<string> support_of_cannot_be_one_dag_selected;
		set<string> yin_support_of_cannot_be_one_dag_selected;

		if(avoid_y_variables_in_select_cannot_be_elements_based_on_supports)
		{
			set<string> temp_support_of_cannot_be_one_dag_selected;
			computeSupport(cannot_be_one_dag_selected, temp_support_of_cannot_be_one_dag_selected, pub_aig_manager);
		
			set_difference(temp_support_of_cannot_be_one_dag_selected.begin(), temp_support_of_cannot_be_one_dag_selected.end(), variables_not_quantified.begin(), variables_not_quantified.end(),inserter(support_of_cannot_be_one_dag_selected, support_of_cannot_be_one_dag_selected.begin()));
			set_difference(temp_support_of_cannot_be_one_dag_selected.begin(), temp_support_of_cannot_be_one_dag_selected.end(), variables_quantified.begin(), variables_quantified.end(),inserter(yin_support_of_cannot_be_one_dag_selected, yin_support_of_cannot_be_one_dag_selected.begin()));
		}
		else
		{
			computeSupport(cannot_be_one_dag_selected, support_of_cannot_be_one_dag_selected, pub_aig_manager);
		}
		

		set<string> union_support_selected;
		set_union(support_of_cofactor_of_mu.begin(), support_of_cofactor_of_mu.end(), support_of_cannot_be_one_dag_selected.begin(), support_of_cannot_be_one_dag_selected.end(),inserter(union_support_selected, union_support_selected.begin()));	
		int size_of_union_support_selected = union_support_selected.size();

		set<string> yin_union_support_selected;
		set_union(yin_support_of_cofactor_of_mu.begin(), yin_support_of_cofactor_of_mu.end(), yin_support_of_cannot_be_one_dag_selected.begin(), yin_support_of_cannot_be_one_dag_selected.end(),inserter(yin_union_support_selected, yin_union_support_selected.begin()));	
		int yin_size_of_union_support_selected = yin_union_support_selected.size();


		#ifdef DEBUG_SKOLEM
		showSet(support_of_cofactor_of_mu, "support_of_cofactor_of_mu");
		showSet(support_of_cannot_be_one_dag_selected, "support_of_cannot_be_one_dag_selected");
		showSet(union_support_selected, "union_support_selected");
		showSet(yin_union_support_selected, "yin_union_support_selected");
		#endif
		
		dags_from_cannot_be_one_set_it++;
		for(;dags_from_cannot_be_one_set_it != dags_from_cannot_be_one_set.end(); dags_from_cannot_be_one_set_it++)
		{
			Aig_Obj_t* cannot_be_one_dag = *dags_from_cannot_be_one_set_it;
			set<string> support_of_cannot_be_one_dag;
			set<string> yin_support_of_cannot_be_one_dag;

			if(avoid_y_variables_in_select_cannot_be_elements_based_on_supports)
			{
				set<string> temp_support_of_cannot_be_one_dag;
				computeSupport(cannot_be_one_dag, temp_support_of_cannot_be_one_dag, pub_aig_manager);
		
				set_difference(temp_support_of_cannot_be_one_dag.begin(), temp_support_of_cannot_be_one_dag.end(), variables_not_quantified.begin(), variables_not_quantified.end(),inserter(support_of_cannot_be_one_dag, support_of_cannot_be_one_dag.begin()));

				set_difference(temp_support_of_cannot_be_one_dag.begin(), temp_support_of_cannot_be_one_dag.end(), variables_quantified.begin(), variables_quantified.end(),inserter(yin_support_of_cannot_be_one_dag, yin_support_of_cannot_be_one_dag.begin()));
			}
			else
			{
				computeSupport(cannot_be_one_dag, support_of_cannot_be_one_dag, pub_aig_manager);
			}
			
			set<string> union_support;
			set_union(support_of_cofactor_of_mu.begin(), support_of_cofactor_of_mu.end(), support_of_cannot_be_one_dag.begin(), support_of_cannot_be_one_dag.end(),inserter(union_support, union_support.begin()));	
			int size_of_union_support = union_support.size();

			set<string> yin_union_support;
			set_union(yin_support_of_cofactor_of_mu.begin(), yin_support_of_cofactor_of_mu.end(), yin_support_of_cannot_be_one_dag.begin(), yin_support_of_cannot_be_one_dag.end(),inserter(yin_union_support, yin_union_support.begin()));	
			int yin_size_of_union_support = yin_union_support.size();

			#ifdef DEBUG_SKOLEM
			showSet(support_of_cannot_be_one_dag, "support_of_cannot_be_one_dag");
			showSet(union_support, "union_support");
			showSet(yin_union_support, "yin_union_support");
			#endif

			if(size_of_union_support < size_of_union_support_selected || ( size_of_union_support == size_of_union_support_selected &&  yin_size_of_union_support < yin_size_of_union_support_selected))
			{
				cannot_be_one_dag_selected = cannot_be_one_dag;
				support_of_cannot_be_one_dag_selected = support_of_cannot_be_one_dag;
				yin_support_of_cannot_be_one_dag_selected = yin_support_of_cannot_be_one_dag;
				size_of_union_support_selected = size_of_union_support;
				yin_size_of_union_support_selected = yin_size_of_union_support;
			}

			#ifdef DEBUG_SKOLEM
			showSet(support_of_cannot_be_one_dag_selected, "support_of_cannot_be_one_dag_selected");
			showSet(union_support_selected, "union_support_selected");
			showSet(yin_union_support_selected, "yin_union_support_selected");
			#endif
		}

		cannot_be_one_part_of_mu = cannot_be_one_dag_selected;
		number_of_cannot_be_one_elements_that_are_true_selected =  1;

		#ifdef ADDITIONAL_ASSERTION_CHECKS_INSIDE_CEGAR
		cout << "\nsize of cannot-be-zero element selected = " << computeSize(cannot_be_one_dag_selected, pub_aig_manager) << endl;
		#endif
	}
	else
	{
		cannot_be_one_part_of_mu = createOr(dags_from_cannot_be_one_set, pub_aig_manager);
		number_of_cannot_be_one_elements_that_are_true_selected = number_of_cannot_be_one_elements_that_are_true;
	}

	assert(cannot_be_one_part_of_mu != NULL);

	return cannot_be_one_part_of_mu;
}



void AIGBasedSkolem::show_present_refinement_hint(map<int, Aig_Obj_t*> &Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX, map<int, Aig_Obj_t*> &Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX)
{
	"\n\nRefinement hint of cannot-be-1\n";
	for(map<int, Aig_Obj_t*>::iterator hint_it = Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX.begin(); hint_it != Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX.end(); hint_it++)
	{
		cout << endl << hint_it->first << "\t" << hint_it->second;
	}

	"\n\nRefinement hint of cannot-be-0\n";
	for(map<int, Aig_Obj_t*>::iterator hint_it = Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX.begin(); hint_it != Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX.end(); hint_it++)
	{
		cout << endl << hint_it->first << "\t" << hint_it->second;
	}
}


void AIGBasedSkolem::obtainSkolemFunctionsInGraphDecomposition(set<Aig_Obj_t*> &uncovered_edges_factors, list<string> &VariablesToEliminate, map<string, Aig_Obj_t*> &variable_to_skolem_function_map, int iterations_of_loop)
{
	variable_to_skolem_function_map.clear();

	if(uncovered_edges_factors.empty()) //i.e. uncovered_edges = true
	{
		#ifdef DEBUG_SKOLEM
		cout << "\nFactors empty\n";
		#endif

		for(list<string>::iterator list_it = VariablesToEliminate.begin(); list_it != VariablesToEliminate.end(); list_it++)
		{
			string variable_to_eliminate = *list_it;

			Aig_Obj_t* skolem_function = createTrue(pub_aig_manager);
			assert(skolem_function != NULL);

			variable_to_skolem_function_map.insert(make_pair(variable_to_eliminate, skolem_function));			
		}

		#ifdef RECORD_KEEP
		string record_file;
		record_file = logfile_prefix;
		record_file += "skolem_function_generation_details.txt";
		FILE* record_fp = fopen(record_file.c_str(), "a+");
		assert(record_fp != NULL);
		fprintf(record_fp, "\n\nAll TRUE skolem functions generated\n");		
		fclose(record_fp);
		#endif	
	
	}
	else if(perform_cegar_on_arbitrary_boolean_formulas)
	{
		#ifdef DEBUG_SKOLEM
		cout << "\nGenerating Skolem functions using SKF-GEN for Arbitrary Boolean Formulae";
		cout << "\nMASK-PRINTING-CEGAR-DETAILS = " << mask_printing_cegar_details;
		cout << "\nMASK-PRINTING-DETAILS-FILE = " << mask_printing_details_file << endl;
		#endif

		list<string> VariablesToEliminate_Copy;
		VariablesToEliminate_Copy = VariablesToEliminate;

		Aig_Obj_t* arbitrary_boolean_formula = createAnd(uncovered_edges_factors, pub_aig_manager);
		assert(arbitrary_boolean_formula != NULL);
		
		Aig_Obj_t* arbitrary_boolean_formula_CO = Aig_ObjCreateCo( pub_aig_manager, arbitrary_boolean_formula ); 
		assert(arbitrary_boolean_formula_CO != NULL);		

		assert(order_of_elimination_of_variables == 0 || order_of_elimination_of_variables == 1 || order_of_elimination_of_variables == 5 || order_of_elimination_of_variables == 6 || order_of_elimination_of_variables == 7);
		fixOrderOfEliminationForArbitraryBooleanFormula(VariablesToEliminate_Copy, arbitrary_boolean_formula, pub_aig_manager);

		Global_VariablesToEliminate = VariablesToEliminate_Copy;
		copy(Global_VariablesToEliminate.begin(), Global_VariablesToEliminate.end(), inserter(Global_VariablesToEliminate_Set, Global_VariablesToEliminate_Set.begin()));

		set<string> support_arbitrary_boolean_formula;
		computeSupport(arbitrary_boolean_formula, support_arbitrary_boolean_formula, pub_aig_manager);
		set_difference(support_arbitrary_boolean_formula.begin(), support_arbitrary_boolean_formula.end(), Global_VariablesToEliminate_Set.begin(), Global_VariablesToEliminate_Set.end(),inserter(Global_VariablesToRemain_Set, Global_VariablesToRemain_Set.begin()));

		input_arbitrary_boolean_formula = arbitrary_boolean_formula;

		struct timeval callskolem_step_start_ms, callskolem_step_finish_ms;
		
		#ifdef RECORD_KEEP
		string record_file;
		record_file = logfile_prefix;
		record_file += "skolem_function_generation_details.txt";
		FILE* record_fp = fopen(record_file.c_str(), "a+");
		assert(record_fp != NULL);

		int number_of_variables_in_formula;
		set<string> support_formula;
		computeSupport(arbitrary_boolean_formula, support_formula, pub_aig_manager);
		number_of_variables_in_formula = support_formula.size();
		int size_of_original_formula = computeSize(arbitrary_boolean_formula, pub_aig_manager);
		int number_of_variables_to_eliminate_in_formula = Global_VariablesToEliminate_Set.size();

		fprintf(record_fp, "\nsize of F(X,Y) = %d\n|X| = %d\n|X+Y| = %d\n", size_of_original_formula, number_of_variables_to_eliminate_in_formula, number_of_variables_in_formula);

		fclose(record_fp);


		string plot_file;
		plot_file = logfile_prefix;
		plot_file += "skolem_function_generation_details_to_plot.txt";
		FILE* plot_fp = fopen(plot_file.c_str(), "a+");
		assert(plot_fp != NULL);
		fprintf(plot_fp, "\n%s\t%s\t%s", benchmark_type.c_str(), benchmark_name.c_str(), machine.c_str());

		string algorithm_string = "arbitrary_boolean_combinations";
		fprintf(plot_fp, "\t%s", algorithm_string.c_str());
		fprintf(plot_fp, "\t%d\t%d\t%d", size_of_original_formula, number_of_variables_to_eliminate_in_formula, number_of_variables_in_formula);

		string order_string_to_print;
		if(order_of_elimination_of_variables == 0)
		{
			order_string_to_print = "alphabetical";	
		}
		else if(order_of_elimination_of_variables == 1)
		{
			order_string_to_print = "least_occurring_first";	
		}
		else if(order_of_elimination_of_variables == 5)
		{
			order_string_to_print = "most_occurring_first";	
		}
		else if(order_of_elimination_of_variables == 6)
		{
			order_string_to_print = "smallest_cofactor1_first";	
		}
		else if(order_of_elimination_of_variables == 7)
		{
			order_string_to_print = "biggest_cofactor1_first";	
		}	
		else
		{
			cout << "\nUnsupported order\n";
			assert(false);
		}

		fprintf(plot_fp, "\t%s\t", order_string_to_print.c_str());

		fclose(plot_fp);
		#endif

		#ifdef DEBUG_SKOLEM
		writeFormulaToFile(pub_aig_manager, arbitrary_boolean_formula, "arbitrary_input_bool_formula", ".v", 0, 0);	
		#endif


		// Calling Skolem that finds r1's and r0's of all nodes 
		// in the arbitrary_boolean_formula in the HashTables

		call_type polarity = original;
		int depth_from_root = 0;
		Skolem(polarity, arbitrary_boolean_formula, depth_from_root);

		if(checkTimeOut()) // check for time-out
		{
			#ifdef RECORD_KEEP
			string record_file;
			record_file = logfile_prefix;
			record_file += "skolem_function_generation_details.txt";
			FILE* record_fp = fopen(record_file.c_str(), "a+");
			assert(record_fp != NULL);

			fprintf(record_fp, "\nTime-out inside the function AIGBasedSkolem::Skolem\n");

			fclose(record_fp);
			#endif

			cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::callSkolem\n";
			timed_out = true; // timed_out flag set
			return;
		
		}


		// We have r1's and r0's in the HashTables
		// Let us create the Skolem functions

		// Get the r1's from the HashTable
				
		vector<Aig_Obj_t*> list_of_r1s_of_formula;
		obtainFromR1HashTable(polarity, arbitrary_boolean_formula, list_of_r1s_of_formula);

		// Get the Skolem functions by negating the r1's

		assert(list_of_r1s_of_formula.size() == Global_VariablesToEliminate.size());

		vector<Aig_Obj_t*> skolem_functions_of_formula;
		for(int i = 0; i < list_of_r1s_of_formula.size(); i++)
		{
			Aig_Obj_t* r1_i = list_of_r1s_of_formula[i];
			assert(r1_i != NULL);

			Aig_Obj_t* skolem_i = createNot(r1_i, pub_aig_manager); 
			assert(skolem_i != NULL);

			skolem_functions_of_formula.push_back(skolem_i);		
		}

		int i = 0;
		for(list<string>::iterator list_it = Global_VariablesToEliminate.begin(); list_it != Global_VariablesToEliminate.end(); list_it++)
		{
			string variable_to_eliminate = *list_it;
		
			#ifdef DEBUG_SKOLEM
			cout << "\nvariable_to_eliminate = " << variable_to_eliminate << endl;
			#endif

			Aig_Obj_t* skolem_i = skolem_functions_of_formula[i];
			assert(skolem_i != NULL);

			#ifdef RECORD_KEEP
			int final_skolem_function_size = computeSize(skolem_i, pub_aig_manager); // AIG Manager API Call
			skolem_function_sizes_before_reverse_substitution.push_back(final_skolem_function_size);
			sum_of_skolem_function_sizes = sum_of_skolem_function_sizes + final_skolem_function_size;

			if(max_skolem_function_size_before_reverse_substitution == -1)
			{
				max_skolem_function_size_before_reverse_substitution = final_skolem_function_size;
			}
			else if(max_skolem_function_size_before_reverse_substitution < final_skolem_function_size)
			{
				max_skolem_function_size_before_reverse_substitution = final_skolem_function_size;
			}
			if(min_skolem_function_size_before_reverse_substitution == -1)
			{
				min_skolem_function_size_before_reverse_substitution = final_skolem_function_size;
			}
			else if(min_skolem_function_size_before_reverse_substitution > final_skolem_function_size)
			{
				min_skolem_function_size_before_reverse_substitution = final_skolem_function_size;
			}
			#endif

		
			#ifdef DEBUG_SKOLEM
			string skolem_file_name = "skolemfunction_before_revsubstitution_";
			skolem_file_name += variable_to_eliminate;
			skolem_file_name += "_";
			skolem_file_name += logfile_prefix;
			skolem_file_name += ".v";
			writeFormulaToFile(pub_aig_manager, skolem_i, skolem_file_name);
			#endif

			i++;
		
		}// for each variable ends here

		gettimeofday (&callskolem_step_start_ms, NULL); 
	
		performReverseSubstitutionOfSkolemFunctions(skolem_functions_of_formula);

		gettimeofday (&callskolem_step_finish_ms, NULL);
		total_time_in_reverse_substitution_on_arbitrary_boolean_formulas = callskolem_step_finish_ms.tv_sec * 1000 + callskolem_step_finish_ms.tv_usec / 1000;
		total_time_in_reverse_substitution_on_arbitrary_boolean_formulas -= callskolem_step_start_ms.tv_sec * 1000 + callskolem_step_start_ms.tv_usec / 1000;

		if(checkTimeOut()) // check for time-out
		{
			#ifdef RECORD_KEEP
			string record_file;
			record_file = logfile_prefix;
			record_file += "skolem_function_generation_details.txt";
			FILE* record_fp = fopen(record_file.c_str(), "a+");
			assert(record_fp != NULL);

			fprintf(record_fp, "\nTime-out inside the function AIGBasedSkolem::performReverseSubstitutionOfSkolemFunctions\n");

			fclose(record_fp);
			#endif

			cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::callSkolem\n";
			timed_out = true; // timed_out flag set
			return;		
		}


		i = 0;
		for(list<string>::iterator list_it = Global_VariablesToEliminate.begin(); list_it != Global_VariablesToEliminate.end(); list_it++)
		{
			string variable_to_eliminate = *list_it;
		
			#ifdef DEBUG_SKOLEM
			cout << "\nvariable_to_eliminate = " << variable_to_eliminate << endl;
			#endif

			Aig_Obj_t* skolem_i = skolem_functions_of_formula[i];
			assert(skolem_i != NULL);

			variable_to_skolem_function_map.insert(make_pair(variable_to_eliminate, skolem_i));	

			#ifdef RECORD_KEEP
			int final_skolem_function_size = computeSize(skolem_i, pub_aig_manager); // AIG Manager API Call

			skolem_function_sizes_after_reverse_substitution.push_back(final_skolem_function_size);
			sum_of_skolem_function_sizes_after_reverse_substitution = sum_of_skolem_function_sizes_after_reverse_substitution + final_skolem_function_size;

			if(max_skolem_function_size_after_reverse_substitution == -1)
			{
				max_skolem_function_size_after_reverse_substitution = final_skolem_function_size;
			}
			else if(max_skolem_function_size_after_reverse_substitution < final_skolem_function_size)
			{
				max_skolem_function_size_after_reverse_substitution = final_skolem_function_size;
			}
			if(min_skolem_function_size_after_reverse_substitution == -1)
			{
				min_skolem_function_size_after_reverse_substitution = final_skolem_function_size;
			}
			else if(min_skolem_function_size_after_reverse_substitution > final_skolem_function_size)
			{
				min_skolem_function_size_after_reverse_substitution = final_skolem_function_size;
			}
			#endif
		
			#ifdef DEBUG_SKOLEM
			string skolem_file_name = "skolemfunction_after_revsubstitution_";
			skolem_file_name += variable_to_eliminate;
			skolem_file_name += "_";
			skolem_file_name += logfile_prefix;
			skolem_file_name += ".v";
			writeFormulaToFile(pub_aig_manager, skolem_i, skolem_file_name);
			#endif

			i++;
		
		}// for each variable ends here	

		#ifdef RECORD_KEEP
		record_file;
		record_file = logfile_prefix;
		record_file += "skolem_function_generation_details.txt";
		record_fp = fopen(record_file.c_str(), "a+");
		assert(record_fp != NULL);

		fprintf(record_fp, "\nfinal-skolem-function-sizes = ");
		for(map<string, Aig_Obj_t*>::iterator variable_to_skolem_function_map_it = variable_to_skolem_function_map.begin(); variable_to_skolem_function_map_it != variable_to_skolem_function_map.end(); variable_to_skolem_function_map_it++)
		{
			fprintf(record_fp, "%d, ", computeSize(variable_to_skolem_function_map_it->second, pub_aig_manager));
		}	
		fclose(record_fp);
		#endif

		// Connect Skolem functions to outputs; otherwise, they will be deleted in the next pass
		for(map<string, Aig_Obj_t*>::iterator map_it = variable_to_skolem_function_map.begin(); map_it != variable_to_skolem_function_map.end(); map_it++)
		{
			Aig_Obj_t* skolem_i = map_it->second;
			Aig_Obj_t* skolem_i_CO = Aig_ObjCreateCo( pub_aig_manager, skolem_i );
			assert(skolem_i_CO != NULL);	
		}	


		for(list<string>::iterator list_it = VariablesToEliminate.begin(); list_it != VariablesToEliminate.end(); list_it++)
		{
			string variable_to_eliminate = *list_it;
			if(variable_to_skolem_function_map.find(variable_to_eliminate) == variable_to_skolem_function_map.end()) 
			{
				// uncovered_edges_factors free of variable_to_eliminate
				Aig_Obj_t* skolem_function = createTrue(pub_aig_manager);
				assert(skolem_function != NULL);
				variable_to_skolem_function_map.insert(make_pair(variable_to_eliminate, skolem_function));		
			}		
	
		}

		clearAllDataStructures();
		setParametersToDefaults();

		bool cleanup_after_applying_cseqcegar_in_graph_decomposition = true;
		// To optionally switch-off cleanup; but don't switch it off unless
		// there's some problem happening due to cleanup. For the cases that 
		// I have tested, there's no problem. 
		if(cleanup_after_applying_cseqcegar_in_graph_decomposition)
		{
			// cleanup data-structures and then set parameters to defaults
			cleanupDatastructuresAndSetParametersOfSeqCegarToDefaults();
		}
		else
		{
			// set parameters to defaults
			setParametersOfSeqCegarToDefaults();
		}
			
	}
	else
	{
		#ifdef DEBUG_SKOLEM
		cout << "\nFactors NOT empty\n";
		#endif

		#ifdef RECORD_KEEP
		string record_file;
		record_file = logfile_prefix;
		record_file += "skolem_function_generation_details.txt";
		FILE* record_fp = fopen(record_file.c_str(), "a+");
		assert(record_fp != NULL);
		fprintf(record_fp, "\n\nSkolem function generation %d\n", iterations_of_loop-1);		
		fclose(record_fp);

		unsigned long long int total_present_skf_duration_ms;
		struct timeval total_present_skf_start_ms, total_present_skf_finish_ms;
		gettimeofday (&total_present_skf_start_ms, NULL); 
		#endif		


		list<string> VariablesToEliminate_Copy;
		VariablesToEliminate_Copy = VariablesToEliminate;

		if(apply_tsietin_encoding_before_calling_cegarskolem_inside_graph_decomposition)
		{
			Aig_Obj_t* single_factor = createAnd(uncovered_edges_factors, pub_aig_manager);
			assert(single_factor != NULL);

			set<Aig_Obj_t*> factors_generated;
			vector<string> tsietin_variables;
			map<string, Aig_Obj_t*> tsietin_variable_to_object_map;

			getFactorsThroughTsietinUptoThreshold(pub_aig_manager, single_factor, factors_generated, tsietin_variables, false, tsietin_variable_to_object_map);
		
			list<string> tsietin_variables_list(tsietin_variables.begin(), tsietin_variables.end());
			VariablesToEliminate_Copy.sort();
			tsietin_variables_list.sort();
			VariablesToEliminate_Copy.merge(tsietin_variables_list);

			for(map<string, Aig_Obj_t*>::iterator tsietin_variable_to_object_map_it = tsietin_variable_to_object_map.begin(); tsietin_variable_to_object_map_it != tsietin_variable_to_object_map.end(); tsietin_variable_to_object_map_it++)
			{
				string tsietin_variable_name = tsietin_variable_to_object_map_it->first;
				Aig_Obj_t* tsietin_variable_obj = tsietin_variable_to_object_map_it->second;
					
				Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.insert(make_pair(tsietin_variable_name, tsietin_variable_obj));
			}

			factorizedSkolemFunctionGenerator(factors_generated, VariablesToEliminate_Copy);
		
		}
		else
		{
			factorizedSkolemFunctionGenerator(uncovered_edges_factors, VariablesToEliminate_Copy);
		}		

		#ifdef RECORD_KEEP
		gettimeofday (&total_present_skf_finish_ms, NULL);
		total_present_skf_duration_ms = total_present_skf_finish_ms.tv_sec * 1000 + total_present_skf_finish_ms.tv_usec / 1000;
		total_present_skf_duration_ms -= total_present_skf_start_ms.tv_sec * 1000 + total_present_skf_start_ms.tv_usec / 1000;

		total_present_skf_duration_ms = total_present_skf_duration_ms - total_time_in_compute_size;

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
		record_fp = fopen(record_file.c_str(), "a+");
		assert(record_fp != NULL);
		
		if(enable_cegar)
		{
			fprintf(record_fp, "\n\n\nordering-used = %s\ntotal-time-in-initial-abstraction-generation-without-size-computation-time = %llu milliseconds\ntotal-time-in-cegar-loops-without-size-computation-time = %llu milliseconds\nsolver-used = %s\nnumber-of-cegar-iterations = %d\ntotal-time-in-reverse-substitution-without-size-computation-time = %llu milliseconds\ntotal-skolem-function-generation-time-without-size-computation-time = %llu milliseconds\nsize-computation-time = %llu\n", order_string_to_print.c_str(), total_time_in_initial_abstraction_generation_in_cegar, total_time_in_cegar_loops_in_cegar, solver.c_str(), cegar_iteration_number, total_time_in_reverse_substitution_in_cegar, total_present_skf_duration_ms, total_time_in_compute_size);
			
		}
		else
		{
			fprintf(record_fp, "\n\n\nordering-used = %s\ntotal-time-in-initial-skolem-function-generation-without-size-computation-time = %llu milliseconds\ntotal-time-in-reverse-substitution-without-size-computation-time = %llu milliseconds\ntotal-skolem-function-generation-time-without-size-computation-time = %llu milliseconds\ntotal-time-in-interpolant-computation = %llu\nsize-computation-time = %llu\n", order_string_to_print.c_str(), total_time_in_initial_abstraction_generation_in_cegar, total_time_in_reverse_substitution_in_cegar, total_present_skf_duration_ms, total_time_in_interpolant_computation, total_time_in_compute_size);
		}
		
		
		
		fprintf(record_fp, "\nfinal-skolem-function-sizes = ");
		for(list<int>::iterator sfs_it = skolem_function_sizes_after_reverse_substitution.begin(); sfs_it != skolem_function_sizes_after_reverse_substitution.end(); sfs_it++)
		{
			fprintf(record_fp, "%d, ", *sfs_it);
		}	
		fclose(record_fp);
		#endif	

		for(list<string>::iterator list_it = VariablesToEliminate.begin(); list_it != VariablesToEliminate.end(); list_it++)
		{
			string variable_to_eliminate = *list_it;
			int index_of_variable_to_eliminate = searchVarNameToVarIndexMap(var_name_to_var_index_map, variable_to_eliminate);
			Aig_Obj_t* skolem_function;
			
			if(index_of_variable_to_eliminate == -1) // uncovered_edges_factors free of variable_to_eliminate
			{
				skolem_function = createTrue(pub_aig_manager);
				assert(skolem_function != NULL);
			}
			else
			{
				skolem_function = searchOneDimensionalMatrix(SkolemFunctions, number_of_vars_to_elim, index_of_variable_to_eliminate);
				assert(skolem_function != NULL);		
			}

			variable_to_skolem_function_map.insert(make_pair(variable_to_eliminate, skolem_function));	

			#ifdef DEBUG_SKOLEM
			cout << "\nvariable_to_eliminate = " << variable_to_eliminate << "\tsize of Skolem function = " << computeSize(skolem_function, pub_aig_manager) << endl;
			#endif
	
		}

		clearAllDataStructures();
	}
}


int AIGBasedSkolem::graphDecomposition(set<Aig_Obj_t*> &transition_function_factors, set<Aig_Obj_t*> &transition_function_parts, list<string> &VariablesToEliminate, map<Aig_Obj_t*, Aig_Obj_t*> &Output_Object_to_RHS_of_Factors, map<Aig_Obj_t*, Aig_Obj_t*> &Output_Object_to_RHS_of_PrimaryOutputs, ABC* abcObj, Abc_Frame_t* abcFrame)
{
	int return_value = 1; // 1 indicates a specific component exists, 0 indicates component does not exist
	assert(!transition_function_factors.empty());
	Aig_Obj_t* transition_function = createAnd(transition_function_factors, pub_aig_manager);
	assert(transition_function != NULL);
	Aig_Obj_t* transition_function_CO = Aig_ObjCreateCo( pub_aig_manager, transition_function ); // to aviod 
	// unwanted cleanup of transition_function
	assert(transition_function_CO != NULL);

	// Let's avoid unnecessary variables from VariablesToEliminate

	#ifdef DEBUG_SKOLEM
	cout << endl << "VariablesToEliminate" << endl;
	showList(VariablesToEliminate);	
	#endif

	set<string> Local_VariablesToEliminate_Set; // All input variables
	copy(VariablesToEliminate.begin(), VariablesToEliminate.end(), inserter(Local_VariablesToEliminate_Set, Local_VariablesToEliminate_Set.begin()));

	set<string> Support_transition_function; // All variables in support
	computeSupport(transition_function, Support_transition_function, pub_aig_manager);

	set<string> Final_VariablesToEliminate_Set;
	set_intersection(Local_VariablesToEliminate_Set.begin(), Local_VariablesToEliminate_Set.end(), Support_transition_function.begin(), Support_transition_function.end(),inserter(Final_VariablesToEliminate_Set, Final_VariablesToEliminate_Set.begin())); // we set the Final_VariablesToEliminate_Set as the input variables that are present in the support

	// set the variables to be eliminated in that order
	VariablesToEliminate.clear();		
	// push back the variables in VariablesToEliminate
	for(set<string>::iterator Final_VariablesToEliminate_Set_it = 	Final_VariablesToEliminate_Set.begin(); Final_VariablesToEliminate_Set_it != Final_VariablesToEliminate_Set.end(); Final_VariablesToEliminate_Set_it++)
	{
		string varible_to_eliminate = *Final_VariablesToEliminate_Set_it;
		VariablesToEliminate.push_back(varible_to_eliminate);
	}		

	#ifdef DEBUG_SKOLEM	
	cout << endl << "VariablesToEliminate after avoiding unnecessary variables" << endl;
	showList(VariablesToEliminate);	
	#endif

	if(component_generation_strategy == "preferred_edge" && purify_failure_condition)
	{
		#ifdef DEBUG_SKOLEM
		string failure_condition_aig_file_name = benchmark_name_without_extension;
		failure_condition_aig_file_name += "_failure_condition";
		writeFormulaToFile(pub_aig_manager, failure_condition_aig, failure_condition_aig_file_name, ".v", 0, 0);
		#endif

		purifyFailureCondition(pub_aig_manager);

		Aig_Obj_t* failure_condition_aig_CO = Aig_ObjCreateCo( pub_aig_manager, failure_condition_aig ); // to aviod unwanted cleanup of failure_condition_aig
		assert(failure_condition_aig_CO != NULL);

		#ifdef DEBUG_SKOLEM
		failure_condition_aig_file_name = benchmark_name_without_extension;
		failure_condition_aig_file_name += "_failure_condition_purified";
		writeFormulaToFile(pub_aig_manager, failure_condition_aig, failure_condition_aig_file_name, ".v", 0, 0);
		#endif
		
	}
		
	#ifdef DEBUG_SKOLEM
	string transition_function_file_name = benchmark_name_without_extension;
	transition_function_file_name += "_transition_function";
	writeFormulaToFile(pub_aig_manager, transition_function, transition_function_file_name, ".v", 0, 0);
	#endif

	map<string, Aig_Obj_t*> variable_to_skolem_function_map;

	if(component_generation_strategy == "preferred_edge")
	{
		Aig_Obj_t* uncovered_edges;
		uncovered_edges = createTrue(pub_aig_manager);
		assert(uncovered_edges != NULL);

		assert(failure_condition_aig != NULL);

		bool more_components_existing = true;	
		int iterations_of_loop = 1;

		Aig_Obj_t* previous_failure_condition_aig;

		while(more_components_existing)// always true; exit is through break inside
		{
		
			set<Aig_Obj_t*> preferred_edges_factors;

			set<string> failure_condition_support;
			computeSupport(failure_condition_aig, failure_condition_support, pub_aig_manager);

			set<string> inputs_in_failure_condition;
			set_intersection(failure_condition_support.begin(), failure_condition_support.end(), input_names_in_circuit.begin(), input_names_in_circuit.end(), inserter(inputs_in_failure_condition, inputs_in_failure_condition.begin()));
			
			#ifdef DEBUG_SKOLEM
			cout << "\nSize of failure_condition_aig = " << computeSize(failure_condition_aig, pub_aig_manager) << endl;
			#endif			

			#ifdef DEBUG_SKOLEM
			string failure_condition_aig_file_name = benchmark_name_without_extension;
			failure_condition_aig_file_name += "_failure_condition";
			cout << "\nSee " << failure_condition_aig_file_name << "...v for failure_condition_aig" << endl;
			writeFormulaToFile(pub_aig_manager, failure_condition_aig, failure_condition_aig_file_name, ".v", 0, iterations_of_loop);
			#endif		
		
			if(!inputs_in_failure_condition.empty())
			{
				#ifdef DEBUG_SKOLEM
				cout << "\nCase where failure condition involves inputs\n";
				#endif

				// In this case, we have Fail(X, I), i.e., Fail gives edges that are bad
				// Hence we should find Skolem functions for I in Fail(X, I)

				// Two options
				if(use_uncovered_edge_with_preferred_edge)
				{
					// Conjoin with uncovered_edges
					Aig_Obj_t* failure_condition_aig_conjoined_with_uncovered_edges;
					failure_condition_aig_conjoined_with_uncovered_edges = createAnd(failure_condition_aig, uncovered_edges, pub_aig_manager); 
					assert(failure_condition_aig_conjoined_with_uncovered_edges != NULL);

					Aig_Obj_t* failure_condition_aig_conjoined_with_uncovered_edges_CO = Aig_ObjCreateCo( pub_aig_manager, failure_condition_aig_conjoined_with_uncovered_edges ); // to aviod unwanted cleanup of failure_condition_aig_conjoined_with_uncovered_edges
					assert(failure_condition_aig_conjoined_with_uncovered_edges_CO != NULL);

					set<string> support_formula;
					computeSupport(failure_condition_aig_conjoined_with_uncovered_edges, support_formula, pub_aig_manager); 

					set<string> VariablesToEliminate_Set(VariablesToEliminate.begin(), VariablesToEliminate.end());

					set<string> varstoelim_in_support_formula;
					set_intersection(support_formula.begin(), support_formula.end(), VariablesToEliminate_Set.begin(), VariablesToEliminate_Set.end(), inserter(varstoelim_in_support_formula, varstoelim_in_support_formula.begin()));

					if(!varstoelim_in_support_formula.empty())
					{
						preferred_edges_factors.insert(failure_condition_aig_conjoined_with_uncovered_edges);
					}

				}
				else
				{
					// Don't conjoin with uncovered_edges

					set<string> support_formula;
					computeSupport(failure_condition_aig, support_formula, pub_aig_manager); 

					set<string> VariablesToEliminate_Set(VariablesToEliminate.begin(), VariablesToEliminate.end());

					set<string> varstoelim_in_support_formula;
					set_intersection(support_formula.begin(), support_formula.end(), VariablesToEliminate_Set.begin(), VariablesToEliminate_Set.end(), inserter(varstoelim_in_support_formula, varstoelim_in_support_formula.begin()));

					if(!varstoelim_in_support_formula.empty())
					{
						preferred_edges_factors.insert(failure_condition_aig);
					}
				}
			}
			else
			{
				#ifdef DEBUG_SKOLEM
				cout << "\nCase where failure condition does NOT involve inputs\n";
				#endif

				// In this case, we have Fail(X). 
				// Hence we should find Skolem functions for I in ~Fail(X)\wedge Fail(F(X, I)), 
				// where X' = F(X, I) is the transition function

				Aig_Obj_t* edge_to_fail_states;
				edge_to_fail_states = obtainEdgeToFailStates(failure_condition_aig, Output_Object_to_RHS_of_Factors);
				assert(edge_to_fail_states != NULL); // Fail(F(X, I))

				#ifdef DEBUG_SKOLEM
				cout << "\nsize of Fail(X) = " << computeSize(failure_condition_aig, pub_aig_manager) << endl;
				cout << "\nsize of Fail(F(X, I)) = " << computeSize(edge_to_fail_states, pub_aig_manager) << endl;
				#endif

				Aig_Obj_t* preferred_edges_factor;
				if(conjoin_negfail_with_failfxi_to_get_preferred_edges)
				{
					preferred_edges_factor = createAnd( createNot(failure_condition_aig, pub_aig_manager), edge_to_fail_states, pub_aig_manager); // ~Fail(X)\wedge Fail(F(X, I)) 
				}
				else
				{
					preferred_edges_factor = edge_to_fail_states; // Fail(F(X, I))
				}
				assert(preferred_edges_factor != NULL); 

				#ifdef DEBUG_SKOLEM
				cout << "\nSize of Pref_Edges(X,I) = " << computeSize(preferred_edges_factor, pub_aig_manager) << endl;
				#endif

				#ifdef DEBUG_SKOLEM
				string preferred_edges_file_name = benchmark_name_without_extension;
				preferred_edges_file_name += "_preferred_edges";
				cout << "\nSee " << preferred_edges_file_name << "...v for preferred_edges" << endl;
				writeFormulaToFile(pub_aig_manager, preferred_edges_factor, preferred_edges_file_name, ".v", 0, iterations_of_loop);
				#endif	

				// Two options
				if(use_uncovered_edge_with_preferred_edge)
				{
					// Conjoin with uncovered_edges

					Aig_Obj_t* preferred_edges_factor_conjoined_with_uncovered_edges;
					preferred_edges_factor_conjoined_with_uncovered_edges = createAnd(preferred_edges_factor, uncovered_edges, pub_aig_manager); 
					assert(preferred_edges_factor_conjoined_with_uncovered_edges != NULL);

					Aig_Obj_t* preferred_edges_factor_conjoined_with_uncovered_edges_CO = Aig_ObjCreateCo( pub_aig_manager, preferred_edges_factor_conjoined_with_uncovered_edges ); // to aviod unwanted cleanup of preferred_edges_factor_conjoined_with_uncovered_edges
					assert(preferred_edges_factor_conjoined_with_uncovered_edges_CO != NULL);
					
					set<string> support_formula;
					computeSupport(preferred_edges_factor_conjoined_with_uncovered_edges, support_formula, pub_aig_manager); 

					set<string> VariablesToEliminate_Set(VariablesToEliminate.begin(), VariablesToEliminate.end());

					set<string> varstoelim_in_support_formula;
					set_intersection(support_formula.begin(), support_formula.end(), VariablesToEliminate_Set.begin(), VariablesToEliminate_Set.end(), inserter(varstoelim_in_support_formula, varstoelim_in_support_formula.begin()));

					if(!varstoelim_in_support_formula.empty())
					{
						preferred_edges_factors.insert(preferred_edges_factor_conjoined_with_uncovered_edges);		
					}

				}
				else
				{	
					// Don't conjoin with uncovered_edges
					Aig_Obj_t* preferred_edges_factor_CO = Aig_ObjCreateCo( pub_aig_manager, preferred_edges_factor ); // to aviod unwanted cleanup of preferred_edges_factor
					assert(preferred_edges_factor_CO != NULL);
			
					set<string> support_formula;
					computeSupport(preferred_edges_factor, support_formula, pub_aig_manager); 

					set<string> VariablesToEliminate_Set(VariablesToEliminate.begin(), VariablesToEliminate.end());

					set<string> varstoelim_in_support_formula;
					set_intersection(support_formula.begin(), support_formula.end(), VariablesToEliminate_Set.begin(), VariablesToEliminate_Set.end(), inserter(varstoelim_in_support_formula, varstoelim_in_support_formula.begin()));

					if(!varstoelim_in_support_formula.empty())
					{
						preferred_edges_factors.insert(preferred_edges_factor);		
					}
	
				}		
				
			}

			#ifdef DEBUG_SKOLEM
			cout << "\nGenerating Skolem functions" << endl;		
			#endif	

			#ifdef RECORD_KEEP
			string record_file;
			record_file = logfile_prefix;
			record_file += "skolem_function_generation_details.txt";
			FILE* record_fp = fopen(record_file.c_str(), "a+");
			assert(record_fp != NULL);
			fprintf(record_fp, "\n\n\nCOMPONENT %d\n", iterations_of_loop);		
			fclose(record_fp);
			#endif

			#ifdef DEBUG_SKOLEM
			cout << "\nObtaining the Skolem functions" << endl;	
			cout << "\nVariablesToEliminate_before_calling_obtainSkolemFunctionsInGraphDecomposition\n";
			showList(VariablesToEliminate);
			#endif

			// This is to see if we get smaller Skolem functions 
			// by employing global time-out's
			if(apply_global_time_outs_in_component_generation)
			{
				time_t elim_start_time;
			  	time(&elim_start_time);
			  	cluster_global_time_out_start = elim_start_time;

				cluster_global_time_out_enabled = true; 
				cluster_global_timed_out = false; 	
			}	

			obtainSkolemFunctionsInGraphDecomposition(preferred_edges_factors, VariablesToEliminate, variable_to_skolem_function_map, iterations_of_loop);

			#ifdef DEBUG_SKOLEM
			cout << "\nVariablesToEliminate_after_calling_obtainSkolemFunctionsInGraphDecomposition\n";
			showList(VariablesToEliminate);
			#endif

			#ifdef DEBUG_SKOLEM
			cout << "\nSkolem functions obtained" << endl;		
			#endif

			#ifdef DEBUG_SKOLEM
			// let's look at the Skolem functions
			for(map<string, Aig_Obj_t*>::iterator map_it = variable_to_skolem_function_map.begin(); map_it != variable_to_skolem_function_map.end(); map_it++)
			{
				string skolem_file_name = "skolemfunction_for_component_generation_";
				skolem_file_name += map_it->first;
				skolem_file_name += "_";
				skolem_file_name += logfile_prefix;
				skolem_file_name += ".v";
				writeFormulaToFile(pub_aig_manager, map_it->second, skolem_file_name);		
			}
			#endif

			#ifdef DEBUG_SKOLEM
			cout << "\nSizes of Skolem functions:\t";	
			for(map<string, Aig_Obj_t*>::iterator map_it = variable_to_skolem_function_map.begin(); map_it != variable_to_skolem_function_map.end(); map_it++)
			{
				cout << computeSize(map_it->second, pub_aig_manager) << "\t"; 		
			}
			cout << endl;
			#endif	

			unsigned long long int step_ms;
			struct timeval step_start_ms, step_finish_ms;	

			#ifdef RECORD_KEEP
			gettimeofday (&step_start_ms, NULL); 
			#endif


			int number_of_state_elements;
			map<int, string> idName;
			list<string> output_names;
			map<string, Aig_Obj_t*> output_name_to_replaced_factor;

			for(map<Aig_Obj_t*, Aig_Obj_t*>::iterator map_it = Output_Object_to_RHS_of_Factors.begin(); map_it != Output_Object_to_RHS_of_Factors.end(); map_it++)
			{
				Aig_Obj_t* output_obj = map_it->first;
				Aig_Obj_t* factor = map_it->second;
				
				Aig_Obj_t* factor_after_replacement;
				factor_after_replacement = replaceVariablesByFormulas(factor, variable_to_skolem_function_map);
				assert(factor_after_replacement != NULL);
				
				map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(output_obj->Id);
				assert(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end());
				string output_name = Ci_id_to_Ci_name_map_it->second;

				assert(output_name.find(LATCHOUTPREFIX) != string::npos);

				int first_location = output_name.find_last_of("_");
				string first_index_string = output_name.substr(first_location+1);
				output_name = "nextstate_";
				output_name += first_index_string;

				output_names.push_back(output_name);
				output_name_to_replaced_factor.insert(make_pair(output_name, factor_after_replacement));	

				#ifdef DEBUG_SKOLEM
				cout << "\nInserted entry for " << output_name << " into  output_name_to_replaced_factor map" << endl;		
				#endif			
				
			}

			#ifdef DEBUG_SKOLEM
			cout << "\noutput_name_to_replaced_factor map created" << endl;		
			#endif

			#ifdef DEBUG_SKOLEM
			// let's look at output_name_to_replaced_factor map
			for(map<string, Aig_Obj_t*>::iterator map_it = output_name_to_replaced_factor.begin(); map_it != output_name_to_replaced_factor.end(); map_it++)
			{
				string replaced_factor_file_name = "replaced_factor_for_component_generation_";
				replaced_factor_file_name += map_it->first;
				replaced_factor_file_name += "_";
				replaced_factor_file_name += logfile_prefix;
				replaced_factor_file_name += ".v";
				writeFormulaToFile(pub_aig_manager, map_it->second, replaced_factor_file_name);		
			}
			#endif

			
			if(!generate_specific_component || component_number_to_be_generated == iterations_of_loop)//write component
			{
				set<int> POSetInAigManager;
				int number_of_cos;

				for(map<Aig_Obj_t*, Aig_Obj_t*>::iterator map_it = Output_Object_to_RHS_of_PrimaryOutputs.begin(); map_it != Output_Object_to_RHS_of_PrimaryOutputs.end(); map_it++)
				{
					Aig_Obj_t* output_obj = map_it->first;
					Aig_Obj_t* output = map_it->second;
				
					Aig_Obj_t* output_after_replacement;
					output_after_replacement = replaceVariablesByFormulas(output, variable_to_skolem_function_map);
					assert(output_after_replacement != NULL);
				
					map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(output_obj->Id);
					assert(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end());
					string output_name = Ci_id_to_Ci_name_map_it->second;

					assert(output_name.find(CIRCUITOUTPREFIX) != string::npos);

					int first_location = output_name.find_last_of("_");
					string first_index_string = output_name.substr(first_location+1);
					output_name = "primaryout_";
					output_name += first_index_string;

					Aig_Obj_t* output_after_replacement_CO = Aig_ObjCreateCo( pub_aig_manager, output_after_replacement ); 
					assert(output_after_replacement_CO != NULL);

					idName.insert(make_pair(output_after_replacement_CO->Id, output_name));	

					POSetInAigManager.insert(output_after_replacement_CO->Id);		

					#ifdef DEBUG_SKOLEM
					cout << "\nInserted entry for " << output_after_replacement_CO->Id << " , " << output_name << " into  idName" << endl;		
					#endif

					#ifdef DEBUG_SKOLEM
					string output_after_replacement_file_name = "output_after_replacement_for_component_generation_";
					output_after_replacement_file_name += output_name;
					output_after_replacement_file_name += "_";
					output_after_replacement_file_name += logfile_prefix;
					output_after_replacement_file_name += ".v";
					writeFormulaToFile(pub_aig_manager, output_after_replacement, output_after_replacement_file_name);					
					#endif
				
				}

				#ifdef DEBUG_SKOLEM
				cout << "\nPrimary outputs added to idName" << endl;		
				#endif
			
				output_names.sort(compare_tsietin);

				number_of_state_elements = output_names.size();

				number_of_cos = number_of_state_elements + POSetInAigManager.size();

				for(list<string>::iterator output_names_it = output_names.begin(); output_names_it != output_names.end(); output_names_it++)
				{
					string output_name = *output_names_it;
					map<string, Aig_Obj_t*>::iterator output_name_to_replaced_factor_it = output_name_to_replaced_factor.find(output_name);
					Aig_Obj_t* factor_after_replacement = output_name_to_replaced_factor_it->second;

					// factor after replacement is formula for a latchout
					Aig_Obj_t* factor_after_replacement_CO = Aig_ObjCreateCo( pub_aig_manager, factor_after_replacement ); 
					assert(factor_after_replacement_CO != NULL);

					idName.insert(make_pair(factor_after_replacement_CO->Id, output_name));

					#ifdef DEBUG_SKOLEM
					cout << "\nInserted entry for " << factor_after_replacement_CO->Id << " , " << output_name << " into  idName" << endl;		
					#endif

				}

				#ifdef DEBUG_SKOLEM
				cout << "\nOutputs added to idName" << endl;		
				#endif

				int i;
				Aig_Obj_t * pObj;
				Aig_ManForEachPiSeq(pub_aig_manager, pObj, i)
				{
					map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(pObj->Id);
					assert(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end());
					string input_name = Ci_id_to_Ci_name_map_it->second;

					if(input_name.find(LATCHPREFIX) != string::npos)
					{
						int first_location = input_name.find_last_of("_");
						string first_index_string = input_name.substr(first_location+1);
						input_name = "state_";
						input_name += first_index_string;

						idName.insert(make_pair(pObj->Id, input_name));

						#ifdef DEBUG_SKOLEM
						cout << "\nInserted entry for " << pObj->Id << " , " << input_name << " added into  idName" << endl;		
						#endif
					}
				}

				#ifdef DEBUG_SKOLEM
				cout << "\nInputs added to idName" << endl;		
				#endif

				#ifdef DEBUG_SKOLEM
				cout << "\nIdnames created" << endl;		
				#endif

				#ifdef DEBUG_SKOLEM
				cout << "\nidName.size() == " << idName.size();
				cout << "\toutput_names.size() == " << output_names.size();
				cout << "\toutput_name_to_replaced_factor.size() == " << output_name_to_replaced_factor.size() << endl;	
				showMap(idName, "idName");
				cout << "\nnumber_of_state_elements = " << number_of_state_elements << endl;
				cout << "\nnumber_of_cos = " << number_of_cos << endl;
				#endif
			
				Abc_Ntk_t* component_network = obtainNetworkFromFragmentOfAIGWithIdNamesWithMultipleEntriesInCOListAllowed(pub_aig_manager, idName, number_of_cos);

				#ifdef DEBUG_SKOLEM
				cout << "\nCalling Abc_NtkMakeSequential" << endl;		
				#endif

				Abc_NtkMakeSequential(component_network, number_of_state_elements);
			
				// Let's look at the network
				abcFrame->pNtkCur = Abc_NtkDup(component_network);

				char verilog_file_char[100];
				string verilog_file = benchmark_name_without_extension;
				char iterations_of_loop_char[10];
				sprintf(iterations_of_loop_char, "%d", iterations_of_loop);
				string iterations_of_loop_string(iterations_of_loop_char);
				verilog_file += "_component";
				verilog_file += iterations_of_loop_string;
				verilog_file += ".v";

				string command = "write ";
				command += verilog_file;
					
				#ifdef DEBUG_SKOLEM
				cout << command << endl;		
				#endif		

				if (abcObj->comExecute(abcFrame, command))
				{
					cout << "cannot execute command " << command << endl;
					assert(false);
				}


				#ifdef RECORD_KEEP
				gettimeofday (&step_finish_ms, NULL);
			   	step_ms = step_finish_ms.tv_sec * 1000 + step_finish_ms.tv_usec / 1000;
			   	step_ms -= step_start_ms.tv_sec * 1000 + step_start_ms.tv_usec / 1000;
		
				record_fp = fopen(record_file.c_str(), "a+");
				assert(record_fp != NULL);
				fprintf(record_fp, "\n\n\ncomponent generation time = %llu\n", step_ms);
				fclose(record_fp);
				#endif

			}//if(!generate_specific_component || component_number_to_be_generated == iterations_of_loop) ends

			Aig_Obj_t* new_part_in_failure_condition_aig;

			// Let us update the failure_condition_aig
			map<string, Aig_Obj_t*> latchin_to_formula_for_latchin;
			for(map<string, Aig_Obj_t*>::iterator output_name_to_replaced_factor_it = output_name_to_replaced_factor.begin(); output_name_to_replaced_factor_it != output_name_to_replaced_factor.end(); output_name_to_replaced_factor_it++)
			{
				string output_name = output_name_to_replaced_factor_it->first;

				int first_location = output_name.find_last_of("_");
				string first_index_string = output_name.substr(first_location+1);
				output_name = LATCHPREFIX;
				output_name += first_index_string;
				
				latchin_to_formula_for_latchin.insert(make_pair(output_name, output_name_to_replaced_factor_it->second));
			}

			#ifdef DEBUG_SKOLEM
			showReplacementMap(latchin_to_formula_for_latchin, "latchin_to_formula_for_latchin");
			#endif

			map<string, Aig_Obj_t*> optimized_latchin_to_formula_for_latchin;
			optimizeReplacementMap(latchin_to_formula_for_latchin, failure_condition_aig, optimized_latchin_to_formula_for_latchin);

			#ifdef DEBUG_SKOLEM
			showReplacementMap(optimized_latchin_to_formula_for_latchin, "optimized_latchin_to_formula_for_latchin", iterations_of_loop);
			#endif

			// new_part_in_failure_condition_aig is Fail(X,I) with X replaced by T(psi(X))
			new_part_in_failure_condition_aig = ReplaceLeavesByExpressionsConcurrently(pub_aig_manager, failure_condition_aig, optimized_latchin_to_formula_for_latchin);
			assert(new_part_in_failure_condition_aig != NULL);
			

			// Interesting to see what this new_part is
			#ifdef DEBUG_SKOLEM
			cout << "\nSize of Fail(F(X,psi(X))) = " << computeSize(new_part_in_failure_condition_aig, pub_aig_manager) << endl;

			cout << "\nSize of original Fail(X) = " << computeSize(failure_condition_aig, pub_aig_manager) << endl;
			#endif

			#ifdef DEBUG_SKOLEM
			string new_part_in_failure_condition_aig_file_name = benchmark_name_without_extension;
			new_part_in_failure_condition_aig_file_name += "_new_part_in_failure_condition_aig";
			writeFormulaToFile(pub_aig_manager, new_part_in_failure_condition_aig, new_part_in_failure_condition_aig_file_name, ".v", 0, iterations_of_loop);			

			if(failure_condition_aig == new_part_in_failure_condition_aig)
			{
				cout << "\nfailure_condition_aig == new_part_in_failure_condition_aig\n";
			}
			else
			{
				cout << "\nfailure_condition_aig != new_part_in_failure_condition_aig\n";
			}
			#endif

			failure_condition_aig = createOr(failure_condition_aig, new_part_in_failure_condition_aig, pub_aig_manager);
			#ifdef DEBUG_SKOLEM
			cout << "\nSize of original expanded Fail(X) = " << computeSize(failure_condition_aig, pub_aig_manager) << endl;
			#endif

			if(apply_fraiging_in_graph_decomposition)
			{
				failure_condition_aig = simplifyAIGUsingFraiging(pub_aig_manager, failure_condition_aig);
			}

			#ifdef DEBUG_SKOLEM
			cout << "\nSize of simplified expanded Fail(X) = " << computeSize(failure_condition_aig, pub_aig_manager) << endl;
			#endif
 
			Aig_Obj_t* failure_condition_aig_CO = Aig_ObjCreateCo( pub_aig_manager, failure_condition_aig ); 
			assert(failure_condition_aig_CO != NULL);

			if(failure_condition_aig == createTrue(pub_aig_manager))
			{
				#ifdef DEBUG_SKOLEM
				cout << "\nFail(X) has become true. The circuit is unsafe\n";
				#endif

				break;	
			}
			
			if(iterations_of_loop > 1)
			{
				if(previous_failure_condition_aig == failure_condition_aig)
				{
					#ifdef DEBUG_SKOLEM
					cout << "\nFail(X) has reached fix-point. No more components need to be generated. Intersect with Initial(X) to check if the circuit is safe\n";
					#endif

					#ifdef DEBUG_SKOLEM
					string fixpoint_failure_condition_aig_file_name = benchmark_name_without_extension;
					fixpoint_failure_condition_aig_file_name += "_fixpoint_failure_condition_aig";
					writeFormulaToFile(pub_aig_manager, failure_condition_aig, fixpoint_failure_condition_aig_file_name, ".v", 0, 0);
					#endif

					break;	
				}
			}

			if(generate_specific_component && component_number_to_be_generated == iterations_of_loop)
			{
				break;			
			}

			previous_failure_condition_aig = failure_condition_aig;

			if(use_uncovered_edge_with_preferred_edge)
			{
				// update uncovered_edges
				Aig_Obj_t* covered_edges_by_component;
				covered_edges_by_component = generateCoveredEdges(transition_function_parts, variable_to_skolem_function_map);
				assert(covered_edges_by_component != NULL);

				Aig_Obj_t* uncovered_edges_by_component;
				uncovered_edges_by_component = createNot(covered_edges_by_component, pub_aig_manager);
				assert(uncovered_edges_by_component != NULL);
				Aig_Obj_t* uncovered_edges_by_component_CO = Aig_ObjCreateCo( pub_aig_manager, uncovered_edges_by_component ); 
				assert(uncovered_edges_by_component_CO != NULL);

				uncovered_edges = createAnd(uncovered_edges, uncovered_edges_by_component, pub_aig_manager);	
				assert(uncovered_edges != NULL);

				Aig_Obj_t* uncovered_edges_CO = Aig_ObjCreateCo( pub_aig_manager, uncovered_edges ); 
				assert(uncovered_edges_CO != NULL);
			}

			iterations_of_loop++;

			number_of_components_generated++;
		
		}// while ends here

		
		string number_components_file = benchmark_name_without_extension;
		number_components_file += "_number_components.txt";
		FILE* number_components_file_fp = fopen(number_components_file.c_str(), "w+");
		fprintf(number_components_file_fp, "%d", iterations_of_loop);
		fclose(number_components_file_fp);
		return_value = iterations_of_loop;
			
	}
	else if(component_generation_strategy == "uncovered_edge")
	{	

		Aig_Obj_t* uncovered_edges;
		uncovered_edges = createTrue(pub_aig_manager);
		assert(uncovered_edges != NULL);

		set<Aig_Obj_t*> uncovered_edges_factors;	

		// 
		// uncovered_edges := true initially
		// uncovered_edges_factors := {}
		//

		bool more_components_existing = true;	

		int iterations_of_loop = 1;

		sat_solver* pSat_for_checking_if_more_components_exist; 

		unsigned long long int step_ms;
		struct timeval step_start_ms, step_finish_ms;	

		while(more_components_existing)
		{
			#ifdef DEBUG_SKOLEM
			cout << "\nStarting loop iteration " << iterations_of_loop << endl;		
			#endif	

			#ifdef RECORD_KEEP
			string record_file;
			record_file = logfile_prefix;
			record_file += "skolem_function_generation_details.txt";
			FILE* record_fp = fopen(record_file.c_str(), "a+");
			assert(record_fp != NULL);
			fprintf(record_fp, "\n\n\nCOMPONENT %d\n", iterations_of_loop);		
			fclose(record_fp);
			#endif

			#ifdef DEBUG_SKOLEM
			cout << "\nObtaining the Skolem functions" << endl;		
			#endif

			
			#ifdef DEBUG_SKOLEM
			cout << "\nVariablesToEliminate_before_calling_obtainSkolemFunctionsInGraphDecomposition\n";
			showList(VariablesToEliminate);	
			#endif

			// This is to see if we get smaller Skolem functions 
			// by employing global time-out's
			if(apply_global_time_outs_in_component_generation)
			{
				time_t elim_start_time;
			  	time(&elim_start_time);
			  	cluster_global_time_out_start = elim_start_time;

				cluster_global_time_out_enabled = true; 
				cluster_global_timed_out = false; 	
			}

			obtainSkolemFunctionsInGraphDecomposition(uncovered_edges_factors, VariablesToEliminate, variable_to_skolem_function_map, iterations_of_loop);

			#ifdef DEBUG_SKOLEM
			cout << "\nVariablesToEliminate_after_calling_obtainSkolemFunctionsInGraphDecomposition\n";
			showList(VariablesToEliminate);
			#endif

			//
			// Find Skolem functions \psi for inputs I in (/\ uncovered_edges_factors), i.e. uncovered_edges
			//

			#ifdef DEBUG_SKOLEM
			cout << "\nSkolem functions obtained" << endl;		
			#endif

			#ifdef DEBUG_SKOLEM
			// Let's look at the variables
			for(map<string, Aig_Obj_t*>::iterator map_it = variable_to_skolem_function_map.begin(); map_it != variable_to_skolem_function_map.end(); map_it++)
			{
				cout << "\nSkolem function for " << map_it->first << " obtained\n";		
			}
			#endif

			#ifdef DEBUG_SKOLEM
			// let's look at the Skolem functions
			for(map<string, Aig_Obj_t*>::iterator map_it = variable_to_skolem_function_map.begin(); map_it != variable_to_skolem_function_map.end(); map_it++)
			{
				string skolem_file_name = "skolemfunction_for_component_generation_";
				skolem_file_name += map_it->first;
				skolem_file_name += "_";
				skolem_file_name += logfile_prefix;
				skolem_file_name += ".v";
				writeFormulaToFile(pub_aig_manager, map_it->second, skolem_file_name);		
			}
			#endif	

			#ifdef RECORD_KEEP
			gettimeofday (&step_start_ms, NULL); 
			#endif

			if(!generate_specific_component || component_number_to_be_generated == iterations_of_loop)//write component
			{

				// 
				// Component is [(X' = f(X, I)) /\ (O = g(X, I))] with I->\psi
				//
		
				if(write_component_as_sequential_circuit)
				{

					#ifdef DEBUG_SKOLEM
					cout << "\nWriting component as sequential circuit" << endl;		
					#endif

					int number_of_state_elements;

					map<int, string> idName;

					list<string> output_names;
					map<string, Aig_Obj_t*> output_name_to_replaced_factor;

					for(map<Aig_Obj_t*, Aig_Obj_t*>::iterator map_it = Output_Object_to_RHS_of_Factors.begin(); map_it != Output_Object_to_RHS_of_Factors.end(); map_it++)
					{
						
						Aig_Obj_t* output_obj = map_it->first;
						Aig_Obj_t* factor = map_it->second;
				
						Aig_Obj_t* factor_after_replacement;
						factor_after_replacement = replaceVariablesByFormulas(factor, variable_to_skolem_function_map);
						assert(factor_after_replacement != NULL);
				
						map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(output_obj->Id);
						assert(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end());
						string output_name = Ci_id_to_Ci_name_map_it->second;

						assert(output_name.find(LATCHOUTPREFIX) != string::npos);

						int first_location = output_name.find_last_of("_");
						string first_index_string = output_name.substr(first_location+1);
						output_name = "nextstate_";
						output_name += first_index_string;

						output_names.push_back(output_name);
						output_name_to_replaced_factor.insert(make_pair(output_name, factor_after_replacement));
						#ifdef DEBUG_SKOLEM
						cout << "\nInserted entry for " << output_name << " into  output_name_to_replaced_factor map" << endl;		
						#endif
				
				
					}

					#ifdef DEBUG_SKOLEM
					cout << "\noutput_name_to_replaced_factor map created" << endl;		
					#endif

					set<int> POSetInAigManager;
					int number_of_cos;

					for(map<Aig_Obj_t*, Aig_Obj_t*>::iterator map_it = Output_Object_to_RHS_of_PrimaryOutputs.begin(); map_it != Output_Object_to_RHS_of_PrimaryOutputs.end(); map_it++)
					{
						Aig_Obj_t* output_obj = map_it->first;
						Aig_Obj_t* output = map_it->second;
				
						Aig_Obj_t* output_after_replacement;
						output_after_replacement = replaceVariablesByFormulas(output, variable_to_skolem_function_map);
						assert(output_after_replacement != NULL);
				
						map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(output_obj->Id);
						assert(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end());
						string output_name = Ci_id_to_Ci_name_map_it->second;

						assert(output_name.find(CIRCUITOUTPREFIX) != string::npos);

						int first_location = output_name.find_last_of("_");
						string first_index_string = output_name.substr(first_location+1);
						output_name = "primaryout_";
						output_name += first_index_string;

						Aig_Obj_t* output_after_replacement_CO = Aig_ObjCreateCo( pub_aig_manager, output_after_replacement ); 
						assert(output_after_replacement_CO != NULL);

						idName.insert(make_pair(output_after_replacement_CO->Id, output_name));	

						POSetInAigManager.insert(output_after_replacement_CO->Id);
						
						#ifdef DEBUG_SKOLEM
						cout << "\nInserted " << output_after_replacement_CO->Id << " -> " << output_name << " into  idName" << endl;		
						#endif			
				
					}

					#ifdef DEBUG_SKOLEM
					cout << "\nReplacement done" << endl;		
					#endif
			
					output_names.sort(compare_tsietin);

					number_of_state_elements = output_names.size();

					number_of_cos = number_of_state_elements + POSetInAigManager.size();

					for(list<string>::iterator output_names_it = output_names.begin(); output_names_it != output_names.end(); output_names_it++)
					{
						string output_name = *output_names_it;
						map<string, Aig_Obj_t*>::iterator output_name_to_replaced_factor_it = output_name_to_replaced_factor.find(output_name);
						Aig_Obj_t* factor_after_replacement = output_name_to_replaced_factor_it->second;

						// factor after replacement is formula for a latchout
						Aig_Obj_t* factor_after_replacement_CO = Aig_ObjCreateCo( pub_aig_manager, factor_after_replacement ); 
						assert(factor_after_replacement_CO != NULL);

						idName.insert(make_pair(factor_after_replacement_CO->Id, output_name));

						#ifdef DEBUG_SKOLEM
						cout << "\nInserted " << factor_after_replacement_CO->Id << " -> " << output_name << " into  idName" << endl;		
						#endif

					}

					#ifdef DEBUG_SKOLEM
					cout << "\nOutput names created" << endl;		
					#endif

					int i;
					Aig_Obj_t * pObj;
					Aig_ManForEachPiSeq(pub_aig_manager, pObj, i)
					{
						map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(pObj->Id);
						assert(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end());
						string input_name = Ci_id_to_Ci_name_map_it->second;

						if(input_name.find(LATCHPREFIX) != string::npos)
						{
							int first_location = input_name.find_last_of("_");
							string first_index_string = input_name.substr(first_location+1);
							input_name = "state_";
							input_name += first_index_string;

							idName.insert(make_pair(pObj->Id, input_name));

							#ifdef DEBUG_SKOLEM
							cout << "\nInserted " << pObj->Id << " -> " << input_name << " into  idName" << endl;		
							#endif
						}
					}

					#ifdef DEBUG_SKOLEM
					cout << "\nIdnames created" << endl;		
					#endif

					#ifdef DEBUG_SKOLEM
					cout << "\nidName.size() == " << idName.size();
					cout << "\toutput_names.size() == " << output_names.size();
					cout << "\toutput_name_to_replaced_factor.size() == " << output_name_to_replaced_factor.size() << endl;	
					#endif
					

					//Abc_Ntk_t* component_network = obtainNetworkFromFragmentOfAIGWithIdNames(pub_aig_manager, idName);
					Abc_Ntk_t* component_network = obtainNetworkFromFragmentOfAIGWithIdNamesWithMultipleEntriesInCOListAllowed(pub_aig_manager, idName, number_of_cos);

					#ifdef DEBUG_SKOLEM
					cout << "\nNetwork created" << endl;		
					#endif

					#ifdef DEBUG_SKOLEM
					cout << "\nNumber of CO's in component_network = " << Abc_NtkCoNum(component_network) << endl;
					#endif

					bool make_sequential = true;//to skip making sequential if needed
					if(make_sequential)
					{
						//Abc_NtkMakeSequential(component_network, Abc_NtkPoNum(component_network));
						Abc_NtkMakeSequential(component_network, number_of_state_elements);

						#ifdef DEBUG_SKOLEM
						cout << "\nNetwork made sequential" << endl;		
						#endif
					}					
			
					// Let's look at the network
					abcFrame->pNtkCur = Abc_NtkDup(component_network);

					char verilog_file_char[100];
					string verilog_file = benchmark_name_without_extension;
					char iterations_of_loop_char[10];
					sprintf(iterations_of_loop_char, "%d", iterations_of_loop);
					string iterations_of_loop_string(iterations_of_loop_char);
					verilog_file += "_component";
					verilog_file += iterations_of_loop_string;
					verilog_file += ".v";

					string command = "write ";
					command += verilog_file;

					//cout << command << endl;		
					if (abcObj->comExecute(abcFrame, command))
					{
						cout << "cannot execute command " << command << endl;
						assert(false);
					}

					#ifdef DEBUG_SKOLEM
					cout << "\nWriting component as sequential circuit is over" << endl;		
					#endif	

				}
				else if(write_component_in_file)
				{
					#ifdef DEBUG_SKOLEM
					cout << "\nWriting components in file" << endl;		
					#endif
					
					Aig_Obj_t* component;
					component = generateComponent(transition_function, variable_to_skolem_function_map);
					assert(component != NULL);

					#ifdef DEBUG_SKOLEM
					string component_file_name = benchmark_name_without_extension;
					component_file_name += "_component";
					writeFormulaToFile(pub_aig_manager, component, component_file_name, ".v", iterations_of_loop, 0);	
					#endif

					Aig_Obj_t* component_CO = Aig_ObjCreateCo( pub_aig_manager, component ); 
					assert(component_CO != NULL);
			

					Aig_Man_t* component_aig_manager;
					component_aig_manager = simplifyUsingConeOfInfluence( pub_aig_manager, Aig_ManCoNum(pub_aig_manager)-1, 1 );
					assert(component_aig_manager != NULL);

					char verilog_file_char[100];
					string verilog_file = benchmark_name_without_extension;
					char iterations_of_loop_char[10];
					sprintf(iterations_of_loop_char, "%d", iterations_of_loop);
					string iterations_of_loop_string(iterations_of_loop_char);
					verilog_file += "_component";
					verilog_file += iterations_of_loop_string;
					char pname[100];
					strcpy(pname, verilog_file.c_str());

					component_aig_manager->pName = pname;
					verilog_file += ".v";
					strcpy(verilog_file_char, verilog_file.c_str());

					int total_no_of_cis = number_of_Cis;
					writeCombinationalCircuitInVerilog(component_aig_manager, 0, 0, 0, total_no_of_cis, verilog_file_char, false );
					cout << "\nComponent " << iterations_of_loop << " written in file " << verilog_file << "\n";


					string dump_file = benchmark_name_without_extension;
					dump_file += "_component";
					dump_file += iterations_of_loop_string;
					dump_file += "_dump";
					writeFormulaToFile(pub_aig_manager, component, dump_file, ".v", 0, 0);

					#ifdef DEBUG_SKOLEM
					cout << "\nWriting components over" << endl;		
					#endif		
				}

			}//write component ends here

			#ifdef RECORD_KEEP
			gettimeofday (&step_finish_ms, NULL);
	   		step_ms = step_finish_ms.tv_sec * 1000 + step_finish_ms.tv_usec / 1000;
	   		step_ms -= step_start_ms.tv_sec * 1000 + step_start_ms.tv_usec / 1000;
		
			record_fp = fopen(record_file.c_str(), "a+");
			assert(record_fp != NULL);
			fprintf(record_fp, "\n\n\ncomponent generation time = %llu\n", step_ms);
			fclose(record_fp);
			#endif

			if(generate_specific_component && component_number_to_be_generated == iterations_of_loop)
			{
				break;			
			}

			number_of_components_generated++;
		
		
			#ifdef RECORD_KEEP
			gettimeofday (&step_start_ms, NULL); 
			#endif

			Aig_Obj_t* covered_edges_by_component;
			covered_edges_by_component = generateCoveredEdges(transition_function_parts, variable_to_skolem_function_map);
			assert(covered_edges_by_component != NULL);


			// 
			// covered edges by component is f(X, I) with I->\psi
			//

			#ifdef RECORD_KEEP
			gettimeofday (&step_finish_ms, NULL);
	   		step_ms = step_finish_ms.tv_sec * 1000 + step_finish_ms.tv_usec / 1000;
	   		step_ms -= step_start_ms.tv_sec * 1000 + step_start_ms.tv_usec / 1000;
		
			record_fp = fopen(record_file.c_str(), "a+");
			assert(record_fp != NULL);
			fprintf(record_fp, "\ncovered edges generation time = %llu\n", step_ms);
			fclose(record_fp);
			#endif

			#ifdef DEBUG_SKOLEM
			string covered_edges_by_component_file_name = benchmark_name_without_extension;
			covered_edges_by_component_file_name += "_covered_edges_by_component";
			writeFormulaToFile(pub_aig_manager, covered_edges_by_component, covered_edges_by_component_file_name, ".v", iterations_of_loop, 0);	
			#endif


			Aig_Obj_t* uncovered_edges_by_component;
			uncovered_edges_by_component = createNot(covered_edges_by_component, pub_aig_manager);
			assert(uncovered_edges_by_component != NULL);
			Aig_Obj_t* uncovered_edges_by_component_CO = Aig_ObjCreateCo( pub_aig_manager, uncovered_edges_by_component ); 
			assert(uncovered_edges_by_component_CO != NULL);

			uncovered_edges_factors.insert(uncovered_edges_by_component);	

			uncovered_edges = createAnd(uncovered_edges, uncovered_edges_by_component, pub_aig_manager);	
			assert(uncovered_edges != NULL);

			#ifdef DEBUG_SKOLEM
			cout << "\nSize of uncovered_edges = " << computeSize(uncovered_edges, pub_aig_manager) << endl;
			#endif

			if(apply_fraiging_in_graph_decomposition)
			{
				uncovered_edges = simplifyAIGUsingFraiging(pub_aig_manager, uncovered_edges);
			}

			#ifdef DEBUG_SKOLEM
			cout << "\nSize of uncovered_edges after FRAIGing = " << computeSize(uncovered_edges, pub_aig_manager) << endl;
			#endif

			Aig_Obj_t* uncovered_edges_CO = Aig_ObjCreateCo(pub_aig_manager, uncovered_edges); 
			assert(uncovered_edges_CO != NULL);


			// 
			// uncovered_edges := uncovered_edges /\ uncovered_edges_by_component
			// insert uncovered_edges_by_component into uncovered_edges_factors
			//

			unsigned long long int cnf_time;
			int formula_size;
			unsigned long long int simplification_time;
			map<string, int> model_of_satcheck;

			#ifdef RECORD_KEEP
			gettimeofday (&step_start_ms, NULL); 
			#endif

			bool skip_test_for_existence_of_more_components;
			skip_test_for_existence_of_more_components = false;			
			
			if(skip_test_for_existence_of_more_components)
			{
				#ifdef DEBUG_SKOLEM
				cout << "\nCheck for existence of more components skipped!\n";
				#endif

				more_components_existing = true;				
				
			}
			else
			{
				bool use_incremental_solver = true;

				if(use_incremental_solver)
				{
					vector<Aig_Obj_t*> positive_assumptions;
					vector<Aig_Obj_t*> negative_assumptions;
			
					int IncrementalLabelCountForCheckingIfMoreComponentsExist = 1;
					t_HashTable<int, int> IncrementalLabelTableForCheckingIfMoreComponentsExist;
					map<string, int> Ci_name_to_Ci_label_mapForCheckingIfMoreComponentsExist; 
 					map<int, string> Ci_label_to_Ci_name_mapForCheckingIfMoreComponentsExist; 

					pSat_for_checking_if_more_components_exist = sat_solver_new();
	
					more_components_existing = isExactnessCheckSatisfiable(pub_aig_manager, uncovered_edges, model_of_satcheck, cnf_time, formula_size, simplification_time, positive_assumptions, negative_assumptions, pSat_for_checking_if_more_components_exist, IncrementalLabelTableForCheckingIfMoreComponentsExist, IncrementalLabelCountForCheckingIfMoreComponentsExist, Ci_name_to_Ci_label_mapForCheckingIfMoreComponentsExist, Ci_label_to_Ci_name_mapForCheckingIfMoreComponentsExist);
		
					sat_solver_delete(pSat_for_checking_if_more_components_exist);
				}
				else // If this is used along with cleanup_after_each_step_in_arbitrary_boolean_combinations, then 
				// seg. fault can happen - note that isSat tries to derive cnf for the entire manager
				{
					more_components_existing = isSat(pub_aig_manager, uncovered_edges, model_of_satcheck, cnf_time, formula_size, simplification_time);

				}
			}

			#ifdef RECORD_KEEP
			gettimeofday (&step_finish_ms, NULL);
	   		step_ms = step_finish_ms.tv_sec * 1000 + step_finish_ms.tv_usec / 1000;
	   		step_ms -= step_start_ms.tv_sec * 1000 + step_start_ms.tv_usec / 1000;
		
			record_fp = fopen(record_file.c_str(), "a+");
			assert(record_fp != NULL);
			fprintf(record_fp, "\nsatisfiability check time = %llu\n", step_ms);
			fclose(record_fp);
			#endif

			#ifdef DEBUG_SKOLEM
			cout << "\nLoop iteration " << iterations_of_loop << " finished\n";		
			#endif

			iterations_of_loop++;

			#ifdef DEBUG_SKOLEM
				//cout << "\nPress any key to continue...";
				//char c = getchar();
			#endif	

			string more_components_file = benchmark_name_without_extension;
			more_components_file += "_component_exists.txt";
			FILE* more_components_file_fp = fopen(more_components_file.c_str(), "w+");
			if(more_components_existing)
			{
				fprintf(more_components_file_fp, "yes");
			}
			else
			{
				fprintf(more_components_file_fp, "no");
			}
			fclose(more_components_file_fp);
		}

		if(!more_components_existing)
		{
			return_value = 0;
		}
		// by default, 	return_value is 1	
	
	}//if(component_generation_strategy == uncovered_edge)
	else
	{
		cout << "\nUnknown component generation strategy " << component_generation_strategy << endl;
		assert(false);
	}

	return return_value;
}


Aig_Obj_t* AIGBasedSkolem::generateComponent(Aig_Obj_t* transition_function, map<string, Aig_Obj_t*> &variable_to_skolem_function_map)
{
	// component is transition_function[variables --> skolem functions]
	Aig_Obj_t* component;
	component = replaceVariablesByFormulas(transition_function, variable_to_skolem_function_map);
	assert(component != NULL);
	
	return component;	
}


Aig_Obj_t* AIGBasedSkolem::generateCoveredEdges(set<Aig_Obj_t*> &transition_function_parts, map<string, Aig_Obj_t*> &variable_to_skolem_function_map)
{
	// covered_edges_by_component is conjunction of 
	//    transition_function_parts[variables --> skolem functions]

	Aig_Obj_t* covered_edges_by_component;
	set<Aig_Obj_t*> covered_edges_by_component_parts;

	for(set<Aig_Obj_t*>::iterator part_it = transition_function_parts.begin(); part_it != transition_function_parts.end(); part_it++)
	{
		Aig_Obj_t* transition_function_part = *part_it; // f_i(X, I)

		Aig_Obj_t* transition_function_part_after_replacement;
		transition_function_part_after_replacement = replaceVariablesByFormulas(transition_function_part, variable_to_skolem_function_map);
		assert(transition_function_part_after_replacement != NULL); // f_i(x, G(X))

		Aig_Obj_t* covered_edges_by_component_part;
		covered_edges_by_component_part = createEquivalence(transition_function_part, transition_function_part_after_replacement, pub_aig_manager);
		assert(covered_edges_by_component_part != NULL); // f_i(X, I) \equiv f_i(x, G(X))
		
		covered_edges_by_component_parts.insert(covered_edges_by_component_part);
	}
	
	covered_edges_by_component = createAnd(covered_edges_by_component_parts, pub_aig_manager);
	assert(covered_edges_by_component != NULL);

	return covered_edges_by_component;	
}


void AIGBasedSkolem::clearAllDataStructures()
{
	// All variables declared in AIGBasedSkolem class to be cleared

	// global variables

	number_of_factors = 0; 
	number_of_vars_to_elim = 0; 

	var_name_to_var_index_map.clear();
	var_index_to_var_name_map.clear();

	
	FactorMatrix.clear();
	SkolemFunctions.clear();		

	AlphaCombineds.clear();
	
	BadSets.clear();

	// local variables

	FactorsWithVariable.clear();
	CofactorOneMatrix.clear();
	CofactorZeroMatrix.clear();
	AlphaMatrix.clear();
	BetaMatrix.clear(); 
	GammaMatrix.clear(); 
	DeltaMatrix.clear();		

	original_factor_sizes.clear(); 
	abstracted_factor_sizes.clear(); 
	original_factor_support_sizes.clear(); 
	original_factor_varstoelim_sizes.clear(); 
		
	FactorsAffectingSkolemFunction.clear(); 
	sizes_of_factors_affecting_variable.clear(); 
	sizes_of_conflict_conjuncts_affecting_variable.clear(); 
	sizes_of_cofactors_affecting_variable.clear(); 
	sizes_of_factors_with_variable.clear();
	PreviousFactorsWithVariable.clear(); 
	
	// All variables declared in helper.cpp to be cleared

	cumulative_time_in_compute_size = cumulative_time_in_compute_size + total_time_in_compute_size;
	// to keep track of cumulative time in size computation across all skolem function generation calls

	// data to plot
	sum_of_number_of_factors_containing_variable = 0;  
 	sum_of_skolem_function_sizes = 0;
 	total_number_of_compose_operations = 0;  
 	total_time_in_compose_operations = 0;
 	total_time_in_alpha_combined = 0;
 	total_time_in_delta_part = 0;
 	total_time_in_correction_part = 0;
 	total_time_in_delta_combined = 0;
 	total_time_in_next_factor = 0;
 	sum_of_skolem_function_sizes_after_reverse_substitution = 0;
 	skolem_function_sizes_after_reverse_substitution.clear();
 	total_time_in_ordering = 0;
 	total_of_skyline_sizes_in_least_cost_ordering = 0;
 	total_time_in_compute_size = 0;
 	total_time_in_compute_support = 0;
 	total_time_in_generator_initialization = 0;
 	sum_of_numbers_of_affecting_factors = 0;

 	max_factor_size = -1;
 	min_factor_size = -1;
 	max_factor_varstoelim_size = -1;
 	min_factor_varstoelim_size = -1;

 	number_of_boolean_operations_for_variable = 0;
 	BooleanOpTime = 0;
 	number_of_support_operations_for_variable = 0;

 	total_number_of_compose_operations_in_initial_skolem_function_generation = 0;
 	total_ComposeTime_in_initial_skolem_function_generation = 0;
 	total_number_of_boolean_operations_in_initial_skolem_function_generation = 0;
 	total_BooleanOpTime_in_initial_skolem_function_generation = 0;
 	total_number_of_support_operations_in_initial_skolem_function_generation = 0;
 	total_FactorFindingTime_in_initial_skolem_function_generation = 0;
 	size_of_quantified_result_in_bdd_like_scheme = 0;


	// declarations for least cost first ordering
 	factor_graph_factors_to_vars_map.clear();
	factor_graph_vars_to_factors_map.clear();
	factor_graph_factors_to_topvars_map.clear();
 	topvars.clear();

 	factor_graph_vars_to_sccnos_map.clear();
 	factor_graph_sccnos_to_sccs_map.clear();

 	vars_to_eqclassnos_map.clear();
 	eqclassnos_to_eqclasses_map.clear();

 	ordered_vars_to_elim.clear();
 	unordered_vars_to_elim.clear();

 	factor_to_costs_map.clear();
 	skolemfunctions_to_costs_map.clear();
 	deltas_to_costs_map.clear();

	// declarations to perform CEGAR style skolem function generation
	cegar_iteration_number = 0; 
	conjunction_of_factors = NULL;
	B_equivalence_part = NULL;	



	LabelTable.clear();
 	LabelCount = 1;
 	Ci_name_to_Ci_label_mapForGetCNF.clear();
 	Ci_label_to_Ci_name_mapForGetCNF.clear();
 	number_of_variables_in_renamed_conjunction_of_factors = 0;
 	total_time_in_smt_solver = 0;
 	
	EvaluationTable.clear();
	sensitivity_list.clear(); 
 	dependency_list.clear(); 
 	size_of_alpha_in_interpolant_computation_for_variable = -1;
 	size_of_beta_in_interpolant_computation_for_variable = -1;
 	time_in_interpolant_computation_for_variable = 0;
 	total_time_in_interpolant_computation = 0;

	connections_starting_at_skolem_function.clear(); 
	connections_ending_at_skolem_function.clear(); 
 	maximum_length_of_connection_in_connection_based_scheme = 0;
 	number_of_connections_in_connection_based_scheme = 0;
 	number_of_connections_updated_in_iteration_in_connection_based_scheme = 0;
 	values_of_variables_from_bad_to_var.clear();
 	values_of_variables_from_var.clear();
 	values_of_Y_variables.clear();

	// declarations to perform incremental solving	
	Z_variable_counter.clear(); 
 	I_variable_counter.clear();
 	temporary_variable_for_incremental_solving_to_object_map.clear();
 
 	IncrementalLabelTableForExactnessCheck.clear();
 	IncrementalLabelCountForExactnessCheck = 1;
 	Ci_name_to_Ci_label_mapForExactnessCheck.clear(); 
 	Ci_label_to_Ci_name_mapForExactnessCheck.clear(); 

	IncrementalLabelTableForMismatchCheck.clear();
 	IncrementalLabelCountForMismatchCheck = 1;
 	Ci_name_to_Ci_label_mapForMismatchCheck.clear(); 
 	Ci_label_to_Ci_name_mapForMismatchCheck.clear();  	


	// the following are for debugging 
 	BetaCombineds.clear();
 	AlphaOrGammaCombineds.clear();
 	GammaDisjunctions.clear();
 	DeltaDisjunctions.clear();
 	DeltasForSpecificVariable.clear();

	// following in data collection 
	total_time_in_initial_abstraction_generation_in_cegar = 0;
 	total_time_in_cegar_loops_in_cegar = 0;
 	total_time_in_connection_substitution_in_cegar = 0;
 	total_time_in_reverse_substitution_in_cegar = 0;

 	total_time_in_exactness_checking_in_cegar = 0;
 	total_time_in_x_new_recompution_in_cegar = 0;
 	total_time_in_reevaluation_in_cegar = 0;
	number_of_exactness_checking_in_cegar = 0;
 	number_of_x_new_recompution_in_cegar = 0;
 	number_of_reevaluation_in_cegar = 0;

 	size_computation_time_in_initialization = 0;
 	size_computation_time_in_initial_abstraction_generation_in_cegar = 0;
 	size_computation_time_in_reverse_substitution_in_cegar = 0;
 	size_computation_time_in_cegar_loops_in_cegar = 0;
 	size_computation_time_in_connection_substitution_in_cegar = 0;
 
	sizes_of_exactness_formulae_in_cegar.clear();
 	times_in_cnf_generation_in_cegar.clear();
 	times_in_sat_solving_in_cegar.clear();
 	times_in_aig_simplification_in_cegar.clear();

	
	cumulative_time_in_true_sat_solving_in_cegar = cumulative_time_in_true_sat_solving_in_cegar + total_time_in_true_sat_solving_in_cegar;

	cumulative_time_in_false_sat_solving_in_cegar = cumulative_time_in_false_sat_solving_in_cegar + total_time_in_false_sat_solving_in_cegar;

	cumulative_time_in_sat_solving_in_cegar = cumulative_time_in_sat_solving_in_cegar + total_time_in_sat_solving_in_cegar;

	cumulative_time_in_simulation_to_replace_sat_in_cegar = cumulative_time_in_simulation_to_replace_sat_in_cegar + total_time_in_simulation_to_replace_sat_in_cegar;

	total_time_in_true_sat_solving_in_cegar = 0;
 	total_time_in_false_sat_solving_in_cegar = 0;
 	total_time_in_sat_solving_in_cegar = 0;
	total_time_in_simulation_to_replace_sat_in_cegar = 0;

	// for using generic Skolem functions inside CEGAR
	cannot_be_one_count = 0;
 	cannot_be_zero_count = 0;
 	cannot_be_string_to_cannot_be_object_map.clear();
 	cannot_be_object_to_cannot_be_dag_map.clear();
 	cannot_be_one_set.clear();
 	cannot_be_zero_set.clear();
	initial_cannot_be_zero_dags.clear();
	initial_cannot_be_zero_objects.clear();
	size_of_conjunction_of_factors = 0;
 	sizes_of_cannot_be_one_elements_of_variable.clear();
 	sizes_of_cannot_be_zero_elements_of_variable.clear();

	cegar_iteration_for_correction_index = 0;
 	variables_not_quantified.clear();
 	original_variables.clear();
 	variables_quantified.clear();
 	total_time_in_mu_evaluation_in_cegar = 0;

	total_time_in_interpolant_computation_in_cegar = 0;
 	total_time_in_dontcare_optimization_in_cegar = 0;
 	D_variable_counter.clear(); 
 	S_variable_counter.clear(); 
 	total_time_in_generalization_in_mu_based_scheme_with_optimizations_in_cegar = 0;

	IncrementalLabelTableForGeneralizationCheck.clear();
 	IncrementalLabelCountForGeneralizationCheck = 1;
 	Ci_name_to_Ci_label_mapForGeneralizationCheck.clear(); 
 	Ci_label_to_Ci_name_mapForGeneralizationCheck.clear(); 
 
 	Y_variable_counter.clear(); 
 	N_i_index_to_N_i_object_map.clear(); 
 	bads_to_exclude.clear(); 
	cumulative_time_in_compute_size = 0;

	assumptions_flag = 1;	
}



void AIGBasedSkolem::benchmarkGeneration(set<Aig_Obj_t*> &transition_function_factors, map<string, Aig_Obj_t*> &output_string_to_transition_function_parts, list<string> &VariablesToEliminate)
{
	int number_of_variables_to_eliminate = VariablesToEliminate.size();
	int original_no_of_cis = number_of_Cis;
		
	assert(!transition_function_factors.empty()); // each element is x_i' \equiv f_i(X, I)
	assert(!output_string_to_transition_function_parts.empty()); // each element is string x_i' --> f_i(X, I)
	
	map<string, Aig_Obj_t*> variable_to_skolem_function_map; // This stores x_i ---> true
	for(list<string>::iterator list_it = VariablesToEliminate.begin(); list_it != VariablesToEliminate.end(); list_it++)
	{
		string variable_to_eliminate = *list_it;

		Aig_Obj_t* skolem_function = createTrue(pub_aig_manager);
		assert(skolem_function != NULL);

		variable_to_skolem_function_map.insert(make_pair(variable_to_eliminate, skolem_function));			
	}
	
	// let's see output_string_to_transition_function_parts
	#ifdef DEBUG_SKOLEM
	cout << "\noutput_string_to_transition_function_parts\n";
	for(map<string, Aig_Obj_t*>::iterator map_it = output_string_to_transition_function_parts.begin(); map_it != output_string_to_transition_function_parts.end(); map_it++)
	{
		cout << endl << map_it->first << "\t" << map_it->second << endl;
		string transition_function_part_file_name = benchmark_name_without_extension;
		transition_function_part_file_name += "_";
		transition_function_part_file_name += map_it->first;
		transition_function_part_file_name += "_transition_function_part";
		writeFormulaToFile(pub_aig_manager, map_it->second, transition_function_part_file_name, ".v", 0, 0);
	}	
	#endif

	map<Aig_Obj_t*, Aig_Obj_t*> input_object_to_transition_function_parts;
	for(map<string, Aig_Obj_t*>::iterator map_it = output_string_to_transition_function_parts.begin(); map_it != output_string_to_transition_function_parts.end(); map_it++)
	{
		string latchout_name = map_it->first;
		int index_of_uscore = latchout_name.find_last_of("_");
	       	string latchout_part = latchout_name.substr(0, index_of_uscore);
		assert(latchout_part == "LATCHOUT");
		string location_str = latchout_name.substr(index_of_uscore+1);
		
		string latchin_name = "LATCHIN_";
		latchin_name += location_str;
	
		map<string, Aig_Obj_t*>::iterator Ci_name_to_Ci_object_map_it = Ci_name_to_Ci_object_map.find(latchin_name);
		assert(Ci_name_to_Ci_object_map_it != Ci_name_to_Ci_object_map.end());
		Aig_Obj_t* input_object = Ci_name_to_Ci_object_map_it->second;
		assert(input_object != NULL);
		
		input_object_to_transition_function_parts.insert(make_pair(input_object, map_it->second));
	}		

	#ifdef DEBUG_SKOLEM
	cout << "\ninput_object_to_transition_function_parts\n";
	int file_counter = 1;
	for(map<Aig_Obj_t*, Aig_Obj_t*>::iterator map_it = input_object_to_transition_function_parts.begin(); map_it != input_object_to_transition_function_parts.end(); map_it++)
	{
		string transition_function_part_file_name = benchmark_name_without_extension;
		transition_function_part_file_name += "_transition_function_part";
		writeFormulaToFile(pub_aig_manager, map_it->second, transition_function_part_file_name, ".v", 0, file_counter);

		string transition_function_name_file_name = benchmark_name_without_extension;
		transition_function_name_file_name += "_transition_function_name";
		writeFormulaToFile(pub_aig_manager, map_it->first, transition_function_name_file_name, ".v", 0, file_counter);

		file_counter++;
	}	
	#endif

	set<Aig_Obj_t*> single_bit_differing_from_true_components;
	// This has (f_1(X, I) = f_1(X, true)) \wedge \ldots \wedge (f_m(X, I) \neq f_m(X, true))
	set<Aig_Obj_t*> single_bit_differing_from_cycle_components;
	// This has (f_1(X, I) = x_1) \wedge \ldots \wedge (f_m(X, I) \neq x_m)

	set<Aig_Obj_t*> all_bit_differing_from_true_components;
	set<Aig_Obj_t*> all_bit_differing_from_cycle_components;

	int part_number = 1;
	int number_of_parts = input_object_to_transition_function_parts.size();
	for(map<Aig_Obj_t*, Aig_Obj_t*>::iterator map_it = input_object_to_transition_function_parts.begin(); map_it != input_object_to_transition_function_parts.end(); map_it++)
	{
		Aig_Obj_t* transition_function_part = map_it->second; // f_i(X, I)
		Aig_Obj_t* transition_function_name = map_it->first; // x_i

		Aig_Obj_t* transition_function_part_after_replacement;
		transition_function_part_after_replacement = replaceVariablesByFormulas(transition_function_part, variable_to_skolem_function_map);
		assert(transition_function_part_after_replacement != NULL); // f_i(x, true)

		Aig_Obj_t* single_bit_differing_from_true_component;
		single_bit_differing_from_true_component = createEquivalence(transition_function_part, transition_function_part_after_replacement, pub_aig_manager);
		assert(single_bit_differing_from_true_component != NULL); // f_i(X, I) \equiv f_i(x, G(X))

		Aig_Obj_t* single_bit_differing_from_cycle_component;
		single_bit_differing_from_cycle_component = createEquivalence(transition_function_part, transition_function_name, pub_aig_manager);
		assert(single_bit_differing_from_cycle_component != NULL); // f_i(X, I) \equiv x_i

		Aig_Obj_t* all_bit_differing_from_true_component = createNot(single_bit_differing_from_true_component, pub_aig_manager);
		assert(all_bit_differing_from_true_component != NULL); 

		Aig_Obj_t* all_bit_differing_from_cycle_component = createNot(single_bit_differing_from_cycle_component, pub_aig_manager);
		assert(all_bit_differing_from_cycle_component != NULL); 

		if(part_number == number_of_parts)
		{
			single_bit_differing_from_true_component = createNot(single_bit_differing_from_true_component, pub_aig_manager);
			assert(single_bit_differing_from_true_component != NULL); // f_i(X, I) \neq f_i(x, G(X))	

			single_bit_differing_from_cycle_component = createNot(single_bit_differing_from_cycle_component, pub_aig_manager);
			assert(single_bit_differing_from_cycle_component != NULL); // f_i(X, I) \neq x_i		
		}
		
		single_bit_differing_from_true_components.insert(single_bit_differing_from_true_component);
		single_bit_differing_from_cycle_components.insert(single_bit_differing_from_cycle_component);
		all_bit_differing_from_true_components.insert(all_bit_differing_from_true_component);
		all_bit_differing_from_cycle_components.insert(all_bit_differing_from_cycle_component);

		part_number++;
	}

	int fresh_count = 1;
	set<Aig_Obj_t*> all_bit_differing_from_true_tseitin_components;
	set<Aig_Obj_t*> fresh_objects_for_all_bit_differing_from_true_tseitin_components;
	for(set<Aig_Obj_t*>::iterator all_bit_differing_from_true_components_it = all_bit_differing_from_true_components.begin(); all_bit_differing_from_true_components_it != all_bit_differing_from_true_components.end(); all_bit_differing_from_true_components_it++)
	{
		Aig_Obj_t* all_bit_differing_from_true_component = *all_bit_differing_from_true_components_it;
		Aig_Obj_t* fresh_object = Aig_ObjCreateCi(pub_aig_manager);	
		assert(fresh_object != NULL);
		fresh_objects_for_all_bit_differing_from_true_tseitin_components.insert(fresh_object);

		char fresh_count_char[100];
		sprintf(fresh_count_char, "%d", fresh_count);
		string fresh_count_string(fresh_count_char);
		string fresh_object_string = "f_";
		fresh_object_string += fresh_count_string;
		fresh_count++;

		int fresh_object_id = Aig_ObjId(fresh_object); 
		Ci_id_to_Ci_name_map.insert(make_pair(fresh_object_id, fresh_object_string));
		Ci_name_to_Ci_number_map.insert(make_pair(fresh_object_string, number_of_Cis));	
		number_of_Cis++;

		Aig_Obj_t* all_bit_differing_from_true_tseitin_component = createEquivalence(fresh_object, all_bit_differing_from_true_component, pub_aig_manager);
		assert(all_bit_differing_from_true_tseitin_component != NULL); 
		all_bit_differing_from_true_tseitin_components.insert(all_bit_differing_from_true_tseitin_component);
	}

	int no_of_cis_with_f_variables = number_of_Cis;

	assert(fresh_objects_for_all_bit_differing_from_true_tseitin_components.size() > 0);
	Aig_Obj_t* all_bit_differing_from_true_tseitin_component = createOr(fresh_objects_for_all_bit_differing_from_true_tseitin_components, pub_aig_manager);
	assert(all_bit_differing_from_true_tseitin_component != NULL); 
	all_bit_differing_from_true_tseitin_components.insert(all_bit_differing_from_true_tseitin_component);	
		
	fresh_count = 1;
	set<Aig_Obj_t*> all_bit_differing_from_cycle_tseitin_components;
	set<Aig_Obj_t*> fresh_objects_for_all_bit_differing_from_cycle_tseitin_components;
	for(set<Aig_Obj_t*>::iterator all_bit_differing_from_cycle_components_it = all_bit_differing_from_cycle_components.begin(); all_bit_differing_from_cycle_components_it != all_bit_differing_from_cycle_components.end(); all_bit_differing_from_cycle_components_it++)
	{
		Aig_Obj_t* all_bit_differing_from_cycle_component = *all_bit_differing_from_cycle_components_it;
		Aig_Obj_t* fresh_object = Aig_ObjCreateCi(pub_aig_manager);	
		assert(fresh_object != NULL);
		fresh_objects_for_all_bit_differing_from_cycle_tseitin_components.insert(fresh_object);

		char fresh_count_char[100];
		sprintf(fresh_count_char, "%d", fresh_count);
		string fresh_count_string(fresh_count_char);
		string fresh_object_string = "g_";
		fresh_object_string += fresh_count_string;
		fresh_count++;

		int fresh_object_id = Aig_ObjId(fresh_object); 
		Ci_id_to_Ci_name_map.insert(make_pair(fresh_object_id, fresh_object_string));
		Ci_name_to_Ci_number_map.insert(make_pair(fresh_object_string, number_of_Cis));	
		number_of_Cis++;

		Aig_Obj_t* all_bit_differing_from_cycle_tseitin_component = createEquivalence(fresh_object, all_bit_differing_from_cycle_component, pub_aig_manager);
		assert(all_bit_differing_from_cycle_tseitin_component != NULL); 
		all_bit_differing_from_cycle_tseitin_components.insert(all_bit_differing_from_cycle_tseitin_component);
	}

	int total_no_of_cis = number_of_Cis;

	assert(fresh_objects_for_all_bit_differing_from_cycle_tseitin_components.size() > 0);
	Aig_Obj_t* all_bit_differing_from_cycle_tseitin_component = createOr(fresh_objects_for_all_bit_differing_from_cycle_tseitin_components, pub_aig_manager);
	assert(all_bit_differing_from_cycle_tseitin_component != NULL); 
	all_bit_differing_from_cycle_tseitin_components.insert(all_bit_differing_from_cycle_tseitin_component);

	assert(single_bit_differing_from_true_components.size() > 0);
	Aig_Obj_t* single_bit_differing_from_true = createAnd(single_bit_differing_from_true_components, pub_aig_manager);
	assert(single_bit_differing_from_true != NULL);
	#ifdef DEBUG_SKOLEM
	string single_bit_differing_from_true_file_name = benchmark_name_without_extension;
	single_bit_differing_from_true_file_name += "_single_bit_differing_from_true";
	writeFormulaToFile(pub_aig_manager, single_bit_differing_from_true, single_bit_differing_from_true_file_name, ".v", 0, 0);
	#endif

	assert(single_bit_differing_from_cycle_components.size() > 0);
	Aig_Obj_t* single_bit_differing_from_cycle = createAnd(single_bit_differing_from_cycle_components, pub_aig_manager);
	assert(single_bit_differing_from_cycle != NULL);
	#ifdef DEBUG_SKOLEM
	string single_bit_differing_from_cycle_file_name = benchmark_name_without_extension;
	single_bit_differing_from_cycle_file_name += "_single_bit_differing_from_cycle";
	writeFormulaToFile(pub_aig_manager, single_bit_differing_from_cycle, single_bit_differing_from_cycle_file_name, ".v", 0, 0);
	#endif

	assert(all_bit_differing_from_true_tseitin_components.size() > 0);
	Aig_Obj_t* all_bit_differing_from_true_tseitin = createAnd(all_bit_differing_from_true_tseitin_components, pub_aig_manager);
	assert(all_bit_differing_from_true_tseitin != NULL);
	#ifdef DEBUG_SKOLEM
	string all_bit_differing_from_true_tseitin_file_name = benchmark_name_without_extension;
	all_bit_differing_from_true_tseitin_file_name += "_all_bit_differing_from_true_tseitin";
	writeFormulaToFile(pub_aig_manager, all_bit_differing_from_true_tseitin, all_bit_differing_from_true_tseitin_file_name, ".v", 0, 0);
	#endif

	assert(all_bit_differing_from_cycle_tseitin_components.size() > 0);
	Aig_Obj_t* all_bit_differing_from_cycle_tseitin = createAnd(all_bit_differing_from_cycle_tseitin_components, pub_aig_manager);
	assert(all_bit_differing_from_cycle_tseitin != NULL);
	#ifdef DEBUG_SKOLEM
	string all_bit_differing_from_cycle_tseitin_file_name = benchmark_name_without_extension;
	all_bit_differing_from_cycle_tseitin_file_name += "_all_bit_differing_from_cycle_tseitin";
	writeFormulaToFile(pub_aig_manager, all_bit_differing_from_cycle_tseitin, all_bit_differing_from_cycle_tseitin_file_name, ".v", 0, 0);
	#endif

	
	// Printing in files	
	
	Aig_Obj_t* single_bit_differing_from_cycle_CO;
	single_bit_differing_from_cycle_CO = Aig_ObjCreateCo( pub_aig_manager, single_bit_differing_from_cycle );
	assert(single_bit_differing_from_cycle_CO != NULL);

	Aig_Man_t* single_bit_differing_from_cycle_aig_manager;
	single_bit_differing_from_cycle_aig_manager = simplifyUsingConeOfInfluence( pub_aig_manager, Aig_ManCoNum(pub_aig_manager)-1, 1 );
	assert(single_bit_differing_from_cycle_aig_manager != NULL);

	char verilog_file_char[100];
	string verilog_file = benchmark_name_without_extension;

	if(existentially_quantify_tseitin_variables_in_benchmark_generation)
	{
		verilog_file += "_single_bit_differing_from_cycle_tseitin_variables_ex_quantified";	
	}
	else
	{
		verilog_file += "_single_bit_differing_from_cycle";	
	}

	char pname[100];
	strcpy(pname, verilog_file.c_str());
	single_bit_differing_from_cycle_aig_manager->pName = pname;
	verilog_file += ".v";
	strcpy(verilog_file_char, verilog_file.c_str());

	if(existentially_quantify_tseitin_variables_in_benchmark_generation)
	{
		writeCombinationalCircuitInVerilog(single_bit_differing_from_cycle_aig_manager, number_of_variables_to_eliminate, original_no_of_cis, no_of_cis_with_f_variables, total_no_of_cis, verilog_file_char, true );	
	}
	else
	{		
		writeCombinationalCircuitInVerilog(single_bit_differing_from_cycle_aig_manager, number_of_variables_to_eliminate, original_no_of_cis, no_of_cis_with_f_variables, total_no_of_cis, verilog_file_char, false );
	}
	
	cout << "\nBenchmark file " << verilog_file << " written\n";

	Aig_Obj_t* single_bit_differing_from_true_CO;
	single_bit_differing_from_true_CO = Aig_ObjCreateCo( pub_aig_manager, single_bit_differing_from_true );
	assert(single_bit_differing_from_true_CO != NULL);

	Aig_Man_t* single_bit_differing_from_true_aig_manager;
	single_bit_differing_from_true_aig_manager = simplifyUsingConeOfInfluence( pub_aig_manager, Aig_ManCoNum(pub_aig_manager)-1, 1 );
	assert(single_bit_differing_from_true_aig_manager != NULL);

	verilog_file = benchmark_name_without_extension;

	if(existentially_quantify_tseitin_variables_in_benchmark_generation)
	{
		verilog_file += "_single_bit_differing_from_true_tseitin_variables_ex_quantified";
	}
	else
	{
		verilog_file += "_single_bit_differing_from_true";
	}

	strcpy(pname, verilog_file.c_str());
	single_bit_differing_from_true_aig_manager->pName = pname;
	verilog_file += ".v";
	strcpy(verilog_file_char, verilog_file.c_str());

	if(existentially_quantify_tseitin_variables_in_benchmark_generation)
	{
		writeCombinationalCircuitInVerilog(single_bit_differing_from_true_aig_manager, number_of_variables_to_eliminate, original_no_of_cis, no_of_cis_with_f_variables, total_no_of_cis, verilog_file_char, true );
	}
	else
	{
		writeCombinationalCircuitInVerilog(single_bit_differing_from_true_aig_manager, number_of_variables_to_eliminate, original_no_of_cis, no_of_cis_with_f_variables, total_no_of_cis, verilog_file_char, false );
	}

	cout << "\nBenchmark file " << verilog_file << " written\n";

	Aig_Obj_t* all_bit_differing_from_cycle_tseitin_CO;
	all_bit_differing_from_cycle_tseitin_CO = Aig_ObjCreateCo( pub_aig_manager, all_bit_differing_from_cycle_tseitin );
	assert(all_bit_differing_from_cycle_tseitin_CO != NULL);

	Aig_Man_t* all_bit_differing_from_cycle_tseitin_aig_manager;
	all_bit_differing_from_cycle_tseitin_aig_manager = simplifyUsingConeOfInfluence( pub_aig_manager, Aig_ManCoNum(pub_aig_manager)-1, 1 );
	assert(all_bit_differing_from_cycle_tseitin_aig_manager != NULL);

	verilog_file = benchmark_name_without_extension;

	if(existentially_quantify_tseitin_variables_in_benchmark_generation)
	{
		verilog_file += "_all_bit_differing_from_cycle_tseitin_tseitin_variables_ex_quantified";
	}
	else
	{
		verilog_file += "_all_bit_differing_from_cycle_tseitin";
	}

	strcpy(pname, verilog_file.c_str());
	all_bit_differing_from_cycle_tseitin_aig_manager->pName = pname;
	verilog_file += ".v";
	strcpy(verilog_file_char, verilog_file.c_str());

	if(existentially_quantify_tseitin_variables_in_benchmark_generation)
	{
		writeCombinationalCircuitInVerilog(all_bit_differing_from_cycle_tseitin_aig_manager, number_of_variables_to_eliminate, original_no_of_cis, no_of_cis_with_f_variables, total_no_of_cis, verilog_file_char, true );	
	}
	else
	{
		writeCombinationalCircuitInVerilog(all_bit_differing_from_cycle_tseitin_aig_manager, number_of_variables_to_eliminate, original_no_of_cis, no_of_cis_with_f_variables, total_no_of_cis, verilog_file_char, false );
	}

	cout << "\nBenchmark file " << verilog_file << " written\n";

	Aig_Obj_t* all_bit_differing_from_true_tseitin_CO;
	all_bit_differing_from_true_tseitin_CO = Aig_ObjCreateCo( pub_aig_manager, all_bit_differing_from_true_tseitin );
	assert(all_bit_differing_from_true_tseitin_CO != NULL);

	Aig_Man_t* all_bit_differing_from_true_tseitin_aig_manager;
	all_bit_differing_from_true_tseitin_aig_manager = simplifyUsingConeOfInfluence( pub_aig_manager, Aig_ManCoNum(pub_aig_manager)-1, 1 );
	assert(all_bit_differing_from_true_tseitin_aig_manager != NULL);

	verilog_file = benchmark_name_without_extension;

	if(existentially_quantify_tseitin_variables_in_benchmark_generation)
	{
		verilog_file += "_all_bit_differing_from_true_tseitin_tseitin_variables_ex_quantified";
	}
	else
	{
		verilog_file += "_all_bit_differing_from_true_tseitin";
	}

	strcpy(pname, verilog_file.c_str());
	all_bit_differing_from_true_tseitin_aig_manager->pName = pname;
	verilog_file += ".v";
	strcpy(verilog_file_char, verilog_file.c_str());

	if(existentially_quantify_tseitin_variables_in_benchmark_generation)
	{
		writeCombinationalCircuitInVerilog(all_bit_differing_from_true_tseitin_aig_manager, number_of_variables_to_eliminate, original_no_of_cis, no_of_cis_with_f_variables, total_no_of_cis, verilog_file_char, true );
	}
	else
	{
		writeCombinationalCircuitInVerilog(all_bit_differing_from_true_tseitin_aig_manager, number_of_variables_to_eliminate, original_no_of_cis, no_of_cis_with_f_variables, total_no_of_cis, verilog_file_char, false );
	}
	
	cout << "\nBenchmark file " << verilog_file << " written\n";
}



Aig_Obj_t* AIGBasedSkolem::computeInitialSkolemFunctionsBadSetsAndCannotBeSets(int var_to_elim_index)
{
	Aig_Obj_t* skolem_function;
	Aig_Obj_t* skolem_function_part1;
	Aig_Obj_t* skolem_function_part2;
	set<Aig_Obj_t*> skolem_function_part1_components;
	set<Aig_Obj_t*> skolem_function_part2_components;

	Aig_Obj_t* initial_cbzero_part_for_bad;
	Aig_Obj_t* initial_cbone_part_for_bad;

	// compute the elements in cb0_k and cb1_k
	set<Aig_Obj_t*> cannot_be_one_set_for_var_to_elim_index;
	set<Aig_Obj_t*> cannot_be_zero_set_for_var_to_elim_index;

	for(set<int>::iterator factor_it = FactorsWithVariable.begin(); factor_it != FactorsWithVariable.end(); factor_it++)
	{
		int factor_index = *factor_it;

		#ifdef DEBUG_SKOLEM
		cout << "\nfactor_index = " << factor_index << endl;
		#endif

		Aig_Obj_t* neg_cofactor_1 = computeNegatedCofactorOne(var_to_elim_index, factor_index); 
		assert(neg_cofactor_1 != NULL);		
		sizes_of_cannot_be_one_elements_of_variable.push_back(computeSize(neg_cofactor_1, pub_aig_manager));

		// connecting to some output to avoid unwanted deletion
		Aig_Obj_t* neg_cofactor_1_CO = Aig_ObjCreateCo(pub_aig_manager, neg_cofactor_1 ); 
		assert(neg_cofactor_1_CO != NULL);

		Aig_Obj_t* neg_cofactor_0 = computeNegatedCofactorZero(var_to_elim_index, factor_index); 
		assert(neg_cofactor_0 != NULL);
		sizes_of_cannot_be_zero_elements_of_variable.push_back(computeSize(neg_cofactor_0, pub_aig_manager));

		// connect to some output to avoid unwanted deletion
		Aig_Obj_t* neg_cofactor_0_CO = Aig_ObjCreateCo(pub_aig_manager, neg_cofactor_0 ); 
		assert(neg_cofactor_0_CO != NULL);
	
		#ifdef DEBUG_SKOLEM
		writeFormulaToFile(pub_aig_manager, neg_cofactor_1, "neg_cofactor_1", ".v", var_to_elim_index, factor_index);	
		writeFormulaToFile(pub_aig_manager, neg_cofactor_0, "neg_cofactor_0", ".v", var_to_elim_index, factor_index);	
		#endif

		// Allocate strings and objects for the dags neg_cofactor_1 and neg_cofactor_0 

		string cannot_be_one_string;
		Aig_Obj_t* cannot_be_one_object;
		allocateStringAndObjectToCannotBeDag(1, neg_cofactor_1, cannot_be_one_string, cannot_be_one_object);

		string cannot_be_zero_string;
		Aig_Obj_t* cannot_be_zero_object;
		allocateStringAndObjectToCannotBeDag(0, neg_cofactor_0, cannot_be_zero_string, cannot_be_zero_object);

		#ifdef DEBUG_SKOLEM
		show_cannot_be_string_to_cannot_be_object_map();
		show_cannot_be_object_to_cannot_be_dag_map();
		#endif

		// Insert the objects in respective cannot-be-sets
		cannot_be_one_set_for_var_to_elim_index.insert(cannot_be_one_object);
		cannot_be_zero_set_for_var_to_elim_index.insert(cannot_be_zero_object);
		
		// Insert the cannot-be-1 dag into the skolem_function_part1_components
		skolem_function_part1_components.insert(neg_cofactor_1);						

		// Insert the cannot-be-0 dag into the skolem_function_part2_components
		skolem_function_part2_components.insert(neg_cofactor_0);
	}// for each factor ends here

	
	if(checkTimeOut()) // check for time-out
	{
		cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::computeInitialSkolemFunctionsBadSetsAndCannotBeSets\n";
		timed_out = true; // timed_out flag set
		return NULL;
	}

	// insert in global tables
	map<int, set<Aig_Obj_t*> >::iterator cannot_be_one_set_it = cannot_be_one_set.find(var_to_elim_index);
	assert(cannot_be_one_set_it == cannot_be_one_set.end());
	cannot_be_one_set.insert(make_pair(var_to_elim_index, cannot_be_one_set_for_var_to_elim_index));

	map<int, set<Aig_Obj_t*> >::iterator cannot_be_zero_set_it = cannot_be_zero_set.find(var_to_elim_index);
	assert(cannot_be_zero_set_it == cannot_be_zero_set.end());
	cannot_be_zero_set.insert(make_pair(var_to_elim_index, cannot_be_zero_set_for_var_to_elim_index));

	// Let's compute the skolem_function
	// skolem_function is 
	//          disjunction of elements in cannot_be_one_set_for_var_to_elim_index \vee 
	//          negation of (disjunction of elements in cannot_be_one_set_for_var_to_elim_index)
	if(cannot_be_one_set_for_var_to_elim_index.empty()) // no condition under which it can't be 1
	// i.e. it can be 1 always
	{
		skolem_function_part1 = createTrue(pub_aig_manager);
		initial_cbone_part_for_bad = createFalse(pub_aig_manager);
	}
	else
	{
		skolem_function_part1 = createOr(skolem_function_part1_components, pub_aig_manager);
		initial_cbone_part_for_bad = skolem_function_part1;
		skolem_function_part1 = createNot(skolem_function_part1, pub_aig_manager);
	}
	assert(skolem_function_part1 != NULL);
	
	if(cannot_be_zero_set_for_var_to_elim_index.empty()) // no condition under which it can't be 0
	// i.e. it can be 0 always
	{
		skolem_function_part2 = createFalse(pub_aig_manager);
		initial_cbzero_part_for_bad = createFalse(pub_aig_manager);
	}
	else
	{
		skolem_function_part2 = createOr(skolem_function_part2_components, pub_aig_manager);
		initial_cbzero_part_for_bad = skolem_function_part2;
	}
	assert(skolem_function_part2 != NULL);


	if(use_cbzero_in_unified_cegar)
	{
		skolem_function = createOr(skolem_function_part2, skolem_function_part1, pub_aig_manager);
	}
	else
	{
		skolem_function = skolem_function_part1;
	}
	
	
	assert(skolem_function != NULL);

	InitialSkolemFunctionSizeBeforeOptimization = computeSize(skolem_function, pub_aig_manager);

	if(use_dontcare_optimization_in_cegar)
	// optimize the skolem_function
	{
		// create Cb1_i \wedge Cb0_i

		// Cb1_i is disjunction of AIGs in cannot_be_one_set_for_var_to_elim_index, i.e. ~skolem_function_part1
		Aig_Obj_t* Cb1_part = createNot(skolem_function_part1, pub_aig_manager);

		// Cb0_i is disjunction of AIGs in cannot_be_zero_set_for_var_to_elim_index, i.e. skolem_function_part2
		Aig_Obj_t* Cb0_part = skolem_function_part2;

		Aig_Obj_t* dontcare_part = createAnd(Cb1_part, Cb0_part, pub_aig_manager);
		assert(dontcare_part != NULL);

		#ifdef DEBUG_SKOLEM
		writeFormulaToFile(pub_aig_manager, dontcare_part, "dontcare_part", ".v", var_to_elim_index, cegar_iteration_number);	
		writeFormulaToFile(pub_aig_manager, skolem_function, "unoptimized_skolem_function", ".v", var_to_elim_index, cegar_iteration_number);	
		#endif

		skolem_function = performDontCareOptimization(pub_aig_manager, skolem_function, dontcare_part);
		assert(skolem_function != NULL);
		
	}

	// connect to some output to avoid unwanted deletion
	Aig_Obj_t* skolem_function_part2_CO = Aig_ObjCreateCo(pub_aig_manager, skolem_function_part2 ); 
	assert(skolem_function_part2_CO != NULL);

	Aig_Obj_t* skolem_function_CO = Aig_ObjCreateCo(pub_aig_manager, skolem_function ); 
	assert(skolem_function_CO != NULL);

	#ifdef DEBUG_SKOLEM
	cout << "\nabstract skolem_function computed\n";	
	#endif

	#ifdef PRINT_SKOLEM_FUNCTIONS
	string skolem_function_file_name = benchmark_name_without_extension;
	skolem_function_file_name += "_skolem_function";
	writeFormulaToFile(pub_aig_manager, skolem_function, skolem_function_file_name, ".v", var_to_elim_index, cegar_iteration_number);
	#endif

	// Enter into matrix
	insertIntoOneDimensionalMatrix(SkolemFunctions, number_of_vars_to_elim, var_to_elim_index, skolem_function, false);


	// Compute Badsets

	if(var_to_elim_index < number_of_vars_to_elim) // No need to compute Bad_{n+1} 
	{
		Aig_Obj_t* bad_set_for_next_var;

		if(compute_initial_bads_from_cbs)
		{
			bad_set_for_next_var = createAnd(initial_cbzero_part_for_bad, initial_cbone_part_for_bad, pub_aig_manager);
		}
		else
		{
		
			set<Aig_Obj_t*> alpha_components; 
			set<Aig_Obj_t*> beta_components; 
		
			for(set<int>::iterator factor_it = FactorsWithVariable.begin(); factor_it != FactorsWithVariable.end(); factor_it++)
			{
				int factor_index = *factor_it;

				#ifdef DEBUG_SKOLEM
				cout << "\nfactor_index = " << factor_index << endl;
				#endif

				// Suppose j = factor_index
				// Get alpha_i_j and beta_i_j

				Aig_Obj_t* alpha_i_j;
				alpha_i_j = computeAlpha(var_to_elim_index, factor_index); 
				assert(alpha_i_j != NULL);

				#ifdef DEBUG_SKOLEM
				writeFormulaToFile(pub_aig_manager, alpha_i_j, "alpha", ".v", var_to_elim_index, factor_index);		
				cout << "\nalpha_" << var_to_elim_index << "_" << factor_index << " obtained\n";			
				#endif

				Aig_Obj_t* beta_i_j;
				beta_i_j = computeBeta(var_to_elim_index, factor_index); 
				assert(beta_i_j != NULL);	
	
				#ifdef DEBUG_SKOLEM
				writeFormulaToFile(pub_aig_manager, beta_i_j, "beta", ".v", var_to_elim_index, factor_index);		
				cout << "\nbeta_" << var_to_elim_index << "_" << factor_index << " obtained\n";			
				#endif
			
				alpha_components.insert(alpha_i_j);
				beta_components.insert(beta_i_j);
						
			}// for each factor ends here
	
			if(checkTimeOut()) // check for time-out
			{
				cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::computeInitialSkolemFunctionsBadSetsAndCannotBeSets\n";
				timed_out = true; // timed_out flag set
				return NULL;
			}


			Aig_Obj_t* alpha_part;
			if(alpha_components.size() == 0) // we should return false in this case (as per defn. of alpha)
			{
				alpha_part = createFalse(pub_aig_manager); 
				assert(alpha_part != NULL);
			}
			else
			{
				alpha_part = createOr(alpha_components, pub_aig_manager);
				assert(alpha_part != NULL);
			}

		
			Aig_Obj_t* beta_part;
			if(beta_components.size() == 0) // we should return false in this case (as per defn. of beta)
			{
				beta_part = createFalse(pub_aig_manager); 
				assert(beta_part != NULL);
			}
			else
			{
				beta_part = createOr(beta_components, pub_aig_manager);
				assert(beta_part != NULL);
			}

		
			bad_set_for_next_var = createAnd(alpha_part, beta_part, pub_aig_manager);

		}
	
		assert(bad_set_for_next_var != NULL);

		// connect to some output to avoid unwanted deletion
		Aig_Obj_t* bad_set_for_next_var_CO = Aig_ObjCreateCo(pub_aig_manager, bad_set_for_next_var ); 
		assert(bad_set_for_next_var_CO != NULL);

		#ifdef DEBUG_SKOLEM
		cout << "\nbad_set_" << var_to_elim_index+1 << " computed\n";
		writeFormulaToFile(pub_aig_manager, bad_set_for_next_var, "bad_set", ".v", var_to_elim_index+1, cegar_iteration_number);	
		#endif

		// Enter into matrix
		insertIntoOneDimensionalMatrix(BadSets, number_of_vars_to_elim, var_to_elim_index+1, bad_set_for_next_var, false);

		CorrectionPartSize = computeSize(bad_set_for_next_var, pub_aig_manager);
	}	
	else
	{
		CorrectionPartSize = -1;
	}

	#ifdef PRINT_VERY_DETAILED_RECORDS_ON_SCREEN
	cout << "\nsize of bad_set_" << var_to_elim_index+1 << " is " << CorrectionPartSize << endl;
	#endif

	if(checkTimeOut()) // check for time-out
	{
		cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::computeInitialSkolemFunctionsBadSetsAndCannotBeSets\n";
		timed_out = true; // timed_out flag set
		return NULL;
	}	

	// Compute ICb0_k in terms of objects and as dag
	// These will be required while recomputing the Skolem functions
	// Let's compute these right now, since later on these sets will get changed

	// we already have ICb0_k dag; let's insert it
	map<int, Aig_Obj_t*>::iterator initial_cannot_be_zero_dags_it = initial_cannot_be_zero_dags.find(var_to_elim_index);
	assert(initial_cannot_be_zero_dags_it == initial_cannot_be_zero_dags.end());
	initial_cannot_be_zero_dags.insert(make_pair(var_to_elim_index, skolem_function_part2));
	
	// Let's compute the ICb0_k object
	Aig_Obj_t* initial_cannot_be_zero_object;
	if(cannot_be_zero_set_for_var_to_elim_index.empty()) // no condition under which it can't be 0
	// i.e. it can be 0 always
	{
		initial_cannot_be_zero_object = createFalse(pub_aig_manager);
	}
	else
	{
		initial_cannot_be_zero_object = createOr(cannot_be_zero_set_for_var_to_elim_index, pub_aig_manager);
	}
	assert(initial_cannot_be_zero_object != NULL);
	// connect to some output to avoid unwanted deletion
	Aig_Obj_t* initial_cannot_be_zero_object_CO = Aig_ObjCreateCo(pub_aig_manager, initial_cannot_be_zero_object ); 
	assert(initial_cannot_be_zero_object_CO != NULL);
	// let's insert it
	map<int, Aig_Obj_t*>::iterator initial_cannot_be_zero_objects_it = initial_cannot_be_zero_objects.find(var_to_elim_index);
	assert(initial_cannot_be_zero_objects_it == initial_cannot_be_zero_objects.end());
	initial_cannot_be_zero_objects.insert(make_pair(var_to_elim_index, initial_cannot_be_zero_object));
		
	return skolem_function;	
}


void AIGBasedSkolem::refineSkolemFunctions_using_Mu_Based_Scheme_With_Optimizations(int correction_index, map<string, int> &Model_of_ExactnessCheck, map<int, Aig_Obj_t*> &Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX, map<int, Aig_Obj_t*> &Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX)
{
	#ifdef RECORD_KEEP
	string record_file;
	record_file = logfile_prefix;
	record_file += "skolem_function_generation_details.txt";
	FILE* record_fp = fopen(record_file.c_str(), "a+");
	assert(record_fp != NULL);
	#endif

	// For easy of processing let's create
	map<int, int> XValues; // XValues[i] gives value of x_i
	map<string, int> YValues; // YValues[y_variable] gives value of y_variable
	map<Aig_Obj_t*, int> cannot_be_object_to_value_map; // maps object of eta_j or sigma_j to value
	map<int, int> cannot_be_one_set_values; // cannot_be_one_set_values[i] gives value of cannot_be_one_set_values_i
	map<int, int> cannot_be_zero_set_values; // cannot_be_zero_set_values[i] gives value of cannot_be_zero_set_values_i

	for(int var_to_elim_index = 1; var_to_elim_index <= number_of_vars_to_elim; var_to_elim_index++)
	{
		string var_to_elim = searchVarIndexToVarNameMap(var_index_to_var_name_map, var_to_elim_index);
		
		map<string, int>::iterator Model_of_ExactnessCheck_it;

		Model_of_ExactnessCheck_it = Model_of_ExactnessCheck.find(var_to_elim);
		assert(Model_of_ExactnessCheck_it != Model_of_ExactnessCheck.end());
		XValues.insert(make_pair(var_to_elim_index, Model_of_ExactnessCheck_it->second));
	}

	for(map<string, int>::iterator model_it = Model_of_ExactnessCheck.begin(); model_it != Model_of_ExactnessCheck.end(); model_it++)
	{
		string variable_name = model_it->first;
		int variable_value = model_it->second;
		
		map<string, Aig_Obj_t*>::iterator cannot_be_string_to_cannot_be_object_map_it = cannot_be_string_to_cannot_be_object_map.find(variable_name);

		if(cannot_be_string_to_cannot_be_object_map_it != cannot_be_string_to_cannot_be_object_map.end()) // variable_name is eta/sigma
		{
			Aig_Obj_t* cannot_be_object = cannot_be_string_to_cannot_be_object_map_it->second;
			cannot_be_object_to_value_map.insert(make_pair(cannot_be_object, variable_value));		
		}
		else if(variables_not_quantified.find(variable_name) != variables_not_quantified.end()) // variable_name is a Y variable
		{
			YValues.insert(make_pair(variable_name, variable_value));
		}
	}

	for(map<int, set<Aig_Obj_t*> >::iterator cannot_be_one_set_it = cannot_be_one_set.begin(); cannot_be_one_set_it != cannot_be_one_set.end(); cannot_be_one_set_it++)
	{
		int var_to_elim_index = cannot_be_one_set_it->first;

		if(var_to_elim_index > correction_index)
		{
			break;
		}

		set<Aig_Obj_t*> cannot_be_one_set_of_variable = cannot_be_one_set_it->second;
		int value_of_cannot_be_one_set_of_variable = 0;

		for(set<Aig_Obj_t*>::iterator cannot_be_one_set_of_variable_it = cannot_be_one_set_of_variable.begin(); cannot_be_one_set_of_variable_it != cannot_be_one_set_of_variable.end(); cannot_be_one_set_of_variable_it++)
		{
			Aig_Obj_t* cannot_be_one_set_object_of_variable = *cannot_be_one_set_of_variable_it;
			
			map<Aig_Obj_t*, int>::iterator cannot_be_object_to_value_map_it = cannot_be_object_to_value_map.find(cannot_be_one_set_object_of_variable);

			if(cannot_be_object_to_value_map_it == cannot_be_object_to_value_map.end())
			{
				cout << "\nProblem with var_to_elim_index = " << var_to_elim_index << "\t cannot_be_one_set_object_of_variable = " << cannot_be_one_set_object_of_variable << endl;
				assert(false);
			}

			int value_of_cannot_be_one_set_object_of_variable = cannot_be_object_to_value_map_it->second;

			if(value_of_cannot_be_one_set_object_of_variable == 1)
			{
				value_of_cannot_be_one_set_of_variable = value_of_cannot_be_one_set_object_of_variable;
				break;
			}
		}

		cannot_be_one_set_values.insert(make_pair(var_to_elim_index, value_of_cannot_be_one_set_of_variable));
	}

	for(map<int, set<Aig_Obj_t*> >::iterator cannot_be_zero_set_it = cannot_be_zero_set.begin(); cannot_be_zero_set_it != cannot_be_zero_set.end(); cannot_be_zero_set_it++)
	{
		int var_to_elim_index = cannot_be_zero_set_it->first;

		if(var_to_elim_index > correction_index)
		{
			break;
		}

		set<Aig_Obj_t*> cannot_be_zero_set_of_variable = cannot_be_zero_set_it->second;
		int value_of_cannot_be_zero_set_of_variable = 0;
		
		for(set<Aig_Obj_t*>::iterator cannot_be_zero_set_of_variable_it = cannot_be_zero_set_of_variable.begin(); cannot_be_zero_set_of_variable_it != cannot_be_zero_set_of_variable.end(); cannot_be_zero_set_of_variable_it++)
		{
			Aig_Obj_t* cannot_be_zero_set_object_of_variable = *cannot_be_zero_set_of_variable_it;
			
			map<Aig_Obj_t*, int>::iterator cannot_be_object_to_value_map_it = cannot_be_object_to_value_map.find(cannot_be_zero_set_object_of_variable);
			assert(cannot_be_object_to_value_map_it != cannot_be_object_to_value_map.end());

			int value_of_cannot_be_zero_set_object_of_variable = cannot_be_object_to_value_map_it->second;

			if(value_of_cannot_be_zero_set_object_of_variable == 1)
			{
				value_of_cannot_be_zero_set_of_variable = value_of_cannot_be_zero_set_object_of_variable;
				break;
			}
		}

		cannot_be_zero_set_values.insert(make_pair(var_to_elim_index, value_of_cannot_be_zero_set_of_variable));
	}

	#ifdef DEBUG_CEGAR
	//#ifdef DEBUG_PAR
	cout << endl;
	for(int var_to_elim_index = 1; var_to_elim_index <= number_of_vars_to_elim; var_to_elim_index++)
	{
		cout << endl << "XValues[" << var_to_elim_index << "] = " << XValues[var_to_elim_index];
	}
	cout << endl;
	for(map<string, int>::iterator YValues_it = YValues.begin(); YValues_it != YValues.end(); YValues_it++)
	{
		cout << endl << "YValues[" << YValues_it->first << "] = " << YValues_it->second;
	}
	cout << endl;
	for(int var_to_elim_index = 1; var_to_elim_index <= correction_index; var_to_elim_index++)
	{
		cout << endl << "cannot_be_one_set_values[" << var_to_elim_index << "] = " << cannot_be_one_set_values[var_to_elim_index];
	}
	cout << endl;
	for(int var_to_elim_index = 1; var_to_elim_index <= correction_index; var_to_elim_index++)
	{
		cout << endl << "cannot_be_zero_set_values[" << var_to_elim_index << "] = " << cannot_be_zero_set_values[var_to_elim_index];
	}
	cout << endl;		
	#endif

	// find origin = largest l s.t. both cannot_be_one_set_values[l] and cannot_be_zero_set_values[l] are true
	// note that Skolem functions from correction_index+1 upto number_of_vars_to_elim are already corrected
	int origin = correction_index; 
	for(int var_to_elim_index = correction_index-1; var_to_elim_index >= 1; var_to_elim_index--)
	{
		if(cannot_be_one_set_values[var_to_elim_index] == 1 && cannot_be_zero_set_values[var_to_elim_index] == 1)
		{
			origin = var_to_elim_index;
			break;
		}
	}

	#ifdef DEBUG_CEGAR
	cout << "\norigin = " << origin << endl;
	#endif

	//#ifdef DEBUG_PAR
	//cout << "\norigin = " << origin << endl;
	//#endif	

	assert(origin <= correction_index-1);
		
	int number_of_cannot_be_one_elements_in_initial_mu;
	int number_of_cannot_be_zero_elements_in_initial_mu;
	int size_of_initial_mu;
	Aig_Obj_t* mu;
	mu = obtain_initial_mu(origin, cannot_be_object_to_value_map, number_of_cannot_be_one_elements_in_initial_mu, number_of_cannot_be_zero_elements_in_initial_mu, size_of_initial_mu);
	assert(mu != NULL);

	#ifdef RECORD_KEEP
	if(!mask_printing_cegar_details)
	{
		fprintf(record_fp, "\t(x@%d,%d+%d,%d)", origin, number_of_cannot_be_one_elements_in_initial_mu, number_of_cannot_be_zero_elements_in_initial_mu, size_of_initial_mu);
	}
	#endif

	#ifdef DEBUG_CEGAR
	string mu_file_name = benchmark_name_without_extension;
	mu_file_name += "_mu";

	cout << "\nInitial mu computed\n";

	writeFormulaToFile(pub_aig_manager, mu, mu_file_name, ".v", cegar_iteration_number, origin);
	#endif


	int destination = origin + 1;
	#ifdef DEBUG_CEGAR
	cout << "\ndestination = " << destination << endl;
	#endif

	while(destination <= correction_index)
	{
		if(!formulaFreeOfVariable(mu, destination)) // mu has x_destination in support
		{
			#ifdef DEBUG_SKOLEM
			cout << "\nmu has x_" << destination << " in its support\n";				
			#endif

			if(XValues[destination] == 1) // x_destination == 1
			{
				#ifdef DEBUG_SKOLEM
				cout << "\nx_" << destination << " == 1\n";
				#endif

				// assert (mu[x_destination --> 1])
				if(cannot_be_zero_set_values[destination] == 1) // Cb0_destination is true
				{
					#ifdef DEBUG_SKOLEM
					cout << "\ncannot_be_zero_set[" << destination << "] == 1\n";
					#endif

					// Let's obtain mu[x_destination --> 1]
					Aig_Obj_t* cofactor_one_of_mu;
					cofactor_one_of_mu = replaceVariableByConstant(mu, destination, 1);
					assert(cofactor_one_of_mu != NULL);
					
					int number_of_cannot_be_zero_elements_that_are_true;
					Aig_Obj_t* disjunction_of_true_cannot_be_zero_dags = obtain_disjunction_of_true_cannot_be_zero_dags(destination, cannot_be_object_to_value_map, cofactor_one_of_mu, number_of_cannot_be_zero_elements_that_are_true);
					assert(disjunction_of_true_cannot_be_zero_dags != NULL);
					int size_of_disjunction_of_true_cannot_be_zero_dags = computeSize(disjunction_of_true_cannot_be_zero_dags, pub_aig_manager);

					mu = createAnd(cofactor_one_of_mu, disjunction_of_true_cannot_be_zero_dags, pub_aig_manager);
					assert(mu != NULL);

					int size_of_changed_mu = computeSize(mu, pub_aig_manager);
					int size_of_new_element_added_to_cannot_be_one_set;

					if(refine_all_locations_in_cegar && !(apply_tsietin_encoding_on_benchmarks && destination <= number_of_tsietin_variables))
					{
						Aig_Obj_t* new_cannot_be_one_dag_at_destination;

						if(use_interpolants_in_cegar)
						{
							new_cannot_be_one_dag_at_destination = optimizeCannotBeOneDagThroughInterpolation(cofactor_one_of_mu, destination);	
						}
						else
						{
							new_cannot_be_one_dag_at_destination = cofactor_one_of_mu;
						}

						int size_of_extra_cannot_be_one_dag_at_destination = -1;
						int number_of_variables_dropped_in_generalization = -1;

						if(use_refinement_from_bottom_in_mu_based_scheme_with_optimizations_in_cegar)
						{
							if      (use_incremental_solving_for_generalization_in_mu_based_scheme_with_optimizations_in_cegar || use_interpolants_in_cegar)
							{
								Aig_Obj_t* extra_cannot_be_one_dag_at_destination;
								extra_cannot_be_one_dag_at_destination = obtainExtraCannotBeOneDagAtDestination(XValues, YValues, destination, number_of_variables_dropped_in_generalization);		
								assert(extra_cannot_be_one_dag_at_destination != NULL);				

								// weakening the extra cannot be one dag
								if(use_interpolants_in_cegar)
								{

									extra_cannot_be_one_dag_at_destination = optimizeCannotBeOneDagThroughInterpolation(extra_cannot_be_one_dag_at_destination, destination);
									assert(extra_cannot_be_one_dag_at_destination != NULL);	
								}

								#ifdef DEBUG_CEGAR
								string extra_cannot_be_one_dag_at_destination_file_name = benchmark_name_without_extension;
								extra_cannot_be_one_dag_at_destination_file_name += "_extra_cannot_be_one_dag_at_destination";

								cout << "\nextra_cannot_be_one_dag_at_destination computed\n";

								writeFormulaToFile(pub_aig_manager, extra_cannot_be_one_dag_at_destination, extra_cannot_be_one_dag_at_destination_file_name, ".v", cegar_iteration_number, destination);
								#endif

								size_of_extra_cannot_be_one_dag_at_destination = computeSize(extra_cannot_be_one_dag_at_destination, pub_aig_manager);

								new_cannot_be_one_dag_at_destination = createOr(new_cannot_be_one_dag_at_destination, extra_cannot_be_one_dag_at_destination, pub_aig_manager);
								assert(new_cannot_be_one_dag_at_destination != NULL);
							}						
						}

						// connecting to some output to avoid unwanted deletion
						Aig_Obj_t* new_cannot_be_one_dag_at_destination_CO = Aig_ObjCreateCo(pub_aig_manager, new_cannot_be_one_dag_at_destination); 
						assert(new_cannot_be_one_dag_at_destination_CO != NULL);
						intermediate_cos_created.insert(new_cannot_be_one_dag_at_destination_CO);

						// First allocate string and object to new_cannot_be_one_dag_at_destination
						string cannot_be_one_string_at_destination;
						Aig_Obj_t* cannot_be_one_object_at_destination;
						allocateStringAndObjectToCannotBeDag(1, new_cannot_be_one_dag_at_destination, cannot_be_one_string_at_destination, cannot_be_one_object_at_destination);

						#ifdef DEBUG_SKOLEM
						cout << "\nnew_cannot_be_one_dag_at_destination for x_" << destination << " is obtained\n";

						string new_cannot_be_one_dag_at_destination_file_name = benchmark_name_without_extension;
						new_cannot_be_one_dag_at_destination_file_name += "_new_cannot_be_one_dag_at_destination";
						writeFormulaToFile(pub_aig_manager, new_cannot_be_one_dag_at_destination, new_cannot_be_one_dag_at_destination_file_name, ".v", destination, cegar_iteration_number);
						show_cannot_be_string_to_cannot_be_object_map();
						show_cannot_be_object_to_cannot_be_dag_map();
						#endif
				
						// Insert new_cannot_be_one_object_at_destination into cannot_be_one_set at destination 
						cannot_be_one_set[destination].insert(cannot_be_one_object_at_destination);
				
						// Insert new_cannot_be_one_object_at_destination into Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX
						Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX.insert(make_pair(destination, cannot_be_one_object_at_destination));

						#ifdef DEBUG_CEGAR
						cout << "\ncannot_be_one_set for x_" << destination << " is modified\n";
						#endif

						// Conjoin ~new_cannot_be_one_object_at_destination to skolem_function at destination
						Aig_Obj_t* current_skolem_function_at_destination;
						current_skolem_function_at_destination = searchOneDimensionalMatrix(SkolemFunctions, number_of_vars_to_elim, destination);
						assert(current_skolem_function_at_destination != NULL);

						Aig_Obj_t* new_skolem_function_at_destination;				
						new_skolem_function_at_destination = createSkolemFunction_In_Mu_Based_Scheme_With_Optimizations(destination);
						// new_skolem_function_at_destination can be created from 
						// cannot_be_one_set[destination] and initial_cannot_be_zero_dags[destination]
						assert(new_skolem_function_at_destination != NULL);	

						int size_of_new_skolem_function_at_destination_unoptimized = computeSize(new_skolem_function_at_destination, pub_aig_manager);

						if(use_dontcare_optimization_in_cegar)
						// optimize the skolem_function
						{
							Aig_Obj_t* dontcare_part = createDontCarePart_In_Mu_Based_Scheme_With_Optimizations(destination);
							assert(dontcare_part != NULL);

							#ifdef DEBUG_SKOLEM
							writeFormulaToFile(pub_aig_manager, dontcare_part, "dontcare_part", ".v", destination, cegar_iteration_number);	
							writeFormulaToFile(pub_aig_manager, new_skolem_function_at_destination, "unoptimized_skolem_function", ".v", destination, cegar_iteration_number);	
							#endif

							new_skolem_function_at_destination = performDontCareOptimization(pub_aig_manager, new_skolem_function_at_destination, dontcare_part);
							assert(new_skolem_function_at_destination != NULL);
		
						}		
			
						if(new_skolem_function_at_destination != current_skolem_function_at_destination) // skolem function is changed
						{
							// connecting to some output to avoid unwanted deletion
							Aig_Obj_t* new_skolem_function_at_destination_CO = Aig_ObjCreateCo( pub_aig_manager, new_skolem_function_at_destination);
							assert(new_skolem_function_at_destination_CO != NULL);
							intermediate_cos_created.insert(new_skolem_function_at_destination_CO);

							// insert the new skolem function
							insertIntoOneDimensionalMatrix(SkolemFunctions, number_of_vars_to_elim, destination, new_skolem_function_at_destination, true);


							#ifdef DEBUG_CEGAR
							cout << "\nSkolem function for x_" << destination << " is modified\n";
							string skolem_function_file_name = benchmark_name_without_extension;
							skolem_function_file_name += "_skolem_function";
							writeFormulaToFile(pub_aig_manager, new_skolem_function_at_destination, skolem_function_file_name, ".v", destination, cegar_iteration_number);
							#endif
						}

						size_of_new_element_added_to_cannot_be_one_set = computeSize(new_cannot_be_one_dag_at_destination, pub_aig_manager);
						int size_of_new_skolem_function_at_destination = computeSize(new_skolem_function_at_destination, pub_aig_manager);

						#ifdef RECORD_KEEP
						if(size_of_extra_cannot_be_one_dag_at_destination == -1)
						{
							if(!mask_printing_cegar_details)
							{
								fprintf(record_fp, "\t(x@%d=1,%d,%d,%d,%d,%d,%d,-,-)", destination, size_of_new_element_added_to_cannot_be_one_set,  number_of_cannot_be_zero_elements_that_are_true, size_of_disjunction_of_true_cannot_be_zero_dags, size_of_changed_mu, size_of_new_skolem_function_at_destination_unoptimized, size_of_new_skolem_function_at_destination);
							}
						}
						else
						{
							if(!mask_printing_cegar_details)
							{
								fprintf(record_fp, "\t(x@%d=1,%d,%d,%d,%d,%d,%d,%d,%d)", destination, size_of_new_element_added_to_cannot_be_one_set,  number_of_cannot_be_zero_elements_that_are_true, size_of_disjunction_of_true_cannot_be_zero_dags, size_of_changed_mu, size_of_new_skolem_function_at_destination_unoptimized, size_of_new_skolem_function_at_destination, size_of_extra_cannot_be_one_dag_at_destination, number_of_variables_dropped_in_generalization);
							}
						}
						#endif
					}
					else
					{
						size_of_new_element_added_to_cannot_be_one_set = -1; //nothing is added to Cb1_k	
						#ifdef RECORD_KEEP
						if(!mask_printing_cegar_details)
						{
							fprintf(record_fp, "\t(x@%d=1,-,%d,%d,%d,-,-,-,-)", destination, number_of_cannot_be_zero_elements_that_are_true, size_of_disjunction_of_true_cannot_be_zero_dags, size_of_changed_mu);
						}
						#endif
					}


					#ifdef DEBUG_CEGAR
					mu_file_name = benchmark_name_without_extension;
					mu_file_name += "_mu";

					cout << "\nmu updated\n";

					writeFormulaToFile(pub_aig_manager, mu, mu_file_name, ".v", cegar_iteration_number, destination);
					#endif
				}
				else if(!refine_all_locations_in_cegar && evaluateMu(mu, XValues, YValues, destination, 0)) //evaluate mu with XValues' where 
				// XValues'[l] = 0 for l = destination and XValues'[l] = XValues[l] for l \neq destination
				{
					#ifdef DEBUG_SKOLEM
					cout << "\ncannot_be_zero_set[" << destination << "] == 0 && mu[x_" << destination << "-->0] == 1\n";
					#endif
					
					int number_of_cannot_be_zero_elements_that_are_true = -1;
					int size_of_disjunction_of_true_cannot_be_zero_dags = -1;
					
					// Let's obtain mu[x_destination --> 1]
					Aig_Obj_t* cofactor_one_of_mu;
					cofactor_one_of_mu = replaceVariableByConstant(mu, destination, 1);
					assert(cofactor_one_of_mu != NULL);

					// Let's obtain mu[x_destination --> 0]
					Aig_Obj_t* cofactor_zero_of_mu;
					cofactor_zero_of_mu = replaceVariableByConstant(mu, destination, 0);
					assert(cofactor_zero_of_mu != NULL);

					mu = createAnd(cofactor_one_of_mu, cofactor_zero_of_mu, pub_aig_manager);
					assert(mu != NULL);

					int size_of_changed_mu = computeSize(mu, pub_aig_manager);
					int size_of_new_element_added_to_cannot_be_one_set = -1; //nothing is added to Cb1_k				

					#ifdef RECORD_KEEP
					if(!mask_printing_cegar_details)
					{
						fprintf(record_fp, "\t(x@%d=1,-,-,-,%d,-,-,-,-)", destination, size_of_changed_mu);
					}
					#endif

					#ifdef DEBUG_CEGAR
					mu_file_name = benchmark_name_without_extension;
					mu_file_name += "_mu";

					cout << "\nmu updated\n";

					writeFormulaToFile(pub_aig_manager, mu, mu_file_name, ".v", cegar_iteration_number, destination);
					#endif
				}
				else // flipping x_destination makes mu zero
				{
					#ifdef DEBUG_SKOLEM
					cout << "\ncannot_be_zero_set[" << destination << "] == 0 && mu[x_" << destination << "-->0] == 0\n";
					#endif

					int number_of_cannot_be_zero_elements_that_are_true = -1;
					int size_of_disjunction_of_true_cannot_be_zero_dags = -1;
					int size_of_changed_mu = -1;

					// Let's obtain mu[x_destination --> 1]
					Aig_Obj_t* cofactor_one_of_mu;
					cofactor_one_of_mu = replaceVariableByConstant(mu, destination, 1);
					assert(cofactor_one_of_mu != NULL);

					Aig_Obj_t* new_cannot_be_one_dag_at_destination;

					if(use_interpolants_in_cegar)
					{
						new_cannot_be_one_dag_at_destination = optimizeCannotBeOneDagThroughInterpolation(cofactor_one_of_mu, destination);	
					}
					else
					{
						new_cannot_be_one_dag_at_destination = cofactor_one_of_mu;
					}

					int size_of_extra_cannot_be_one_dag_at_destination = -1;
					int number_of_variables_dropped_in_generalization = -1;

					if(use_refinement_from_bottom_in_mu_based_scheme_with_optimizations_in_cegar)
					{
						if(use_incremental_solving_for_generalization_in_mu_based_scheme_with_optimizations_in_cegar || use_interpolants_in_cegar)
						{
							Aig_Obj_t* extra_cannot_be_one_dag_at_destination;
							extra_cannot_be_one_dag_at_destination = obtainExtraCannotBeOneDagAtDestination(XValues, YValues, destination, number_of_variables_dropped_in_generalization);		
							assert(extra_cannot_be_one_dag_at_destination != NULL);				

							// weakening the extra cannot be one dag
							if(use_interpolants_in_cegar)
							{

								extra_cannot_be_one_dag_at_destination = optimizeCannotBeOneDagThroughInterpolation(extra_cannot_be_one_dag_at_destination, destination);
								assert(extra_cannot_be_one_dag_at_destination != NULL);	
							}

							#ifdef DEBUG_CEGAR
							string extra_cannot_be_one_dag_at_destination_file_name = benchmark_name_without_extension;
							extra_cannot_be_one_dag_at_destination_file_name += "_extra_cannot_be_one_dag_at_destination";

							cout << "\nextra_cannot_be_one_dag_at_destination computed\n";

							writeFormulaToFile(pub_aig_manager, extra_cannot_be_one_dag_at_destination, extra_cannot_be_one_dag_at_destination_file_name, ".v", cegar_iteration_number, destination);
							#endif

							size_of_extra_cannot_be_one_dag_at_destination = computeSize(extra_cannot_be_one_dag_at_destination, pub_aig_manager);

							new_cannot_be_one_dag_at_destination = createOr(new_cannot_be_one_dag_at_destination, extra_cannot_be_one_dag_at_destination, pub_aig_manager);
							assert(new_cannot_be_one_dag_at_destination != NULL);
						}						
					}

					// connecting to some output to avoid unwanted deletion
					Aig_Obj_t* new_cannot_be_one_dag_at_destination_CO = Aig_ObjCreateCo(pub_aig_manager, new_cannot_be_one_dag_at_destination); 
					assert(new_cannot_be_one_dag_at_destination_CO != NULL);
					intermediate_cos_created.insert(new_cannot_be_one_dag_at_destination_CO);
					

					// First allocate string and object to new_cannot_be_one_dag_at_destination
					string cannot_be_one_string_at_destination;
					Aig_Obj_t* cannot_be_one_object_at_destination;
					allocateStringAndObjectToCannotBeDag(1, new_cannot_be_one_dag_at_destination, cannot_be_one_string_at_destination, cannot_be_one_object_at_destination);

					#ifdef DEBUG_SKOLEM
					cout << "\nnew_cannot_be_one_dag_at_destination for x_" << destination << " is obtained\n";

					string new_cannot_be_one_dag_at_destination_file_name = benchmark_name_without_extension;
					new_cannot_be_one_dag_at_destination_file_name += "_new_cannot_be_one_dag_at_destination";
					writeFormulaToFile(pub_aig_manager, new_cannot_be_one_dag_at_destination, new_cannot_be_one_dag_at_destination_file_name, ".v", destination, cegar_iteration_number);
					show_cannot_be_string_to_cannot_be_object_map();
					show_cannot_be_object_to_cannot_be_dag_map();
					#endif
				
					// Insert new_cannot_be_one_object_at_destination into cannot_be_one_set at destination 
					cannot_be_one_set[destination].insert(cannot_be_one_object_at_destination);
				
					// Insert new_cannot_be_one_object_at_destination into Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX
					Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX.insert(make_pair(destination, cannot_be_one_object_at_destination));

					#ifdef DEBUG_CEGAR
					cout << "\ncannot_be_one_set for x_" << destination << " is modified\n";
					#endif

					// Conjoin ~new_cannot_be_one_object_at_destination to skolem_function at destination
					Aig_Obj_t* current_skolem_function_at_destination;
					current_skolem_function_at_destination = searchOneDimensionalMatrix(SkolemFunctions, number_of_vars_to_elim, destination);
					assert(current_skolem_function_at_destination != NULL);

					Aig_Obj_t* new_skolem_function_at_destination;				
					new_skolem_function_at_destination = createSkolemFunction_In_Mu_Based_Scheme_With_Optimizations(destination);
					// new_skolem_function_at_destination can be created from 
					// cannot_be_one_set[destination] and initial_cannot_be_zero_dags[destination]
					assert(new_skolem_function_at_destination != NULL);	

					int size_of_new_skolem_function_at_destination_unoptimized = computeSize(new_skolem_function_at_destination, pub_aig_manager);

					if(use_dontcare_optimization_in_cegar)
					// optimize the skolem_function
					{
						Aig_Obj_t* dontcare_part = createDontCarePart_In_Mu_Based_Scheme_With_Optimizations(destination);
						assert(dontcare_part != NULL);

						#ifdef DEBUG_SKOLEM
						writeFormulaToFile(pub_aig_manager, dontcare_part, "dontcare_part", ".v", destination, cegar_iteration_number);	
						writeFormulaToFile(pub_aig_manager, new_skolem_function_at_destination, "unoptimized_skolem_function", ".v", destination, cegar_iteration_number);	
						#endif

						new_skolem_function_at_destination = performDontCareOptimization(pub_aig_manager, new_skolem_function_at_destination, dontcare_part);
						assert(new_skolem_function_at_destination != NULL);
		
					}		
			
					if(new_skolem_function_at_destination != current_skolem_function_at_destination) // skolem function is changed
					{
						// connecting to some output to avoid unwanted deletion
						Aig_Obj_t* new_skolem_function_at_destination_CO = Aig_ObjCreateCo( pub_aig_manager, new_skolem_function_at_destination);
						assert(new_skolem_function_at_destination_CO != NULL);
						intermediate_cos_created.insert(new_skolem_function_at_destination_CO);

						// insert the new skolem function
						insertIntoOneDimensionalMatrix(SkolemFunctions, number_of_vars_to_elim, destination, new_skolem_function_at_destination, true);


						#ifdef DEBUG_CEGAR
						cout << "\nSkolem function for x_" << destination << " is modified\n";
						string skolem_function_file_name = benchmark_name_without_extension;
						skolem_function_file_name += "_skolem_function";
						writeFormulaToFile(pub_aig_manager, new_skolem_function_at_destination, skolem_function_file_name, ".v", destination, cegar_iteration_number);
						#endif
					}

					int size_of_new_element_added_to_cannot_be_one_set = computeSize(new_cannot_be_one_dag_at_destination, pub_aig_manager);
					int size_of_new_skolem_function_at_destination = computeSize(new_skolem_function_at_destination, pub_aig_manager);

					#ifdef RECORD_KEEP
					if(size_of_extra_cannot_be_one_dag_at_destination == -1)
					{
						if(!mask_printing_cegar_details)
						{
							fprintf(record_fp, "\t(x@%d=1,%d,-,-,-,%d,%d,-,-)", destination, size_of_new_element_added_to_cannot_be_one_set,  size_of_new_skolem_function_at_destination_unoptimized, size_of_new_skolem_function_at_destination);
						}
					}
					else
					{
						if(!mask_printing_cegar_details)
						{
							fprintf(record_fp, "\t(x@%d=1,%d,-,-,-,%d,%d,%d,%d)", destination, size_of_new_element_added_to_cannot_be_one_set,  size_of_new_skolem_function_at_destination_unoptimized, size_of_new_skolem_function_at_destination, size_of_extra_cannot_be_one_dag_at_destination, number_of_variables_dropped_in_generalization);
						}
					}
					#endif

					break;					
				} // flipping x_destination makes mu zero ends here
			}// if(x_destination == 1) ends here
			else // if(x_destination == 0)
			{
				#ifdef DEBUG_SKOLEM
				cout << "\nx_" << destination << " == 0\n";
				#endif

				// assert (mu[x_destination --> 0])
				if(!refine_all_locations_in_cegar && evaluateMu(mu, XValues, YValues, destination, 1)) //evaluate mu with XValues' where 
				// XValues'[l] = 1 for l = destination and XValues'[l] = XValues[l] for l \neq destination
				{
					#ifdef DEBUG_SKOLEM
					cout << "\nmu[x_" << destination << "-->1] == 1\n";
					#endif
					
					int number_of_cannot_be_one_elements_that_are_true = -1;
					int size_of_disjunction_of_true_cannot_be_one_dags = -1;
					
					// Let's obtain mu[x_destination --> 1]
					Aig_Obj_t* cofactor_one_of_mu;
					cofactor_one_of_mu = replaceVariableByConstant(mu, destination, 1);
					assert(cofactor_one_of_mu != NULL);

					// Let's obtain mu[x_destination --> 0]
					Aig_Obj_t* cofactor_zero_of_mu;
					cofactor_zero_of_mu = replaceVariableByConstant(mu, destination, 0);
					assert(cofactor_zero_of_mu != NULL);

					mu = createAnd(cofactor_one_of_mu, cofactor_zero_of_mu, pub_aig_manager);
					assert(mu != NULL);

					int size_of_changed_mu = computeSize(mu, pub_aig_manager);
					int size_of_new_element_added_to_cannot_be_zero_set = -1; //nothing is added to Cb0_k				

					#ifdef RECORD_KEEP
					if(!mask_printing_cegar_details)
					{
						fprintf(record_fp, "\t(x@%d=0,-,-,-,%d,-,-,-,-)", destination, size_of_changed_mu);
					}
					#endif

					#ifdef DEBUG_CEGAR
					mu_file_name = benchmark_name_without_extension;
					mu_file_name += "_mu";

					cout << "\nmu updated\n";

					writeFormulaToFile(pub_aig_manager, mu, mu_file_name, ".v", cegar_iteration_number, destination);
					#endif
				}
				else
				{
					assert(cannot_be_one_set_values[destination] == 1); // Cb1_destination is true

					#ifdef DEBUG_SKOLEM
					cout << "\ncannot_be_one_set[" << destination << "] == 1\n";
					#endif

					// Let's obtain mu[x_destination --> 0]
					Aig_Obj_t* cofactor_zero_of_mu;
					cofactor_zero_of_mu = replaceVariableByConstant(mu, destination, 0);
					assert(cofactor_zero_of_mu != NULL);
					
					int number_of_cannot_be_one_elements_that_are_true;
					Aig_Obj_t* disjunction_of_true_cannot_be_one_dags = obtain_disjunction_of_true_cannot_be_one_dags(destination, cannot_be_object_to_value_map, cofactor_zero_of_mu, number_of_cannot_be_one_elements_that_are_true);
					assert(disjunction_of_true_cannot_be_one_dags != NULL);
					int size_of_disjunction_of_true_cannot_be_one_dags = computeSize(disjunction_of_true_cannot_be_one_dags, pub_aig_manager);

					mu = createAnd(cofactor_zero_of_mu, disjunction_of_true_cannot_be_one_dags, pub_aig_manager);
					assert(mu != NULL);

					int size_of_changed_mu = computeSize(mu, pub_aig_manager);
					int size_of_new_element_added_to_cannot_be_zero_set;

					if(refine_all_locations_in_cegar && accumulate_formulae_in_cbzero_in_cegar && !(apply_tsietin_encoding_on_benchmarks && destination <= number_of_tsietin_variables) )			
					{
						Aig_Obj_t* new_cannot_be_zero_dag_at_destination;
						new_cannot_be_zero_dag_at_destination = cofactor_zero_of_mu;
						assert(new_cannot_be_zero_dag_at_destination != NULL);
						// connecting to some output to avoid unwanted deletion
						Aig_Obj_t* new_cannot_be_zero_dag_at_destination_CO = Aig_ObjCreateCo(pub_aig_manager, new_cannot_be_zero_dag_at_destination); 
						assert(new_cannot_be_zero_dag_at_destination_CO != NULL);
						intermediate_cos_created.insert(new_cannot_be_zero_dag_at_destination_CO);

						// First allocate string and object to new_cannot_be_zero_dag_at_destination
						string cannot_be_zero_string_at_destination;
						Aig_Obj_t* cannot_be_zero_object_at_destination;
						allocateStringAndObjectToCannotBeDag(1, new_cannot_be_zero_dag_at_destination, cannot_be_zero_string_at_destination, cannot_be_zero_object_at_destination);

						#ifdef DEBUG_SKOLEM
						cout << "\nnew_cannot_be_zero_dag_at_destination for x_" << destination << " is obtained\n";

						string new_cannot_be_zero_dag_at_destination_file_name = benchmark_name_without_extension;
						new_cannot_be_zero_dag_at_destination_file_name += "_new_cannot_be_zero_dag_at_destination";
						writeFormulaToFile(pub_aig_manager, new_cannot_be_zero_dag_at_destination, new_cannot_be_zero_dag_at_destination_file_name, ".v", destination, cegar_iteration_number);
						show_cannot_be_string_to_cannot_be_object_map();
						show_cannot_be_object_to_cannot_be_dag_map();
						#endif
				
						// Insert new_cannot_be_zero_object_at_destination into cannot_be_zero_set at destination 
						cannot_be_zero_set[destination].insert(cannot_be_zero_object_at_destination);
				
						// Insert new_cannot_be_zero_object_at_destination into Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX
						Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX.insert(make_pair(destination, cannot_be_zero_object_at_destination));

						#ifdef DEBUG_CEGAR
						cout << "\ncannot_be_zero_set for x_" << destination << " is modified\n";
						#endif

						size_of_new_element_added_to_cannot_be_zero_set = computeSize(new_cannot_be_zero_dag_at_destination, pub_aig_manager);
						
						#ifdef RECORD_KEEP
						if(!mask_printing_cegar_details)
						{
							fprintf(record_fp, "\t(x@%d=0,%d,%d,%d,%d,-,-,-,-)", destination, size_of_new_element_added_to_cannot_be_zero_set, number_of_cannot_be_one_elements_that_are_true, size_of_disjunction_of_true_cannot_be_one_dags, size_of_changed_mu);
						}
						#endif
					}
					else
					{
						size_of_new_element_added_to_cannot_be_zero_set = -1; //nothing is added to Cb0_k				

						#ifdef RECORD_KEEP
						if(!mask_printing_cegar_details)
						{
							fprintf(record_fp, "\t(x@%d=0,-,%d,%d,%d,-,-,-,-)", destination, number_of_cannot_be_one_elements_that_are_true, size_of_disjunction_of_true_cannot_be_one_dags, size_of_changed_mu);
						}
						#endif
					}

					#ifdef DEBUG_CEGAR
					mu_file_name = benchmark_name_without_extension;
					mu_file_name += "_mu";

					cout << "\nmu updated\n";

					writeFormulaToFile(pub_aig_manager, mu, mu_file_name, ".v", cegar_iteration_number, destination);
					#endif	
				}// else of mu with XValues' is 1	
			
			}// if(x_destination == 0) ends here
						
		}// mu has x_destination in support ends here

		destination = destination + 1;

	}// while(destination <= number_of_vars_to_elim) ends here

	assert(destination <= correction_index);

	#ifdef RECORD_KEEP
	fclose(record_fp);
	#endif

}



bool AIGBasedSkolem::evaluateMu(Aig_Obj_t* mu, map<int, int> &XValues, map<string, int> &YValues, int destination, int value_at_destination)
{
	#ifdef DETAILED_RECORD_KEEP
	unsigned long long int step_ms;
	struct timeval step_start_ms, step_finish_ms;
	gettimeofday (&step_start_ms, NULL); 	
	#endif 


	assert(mu != NULL);

	map<string, bool> variable_to_value_map;
	for(map<string, int>::iterator yvalues_it = YValues.begin(); yvalues_it != YValues.end(); yvalues_it++)
	{
		bool bool_value;
		if(yvalues_it->second == 1)
		{
			bool_value = true;
		}
		else
		{
			assert(yvalues_it->second == 0);
			bool_value = false;
		}

		variable_to_value_map.insert(make_pair(yvalues_it->first, bool_value));
		#ifdef DEBUG_SKOLEM
			cout << endl << yvalues_it->first << " --> " << bool_value << " inserted into variable_to_value_map\n";
		#endif
	}
	
	for(int var_to_elim_index = number_of_vars_to_elim; var_to_elim_index > destination; var_to_elim_index--)
	{
		string var_to_elim = searchVarIndexToVarNameMap(var_index_to_var_name_map, var_to_elim_index);
		
		int value = XValues[var_to_elim_index];
		bool bool_value;
		if(value == 1)
		{
			bool_value = true;
		}
		else
		{
			assert(value == 0);
			bool_value = false;
		}

		variable_to_value_map.insert(make_pair(var_to_elim, bool_value));	

		#ifdef DEBUG_SKOLEM
			cout << endl << var_to_elim << " --> " << bool_value << " inserted into variable_to_value_map\n";
		#endif		
	}

	string var_to_elim_at_destination = searchVarIndexToVarNameMap(var_index_to_var_name_map, destination);
		
	bool bool_value_at_destination;
	if(value_at_destination == 1)
	{
		bool_value_at_destination = true;
	}
	else
	{
		assert(value_at_destination == 0);
		bool_value_at_destination = false;
	}

	variable_to_value_map.insert(make_pair(var_to_elim_at_destination, bool_value_at_destination));	

	#ifdef DEBUG_SKOLEM
		cout << endl << var_to_elim_at_destination << " --> " << bool_value_at_destination << " inserted into variable_to_value_map\n";
	#endif

	
	bool result_value = evaluateFormulaOfCi(mu,  variable_to_value_map);
	
	#ifdef DETAILED_RECORD_KEEP
	gettimeofday (&step_finish_ms, NULL);
   	step_ms = step_finish_ms.tv_sec * 1000 + step_finish_ms.tv_usec / 1000;
   	step_ms -= step_start_ms.tv_sec * 1000 + step_start_ms.tv_usec / 1000;

	total_time_in_mu_evaluation_in_cegar = total_time_in_mu_evaluation_in_cegar + step_ms;
	#endif

	#ifdef DEBUG_SKOLEM
		cout << endl << "result_value = " << result_value << endl;
		cout << "Time to evaluate mu with size " << computeSize(mu, pub_aig_manager) << " is: " << step_ms << "milli seconds\n";
	#endif

	return result_value;

}



Aig_Obj_t* AIGBasedSkolem::createSkolemFunction_In_Mu_Based_Scheme_With_Optimizations(int destination)
{
	map<int, set<Aig_Obj_t*> >::iterator cannot_be_one_set_it = cannot_be_one_set.find(destination);
	assert(cannot_be_one_set_it != cannot_be_one_set.end());

	set<Aig_Obj_t*> cannot_be_one_set_objects = cannot_be_one_set_it->second;
	// let's find the corresponding dags

	Aig_Obj_t* skolem_function_part1;
	set<Aig_Obj_t*> skolem_function_part1_components;

	for(set<Aig_Obj_t*>::iterator cannot_be_one_set_objects_it = cannot_be_one_set_objects.begin(); cannot_be_one_set_objects_it != cannot_be_one_set_objects.end();  cannot_be_one_set_objects_it++)
	{
		Aig_Obj_t* cannot_be_object = *cannot_be_one_set_objects_it;
		assert(cannot_be_object != NULL);

		map<Aig_Obj_t*, Aig_Obj_t*>::iterator cannot_be_object_to_cannot_be_dag_map_it = cannot_be_object_to_cannot_be_dag_map.find(cannot_be_object);
		assert(cannot_be_object_to_cannot_be_dag_map_it != cannot_be_object_to_cannot_be_dag_map.end());
				
		Aig_Obj_t* cannot_be_dag = cannot_be_object_to_cannot_be_dag_map_it->second;
		assert(cannot_be_dag != NULL);
		
		skolem_function_part1_components.insert(cannot_be_dag);		
	}

	if(skolem_function_part1_components.empty()) // no condition under which it can't be 1
	// i.e. it can be 1 always
	{
		skolem_function_part1 = createTrue(pub_aig_manager);
	}
	else
	{
		skolem_function_part1 = createOr(skolem_function_part1_components, pub_aig_manager);
		skolem_function_part1 = createNot(skolem_function_part1, pub_aig_manager);
	}
	assert(skolem_function_part1 != NULL);
	
	map<int, Aig_Obj_t*>::iterator initial_cannot_be_zero_dags_it = initial_cannot_be_zero_dags.find(destination);
	assert(initial_cannot_be_zero_dags_it != initial_cannot_be_zero_dags.end());
	Aig_Obj_t* skolem_function_part2 = initial_cannot_be_zero_dags_it->second;
	
	
	Aig_Obj_t* skolem_function;
	skolem_function = createOr(skolem_function_part2, skolem_function_part1, pub_aig_manager);
	assert(skolem_function != NULL);	

	return skolem_function;
}



Aig_Obj_t* AIGBasedSkolem::optimizeCannotBeOneDagThroughInterpolation(Aig_Obj_t* original_cannot_be_one_dag, int destination)
{
	#ifdef DEBUG_SKOLEM
	cout << "\noptimizing cannot-be-1 dag through interpolation\n";
	#endif
	
	Aig_Obj_t* optimized_cannot_be_one_dag;

	unsigned long long int interpolate_ms;
	struct timeval interpolate_start_ms, interpolate_finish_ms;
	gettimeofday (&interpolate_start_ms, NULL); 

	Aig_Obj_t* interpolant;// interpolate(e_k, \phi)
	interpolant = Interpolate(pub_aig_manager, original_cannot_be_one_dag, conjunction_of_factors);
	if(interpolant != NULL)
	{
		#ifdef DEBUG_SKOLEM
		cout << "\ne_k and phi is unsat; interpolant(e_k, phi) returned\n";
		#endif

		optimized_cannot_be_one_dag = interpolant;
	}
	else // e_k \wedge \phi is not unsat
	{
		#ifdef DEBUG_SKOLEM
		cout << "\ne_k and phi is sat\n";
		#endif

		// obtain AIG for x_destination
		string var_to_elim_at_destination = searchVarIndexToVarNameMap(var_index_to_var_name_map, destination);

		map<string, Aig_Obj_t*>::iterator Ci_to_eliminate_name_to_Ci_to_eliminate_object_map_it = Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.find(var_to_elim_at_destination);
		assert(Ci_to_eliminate_name_to_Ci_to_eliminate_object_map_it != Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.end());			
		Aig_Obj_t* var_to_elim_at_destination_obj = Ci_to_eliminate_name_to_Ci_to_eliminate_object_map_it->second;
		assert(var_to_elim_at_destination_obj != NULL);

		Aig_Obj_t* conjoined_dag = createAnd(conjunction_of_factors, var_to_elim_at_destination_obj, pub_aig_manager);			
		assert(conjoined_dag != NULL); // \phi \wedge x_k is created

		// interpolate(e_k, \phi \wedge x_k)
		interpolant = Interpolate(pub_aig_manager, original_cannot_be_one_dag, conjoined_dag);	
		assert(interpolant != NULL);

		#ifdef DEBUG_SKOLEM
		cout << "\ninterpolant(e_k, phi and x_k) returned\n";
		#endif

		optimized_cannot_be_one_dag = interpolant;
	}
	
	

	gettimeofday (&interpolate_finish_ms, NULL);
   	interpolate_ms = interpolate_finish_ms.tv_sec * 1000 + interpolate_finish_ms.tv_usec / 1000;
   	interpolate_ms -= interpolate_start_ms.tv_sec * 1000 + interpolate_start_ms.tv_usec / 1000;
	cout << "\ncomputeSkolemFunctionAsInterpolant finished in " << interpolate_ms << " milliseconds\n";
	total_time_in_interpolant_computation_in_cegar = total_time_in_interpolant_computation_in_cegar + interpolate_ms;

	return optimized_cannot_be_one_dag;	
}



Aig_Obj_t* AIGBasedSkolem::createDontCarePart_In_Mu_Based_Scheme_With_Optimizations(int destination)
{
	map<int, set<Aig_Obj_t*> >::iterator cannot_be_one_set_it = cannot_be_one_set.find(destination);
	assert(cannot_be_one_set_it != cannot_be_one_set.end());

	set<Aig_Obj_t*> cannot_be_one_set_objects = cannot_be_one_set_it->second;
	// let's find the corresponding dags

	Aig_Obj_t* dont_care_part1;
	set<Aig_Obj_t*> dont_care_part1_components;

	for(set<Aig_Obj_t*>::iterator cannot_be_one_set_objects_it = cannot_be_one_set_objects.begin(); cannot_be_one_set_objects_it != cannot_be_one_set_objects.end();  cannot_be_one_set_objects_it++)
	{
		Aig_Obj_t* cannot_be_object = *cannot_be_one_set_objects_it;
		assert(cannot_be_object != NULL);

		map<Aig_Obj_t*, Aig_Obj_t*>::iterator cannot_be_object_to_cannot_be_dag_map_it = cannot_be_object_to_cannot_be_dag_map.find(cannot_be_object);
		assert(cannot_be_object_to_cannot_be_dag_map_it != cannot_be_object_to_cannot_be_dag_map.end());
				
		Aig_Obj_t* cannot_be_dag = cannot_be_object_to_cannot_be_dag_map_it->second;
		assert(cannot_be_dag != NULL);
		
		dont_care_part1_components.insert(cannot_be_dag);		
	}

	if(dont_care_part1_components.empty()) 
	{
		dont_care_part1 = createFalse(pub_aig_manager);
	}
	else
	{
		dont_care_part1 = createOr(dont_care_part1_components, pub_aig_manager);
	}
	assert(dont_care_part1 != NULL);
	
	
	map<int, set<Aig_Obj_t*> >::iterator cannot_be_zero_set_it = cannot_be_zero_set.find(destination);
	assert(cannot_be_zero_set_it != cannot_be_zero_set.end());

	set<Aig_Obj_t*> cannot_be_zero_set_objects = cannot_be_zero_set_it->second;
	// let's find the corresponding dags

	Aig_Obj_t* dont_care_part2;
	set<Aig_Obj_t*> dont_care_part2_components;

	for(set<Aig_Obj_t*>::iterator cannot_be_zero_set_objects_it = cannot_be_zero_set_objects.begin(); cannot_be_zero_set_objects_it != cannot_be_zero_set_objects.end();  cannot_be_zero_set_objects_it++)
	{
		Aig_Obj_t* cannot_be_object = *cannot_be_zero_set_objects_it;
		assert(cannot_be_object != NULL);

		map<Aig_Obj_t*, Aig_Obj_t*>::iterator cannot_be_object_to_cannot_be_dag_map_it = cannot_be_object_to_cannot_be_dag_map.find(cannot_be_object);
		assert(cannot_be_object_to_cannot_be_dag_map_it != cannot_be_object_to_cannot_be_dag_map.end());
				
		Aig_Obj_t* cannot_be_dag = cannot_be_object_to_cannot_be_dag_map_it->second;
		assert(cannot_be_dag != NULL);
		
		dont_care_part2_components.insert(cannot_be_dag);		
	}

	if(dont_care_part2_components.empty()) 
	{
		dont_care_part2 = createFalse(pub_aig_manager);
	}
	else
	{
		dont_care_part2 = createOr(dont_care_part2_components, pub_aig_manager);
	}
	assert(dont_care_part2 != NULL);

	
	Aig_Obj_t* dont_care_part;
	dont_care_part = createAnd(dont_care_part1, dont_care_part2, pub_aig_manager);
	assert(dont_care_part != NULL);	

	return dont_care_part;
}


Aig_Obj_t* AIGBasedSkolem::obtainExtraCannotBeOneDagAtDestination(map<int, int> &XValues, map<string, int> &YValues, int destination, int &number_of_variables_dropped_in_generalization)
{
	set<string> variables_avoided;		

	unsigned long long int generalize_ms;
	struct timeval generalize_start_ms, generalize_finish_ms;
	gettimeofday (&generalize_start_ms, NULL);

	if(use_incremental_solving_for_generalization_in_mu_based_scheme_with_optimizations_in_cegar)
	{
		obtainGeneralizedModelByIncrementalSolvingInObtainingExtraCannotBeOneDagAtDestination(XValues, YValues, destination, variables_avoided);
	}

	gettimeofday (&generalize_finish_ms, NULL);
   	generalize_ms = generalize_finish_ms.tv_sec * 1000 + generalize_finish_ms.tv_usec / 1000;
   	generalize_ms -= generalize_start_ms.tv_sec * 1000 + generalize_start_ms.tv_usec / 1000;
	#ifdef DEBUG_SKOLEM
	cout << "\nGeneralization finished in " << generalize_ms << " milliseconds\n";
	#endif
	total_time_in_generalization_in_mu_based_scheme_with_optimizations_in_cegar = total_time_in_generalization_in_mu_based_scheme_with_optimizations_in_cegar + generalize_ms;

	number_of_variables_dropped_in_generalization = variables_avoided.size();

	// Return the conjunction of x's below destination and y's as per their values
	set<Aig_Obj_t*> extra_cannot_be_one_dag_components;

	// all y variables keep their values in the existing model
	for(map<string, int>::iterator yvalues_it = YValues.begin(); yvalues_it != YValues.end(); yvalues_it++)
	{
		string variable_name = yvalues_it->first;
		int variable_value = yvalues_it->second;

		if(variables_avoided.find(variable_name) != variables_avoided.end())
		{
			continue;
		}

		Aig_Obj_t* variable_object;
		map<string, Aig_Obj_t*>::iterator Ci_name_to_Ci_object_map_it = Ci_name_to_Ci_object_map.find(variable_name);
		assert(Ci_name_to_Ci_object_map_it != Ci_name_to_Ci_object_map.end());

		variable_object = Ci_name_to_Ci_object_map_it->second;

		if(variable_value == 1) // variable_value is true
		{
			extra_cannot_be_one_dag_components.insert(variable_object);
		}
		else if(variable_value == 0) // variable_value is false
		{
			extra_cannot_be_one_dag_components.insert(createNot(variable_object, pub_aig_manager));
		}
	}

	// assert that all x_new variables upto destination keep their values in the existing model
	for(int var_to_elim_index = number_of_vars_to_elim; var_to_elim_index >= 1; var_to_elim_index--)
	{
		if(var_to_elim_index <= destination)
		{
			break;
		}
		else
		{
			string variable_name = searchVarIndexToVarNameMap(var_index_to_var_name_map, var_to_elim_index);

			if(variables_avoided.find(variable_name) != variables_avoided.end())
			{
				continue;
			}

			Aig_Obj_t* variable_object;
			map<string, Aig_Obj_t*>::iterator Ci_name_to_Ci_object_map_it = Ci_name_to_Ci_object_map.find(variable_name);
			assert(Ci_name_to_Ci_object_map_it != Ci_name_to_Ci_object_map.end());
			variable_object = Ci_name_to_Ci_object_map_it->second;

			map<int, int>::iterator XValues_it = XValues.find(var_to_elim_index);
			assert(XValues_it != XValues.end());

			if(XValues_it->second == 1) // variable_value is true
			{
				extra_cannot_be_one_dag_components.insert(variable_object);
			}
			else if(XValues_it->second == 0) // variable_value is false
			{
				extra_cannot_be_one_dag_components.insert(createNot(variable_object, pub_aig_manager));
			}
		}
	}

	Aig_Obj_t* extra_cannot_be_one_dag;
	if(extra_cannot_be_one_dag_components.size() == 0)
	{
		extra_cannot_be_one_dag = createTrue(pub_aig_manager);	
	}
	else
	{
		extra_cannot_be_one_dag = createAnd(extra_cannot_be_one_dag_components, pub_aig_manager);
	}
	assert(extra_cannot_be_one_dag != NULL);

	return extra_cannot_be_one_dag;
}


void AIGBasedSkolem::obtainGeneralizedModelByIncrementalSolvingInObtainingExtraCannotBeOneDagAtDestination(map<int, int> &XValues, map<string, int> &YValues, int destination, set<string> &variables_avoided)
{
	map<string, Aig_Obj_t*> positive_objects;
	map<string, Aig_Obj_t*> negative_objects;

	set<string> variables_to_consider;

	vector<Aig_Obj_t*> positive_assumptions;
	vector<Aig_Obj_t*> negative_assumptions;

	Aig_Obj_t* increment;

	bool result_of_generalization_check;
	map<string, int> Model_of_Generalizationcheck;

	unsigned long long int cnf_time;
	int formula_size;
	unsigned long long int simplification_time;
	
	for(map<string, int>::iterator yvalues_it = YValues.begin(); yvalues_it != YValues.end(); yvalues_it++)
	{
		string variable_name = yvalues_it->first;
		int variable_value = yvalues_it->second;

		Aig_Obj_t* variable_object;
		map<string, Aig_Obj_t*>::iterator Ci_name_to_Ci_object_map_it = Ci_name_to_Ci_object_map.find(variable_name);
		assert(Ci_name_to_Ci_object_map_it != Ci_name_to_Ci_object_map.end());

		variable_object = Ci_name_to_Ci_object_map_it->second;

		if(variable_value == 1) // variable_value is true
		{
			positive_objects.insert(make_pair(variable_name, variable_object));
			positive_assumptions.push_back(variable_object);
		}
		else if(variable_value == 0) // variable_value is false
		{
			negative_objects.insert(make_pair(variable_name, variable_object));
			negative_assumptions.push_back(variable_object);
		}
		else
		{
			assert(false);
		}

		variables_to_consider.insert(variable_name);
	}

	for(int var_to_elim_index = number_of_vars_to_elim; var_to_elim_index >= 1; var_to_elim_index--)
	{
		if(var_to_elim_index <= destination)
		{
			break;
		}
		else
		{
			string variable_name = searchVarIndexToVarNameMap(var_index_to_var_name_map, var_to_elim_index);

			Aig_Obj_t* variable_object;
			map<string, Aig_Obj_t*>::iterator Ci_name_to_Ci_object_map_it = Ci_name_to_Ci_object_map.find(variable_name);
			assert(Ci_name_to_Ci_object_map_it != Ci_name_to_Ci_object_map.end());
			variable_object = Ci_name_to_Ci_object_map_it->second;

			map<int, int>::iterator XValues_it = XValues.find(var_to_elim_index);
			assert(XValues_it != XValues.end());

			if(XValues_it->second == 1) // variable_value is true
			{
				positive_objects.insert(make_pair(variable_name, variable_object));
				positive_assumptions.push_back(variable_object);
			}
			else if(XValues_it->second == 0) // variable_value is false
			{
				negative_objects.insert(make_pair(variable_name, variable_object));
				negative_assumptions.push_back(variable_object);
			}
			else
			{
				assert(false);
			}

			variables_to_consider.insert(variable_name);
		}
	}

	string variable_name_at_destination = searchVarIndexToVarNameMap(var_index_to_var_name_map, destination);

	Aig_Obj_t* variable_object_at_destination;
	map<string, Aig_Obj_t*>::iterator Ci_name_to_Ci_object_map_it = Ci_name_to_Ci_object_map.find(variable_name_at_destination);
	assert(Ci_name_to_Ci_object_map_it != Ci_name_to_Ci_object_map.end());
	variable_object_at_destination = Ci_name_to_Ci_object_map_it->second;
	positive_objects.insert(make_pair(variable_name_at_destination, variable_object_at_destination));
	positive_assumptions.push_back(variable_object_at_destination);

	if(!incremental_solver_for_generalization_check_initialized)
	{
		increment = conjunction_of_factors;
		incremental_solver_for_generalization_check_initialized = true;	
	}
	else
	{
		increment = createTrue(pub_aig_manager);
	}
	assert(increment != NULL);

	result_of_generalization_check = isExactnessCheckSatisfiable(pub_aig_manager, increment, Model_of_Generalizationcheck, cnf_time, formula_size, simplification_time, positive_assumptions, negative_assumptions, pSat_for_generalization_check, IncrementalLabelTableForGeneralizationCheck, IncrementalLabelCountForGeneralizationCheck, Ci_name_to_Ci_label_mapForGeneralizationCheck, Ci_label_to_Ci_name_mapForGeneralizationCheck);

	assert(!result_of_generalization_check); //x_destination = 1 and variables below as per model should give unsat
	
	for(set<string>::iterator variables_to_consider_it = variables_to_consider.begin(); variables_to_consider_it != variables_to_consider.end();  variables_to_consider_it++)
	{
		string variable_to_consider = *variables_to_consider_it;		

		positive_assumptions.clear();
		negative_assumptions.clear();

		for(map<string, Aig_Obj_t*>::iterator positive_objects_it = positive_objects.begin(); positive_objects_it != positive_objects.end(); positive_objects_it++)
		{
			string positive_variable_name = positive_objects_it->first;
			Aig_Obj_t* positive_object_of_variable_name = positive_objects_it->second;

			if(positive_variable_name != variable_to_consider && variables_avoided.find(positive_variable_name) == variables_avoided.end())
			{
				positive_assumptions.push_back(positive_object_of_variable_name);	
			}
		}

		for(map<string, Aig_Obj_t*>::iterator negative_objects_it = negative_objects.begin(); negative_objects_it != negative_objects.end(); negative_objects_it++)
		{
			string negative_variable_name = negative_objects_it->first;
			Aig_Obj_t* negative_object_of_variable_name = negative_objects_it->second;

			if(negative_variable_name != variable_to_consider && variables_avoided.find(negative_variable_name) == variables_avoided.end())
			{
				negative_assumptions.push_back(negative_object_of_variable_name);	
			}
		}

		increment = createTrue(pub_aig_manager);	
		assert(increment != NULL);

		result_of_generalization_check = isExactnessCheckSatisfiable(pub_aig_manager, increment, Model_of_Generalizationcheck, cnf_time, formula_size, simplification_time, positive_assumptions, negative_assumptions, pSat_for_generalization_check, IncrementalLabelTableForGeneralizationCheck, IncrementalLabelCountForGeneralizationCheck, Ci_name_to_Ci_label_mapForGeneralizationCheck, Ci_label_to_Ci_name_mapForGeneralizationCheck);
		
		if(!result_of_generalization_check)
		// GeneralizationCheck unsat i.e. we can avoid variable_to_consider
		{
			#ifdef DEBUG_SKOLEM
			cout << "\nWe CAN avoid " << variable_to_consider << endl;			
			#endif

			variables_avoided.insert(variable_to_consider);
		}
		else // we cannot avoid variable_to_consider
		{
			#ifdef DEBUG_SKOLEM
			cout << "\nWe CANNOT avoid " << variable_to_consider << endl;			
			#endif
		}
	} // take each variable to consider		
} // function ends here



void AIGBasedSkolem::skolemFunctionGeneratorUsingBloqqer(set<Aig_Obj_t*> &Factors_new, list<string> &VariablesToEliminate)
{
	unsigned long long int total_ms;
	struct timeval total_start_ms, total_finish_ms;
	gettimeofday (&total_start_ms, NULL); 

	set<string> VariablesToEliminate_Set(VariablesToEliminate.begin(), VariablesToEliminate.end());
	set<Aig_Obj_t*> Factors;	
	if(drop_free_factors)
	{
		for(set<Aig_Obj_t*>::iterator factor_it = Factors_new.begin(); factor_it != Factors_new.end(); factor_it++)
		{
			Aig_Obj_t* factor = *factor_it;
			assert(factor != NULL);		

			set<string> support_factor;
			computeSupport(factor, support_factor, pub_aig_manager); 

			set<string> varstoelim_in_support_factor;
			set_intersection(support_factor.begin(), support_factor.end(), VariablesToEliminate_Set.begin(), VariablesToEliminate_Set.end(), inserter(varstoelim_in_support_factor, varstoelim_in_support_factor.begin()));

			if(!varstoelim_in_support_factor.empty())
			{
				Factors.insert(factor);
			}
		}//for
	}//if(drop_free_factors) ends here
	else
	{
		Factors = Factors_new;
	}
	

	
	conjunction_of_factors = createAnd(Factors, pub_aig_manager);
	
	string qdimacs_file = benchmark_name_without_extension;
	qdimacs_file += "_bloqqer.qdimacs";

	string model_file = benchmark_name_without_extension;
	model_file += "_bloqqer.model";

	unsigned long long int con_ms;
	struct timeval con_start_ms, con_finish_ms;
	gettimeofday (&con_start_ms, NULL); 	

	convertToQDimacs(conjunction_of_factors, VariablesToEliminate_Set, pub_aig_manager, qdimacs_file);

	gettimeofday (&con_finish_ms, NULL);
   	con_ms = con_finish_ms.tv_sec * 1000 + con_finish_ms.tv_usec / 1000;
   	con_ms -= con_start_ms.tv_sec * 1000 + con_start_ms.tv_usec / 1000;
	//cout << "\nConversion to QDIMACS in " << con_ms << " milliseconds\n";


	string plot_file;
	plot_file = logfile_prefix;
	plot_file += "skolem_function_generation_details_to_plot.txt";
	FILE* plot_fp = fopen(plot_file.c_str(), "a+");
	assert(plot_fp != NULL);
	fprintf(plot_fp, "\n%s\t%s\t%s\tbloqqer\t%llu\t", benchmark_type.c_str(), benchmark_name.c_str(), machine.c_str(), con_ms);


	bool satisfiable;

	if(skip_satisfiability_check_before_bloqqer)
	{
		satisfiable = true;
	}
	else
	{
		
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
				satisfiable = true;
			}
			else if(word == "UNSAT")
			{
				satisfiable = false;
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
				satisfiable = true;
			}
			else if(word == "UNSAT")
			{
				satisfiable = false;
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

	
	if(!satisfiable)
	{
		cout << "\nProblem is unsat! Bloqqer cannot solve this!\n";
		fprintf(plot_fp, "\tunsat\t0");
	}
	else if(!exit_after_generating_qdimacs)
	{
		cout << "\nProblem is sat! Bloqqer can solve this!\n";

		unsigned long long int step_ms;
		struct timeval step_start_ms, step_finish_ms;
		gettimeofday (&step_start_ms, NULL); 	
	
		string qrat_file;
		string qrat_tmp_file;
		string out_file;
		string log_file;

		qrat_file = qdimacs_file;
		qrat_file += ".qrat";

		qrat_tmp_file = qdimacs_file;
		qrat_tmp_file += ".qrat.tmp";

		out_file = qdimacs_file;
		out_file += ".out";

		log_file = qdimacs_file;
		log_file += ".log";

		string command = "bloqqer --qrat="; 
		command += qrat_tmp_file;
		command += " ";
		command += qdimacs_file;
		command += " ";
		command += out_file;
		cout << endl << command << endl;
		system(command.c_str());

		command = "./filter "; 
		command += qrat_tmp_file;
		command += " > ";
		command += qrat_file;
		cout << endl << command << endl;
		system(command.c_str());

		command = "qrat-trim "; 
		command += qdimacs_file;
		command += " ";
		command += qrat_file;
		command += " -S";
		command += " > ";
		command += log_file;
		cout << endl << command << endl;
		system(command.c_str());

		
		gettimeofday (&step_finish_ms, NULL);
   		step_ms = step_finish_ms.tv_sec * 1000 + step_finish_ms.tv_usec / 1000;
   		step_ms -= step_start_ms.tv_sec * 1000 + step_start_ms.tv_usec / 1000;
		cout << "\nbloqqer found Skolem functions in " << step_ms << " milliseconds\n";
		
		fprintf(plot_fp, "\tsat\t%llu", step_ms);

	}


	gettimeofday (&total_finish_ms, NULL);
   	total_ms = total_finish_ms.tv_sec * 1000 + total_finish_ms.tv_usec / 1000;
   	total_ms -= total_start_ms.tv_sec * 1000 + total_start_ms.tv_usec / 1000;
	//cout << "\nTotal time = " << total_ms << " milliseconds\n";

	fprintf(plot_fp, "\t%llu", total_ms);

	fclose(plot_fp);
}


Aig_Obj_t* AIGBasedSkolem::computeCofactorOneOrNegCofactorZero(int var_to_elim_index)
{
	// Let us compute ~cofactorzero_{var_to_elim_index}\vee cofactorone_{var_to_elim_index}
	// Suppose i = var_to_elim_index

	// ~cofactorzero_{i} is
	// ~(conjunction of co-factor-0_i_j's)
	// cofactorone_{i} is
	// (conjunction of co-factor-1_i_j's)
	set<Aig_Obj_t*> cofactor_zero_components; 
	set<Aig_Obj_t*> cofactor_one_components; 

	#ifdef DEBUG_SKOLEM
	cout << "\ncomputing components of cofactor_zero and cofactor_one\n";
	#endif

	#ifdef RECORD_KEEP
	int number_of_factors_containing_var_to_elim_index = FactorsWithVariable.size();
	#endif

	for(set<int>::iterator factor_it = FactorsWithVariable.begin(); factor_it != FactorsWithVariable.end(); factor_it++)
	{
		int factor_index = *factor_it;

		#ifdef DEBUG_SKOLEM
		cout << "\nfactor_index = " << factor_index << endl;
		#endif

		Aig_Obj_t* cofactor_1_i_j;
		cofactor_1_i_j = computeCofactorOne(var_to_elim_index, factor_index); 
		assert(cofactor_1_i_j != NULL);	

		Aig_Obj_t* cofactor_0_i_j;
		cofactor_0_i_j = computeCofactorZero(var_to_elim_index, factor_index); 
		assert(cofactor_0_i_j != NULL);	

		#ifdef DEBUG_SKOLEM
		writeFormulaToFile(pub_aig_manager, cofactor_1_i_j, "cofactor_1_i_j", ".v", var_to_elim_index, factor_index);		
		writeFormulaToFile(pub_aig_manager, cofactor_0_i_j, "cofactor_0_i_j", ".v", var_to_elim_index, factor_index);	
		#endif

		cofactor_one_components.insert(cofactor_1_i_j);			
		cofactor_zero_components.insert(cofactor_0_i_j);	

		FactorsAffectingSkolemFunction.push_back(factor_index);
						
	}// for each factor ends here

	Aig_Obj_t* cofactor_zero;				
	if(cofactor_zero_components.size() == 0) 
	{
		cofactor_zero = createTrue(pub_aig_manager); 
		assert(cofactor_zero != NULL);
	}
	else
	{
		cofactor_zero = createAnd(cofactor_zero_components, pub_aig_manager);
		assert(cofactor_zero != NULL);
	}

	Aig_Obj_t* cofactor_one;				
	if(cofactor_one_components.size() == 0) 
	{
		cofactor_one = createTrue(pub_aig_manager); 
		assert(cofactor_one != NULL);
	}
	else
	{
		cofactor_one = createAnd(cofactor_one_components, pub_aig_manager);
		assert(cofactor_one != NULL);
	}

	Aig_Obj_t* cofactor_one_or_neg_cofactor_zero;
	cofactor_one_or_neg_cofactor_zero = createOr(cofactor_one, createNot(cofactor_zero, pub_aig_manager), pub_aig_manager);
	assert(cofactor_one_or_neg_cofactor_zero != NULL);

	#ifdef DEBUG_SKOLEM
	writeFormulaToFile(pub_aig_manager, cofactor_one_or_neg_cofactor_zero, "cofactor_one_or_neg_cofactor_zero", ".v", var_to_elim_index, 0);				
	#endif

	#ifdef RECORD_KEEP
	NumberOfFactors = number_of_factors_containing_var_to_elim_index;
	#endif

	return cofactor_one_or_neg_cofactor_zero;
}



bool AIGBasedSkolem::checkIfSkolemFunctionAtGivenIndexIsExact_using_Mu_Based_Scheme_With_Optimizations_With_Unified_Code_And_Incremental_Solving(int correction_index, map<string, int> &Model_of_ExactnessCheck, map<int, Aig_Obj_t*> &Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX, map<int, Aig_Obj_t*> &Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX, list<string> &VariablesToEliminate)
{
	#ifdef RECORD_KEEP
		string record_file;
		record_file = logfile_prefix;
		record_file += "skolem_function_generation_details.txt";
		FILE* record_fp = fopen(record_file.c_str(), "a+");
		assert(record_fp != NULL);
	#endif

	if(cegar_iteration_number == 0)
	{
		#ifdef DEBUG_CEGAR
		cout << "\nCase with cegar_iteration_number == 0 \n";
		#endif

		Aig_Obj_t* epsilon_zero;

		// correction_index must be number_of_vars_to_elim
		assert(correction_index == number_of_vars_to_elim);

		// Create the dag for epsilon_zero:
		

		// dag for epsilon_zero is: 

		// F(x_1',...,x_n',Y) \wedge

		// (B_1 \vee ... \vee B_{n-1}) \wedge (B_1 = dag for bad_1) \wedge ... (B_{n-1} = dag for bad_{n-1}) \wedge

		// (x_2 = psi_2) \wedge ... \wedge (x_n = psi_n) \wedge 
		
		// (eta_1 = dag for eta_1) \wedge ... \wedge (eta_l = dag for eta_l) \wedge
		// (sigma_1 = dag for sigma_1) \wedge ... \wedge (sigma_s = dag for sigma_s) \wedge
		// we need to consider eta's and sigma's of all x_i's

		// Let's first create dag for 
		// (eta_1 = dag for eta_1) \wedge ... \wedge (eta_l = dag for eta_l) \wedge
		// (sigma_1 = dag for sigma_1) \wedge ... \wedge (sigma_s = dag for sigma_s)
		// in Cb_part

		Aig_Obj_t* Cb_part;
		set<Aig_Obj_t*> Cb_objects;

		for(map<int, set<Aig_Obj_t*> >::iterator cannot_be_one_set_it = cannot_be_one_set.begin(); cannot_be_one_set_it != cannot_be_one_set.end(); cannot_be_one_set_it++)
		{
			int var_to_elim_index = cannot_be_one_set_it->first;
			
			set<Aig_Obj_t*> cannot_be_one_set_objects = cannot_be_one_set_it->second;
			// let's find the corresponding dags

			for(set<Aig_Obj_t*>::iterator cannot_be_one_set_objects_it = cannot_be_one_set_objects.begin(); cannot_be_one_set_objects_it != cannot_be_one_set_objects.end();  cannot_be_one_set_objects_it++)
			{
				Aig_Obj_t* cannot_be_object = *cannot_be_one_set_objects_it;
				assert(cannot_be_object != NULL);

				map<Aig_Obj_t*, Aig_Obj_t*>::iterator cannot_be_object_to_cannot_be_dag_map_it = cannot_be_object_to_cannot_be_dag_map.find(cannot_be_object);
				assert(cannot_be_object_to_cannot_be_dag_map_it != cannot_be_object_to_cannot_be_dag_map.end());
				
				Aig_Obj_t* cannot_be_dag = cannot_be_object_to_cannot_be_dag_map_it->second;
				assert(cannot_be_dag != NULL);
			
				Aig_Obj_t* Cb_equivalence = createEquivalence(cannot_be_object, cannot_be_dag, pub_aig_manager);
				Cb_objects.insert(Cb_equivalence);
			}	
		}

		for(map<int, set<Aig_Obj_t*> >::iterator cannot_be_zero_set_it = cannot_be_zero_set.begin(); cannot_be_zero_set_it != cannot_be_zero_set.end(); cannot_be_zero_set_it++)
		{
			int var_to_elim_index = cannot_be_zero_set_it->first;
			
			set<Aig_Obj_t*> cannot_be_zero_set_objects = cannot_be_zero_set_it->second;
			// let's find the corresponding dags

			for(set<Aig_Obj_t*>::iterator cannot_be_zero_set_objects_it = cannot_be_zero_set_objects.begin(); cannot_be_zero_set_objects_it != cannot_be_zero_set_objects.end();  cannot_be_zero_set_objects_it++)
			{
				Aig_Obj_t* cannot_be_object = *cannot_be_zero_set_objects_it;
				assert(cannot_be_object != NULL);

				map<Aig_Obj_t*, Aig_Obj_t*>::iterator cannot_be_object_to_cannot_be_dag_map_it = cannot_be_object_to_cannot_be_dag_map.find(cannot_be_object);
				assert(cannot_be_object_to_cannot_be_dag_map_it != cannot_be_object_to_cannot_be_dag_map.end());
				
				Aig_Obj_t* cannot_be_dag = cannot_be_object_to_cannot_be_dag_map_it->second;
				assert(cannot_be_dag != NULL);
			
				Aig_Obj_t* Cb_equivalence = createEquivalence(cannot_be_object, cannot_be_dag, pub_aig_manager);
				Cb_objects.insert(Cb_equivalence);
			}	
		}

		assert(!Cb_objects.empty());
		Cb_part = createAnd(Cb_objects, pub_aig_manager);
		assert(Cb_part != NULL);
		// connect to some output to avoid unwanted deletion
		Aig_Obj_t* Cb_part_CO = Aig_ObjCreateCo(pub_aig_manager, Cb_part ); 
		assert(Cb_part_CO != NULL);
		intermediate_cos_created.insert(Cb_part_CO);


		// Let's create dag for (x_2 = psi_2) \wedge ... \wedge (x_n = psi_n)
		// We need to add exact Skolem functions for Tsietin variables if apply_tsietin_encoding_on_benchmarks is true
		
		Aig_Obj_t* S_equivalence_part;
		set<Aig_Obj_t*> S_equivalence_objects;

		// we need to create psi_i as  disjunction of elements in initial_cannot_be_zero_objects[i] 
		// \vee negation of disjunction of elements in cannot-be-one-set[i]
		for(map<int, set<Aig_Obj_t*> >::iterator cannot_be_one_set_it = cannot_be_one_set.begin(); cannot_be_one_set_it != cannot_be_one_set.end(); cannot_be_one_set_it++)
		{
			int var_to_elim_index = cannot_be_one_set_it->first;

			if(apply_tsietin_encoding_on_benchmarks)
			{
				if(var_to_elim_index <= number_of_tsietin_variables)
				{
					#ifdef DEBUG_SKOLEM
					cout << endl << var_to_elim_index << " <= " << number_of_tsietin_variables <<", hence exact Skolem fuctions to be used\n";
					#endif
					continue; // no need to add abstract Skolem functions
				}
			}

			// obtaining dag for x_i
			string var_to_elim = searchVarIndexToVarNameMap(var_index_to_var_name_map, var_to_elim_index);

			map<string, Aig_Obj_t*>::iterator Ci_to_eliminate_name_to_Ci_to_eliminate_object_map_it = Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.find(var_to_elim);
			assert(Ci_to_eliminate_name_to_Ci_to_eliminate_object_map_it != Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.end());			
			Aig_Obj_t* var_to_elim_obj = Ci_to_eliminate_name_to_Ci_to_eliminate_object_map_it->second;

			// obtaining \psi_i_part2
			Aig_Obj_t* psi_i_part2;
			set<Aig_Obj_t*> psi_i_part2_components = cannot_be_one_set_it->second;
			if(psi_i_part2_components.empty())
			{
				psi_i_part2 = createTrue(pub_aig_manager);
			}
			else
			{
				psi_i_part2 = createOr(psi_i_part2_components, pub_aig_manager);
				psi_i_part2 = createNot(psi_i_part2, pub_aig_manager);
			}
			assert(psi_i_part2 != NULL);
			
			// initialize Z_variable_counter[var_to_elim_index] to 0
			Z_variable_counter.insert(make_pair(var_to_elim_index, 0));

			int z_i_count = Z_variable_counter[var_to_elim_index]; // 0 here
			
			string z_i_string = obtainZVariableString(var_to_elim_index, z_i_count); // obtain the string Z_{var_to_elim_index}_0

			// check if object for z_i_string is already existing; if yes return it; otherwise create, 
			// update temporary_variable_for_incremental_solving_to_object_map and return
			Aig_Obj_t* z_i_object = obtainObjectOfTemporaryVariableForIncrementalSolving(z_i_string);
			assert(z_i_object != NULL);

			psi_i_part2 = createAnd(psi_i_part2, z_i_object, pub_aig_manager);	
			assert(psi_i_part2 != NULL);		

		
			// obtaining \psi_i_part1
			Aig_Obj_t* psi_i_part1;

			map<int, Aig_Obj_t*>::iterator initial_cannot_be_zero_objects_it = initial_cannot_be_zero_objects.find(var_to_elim_index);
			assert(initial_cannot_be_zero_objects_it != initial_cannot_be_zero_objects.end());

			psi_i_part1 = initial_cannot_be_zero_objects_it->second;
			assert(psi_i_part1 != NULL);
			

			// obtaining \psi_i
			Aig_Obj_t* psi_i;
			psi_i = createOr(createAnd(use_cbzero_in_unified_cegar_aig, psi_i_part1, pub_aig_manager), psi_i_part2, pub_aig_manager);
			assert(psi_i != NULL);			

			Aig_Obj_t* S_equivalence_i = createEquivalence(var_to_elim_obj, psi_i, pub_aig_manager);

			if(true) //var_to_elim_index > 1 is sufficeint; but may need code change
			{
				S_equivalence_objects.insert(S_equivalence_i);	
			}
		}

		if(apply_tsietin_encoding_on_benchmarks)
		{
			for(int tsietin_location_index = 1; tsietin_location_index <= number_of_tsietin_variables; tsietin_location_index++)
			{
				// obtaining dag for x_i
				string var_to_elim = searchVarIndexToVarNameMap(var_index_to_var_name_map, tsietin_location_index);

				map<string, Aig_Obj_t*>::iterator Ci_to_eliminate_name_to_Ci_to_eliminate_object_map_it = Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.find(var_to_elim);
				assert(Ci_to_eliminate_name_to_Ci_to_eliminate_object_map_it != Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.end());			
				Aig_Obj_t* var_to_elim_obj = Ci_to_eliminate_name_to_Ci_to_eliminate_object_map_it->second;

				// obtaining \psi_i
				Aig_Obj_t* psi_i;
				map<string, Aig_Obj_t*>::iterator tsietin_variable_to_exact_skolem_function_map_it = tsietin_variable_to_exact_skolem_function_map.find(var_to_elim);
				assert(tsietin_variable_to_exact_skolem_function_map_it != tsietin_variable_to_exact_skolem_function_map.end());

				psi_i = tsietin_variable_to_exact_skolem_function_map_it->second;
				assert(psi_i != NULL);			

				Aig_Obj_t* S_equivalence_i = createEquivalence(var_to_elim_obj, psi_i, pub_aig_manager);

				S_equivalence_objects.insert(S_equivalence_i);	

				#ifdef DEBUG_SKOLEM
				cout << endl << "Exact Skolem function used for x[" << tsietin_location_index << "] = " << var_to_elim << endl;
				#endif			

			}
		}
		
		if(S_equivalence_objects.empty())
		{
			S_equivalence_part = createTrue(pub_aig_manager);
		}
		else
		{
			S_equivalence_part = createAnd(S_equivalence_objects, pub_aig_manager);
		}
		assert(S_equivalence_part != NULL);

		// connect to some output to avoid unwanted deletion
		Aig_Obj_t* S_equivalence_part_CO = Aig_ObjCreateCo(pub_aig_manager, S_equivalence_part ); 
		assert(S_equivalence_part_CO != NULL);
		intermediate_cos_created.insert(S_equivalence_part_CO);


		// Let's create dag for
		// (B_1 = dag for bad_1) \wedge ... \wedge (B_{i} = dag for bad_{i})
		// We need to exclude Tsietin variables if apply_tsietin_encoding_on_benchmarks is true
		Aig_Obj_t* B_equivalence_part;
		set<Aig_Obj_t*> B_equivalence_objects;
		Aig_Obj_t* B_part;
		set<Aig_Obj_t*> B_objects;

		for(int bad_location_index = 1; bad_location_index <= number_of_vars_to_elim; bad_location_index++)
		{

			if(apply_tsietin_encoding_on_benchmarks)
			{
				if(bad_location_index <= number_of_tsietin_variables)
				{
					#ifdef DEBUG_SKOLEM
					cout << endl << bad_location_index << " <= " << number_of_tsietin_variables <<", hence exact Skolem fuctions to be used\n";
					#endif
					continue; // no need to add bads for these locations; Skolem functions already exact
				}
			}

			Aig_Obj_t* bad_set_obj;
			bad_set_obj = searchOneDimensionalMatrix(BadSets, number_of_vars_to_elim, bad_location_index);
			assert(bad_set_obj != NULL); 

			// Obtaining dag for bad_set_obj
			map<int, Aig_Obj_t*>::iterator B_i_index_to_B_i_object_map_iterator = B_i_index_to_B_i_object_map.find(bad_location_index);
			assert(B_i_index_to_B_i_object_map_iterator != B_i_index_to_B_i_object_map.end());
			Aig_Obj_t* B_obj = B_i_index_to_B_i_object_map_iterator->second;
			assert(B_obj != NULL); 

			B_objects.insert(B_obj);

			Aig_Obj_t* B_equivalence_i = createEquivalence(bad_set_obj, B_obj, pub_aig_manager);
			B_equivalence_objects.insert(B_equivalence_i);
			
		}

		assert(!B_equivalence_objects.empty());
		B_equivalence_part = createAnd(B_equivalence_objects, pub_aig_manager);
		assert(B_equivalence_part != NULL);
		// connect to some output to avoid unwanted deletion
		Aig_Obj_t* B_equivalence_part_CO = Aig_ObjCreateCo(pub_aig_manager, B_equivalence_part ); 
		assert(B_equivalence_part_CO != NULL);
		intermediate_cos_created.insert(B_equivalence_part_CO);

		Aig_Obj_t* negated_conjunction_of_factors = createNot(conjunction_of_factors, pub_aig_manager);
		assert(negated_conjunction_of_factors != NULL);

		// create aig for ite(use_bads_in_unified_cegar_aig, B_equivalence_part wedge disjunction_of_bad_symbols, negated_conjunction_of_factors)
		Aig_Obj_t* prevention_part;
		prevention_part = createIte(use_bads_in_unified_cegar_aig, createAnd(B_equivalence_part, disjunction_of_bad_symbols, pub_aig_manager), negated_conjunction_of_factors, pub_aig_manager);
		// connect to some output to avoid unwanted deletion
		Aig_Obj_t* prevention_part_CO = Aig_ObjCreateCo(pub_aig_manager, prevention_part ); 
		assert(prevention_part_CO != NULL);
		intermediate_cos_created.insert(prevention_part_CO);


		#ifdef DEBUG_SKOLEM
		string Cb_part_file_name = benchmark_name_without_extension;
		Cb_part_file_name += "_Cb_part";

		string S_equivalence_part_file_name = benchmark_name_without_extension;
		S_equivalence_part_file_name += "_S_equivalence_part";

		string B_equivalence_part_file_name = benchmark_name_without_extension;
		B_equivalence_part_file_name += "_B_equivalence_part";

		string prevention_part_file_name = benchmark_name_without_extension;
		prevention_part_file_name += "_prevention_part";

		cout << "\nCb_part computed\n";
		cout << "\nS_equivalence_part computed\n";
		cout << "\nB_equivalence_part computed\n";
		cout << "\nprevention_part computed\n";
		
		writeFormulaToFile(pub_aig_manager, Cb_part, Cb_part_file_name, ".v", cegar_iteration_number, 0);
		writeFormulaToFile(pub_aig_manager, S_equivalence_part, S_equivalence_part_file_name, ".v", cegar_iteration_number, 0);
		writeFormulaToFile(pub_aig_manager, B_equivalence_part, B_equivalence_part_file_name, ".v", cegar_iteration_number, 0);
		writeFormulaToFile(pub_aig_manager, prevention_part, prevention_part_file_name, ".v", cegar_iteration_number, 0);
		#endif	


		set<Aig_Obj_t*> epsilon_zero_objects;
		epsilon_zero_objects.insert(Cb_part);
		epsilon_zero_objects.insert(S_equivalence_part);
		epsilon_zero_objects.insert(prevention_part);
		epsilon_zero_objects.insert(renamed_conjunction_of_factors);
				

		epsilon_zero = createAnd(epsilon_zero_objects, pub_aig_manager);
		assert(epsilon_zero != NULL);
		// connect to some output to avoid unwanted deletion
		Aig_Obj_t* epsilon_zero_CO = Aig_ObjCreateCo(pub_aig_manager, epsilon_zero ); 
		assert(epsilon_zero_CO != NULL);
		intermediate_cos_created.insert(epsilon_zero_CO);

		if(Aig_IsComplement(epsilon_zero) && Aig_Regular(epsilon_zero) == createTrue(pub_aig_manager))
		// epsilon_zero is false
		{
			#ifdef DEBUG_CEGAR
			cout << "\nAIG for epsilon_zero is false; no need to call the sat-solver\n";
			#endif

			#ifdef RECORD_KEEP
			number_of_exactness_checking_in_cegar++;

			if(!mask_printing_cegar_details)
			{
				fprintf(record_fp, "\t0(0,0)(1)");
			}

			fclose(record_fp);
			#endif

			return true;
		}

		vector<Aig_Obj_t*> positive_assumptions_in_exactness_check;
		vector<Aig_Obj_t*> negative_assumptions_in_exactness_check;

		obtainAssumptionsInExactnessCheck_using_Generic_Skolem_Functions_With_Unified_Code_And_Incremental_Solving(correction_index, positive_assumptions_in_exactness_check, negative_assumptions_in_exactness_check);
		assert(positive_assumptions_in_exactness_check.size() != 0);

		if(assumptions_flag == 0)
		{
			assert(negative_assumptions_in_exactness_check.size() == 0);
		}
		else if(assumptions_flag == 1)
		{
			assert(negative_assumptions_in_exactness_check.size() == 1);
		}
		else
		{
			assert(false);
		}
			
					
		// Use incremental solver call
		#ifdef DEBUG_CEGAR
		string epsilon_zero_file_name = benchmark_name_without_extension;
		epsilon_zero_file_name += "_epsilon_zero";
		cout << "\nepsilon_zero computed\n";
		writeFormulaToFile(pub_aig_manager, epsilon_zero, epsilon_zero_file_name, ".v", cegar_iteration_number, 0);

		cout << endl << "Adding clauses of epsilon_zero to SAT-Solver, and calling SAT-Solver\n";
		#endif

		#ifdef DETAILED_RECORD_KEEP
		unsigned long long int solver_ms;
		struct timeval solver_start_ms, solver_finish_ms;
		gettimeofday (&solver_start_ms, NULL);	
		#endif

		// Give to SAT-Solver and get unsat / sat with model
		unsigned long long int cnf_time;
		int formula_size;
		unsigned long long int simplification_time;
		bool result_of_exactnesscheck;

		if(use_generic_sat_solver_interface)
		{
			if(sat_solver_used_in_cegar == "abc")
			{
				result_of_exactnesscheck = getIncrementAsCNF_AddToSolver_and_CallSolver_With_Assumptions(pub_aig_manager, epsilon_zero, Model_of_ExactnessCheck, cnf_time, formula_size, simplification_time, positive_assumptions_in_exactness_check, negative_assumptions_in_exactness_check, pSat_for_exactness_check, IncrementalLabelTableForExactnessCheck, IncrementalLabelCountForExactnessCheck, Ci_name_to_Ci_label_mapForExactnessCheck, Ci_label_to_Ci_name_mapForExactnessCheck);
			}
			else // for other SAT solvers
			{
				assert(false);
			}	
		}
		else
		{
			result_of_exactnesscheck = isExactnessCheckSatisfiable(pub_aig_manager, epsilon_zero, Model_of_ExactnessCheck, cnf_time, formula_size, simplification_time, positive_assumptions_in_exactness_check, negative_assumptions_in_exactness_check, pSat_for_exactness_check, IncrementalLabelTableForExactnessCheck, IncrementalLabelCountForExactnessCheck, Ci_name_to_Ci_label_mapForExactnessCheck, Ci_label_to_Ci_name_mapForExactnessCheck);
		
		}
	
		#ifdef DETAILED_RECORD_KEEP
		gettimeofday (&solver_finish_ms, NULL);
		solver_ms = solver_finish_ms.tv_sec * 1000 + solver_finish_ms.tv_usec / 1000;
		solver_ms -= solver_start_ms.tv_sec * 1000 + solver_start_ms.tv_usec / 1000;
		if(!mask_printing_cegar_details)
		{
			cout << "\nsolver finished in " << solver_ms << " milliseconds\n";
		}

		total_time_in_smt_solver = total_time_in_smt_solver + solver_ms;
		total_time_in_exactness_checking_in_cegar = total_time_in_exactness_checking_in_cegar + solver_ms;
		number_of_exactness_checking_in_cegar++;
		#endif

		#ifdef RECORD_KEEP
		if(!mask_printing_cegar_details)
		{
			fprintf(record_fp, "\t%llu(%llu,%llu)(%d)", solver_ms, cnf_time, simplification_time, formula_size);
		}

		fclose(record_fp);
		#endif


		#ifdef DEBUG_SKOLEM
		displayModelFromSATSolver(Model_of_ExactnessCheck);
		cout << endl << "result_of_exactnesscheck = " << result_of_exactnesscheck << endl;
		#endif

		removeTemporaryVariablesFromModel(Model_of_ExactnessCheck);

		#ifdef DEBUG_SKOLEM
		cout << "\nModel after removing temporary variables\n";
		displayModelFromSATSolver(Model_of_ExactnessCheck);
		cout << endl << "result_of_exactnesscheck = " << result_of_exactnesscheck << endl;
		#endif

		if(!result_of_exactnesscheck)
		// ExactnessCheck unsat i.e. skolem function at correction_index is exact
		{
			return true;
		}
		else // skolem function at correction_index is inexact
		{
			return false;
		}
		
	} // if(cegar_iteration_number == 0) ends here
	else if(cegar_iteration_for_correction_index == 0) 
	{
		#ifdef DEBUG_CEGAR
		cout << "\nCase with cegar_iteration_for_correction_index == 0 \n";
		#endif

		assert(correction_index < number_of_vars_to_elim);

		Aig_Obj_t* delta_epsilon_i;

		int corrected_index = correction_index + 1;
		
		// obtaining object for x_{corrected_index}
		string var_to_elim = searchVarIndexToVarNameMap(var_index_to_var_name_map, corrected_index);

		map<string, Aig_Obj_t*>::iterator Ci_to_eliminate_name_to_Ci_to_eliminate_object_map_it = Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.find(var_to_elim);
		assert(Ci_to_eliminate_name_to_Ci_to_eliminate_object_map_it != Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.end());			
		Aig_Obj_t* var_to_elim_obj = Ci_to_eliminate_name_to_Ci_to_eliminate_object_map_it->second;
		assert(var_to_elim_obj != NULL);		
		
		// obtaining dag for x_{corrected_index}'
		map<int, Aig_Obj_t*>::iterator Ci_to_eliminate_renamed_to_Ci_to_eliminate_renamed_object_map_it = Ci_to_eliminate_renamed_to_Ci_to_eliminate_renamed_object_map.find(corrected_index);
		assert(Ci_to_eliminate_renamed_to_Ci_to_eliminate_renamed_object_map_it != Ci_to_eliminate_renamed_to_Ci_to_eliminate_renamed_object_map.end());			
		Aig_Obj_t* var_to_elim_renamed_obj = Ci_to_eliminate_renamed_to_Ci_to_eliminate_renamed_object_map_it->second;
		assert(var_to_elim_renamed_obj != NULL);		
		
		// creating (x_{corrected_index} = x_{corrected_index}')
		Aig_Obj_t* x_equivalence = createEquivalence(var_to_elim_obj, var_to_elim_renamed_obj, pub_aig_manager);
		assert(x_equivalence != NULL);

		// connect to some output to avoid unwanted deletion
		Aig_Obj_t* x_equivalence_CO = Aig_ObjCreateCo(pub_aig_manager, x_equivalence ); 
		assert(x_equivalence_CO != NULL);
		intermediate_cos_created.insert(x_equivalence_CO);

		#ifdef DEBUG_SKOLEM
		string x_equivalence_file_name = benchmark_name_without_extension;
		x_equivalence_file_name += "_x_equivalence";

		cout << "\nx_equivalence computed\n";
		
		writeFormulaToFile(pub_aig_manager, x_equivalence, x_equivalence_file_name, ".v", cegar_iteration_number, 0);
		#endif

		if(allow_intermediate_generic_sat_calls) 
		{
			// There can be hints; incorporate them
			if(!Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX.empty() || !Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX.empty())
			{
				Aig_Obj_t* Cb_part;
				set<Aig_Obj_t*> Cb_objects;

				Aig_Obj_t* Z_part;
				set<Aig_Obj_t*> Z_objects;

				for(map<int, Aig_Obj_t*>::iterator hint_it = Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX.begin(); hint_it != Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX.end(); hint_it++)
				{
					int destination = hint_it->first;
					Aig_Obj_t* new_cannot_be_one_object_at_destination = hint_it->second;

					map<Aig_Obj_t*, Aig_Obj_t*>::iterator cannot_be_object_to_cannot_be_dag_map_it = cannot_be_object_to_cannot_be_dag_map.find(new_cannot_be_one_object_at_destination);
					assert(cannot_be_object_to_cannot_be_dag_map_it != cannot_be_object_to_cannot_be_dag_map.end());
					Aig_Obj_t* new_cannot_be_one_dag_at_destination = cannot_be_object_to_cannot_be_dag_map_it->second;

					Aig_Obj_t* Cb_one_equivalence = createEquivalence(new_cannot_be_one_object_at_destination, new_cannot_be_one_dag_at_destination, pub_aig_manager);
					assert(Cb_one_equivalence != NULL);

					Cb_objects.insert(Cb_one_equivalence);

		
					int present_z_j_k_count = Z_variable_counter[destination];
					int next_z_j_k_count = present_z_j_k_count + 1;
					Z_variable_counter[destination] = next_z_j_k_count;

					string present_z_j_k_string = obtainZVariableString(destination, present_z_j_k_count); // obtain the string Z_{destination}_{present_z_j_k_count}
					Aig_Obj_t* present_z_j_k_object = obtainExistingObjectOfTemporaryVariableForIncrementalSolving(present_z_j_k_string);
					assert(present_z_j_k_object != NULL);
				
					string next_z_j_k_string = obtainZVariableString(destination, next_z_j_k_count); // obtain the string Z_{destination}_{next_z_j_k_count}
					Aig_Obj_t* next_z_j_k_object = obtainObjectOfTemporaryVariableForIncrementalSolving(next_z_j_k_string);
					assert(next_z_j_k_object != NULL);

					Aig_Obj_t* R_i_j_increment = createEquivalence(present_z_j_k_object, createAnd(createNot(new_cannot_be_one_object_at_destination, pub_aig_manager), next_z_j_k_object, pub_aig_manager), pub_aig_manager);
					assert(R_i_j_increment != NULL);

					Z_objects.insert(R_i_j_increment);
				}
		
		
				for(map<int, Aig_Obj_t*>::iterator hint_it = Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX.begin(); hint_it != Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX.end(); hint_it++)
				{
					int destination = hint_it->first;
					Aig_Obj_t* new_cannot_be_zero_object_at_destination = hint_it->second;

					map<Aig_Obj_t*, Aig_Obj_t*>::iterator cannot_be_object_to_cannot_be_dag_map_it = cannot_be_object_to_cannot_be_dag_map.find(new_cannot_be_zero_object_at_destination);
					assert(cannot_be_object_to_cannot_be_dag_map_it != cannot_be_object_to_cannot_be_dag_map.end());
					Aig_Obj_t* new_cannot_be_zero_dag_at_destination = cannot_be_object_to_cannot_be_dag_map_it->second;

					Aig_Obj_t* Cb_zero_equivalence = createEquivalence(new_cannot_be_zero_object_at_destination, new_cannot_be_zero_dag_at_destination, pub_aig_manager);
					assert(Cb_zero_equivalence != NULL);

					Cb_objects.insert(Cb_zero_equivalence);
				}
		
				if(Cb_objects.empty() && Z_objects.empty())
				{
					delta_epsilon_i = createTrue(pub_aig_manager);
				}
				else
				{		
					assert(!Cb_objects.empty());
					Cb_part = createAnd(Cb_objects, pub_aig_manager);
					assert(Cb_part != NULL);
					// connect to some output to avoid unwanted deletion
					Aig_Obj_t* Cb_part_CO = Aig_ObjCreateCo(pub_aig_manager, Cb_part ); 
					assert(Cb_part_CO != NULL);
					intermediate_cos_created.insert(Cb_part_CO);

					assert(!Z_objects.empty());
					Z_part = createAnd(Z_objects, pub_aig_manager);
					assert(Z_part != NULL);
					// connect to some output to avoid unwanted deletion
					Aig_Obj_t* Z_part_CO = Aig_ObjCreateCo(pub_aig_manager, Z_part ); 
					assert(Z_part_CO != NULL);
					intermediate_cos_created.insert(Z_part_CO );


					#ifdef DEBUG_SKOLEM
					string Cb_part_file_name = benchmark_name_without_extension;
					Cb_part_file_name += "_Cb_part";

					string Z_part_file_name = benchmark_name_without_extension;
					Z_part_file_name += "_Z_part";

					cout << "\nCb_part computed\n";
					cout << "\nZ_part computed\n";

					writeFormulaToFile(pub_aig_manager, Cb_part, Cb_part_file_name, ".v", cegar_iteration_number, 0);
					writeFormulaToFile(pub_aig_manager, Z_part, Z_part_file_name, ".v", cegar_iteration_number, 0);
					#endif

					delta_epsilon_i = createAnd(Cb_part, Z_part, pub_aig_manager);
				}	
			}// There are hints ends here
			else
			{
				delta_epsilon_i = createTrue(pub_aig_manager);
			}// No hints

			delta_epsilon_i = createAnd(delta_epsilon_i, x_equivalence, pub_aig_manager);
			
		}
		else 
		{
			assert(Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX.empty() && Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX.empty());
			delta_epsilon_i = x_equivalence;			
		}

		assert(delta_epsilon_i != NULL);
		// connect to some output to avoid unwanted deletion
		Aig_Obj_t* delta_epsilon_i_CO = Aig_ObjCreateCo(pub_aig_manager, delta_epsilon_i ); 
		assert(delta_epsilon_i_CO != NULL);
		intermediate_cos_created.insert(delta_epsilon_i_CO);

		#ifdef DEBUG_CEGAR
		string delta_epsilon_i_file_name = benchmark_name_without_extension;
		delta_epsilon_i_file_name += "_delta_epsilon_i";
		cout << "\ndelta_epsilon_i computed\n";
		writeFormulaToFile(pub_aig_manager, delta_epsilon_i, delta_epsilon_i_file_name, ".v", cegar_iteration_number, 0);

		cout << endl << "Adding clauses of delta_epsilon_i to SAT-Solver, and calling SAT-Solver\n";
		#endif
		
		vector<Aig_Obj_t*> positive_assumptions_in_exactness_check;
		vector<Aig_Obj_t*> negative_assumptions_in_exactness_check;

		obtainAssumptionsInExactnessCheck_using_Generic_Skolem_Functions_With_Unified_Code_And_Incremental_Solving(correction_index, positive_assumptions_in_exactness_check, negative_assumptions_in_exactness_check);
		//assert(positive_assumptions_in_exactness_check.size() != 0);
		//assert(negative_assumptions_in_exactness_check.size() != 0);


		// Use incremental solver call
		#ifdef DEBUG_CEGAR
		cout << endl << "Adding clauses of delta_epsilon_i to SAT-Solver, and calling SAT-Solver\n";
		#endif

		#ifdef DETAILED_RECORD_KEEP
		unsigned long long int solver_ms;
		struct timeval solver_start_ms, solver_finish_ms;
		gettimeofday (&solver_start_ms, NULL); 	
		#endif

		// Give to SAT-Solver and get unsat / sat with model
		unsigned long long int cnf_time;
		int formula_size;
		unsigned long long int simplification_time;
		bool result_of_exactnesscheck;

		if(use_generic_sat_solver_interface)
		{
			if(sat_solver_used_in_cegar == "abc")
			{
				result_of_exactnesscheck = getIncrementAsCNF_AddToSolver_and_CallSolver_With_Assumptions(pub_aig_manager, delta_epsilon_i, Model_of_ExactnessCheck, cnf_time, formula_size, simplification_time, positive_assumptions_in_exactness_check, negative_assumptions_in_exactness_check, pSat_for_exactness_check, IncrementalLabelTableForExactnessCheck, IncrementalLabelCountForExactnessCheck, Ci_name_to_Ci_label_mapForExactnessCheck, Ci_label_to_Ci_name_mapForExactnessCheck);
			}
			else // for other SAT solvers
			{
				assert(false);
			}	
		}
		else
		{		
		 	result_of_exactnesscheck = isExactnessCheckSatisfiable(pub_aig_manager, delta_epsilon_i, Model_of_ExactnessCheck, cnf_time, formula_size, simplification_time, positive_assumptions_in_exactness_check, negative_assumptions_in_exactness_check, pSat_for_exactness_check, IncrementalLabelTableForExactnessCheck, IncrementalLabelCountForExactnessCheck, Ci_name_to_Ci_label_mapForExactnessCheck, Ci_label_to_Ci_name_mapForExactnessCheck);

		}
	
		#ifdef DETAILED_RECORD_KEEP
		gettimeofday (&solver_finish_ms, NULL);
		solver_ms = solver_finish_ms.tv_sec * 1000 + solver_finish_ms.tv_usec / 1000;
		solver_ms -= solver_start_ms.tv_sec * 1000 + solver_start_ms.tv_usec / 1000;
		
		if(!mask_printing_cegar_details)
		{
			cout << "\nsolver finished in " << solver_ms << " milliseconds\n";
		}

		total_time_in_smt_solver = total_time_in_smt_solver + solver_ms;
		total_time_in_exactness_checking_in_cegar = total_time_in_exactness_checking_in_cegar + solver_ms;
		number_of_exactness_checking_in_cegar++;
		#endif

		#ifdef RECORD_KEEP
		if(!mask_printing_cegar_details)
		{
			fprintf(record_fp, "\t%llu(%llu,%llu)(%d)", solver_ms, cnf_time, simplification_time, formula_size);
		}

		fclose(record_fp);
		#endif


		#ifdef DEBUG_SKOLEM
		displayModelFromSATSolver(Model_of_ExactnessCheck);
		cout << endl << "result_of_exactnesscheck = " << result_of_exactnesscheck << endl;
		#endif

		removeTemporaryVariablesFromModel(Model_of_ExactnessCheck);

		#ifdef DEBUG_SKOLEM
		cout << "\nModel after removing temporary variables\n";
		displayModelFromSATSolver(Model_of_ExactnessCheck);
		cout << endl << "result_of_exactnesscheck = " << result_of_exactnesscheck << endl;
		#endif
	
		if(!result_of_exactnesscheck)
		// ExactnessCheck unsat i.e. skolem function at correction_index is exact
		{
			return true;
		}
		else // skolem function at correction_index is inexact
		{
			return false;
		}
		
	}// if(cegar_iteration_for_correction_index == 0) ends here
	else // if(cegar_iteration_for_correction_index > 0)
	{
		#ifdef DEBUG_CEGAR
		cout << "\nCase with cegar_iteration_for_correction_index > 0 \n";

		if(Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX.empty() && Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX.empty())
		{
			cout << "\nRefinement hints are empty\n";
		}
		else
		{
			cout << "\nRefinement hints are NOT empty\n";
		}
		#endif

		#ifdef DEBUG_CEGAR
		show_present_refinement_hint(Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX, Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX);
		#endif

		Aig_Obj_t* delta_epsilon_i;

		// Create the dag for delta_epsilon_i:
		// for each o_j added in Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX
		// (o_j = dag_j) \wedge 
		// (Z_i_k = Z_i_{k+1} \wedge o_j) \wedge 
		
		Aig_Obj_t* Cb_part;
		set<Aig_Obj_t*> Cb_objects;

		Aig_Obj_t* Z_part;
		set<Aig_Obj_t*> Z_objects;

		for(map<int, Aig_Obj_t*>::iterator hint_it = Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX.begin(); hint_it != Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX.end(); hint_it++)
		{
			int destination = hint_it->first;
			Aig_Obj_t* new_cannot_be_one_object_at_destination = hint_it->second;

			map<Aig_Obj_t*, Aig_Obj_t*>::iterator cannot_be_object_to_cannot_be_dag_map_it = cannot_be_object_to_cannot_be_dag_map.find(new_cannot_be_one_object_at_destination);
			assert(cannot_be_object_to_cannot_be_dag_map_it != cannot_be_object_to_cannot_be_dag_map.end());
			Aig_Obj_t* new_cannot_be_one_dag_at_destination = cannot_be_object_to_cannot_be_dag_map_it->second;

			Aig_Obj_t* Cb_one_equivalence = createEquivalence(new_cannot_be_one_object_at_destination, new_cannot_be_one_dag_at_destination, pub_aig_manager);
			assert(Cb_one_equivalence != NULL);

			Cb_objects.insert(Cb_one_equivalence);

		
			int present_z_j_k_count = Z_variable_counter[destination];
			int next_z_j_k_count = present_z_j_k_count + 1;
			Z_variable_counter[destination] = next_z_j_k_count;

			string present_z_j_k_string = obtainZVariableString(destination, present_z_j_k_count); // obtain the string Z_{destination}_{present_z_j_k_count}
			Aig_Obj_t* present_z_j_k_object = obtainExistingObjectOfTemporaryVariableForIncrementalSolving(present_z_j_k_string);
			assert(present_z_j_k_object != NULL);
				
			string next_z_j_k_string = obtainZVariableString(destination, next_z_j_k_count); // obtain the string Z_{destination}_{next_z_j_k_count}
			Aig_Obj_t* next_z_j_k_object = obtainObjectOfTemporaryVariableForIncrementalSolving(next_z_j_k_string);
			assert(next_z_j_k_object != NULL);

			Aig_Obj_t* R_i_j_increment = createEquivalence(present_z_j_k_object, createAnd(createNot(new_cannot_be_one_object_at_destination, pub_aig_manager), next_z_j_k_object, pub_aig_manager), pub_aig_manager);
			assert(R_i_j_increment != NULL);

			Z_objects.insert(R_i_j_increment);
		}
		
		
		for(map<int, Aig_Obj_t*>::iterator hint_it = Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX.begin(); hint_it != Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX.end(); hint_it++)
		{
			int destination = hint_it->first;
			Aig_Obj_t* new_cannot_be_zero_object_at_destination = hint_it->second;

			map<Aig_Obj_t*, Aig_Obj_t*>::iterator cannot_be_object_to_cannot_be_dag_map_it = cannot_be_object_to_cannot_be_dag_map.find(new_cannot_be_zero_object_at_destination);
			assert(cannot_be_object_to_cannot_be_dag_map_it != cannot_be_object_to_cannot_be_dag_map.end());
			Aig_Obj_t* new_cannot_be_zero_dag_at_destination = cannot_be_object_to_cannot_be_dag_map_it->second;

			Aig_Obj_t* Cb_zero_equivalence = createEquivalence(new_cannot_be_zero_object_at_destination, new_cannot_be_zero_dag_at_destination, pub_aig_manager);
			assert(Cb_zero_equivalence != NULL);

			Cb_objects.insert(Cb_zero_equivalence);
		}
		
		if(Cb_objects.empty() && Z_objects.empty())
		{
			delta_epsilon_i = createTrue(pub_aig_manager);
		}
		else
		{		
			assert(!Cb_objects.empty());
			Cb_part = createAnd(Cb_objects, pub_aig_manager);
			assert(Cb_part != NULL);
			// connect to some output to avoid unwanted deletion
			Aig_Obj_t* Cb_part_CO = Aig_ObjCreateCo(pub_aig_manager, Cb_part ); 
			assert(Cb_part_CO != NULL);
			intermediate_cos_created.insert(Cb_part_CO);

			assert(!Z_objects.empty());
			Z_part = createAnd(Z_objects, pub_aig_manager);
			assert(Z_part != NULL);
			// connect to some output to avoid unwanted deletion
			Aig_Obj_t* Z_part_CO = Aig_ObjCreateCo(pub_aig_manager, Z_part ); 
			assert(Z_part_CO != NULL);
			intermediate_cos_created.insert(Z_part_CO);


			#ifdef DEBUG_SKOLEM
			string Cb_part_file_name = benchmark_name_without_extension;
			Cb_part_file_name += "_Cb_part";

			string Z_part_file_name = benchmark_name_without_extension;
			Z_part_file_name += "_Z_part";

			cout << "\nCb_part computed\n";
			cout << "\nZ_part computed\n";

			writeFormulaToFile(pub_aig_manager, Cb_part, Cb_part_file_name, ".v", cegar_iteration_number, 0);
			writeFormulaToFile(pub_aig_manager, Z_part, Z_part_file_name, ".v", cegar_iteration_number, 0);
			#endif

			delta_epsilon_i = createAnd(Cb_part, Z_part, pub_aig_manager);
		}

		assert(delta_epsilon_i != NULL);
		// connect to some output to avoid unwanted deletion
		Aig_Obj_t* delta_epsilon_i_CO = Aig_ObjCreateCo(pub_aig_manager, delta_epsilon_i ); 
		assert(delta_epsilon_i_CO != NULL);
		intermediate_cos_created.insert(delta_epsilon_i_CO);


		#ifdef DEBUG_CEGAR
		string delta_epsilon_i_file_name = benchmark_name_without_extension;
		delta_epsilon_i_file_name += "_delta_epsilon_i";
		cout << "\ndelta_epsilon_i computed\n";
		writeFormulaToFile(pub_aig_manager, delta_epsilon_i, delta_epsilon_i_file_name, ".v", cegar_iteration_number, 0);

		cout << endl << "Adding clauses of delta_epsilon_i to SAT-Solver, and calling SAT-Solver\n";
		#endif

		vector<Aig_Obj_t*> positive_assumptions_in_exactness_check;
		vector<Aig_Obj_t*> negative_assumptions_in_exactness_check;

		obtainAssumptionsInExactnessCheck_using_Generic_Skolem_Functions_With_Unified_Code_And_Incremental_Solving(correction_index, positive_assumptions_in_exactness_check, negative_assumptions_in_exactness_check);
		//assert(positive_assumptions_in_exactness_check.size() != 0);
		//assert(negative_assumptions_in_exactness_check.size() != 0);


		// Use incremental solver call
		#ifdef DEBUG_CEGAR
		cout << endl << "Adding clauses of delta_epsilon_i to SAT-Solver, and calling SAT-Solver\n";
		#endif

		#ifdef DETAILED_RECORD_KEEP
		unsigned long long int solver_ms;
		struct timeval solver_start_ms, solver_finish_ms;
		gettimeofday (&solver_start_ms, NULL); 	
		#endif

		// Give to SAT-Solver and get unsat / sat with model
		unsigned long long int cnf_time;
		int formula_size;
		unsigned long long int simplification_time;
		bool result_of_exactnesscheck;

		if(use_generic_sat_solver_interface)
		{
			if(sat_solver_used_in_cegar == "abc")
			{
				result_of_exactnesscheck = getIncrementAsCNF_AddToSolver_and_CallSolver_With_Assumptions(pub_aig_manager, delta_epsilon_i, Model_of_ExactnessCheck, cnf_time, formula_size, simplification_time, positive_assumptions_in_exactness_check, negative_assumptions_in_exactness_check, pSat_for_exactness_check, IncrementalLabelTableForExactnessCheck, IncrementalLabelCountForExactnessCheck, Ci_name_to_Ci_label_mapForExactnessCheck, Ci_label_to_Ci_name_mapForExactnessCheck);
			}
			else // for other SAT solvers
			{
				assert(false);
			}	
		}
		else
		{
			result_of_exactnesscheck = isExactnessCheckSatisfiable(pub_aig_manager, delta_epsilon_i, Model_of_ExactnessCheck, cnf_time, formula_size, simplification_time, positive_assumptions_in_exactness_check, negative_assumptions_in_exactness_check, pSat_for_exactness_check, IncrementalLabelTableForExactnessCheck, IncrementalLabelCountForExactnessCheck, Ci_name_to_Ci_label_mapForExactnessCheck, Ci_label_to_Ci_name_mapForExactnessCheck);
		
		}
	
		#ifdef DETAILED_RECORD_KEEP
		gettimeofday (&solver_finish_ms, NULL);
		solver_ms = solver_finish_ms.tv_sec * 1000 + solver_finish_ms.tv_usec / 1000;
		solver_ms -= solver_start_ms.tv_sec * 1000 + solver_start_ms.tv_usec / 1000;

		if(!mask_printing_cegar_details)
		{
			cout << "\nsolver finished in " << solver_ms << " milliseconds\n";
		}

		total_time_in_smt_solver = total_time_in_smt_solver + solver_ms;
		total_time_in_exactness_checking_in_cegar = total_time_in_exactness_checking_in_cegar + solver_ms;
		number_of_exactness_checking_in_cegar++;
		#endif

		#ifdef RECORD_KEEP
		if(!mask_printing_cegar_details)
		{
			fprintf(record_fp, "\t%llu(%llu,%llu)(%d)", solver_ms, cnf_time, simplification_time, formula_size);
		}

		fclose(record_fp);
		#endif


		#ifdef DEBUG_SKOLEM
		displayModelFromSATSolver(Model_of_ExactnessCheck);
		cout << endl << "result_of_exactnesscheck = " << result_of_exactnesscheck << endl;
		#endif

		removeTemporaryVariablesFromModel(Model_of_ExactnessCheck);

		#ifdef DEBUG_SKOLEM
		cout << "\nModel after removing temporary variables\n";
		displayModelFromSATSolver(Model_of_ExactnessCheck);
		cout << endl << "result_of_exactnesscheck = " << result_of_exactnesscheck << endl;
		#endif
	
		if(!result_of_exactnesscheck)
		// ExactnessCheck unsat i.e. skolem function at correction_index is exact
		{
			return true;
		}
		else // skolem function at correction_index is inexact
		{
			return false;
		}

	} // if(cegar_iteration_for_correction_index > 0) ends here	
}



void AIGBasedSkolem::obtainAssumptionsInExactnessCheck_using_Generic_Skolem_Functions_With_Unified_Code_And_Incremental_Solving(int correction_index, vector<Aig_Obj_t*> &positive_assumptions_in_exactness_check, vector<Aig_Obj_t*> &negative_assumptions_in_exactness_check)
{
	// positive_assumptions_in_exactness_check includes
	//	Z_i_j for each i = variable_to_eliminate and j = Z_variable_counter[i]

	for(int var_to_elim_index = 1; var_to_elim_index <= number_of_vars_to_elim; var_to_elim_index++)
	{
		if(apply_tsietin_encoding_on_benchmarks)
		{
			if(var_to_elim_index <= number_of_tsietin_variables)
			{
				#ifdef DEBUG_SKOLEM
				cout << endl << var_to_elim_index << " <= " << number_of_tsietin_variables <<", hence exact Skolem fuctions to be used\n";
				#endif
				continue; // no need to add abstract Skolem functions
			}
		}

		map<int, int>::iterator Z_variable_counter_it = Z_variable_counter.find(var_to_elim_index);
		assert(Z_variable_counter_it != Z_variable_counter.end());
		
		int z_i_count = Z_variable_counter_it->second;
		string z_i_string = obtainZVariableString(var_to_elim_index, z_i_count); // obtain the string Z_{var_to_elim_index}_{z_i_count}

		Aig_Obj_t* z_i_object = obtainExistingObjectOfTemporaryVariableForIncrementalSolving(z_i_string);
		assert(z_i_object != NULL);
		
		positive_assumptions_in_exactness_check.push_back(z_i_object);
	}

	if(assumptions_flag == 1)
	{
		// obtaining dag for x_{correction_index}
		string var_to_elim = searchVarIndexToVarNameMap(var_index_to_var_name_map, correction_index);

		map<string, Aig_Obj_t*>::iterator Ci_to_eliminate_name_to_Ci_to_eliminate_object_map_it = Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.find(var_to_elim);
		assert(Ci_to_eliminate_name_to_Ci_to_eliminate_object_map_it != Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.end());			
		Aig_Obj_t* var_to_elim_obj = Ci_to_eliminate_name_to_Ci_to_eliminate_object_map_it->second;
		assert(var_to_elim_obj != NULL);		
		positive_assumptions_in_exactness_check.push_back(var_to_elim_obj);

		// obtaining dag for x_{correction_index}'
		map<int, Aig_Obj_t*>::iterator Ci_to_eliminate_renamed_to_Ci_to_eliminate_renamed_object_map_it = Ci_to_eliminate_renamed_to_Ci_to_eliminate_renamed_object_map.find(correction_index);
		assert(Ci_to_eliminate_renamed_to_Ci_to_eliminate_renamed_object_map_it != Ci_to_eliminate_renamed_to_Ci_to_eliminate_renamed_object_map.end());			
		Aig_Obj_t* var_to_elim_renamed_obj = Ci_to_eliminate_renamed_to_Ci_to_eliminate_renamed_object_map_it->second;
		assert(var_to_elim_renamed_obj != NULL);		
		negative_assumptions_in_exactness_check.push_back(var_to_elim_renamed_obj);

		if(use_bads_in_unified_cegar == 1)
		{

			bool use_support_based_bad_exclusion = true;
			if(use_support_based_bad_exclusion)
			{
				if(correction_index < number_of_vars_to_elim)
				{
					map<int, set<int> >::iterator bads_to_exclude_it = bads_to_exclude.find(correction_index);
					set<int> bads_to_exclude_for_correction_index = bads_to_exclude_it->second;

					for(set<int>::iterator bads_to_exclude_for_correction_index_it = bads_to_exclude_for_correction_index.begin(); bads_to_exclude_for_correction_index_it != bads_to_exclude_for_correction_index.end(); bads_to_exclude_for_correction_index_it++)
					{
						int bad_index = *bads_to_exclude_for_correction_index_it;
				
						map<int, Aig_Obj_t*>::iterator B_i_index_to_B_i_object_map_iterator = B_i_index_to_B_i_object_map.find(bad_index);
						assert(B_i_index_to_B_i_object_map_iterator != B_i_index_to_B_i_object_map.end());
						Aig_Obj_t* B_obj = B_i_index_to_B_i_object_map_iterator->second;
						assert(B_obj != NULL); 

						negative_assumptions_in_exactness_check.push_back(B_obj);
					}
				}
			}
			else
			{
				for(int var_to_elim_index = number_of_vars_to_elim; var_to_elim_index >= correction_index+1; var_to_elim_index--)
				{
					map<int, Aig_Obj_t*>::iterator B_i_index_to_B_i_object_map_iterator = B_i_index_to_B_i_object_map.find(var_to_elim_index);
					assert(B_i_index_to_B_i_object_map_iterator != B_i_index_to_B_i_object_map.end());
					Aig_Obj_t* B_obj = B_i_index_to_B_i_object_map_iterator->second;
					assert(B_obj != NULL); 

					negative_assumptions_in_exactness_check.push_back(B_obj);
				}
			}
		}//if(use_bads_in_unified_cegar == 1) ends here

	}//if(assumptions_flag == 1) ends here

}



void AIGBasedSkolem::generateSkolemFunctionsForGameBenchmarks(set<Aig_Obj_t*> &original_factors, vector< list<string> > &VariablesToEliminateForGameBenchmarks, char TypeOfInnerQuantifier)
{
	assert(!original_factors.empty());
	assert(TypeOfInnerQuantifier == 'e' || TypeOfInnerQuantifier == 'u');
	assert(VariablesToEliminateForGameBenchmarks.size() > 0);


	Aig_Obj_t* present_formula = createAnd(original_factors, pub_aig_manager);
	assert(present_formula != NULL);
	Aig_Obj_t* present_formula_CO = Aig_ObjCreateCo( pub_aig_manager, present_formula ); // to aviod 
	// unwanted cleanup of present_formula
	assert(present_formula_CO != NULL);

	for(int quantifier_block = 0; quantifier_block < VariablesToEliminateForGameBenchmarks.size(); quantifier_block++)	
	{
		char TypeOfQuantifier;

		if(quantifier_block % 2 == 0)
		{
			TypeOfQuantifier = TypeOfInnerQuantifier;
		}
		else
		{
			if(TypeOfInnerQuantifier == 'e')
			{
				TypeOfQuantifier = 'a';
			}
			else
			{
				TypeOfQuantifier = 'e';
			}
		}

		list<string> VariablesToEliminate = VariablesToEliminateForGameBenchmarks[quantifier_block];

		if(TypeOfQuantifier == 'a')	
		{
			// present_formula should become \neg present_formula
			present_formula = createNot(present_formula, pub_aig_manager);
		}

		set<Aig_Obj_t*> Factors;
		Factors.clear();
		// obtain factors by factorizing the present_formula
		andFlattening(present_formula, Factors);
		assert(Factors.size() > 0);

		recreateCiMaps(VariablesToEliminate);

		#ifdef DEBUG_SKOLEM
		cout << "\nCalling Skolem function generator for quantifier block " << 	TypeOfQuantifier << "_" << quantifier_block << endl;	
		
		cout << "\nFactors\n";
		int factor_index = 1;
		for(set<Aig_Obj_t*>::iterator Factors_it = Factors.begin(); Factors_it != Factors.end(); Factors_it++)
		{
			writeFormulaToFile(pub_aig_manager, *Factors_it, "game_factor", ".v", quantifier_block, factor_index);	
			factor_index++;			
		}

		cout << "\nVariablesToEliminate\n";
		showList(VariablesToEliminate);
		#endif	

		map<string, Aig_Obj_t*> variable_to_skolem_function_map;
		variable_to_skolem_function_map.clear();

		obtainSkolemFunctionsInGameBenchmarks(Factors, VariablesToEliminate, variable_to_skolem_function_map, quantifier_block, TypeOfQuantifier);

		#ifdef DEBUG_SKOLEM
		cout << "\nSkolem function generator for quantifier block " << 	TypeOfQuantifier << "_" << quantifier_block << " finished " << endl;

		cout << "\nSkolem functions\n";
		int variable_index = 1;
		for(map<string, Aig_Obj_t*>::iterator map_it = variable_to_skolem_function_map.begin(); map_it != variable_to_skolem_function_map.end(); map_it++)
		{
			writeFormulaToFile(pub_aig_manager, map_it->second, "game_skolem_function", ".v", quantifier_block, variable_index);
			variable_index++;	
		}
		#endif	
		
		// finding \exists X. (present_formula)
		Aig_Obj_t* exists_present_formula; 
		exists_present_formula = replaceVariablesByFormulas(present_formula, variable_to_skolem_function_map);
		assert(exists_present_formula != NULL);

		Aig_Obj_t* exists_present_formula_CO = Aig_ObjCreateCo( pub_aig_manager, exists_present_formula ); 
		assert(exists_present_formula_CO != NULL);

		if(TypeOfQuantifier == 'a')	
		{
			// present_formula should become \neg \exists X. (present_formula)
			present_formula = createNot(exists_present_formula, pub_aig_manager);			
		}
		else
		{
			present_formula = exists_present_formula;
		}

		#ifdef DEBUG_SKOLEM
		writeFormulaToFile(pub_aig_manager, present_formula, "present_formula", ".v", quantifier_block, 0);
		#endif
				
		#ifdef DEBUG_SKOLEM
		//cout << "\nPress any key to continue...";
		//char c = getchar();
		#endif	
	}// for ends here
}// function ends here



void AIGBasedSkolem::obtainSkolemFunctionsInGameBenchmarks(set<Aig_Obj_t*> &Factors, list<string> &VariablesToEliminate, map<string, Aig_Obj_t*> &variable_to_skolem_function_map, int quantifier_block, char TypeOfQuantifier)
{

	// set the logfile_prefix appropriately
	logfile_prefix = original_logfile_prefix; 
				
	char quantifier_block_char[100];
	sprintf(quantifier_block_char, "%d", quantifier_block+1);
	string quantifier_block_string(quantifier_block_char);

	if(TypeOfQuantifier == 'e')
	{
		logfile_prefix += "exists_";
	}
	else
	{
		logfile_prefix += "forall_";
	}

	logfile_prefix += quantifier_block_string;
	logfile_prefix += "_";

	// change the benchmark_name appropriately
	benchmark_name = original_benchmark_name;	
	if(TypeOfQuantifier == 'e')
	{
		benchmark_name += "_exists_";
	}
	else
	{
		benchmark_name += "_forall_";
	}
	benchmark_name += quantifier_block_string;

	// initialize the times
	unsigned long long int total_duration_ms;
	struct timeval total_start_ms, total_finish_ms;
	gettimeofday (&total_start_ms, NULL); 


	// initialize the details.txt file
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


	// restart the timeout settings
	if(time_out_enabled)
	{
		time_t elim_start_time;
		time(&elim_start_time);
		time_out_start = elim_start_time;
	}

	// both CEGAR and MONOLITHIC are in factorizedSkolemFunctionGenerator
	list<string> VariablesToEliminate_Copy;
	VariablesToEliminate_Copy = VariablesToEliminate;

	factorizedSkolemFunctionGenerator(Factors, VariablesToEliminate_Copy);

	if(time_out_enabled && timed_out)
	{
		cout << "\nTime-out from skolem-function generator\n";
	}

	// printing the statitics
	gettimeofday (&total_finish_ms, NULL);
	total_duration_ms = total_finish_ms.tv_sec * 1000 + total_finish_ms.tv_usec / 1000;
	total_duration_ms -= total_start_ms.tv_sec * 1000 + total_start_ms.tv_usec / 1000;

	assert(problem_kind == "variable_elimination"); 
	
	total_duration_ms = total_duration_ms - total_time_in_compute_size;
	

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
				
				
	if(enable_cegar)
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

	if(enable_cegar && perform_reverse_substitution)
	{
		fprintf(record_fp, "\nnumber-of-composes-in-reverse-substitution = %d", number_of_compose_operations_for_variable);
		fprintf(record_fp, "\nfinal-skolem-function-sizes = ");
		for(list<int>::iterator sfs_it = skolem_function_sizes_after_reverse_substitution.begin(); sfs_it != skolem_function_sizes_after_reverse_substitution.end(); sfs_it++)
		{
			fprintf(record_fp, "%d, ", *sfs_it);
		}
	}
	else if(perform_reverse_substitution)
	{
		fprintf(record_fp, "\ncompose-in-reverse-substitution = %d", number_of_compose_operations_for_variable);
		fprintf(record_fp, "\ntime-in-reverse-substitution = %llu", ComposeTime);
		fprintf(record_fp, "\nfinal-skolem-function-sizes = ");
		for(list<int>::iterator sfs_it = skolem_function_sizes_after_reverse_substitution.begin(); sfs_it != skolem_function_sizes_after_reverse_substitution.end(); sfs_it++)
		{
			fprintf(record_fp, "%d, ", *sfs_it);
		}
	}
	else
	{
		fprintf(record_fp, "\ncompose-in-reverse-substitution = -");
		fprintf(record_fp, "\ntime-in-reverse-substitution = -");
		fprintf(record_fp, "\nfinal-skolem-function-sizes = -");
	}
	
	fclose(record_fp);

	if(!use_bloqqer)
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
			fprintf(plot_fp, "\t%f\t%f", (float)sum_of_number_of_factors_containing_variable/(float)(number_of_vars_to_elim), (float)sum_of_skolem_function_sizes/(float)(number_of_vars_to_elim));						
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
			fprintf(plot_fp, "%d\t%llu\t%f\t%s\t%llu\t", cegar_iteration_number, total_time_in_reverse_substitution_in_cegar, (float)sum_of_skolem_function_sizes_after_reverse_substitution/(float)(number_of_vars_to_elim), order_string_to_print.c_str(), total_time_in_ordering);
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

	Aig_ManShow(pub_aig_manager, 0, NULL); 
	#endif


	// get the Skolem functions in a map
	for(list<string>::iterator list_it = VariablesToEliminate.begin(); list_it != VariablesToEliminate.end(); list_it++)
	{
		string variable_to_eliminate = *list_it;
		int index_of_variable_to_eliminate = searchVarNameToVarIndexMap(var_name_to_var_index_map, variable_to_eliminate);
		Aig_Obj_t* skolem_function;
			
		if(index_of_variable_to_eliminate == -1) // Factors free of variable_to_eliminate
		{
			skolem_function = createTrue(pub_aig_manager);
			assert(skolem_function != NULL);
		}
		else
		{
			skolem_function = searchOneDimensionalMatrix(SkolemFunctions, number_of_vars_to_elim, index_of_variable_to_eliminate);
			assert(skolem_function != NULL);		
		}

		variable_to_skolem_function_map.insert(make_pair(variable_to_eliminate, skolem_function));		
	}

	clearAllDataStructures();	
}



void AIGBasedSkolem::recreateCiMaps(list<string> &VariablesToEliminate)
{
	// recreate the Ci_... maps
	Ci_id_to_Ci_name_map.clear();
	for(map<int, string>::iterator map_it = initial_Ci_id_to_Ci_name_map.begin(); map_it != initial_Ci_id_to_Ci_name_map.end(); map_it++)
	{
		Ci_id_to_Ci_name_map.insert(make_pair(map_it->first, map_it->second));
	}

	Ci_name_to_Ci_number_map.clear();
	for(map<string, int>::iterator map_it = initial_Ci_name_to_Ci_number_map.begin(); map_it != initial_Ci_name_to_Ci_number_map.end(); map_it++)
	{
		Ci_name_to_Ci_number_map.insert(make_pair(map_it->first, map_it->second));
	}

	Ci_name_to_Ci_object_map.clear();
	for(map<string, Aig_Obj_t*>::iterator map_it = initial_Ci_name_to_Ci_object_map.begin(); map_it != initial_Ci_name_to_Ci_object_map.end(); map_it++)
	{
		Ci_name_to_Ci_object_map.insert(make_pair(map_it->first, map_it->second));
	}

	number_of_Cis = initial_number_of_Cis;

	// recreate Ci_to_eliminate_name_to_Ci_to_eliminate_object_map
	Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.clear();
	for(list<string>::iterator VariablesToEliminate_it = VariablesToEliminate.begin(); VariablesToEliminate_it != VariablesToEliminate.end(); VariablesToEliminate_it++)
	{
		string variable_to_eliminate = *VariablesToEliminate_it;
		
		map<string, Aig_Obj_t*>::iterator Ci_name_to_Ci_object_map_it = Ci_name_to_Ci_object_map.find(variable_to_eliminate);
		assert(Ci_name_to_Ci_object_map_it != Ci_name_to_Ci_object_map.end());

		Aig_Obj_t* variable_to_eliminate_obj = Ci_name_to_Ci_object_map_it->second;

		Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.insert(make_pair(variable_to_eliminate, variable_to_eliminate_obj));
	}

	// some maps are to be cleared
	aig_bad_set = NULL;
	B_i_index_to_B_i_object_map.clear();
	connection_string_to_connection_object_map.clear();
	Ci_to_eliminate_renamed_to_Ci_to_eliminate_renamed_object_map.clear();
	Ci_to_eliminate_renamed_name_to_Ci_to_eliminate_renamed_object_map.clear();
	
}



void AIGBasedSkolem::satisfiableBenchmarkGeneration(set<Aig_Obj_t*> &transition_function_factors, map<string, Aig_Obj_t*> &output_string_to_transition_function_parts, list<string> &VariablesToEliminate)
{
	int number_of_variables_to_eliminate = VariablesToEliminate.size();
	int original_no_of_cis = number_of_Cis;
		
	assert(!transition_function_factors.empty()); // each element is x_i' \equiv f_i(X, I)
	assert(!output_string_to_transition_function_parts.empty()); // each element is string x_i' \mapsto f_i(X, I)
	
	map<string, Aig_Obj_t*> variable_to_skolem_function_map; // This stores I_i ---> some (complex) formula
	int toggle_counter = 1; // to decide whether to use true/false
	for(list<string>::iterator list_it = VariablesToEliminate.begin(); list_it != VariablesToEliminate.end(); list_it++)
	{
		string variable_to_eliminate = *list_it;

		Aig_Obj_t* skolem_function;

		if(toggle_counter % 2 == 1)
		{
			cout << endl << variable_to_eliminate << " ---> true\n";

			skolem_function = createTrue(pub_aig_manager);
		}
		else
		{
			if(make_alternate_entries_toggle_in_initial_variable_to_skolem_function_map)
			{
				skolem_function = createFalse(pub_aig_manager);
				cout << endl << variable_to_eliminate << " ---> false\n";
			}
			else
			{
				skolem_function = createTrue(pub_aig_manager);
				cout << endl << variable_to_eliminate << " ---> true\n";
			}
		}

		assert(skolem_function != NULL);

		variable_to_skolem_function_map.insert(make_pair(variable_to_eliminate, skolem_function));			

		toggle_counter++;
	}
	
	// let's see output_string_to_transition_function_parts
	#ifdef DEBUG_SKOLEM
	cout << "\noutput_string_to_transition_function_parts\n";
	for(map<string, Aig_Obj_t*>::iterator map_it = output_string_to_transition_function_parts.begin(); map_it != output_string_to_transition_function_parts.end(); map_it++)
	{
		cout << endl << map_it->first << "\t" << map_it->second << endl;
		string transition_function_part_file_name = benchmark_name_without_extension;
		transition_function_part_file_name += "_";
		transition_function_part_file_name += map_it->first;
		transition_function_part_file_name += "_transition_function_part";
		writeFormulaToFile(pub_aig_manager, map_it->second, transition_function_part_file_name, ".v", 0, 0);
	}	
	#endif

	Aig_Obj_t* full_transition_function_part = NULL;

	map<Aig_Obj_t*, Aig_Obj_t*> input_object_to_transition_function_parts;
	for(map<string, Aig_Obj_t*>::iterator map_it = output_string_to_transition_function_parts.begin(); map_it != output_string_to_transition_function_parts.end(); map_it++)
	{
		string latchout_name = map_it->first;
		int index_of_uscore = latchout_name.find_last_of("_");
	       	string latchout_part = latchout_name.substr(0, index_of_uscore);
		assert(latchout_part == "LATCHOUT");
		string location_str = latchout_name.substr(index_of_uscore+1);
		
		string latchin_name = "LATCHIN_";
		latchin_name += location_str;
	
		map<string, Aig_Obj_t*>::iterator Ci_name_to_Ci_object_map_it = Ci_name_to_Ci_object_map.find(latchin_name);
		assert(Ci_name_to_Ci_object_map_it != Ci_name_to_Ci_object_map.end());
		Aig_Obj_t* input_object = Ci_name_to_Ci_object_map_it->second;
		assert(input_object != NULL);
		
		input_object_to_transition_function_parts.insert(make_pair(input_object, map_it->second));

		if(make_variable_to_skolem_function_map_complex && function_to_make_variable_to_skolem_function_map_complex == "F")
		{
			if(full_transition_function_part == NULL)
			{
				full_transition_function_part = map_it->second;
			}
			else
			{
				full_transition_function_part = createAnd(full_transition_function_part, map_it->second, pub_aig_manager);
			}
		}
	}		

	#ifdef DEBUG_SKOLEM
	cout << "\ninput_object_to_transition_function_parts\n";
	int file_counter = 1;
	for(map<Aig_Obj_t*, Aig_Obj_t*>::iterator map_it = input_object_to_transition_function_parts.begin(); map_it != input_object_to_transition_function_parts.end(); map_it++)
	{
		string transition_function_part_file_name = benchmark_name_without_extension;
		transition_function_part_file_name += "_transition_function_part";
		writeFormulaToFile(pub_aig_manager, map_it->second, transition_function_part_file_name, ".v", 0, file_counter);

		string transition_function_name_file_name = benchmark_name_without_extension;
		transition_function_name_file_name += "_transition_function_name";
		writeFormulaToFile(pub_aig_manager, map_it->first, transition_function_name_file_name, ".v", 0, file_counter);

		file_counter++;
	}	
	#endif

	if(make_initial_variable_to_skolem_function_map_a_formula)
	{
		map<Aig_Obj_t*, Aig_Obj_t*>::iterator input_object_to_transition_function_parts_it = input_object_to_transition_function_parts.begin();		

		for(map<string, Aig_Obj_t*>::iterator initial_variable_to_skolem_function_map_it = variable_to_skolem_function_map.begin(); initial_variable_to_skolem_function_map_it != variable_to_skolem_function_map.end(); initial_variable_to_skolem_function_map_it++)
		{	
			if(input_object_to_transition_function_parts_it == input_object_to_transition_function_parts.end()) //end reached; wrap-wround
			{
				input_object_to_transition_function_parts_it = input_object_to_transition_function_parts.begin();
			}

			initial_variable_to_skolem_function_map_it->second = input_object_to_transition_function_parts_it->first;

			// to show the entry
			map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(Aig_ObjId(initial_variable_to_skolem_function_map_it->second));
			assert(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end());
			cout << endl << initial_variable_to_skolem_function_map_it->first << " ---> " << Ci_id_to_Ci_name_map_it->second << endl;
			
			input_object_to_transition_function_parts_it++;			
		}	
	}


	set<Aig_Obj_t*> all_bit_differing_from_cycle_components;
	set<Aig_Obj_t*> all_bit_same_as_true_components;

	int part_number = 1;
	int number_of_parts = input_object_to_transition_function_parts.size();

	map<string, Aig_Obj_t*>::iterator variable_to_skolem_function_map_it = variable_to_skolem_function_map.begin();
	assert(variable_to_skolem_function_map_it != variable_to_skolem_function_map.end());
	bool end_of_variable_to_skolem_function_map_reached = false;
	int location_in_variable_to_skolem_function_map = 1;

	for(map<Aig_Obj_t*, Aig_Obj_t*>::iterator map_it = input_object_to_transition_function_parts.begin(); map_it != input_object_to_transition_function_parts.end(); map_it++)
	{
		Aig_Obj_t* transition_function_part = map_it->second; // f_i(X, I)
		Aig_Obj_t* transition_function_name = map_it->first; // x_i

		#ifdef DEBUG_SKOLEM
		// Just see the sizes of elements in variable_to_skolem_function_map
		cout << endl << "variable_to_skolem_function_map";
		for(map<string, Aig_Obj_t*>::iterator variable_to_skolem_function_map_it2 = variable_to_skolem_function_map.begin(); variable_to_skolem_function_map_it2 != variable_to_skolem_function_map.end(); variable_to_skolem_function_map_it2++)
		{
			cout << endl <<  variable_to_skolem_function_map_it2->first << "\t" << computeSize(variable_to_skolem_function_map_it2->second, pub_aig_manager);
		}
		cout << endl;
		#endif


		Aig_Obj_t* transition_function_part_after_replacement;
		transition_function_part_after_replacement = replaceVariablesByFormulas(transition_function_part, variable_to_skolem_function_map); // replace I in f_i(X, I) by corresponding formulae in map, initially all true's
		assert(transition_function_part_after_replacement != NULL); // f_i(x, true)

		cout << "\nSize of transition_function_part_after_replacement = " << computeSize(transition_function_part_after_replacement, pub_aig_manager) << endl;


		Aig_Obj_t* full_transition_function_part_after_replacement;
		if(make_variable_to_skolem_function_map_complex && function_to_make_variable_to_skolem_function_map_complex == "F")
		{
			full_transition_function_part_after_replacement = replaceVariablesByFormulas(full_transition_function_part, variable_to_skolem_function_map); // replace I in f_i(X, I)\wedge ... \wedge f_n(X, I) by corresponding formulae in map
			assert(full_transition_function_part_after_replacement != NULL); 

			cout << "\nSize of full_transition_function_part_after_replacement = " << computeSize(full_transition_function_part_after_replacement, pub_aig_manager) << endl;
			if(full_transition_function_part_after_replacement == createFalse(pub_aig_manager))
			{
				cout << "\nfull_transition_function_part_after_replacement is False\n";
			}
			else if(full_transition_function_part_after_replacement == createTrue(pub_aig_manager))
			{
				cout << "\nfull_transition_function_part_after_replacement is True\n";
			}
		}


		if(make_variable_to_skolem_function_map_complex && !end_of_variable_to_skolem_function_map_reached)
		{
			variable_to_skolem_function_map_it++;
			location_in_variable_to_skolem_function_map++;

			if(variable_to_skolem_function_map_it != variable_to_skolem_function_map.end())
			{
				if(function_to_make_variable_to_skolem_function_map_complex == "F")
				{
					variable_to_skolem_function_map_it->second = full_transition_function_part_after_replacement;
				}
				else
				{
					variable_to_skolem_function_map_it->second = transition_function_part_after_replacement;
				}

				cout << "\nlocation " << location_in_variable_to_skolem_function_map << "in variable_to_skolem_function_map changed\n";
			}
			else
			{
				// we have reached at the end of map
				end_of_variable_to_skolem_function_map_reached = true;

				cout << "\nwe have reached at the end of map; we will start from the beginning\n";
				variable_to_skolem_function_map_it = variable_to_skolem_function_map.begin();
				location_in_variable_to_skolem_function_map = 1;

				if(function_to_make_variable_to_skolem_function_map_complex == "F")
				{
					variable_to_skolem_function_map_it->second = full_transition_function_part_after_replacement;
				}
				else
				{
					variable_to_skolem_function_map_it->second = transition_function_part_after_replacement;
				}

				cout << "\nlocation " << location_in_variable_to_skolem_function_map << "in variable_to_skolem_function_map changed\n";
				end_of_variable_to_skolem_function_map_reached = false;
				
			}
		}

		Aig_Obj_t* single_bit_same_as_true_component;
		single_bit_same_as_true_component = createEquivalence(transition_function_part_after_replacement, transition_function_name, pub_aig_manager);
		assert(single_bit_same_as_true_component != NULL); // f_i(X, true) \equiv x_i

		if(limit_on_number_of_extra_conjuncts == -1)
		{
			all_bit_same_as_true_components.insert(single_bit_same_as_true_component);
		}
		else if(part_number <= limit_on_number_of_extra_conjuncts)
		{
			cout << endl << "factor_" << part_number << " added\n";
			all_bit_same_as_true_components.insert(single_bit_same_as_true_component);
		}
		else
		{
			cout << endl << "factor_" << part_number << " NOT added\n";
		}

		Aig_Obj_t* single_bit_differing_from_cycle_component;
		single_bit_differing_from_cycle_component = createEquivalence(transition_function_part, transition_function_name, pub_aig_manager);
		assert(single_bit_differing_from_cycle_component != NULL); // f_i(X, I) \equiv x_i


		Aig_Obj_t* all_bit_differing_from_cycle_component = createNot(single_bit_differing_from_cycle_component, pub_aig_manager);
		assert(all_bit_differing_from_cycle_component != NULL); // f_i(X, I) \neq x_i

		all_bit_differing_from_cycle_components.insert(all_bit_differing_from_cycle_component);

		part_number++;
	}

	Aig_Obj_t* all_bit_same_as_true;

	if(all_bit_same_as_true_components.empty())
	{
		all_bit_same_as_true = createFalse(pub_aig_manager);
	}
	else
	{
		all_bit_same_as_true = createAnd(all_bit_same_as_true_components, pub_aig_manager);
	}

	// (f_1(X, true) \equiv x_1 \wedge ... \wedge f_n(X, true) \equiv x_n)
	assert(all_bit_same_as_true != NULL); 

	#ifdef DEBUG_SKOLEM
	string all_bit_same_as_true_file_name = benchmark_name_without_extension;
	all_bit_same_as_true_file_name += "_all_bit_same_as_true";
	writeFormulaToFile(pub_aig_manager, all_bit_same_as_true, all_bit_same_as_true_file_name, ".v", 0, 0);
	#endif

	int fresh_count = 1;
	int no_of_cis_with_f_variables = number_of_Cis;

	set<Aig_Obj_t*> all_bit_differing_from_cycle_tseitin_components;
	set<Aig_Obj_t*> fresh_objects_for_all_bit_differing_from_cycle_tseitin_components;
	for(set<Aig_Obj_t*>::iterator all_bit_differing_from_cycle_components_it = all_bit_differing_from_cycle_components.begin(); all_bit_differing_from_cycle_components_it != all_bit_differing_from_cycle_components.end(); all_bit_differing_from_cycle_components_it++)
	{
		Aig_Obj_t* all_bit_differing_from_cycle_component = *all_bit_differing_from_cycle_components_it;
		Aig_Obj_t* fresh_object = Aig_ObjCreateCi(pub_aig_manager);	
		assert(fresh_object != NULL);
		fresh_objects_for_all_bit_differing_from_cycle_tseitin_components.insert(fresh_object);

		char fresh_count_char[100];
		sprintf(fresh_count_char, "%d", fresh_count);
		string fresh_count_string(fresh_count_char);
		string fresh_object_string = "g_";
		fresh_object_string += fresh_count_string;
		fresh_count++;

		int fresh_object_id = Aig_ObjId(fresh_object); 
		Ci_id_to_Ci_name_map.insert(make_pair(fresh_object_id, fresh_object_string));
		Ci_name_to_Ci_number_map.insert(make_pair(fresh_object_string, number_of_Cis));	
		number_of_Cis++;

		Aig_Obj_t* all_bit_differing_from_cycle_tseitin_component = createEquivalence(fresh_object, all_bit_differing_from_cycle_component, pub_aig_manager);
		assert(all_bit_differing_from_cycle_tseitin_component != NULL); 
		all_bit_differing_from_cycle_tseitin_components.insert(all_bit_differing_from_cycle_tseitin_component);
	}

	if(extend_tsietin_encoding_to_extra_part)
	{
		Aig_Obj_t* fresh_object = Aig_ObjCreateCi(pub_aig_manager);	
		assert(fresh_object != NULL);
		fresh_objects_for_all_bit_differing_from_cycle_tseitin_components.insert(fresh_object);

		char fresh_count_char[100];
		sprintf(fresh_count_char, "%d", fresh_count);
		string fresh_count_string(fresh_count_char);
		string fresh_object_string = "g_";
		fresh_object_string += fresh_count_string;
		fresh_count++;

		int fresh_object_id = Aig_ObjId(fresh_object); 
		Ci_id_to_Ci_name_map.insert(make_pair(fresh_object_id, fresh_object_string));
		Ci_name_to_Ci_number_map.insert(make_pair(fresh_object_string, number_of_Cis));	
		number_of_Cis++;

		Aig_Obj_t* all_bit_same_as_true_component = createEquivalence(fresh_object, all_bit_same_as_true, pub_aig_manager);
		assert(all_bit_same_as_true_component != NULL); 
		all_bit_differing_from_cycle_tseitin_components.insert(all_bit_same_as_true_component);
	}

	int total_no_of_cis = number_of_Cis;

	assert(fresh_objects_for_all_bit_differing_from_cycle_tseitin_components.size() > 0);
	Aig_Obj_t* all_bit_differing_from_cycle_tseitin_component = createOr(fresh_objects_for_all_bit_differing_from_cycle_tseitin_components, pub_aig_manager);
	assert(all_bit_differing_from_cycle_tseitin_component != NULL); 
	all_bit_differing_from_cycle_tseitin_components.insert(all_bit_differing_from_cycle_tseitin_component);

	assert(all_bit_differing_from_cycle_tseitin_components.size() > 0);

	cout << "\nNumber of top-level conjuncts = " << all_bit_differing_from_cycle_tseitin_components.size() << endl;

	Aig_Obj_t* all_bit_differing_from_cycle_tseitin = createAnd(all_bit_differing_from_cycle_tseitin_components, pub_aig_manager);
	assert(all_bit_differing_from_cycle_tseitin != NULL);

	if(!extend_tsietin_encoding_to_extra_part)
	{
		// disjoin this with all_bit_same_as_true
		all_bit_differing_from_cycle_tseitin = createOr(all_bit_differing_from_cycle_tseitin, all_bit_same_as_true, pub_aig_manager);
	}

	#ifdef DEBUG_SKOLEM
	string all_bit_differing_from_cycle_tseitin_file_name = benchmark_name_without_extension;
	all_bit_differing_from_cycle_tseitin_file_name += "_all_bit_differing_from_cycle_tseitin";
	writeFormulaToFile(pub_aig_manager, all_bit_differing_from_cycle_tseitin, all_bit_differing_from_cycle_tseitin_file_name, ".v", 0, 0);
	#endif

	
	// Printing in files	
	
	Aig_Obj_t* all_bit_differing_from_cycle_tseitin_CO;
	all_bit_differing_from_cycle_tseitin_CO = Aig_ObjCreateCo( pub_aig_manager, all_bit_differing_from_cycle_tseitin );
	assert(all_bit_differing_from_cycle_tseitin_CO != NULL);

	Aig_Man_t* all_bit_differing_from_cycle_tseitin_aig_manager;
	all_bit_differing_from_cycle_tseitin_aig_manager = simplifyUsingConeOfInfluence( pub_aig_manager, Aig_ManCoNum(pub_aig_manager)-1, 1 );
	assert(all_bit_differing_from_cycle_tseitin_aig_manager != NULL);

	char pname[100];
	char verilog_file_char[100];

	char limit_on_number_of_extra_conjuncts_char[100];
	sprintf(limit_on_number_of_extra_conjuncts_char, "%d", limit_on_number_of_extra_conjuncts);
	string limit_on_number_of_extra_conjuncts_string(limit_on_number_of_extra_conjuncts_char);

	string verilog_file = benchmark_name_without_extension;
	verilog_file += "_sat_";

	if(make_variable_to_skolem_function_map_complex)
	{
		if(function_to_make_variable_to_skolem_function_map_complex == "F")
		{
			verilog_file += "F_";
		}
		
	}
	else
	{
		verilog_file += "simple_";
	}

	if(make_initial_variable_to_skolem_function_map_a_formula)
	{
		verilog_file += "init_formula_";
	}

	verilog_file += limit_on_number_of_extra_conjuncts_string;
	
	if(extend_tsietin_encoding_to_extra_part)
	{
		verilog_file += "_flattened";
	}

	verilog_file += "_extra_bit_differing_from_cycle_tseitin";
	strcpy(pname, verilog_file.c_str());
	all_bit_differing_from_cycle_tseitin_aig_manager->pName = pname;
	verilog_file += ".v";
	strcpy(verilog_file_char, verilog_file.c_str());
	writeCombinationalCircuitInVerilog(all_bit_differing_from_cycle_tseitin_aig_manager, number_of_variables_to_eliminate, original_no_of_cis, no_of_cis_with_f_variables, total_no_of_cis, verilog_file_char,  true);
	cout << "\nBenchmark file " << verilog_file << " written\n";	
}




Aig_Obj_t* AIGBasedSkolem::obtainEdgeToFailStates(Aig_Obj_t* failure_condition_aig, map<Aig_Obj_t*, Aig_Obj_t*> &Output_Object_to_RHS_of_Factors)
{
	assert(failure_condition_aig != NULL);
	map<string, Aig_Obj_t*> replacement_map;

	for(map<Aig_Obj_t*, Aig_Obj_t*>::iterator map_it = Output_Object_to_RHS_of_Factors.begin(); map_it != Output_Object_to_RHS_of_Factors.end(); map_it++)
	{
		Aig_Obj_t* output_object = map_it->first;
		Aig_Obj_t* rhs = map_it->second;		

		int output_id = Aig_ObjId(output_object); 
		map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(output_id);
		assert(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end());
		string output_name = Ci_id_to_Ci_name_map_it->second;

		#ifdef DEBUG_SKOLEM
		cout << "\noutput_name = " << output_name << "\tsize of rhs = " << computeSize(rhs, pub_aig_manager) << endl;
		#endif

		int index_of_uscore = output_name.find_last_of("_");
	       	string latchout_part = output_name.substr(0, index_of_uscore);
		assert(latchout_part == "LATCHOUT");
		string location_str = output_name.substr(index_of_uscore+1);
		
		string latchin_name = "LATCHIN_";
		latchin_name += location_str;

		#ifdef DEBUG_SKOLEM
		cout << "\nlatchin_name = " << latchin_name << endl;
		string rhs_file_name = benchmark_name_without_extension;
		rhs_file_name += "_";
		rhs_file_name += latchin_name;
		rhs_file_name += "_rhs";
		writeFormulaToFile(pub_aig_manager, rhs, rhs_file_name, ".v", 0, 0);
		#endif

		replacement_map.insert(make_pair(latchin_name, rhs));
	}

	// Avoid unncessary entries from replacement_map
	#ifdef DEBUG_SKOLEM
	showReplacementMap(replacement_map, "replacement_map", 1);
	#endif

	map<string, Aig_Obj_t*> optimized_replacement_map;
	optimizeReplacementMap(replacement_map, failure_condition_aig, optimized_replacement_map);

	#ifdef DEBUG_SKOLEM
	showReplacementMap(optimized_replacement_map, "optimized_replacement_map", 2);
	#endif
		

	Aig_Obj_t* failure_condition_aig_after_replacement;
	//failure_condition_aig_after_replacement = replaceVariablesByFormulas(failure_condition_aig, optimized_replacement_map);
	failure_condition_aig_after_replacement = ReplaceLeavesByExpressionsConcurrently(pub_aig_manager, failure_condition_aig, optimized_replacement_map);
	assert(failure_condition_aig_after_replacement != NULL);

	#ifdef DEBUG_SKOLEM
	string failure_condition_aig_file_name = benchmark_name_without_extension;
	failure_condition_aig_file_name += "_failure_condition_aig";
	writeFormulaToFile(pub_aig_manager, failure_condition_aig, failure_condition_aig_file_name, ".v", 0, 0);
	
	string failure_condition_aig_after_replacement_file_name = benchmark_name_without_extension;
	failure_condition_aig_after_replacement_file_name += "_failure_condition_aig_after_replacement";
	writeFormulaToFile(pub_aig_manager, failure_condition_aig_after_replacement, failure_condition_aig_after_replacement_file_name, ".v", 0, 0);
	#endif

	return failure_condition_aig_after_replacement;
}


void AIGBasedSkolem::callMonoSkolem(call_type original_polarity, Aig_Obj_t* original_formula, call_type polarity, Aig_Obj_t* formula, int depth_from_root)
{
	number_of_monoskolem_calls_on_arbitrary_boolean_formulas++;

	#ifdef DETAILED_RECORD_KEEP
	struct timeval callmonoskolem_step_start_ms, callmonoskolem_step_finish_ms;
	unsigned long long int callmonoskolem_time;
	int max_r1_size = -1, max_r0_size = -1;
	int min_r1_size = -1, min_r0_size = -1;
	int total_r1_size = 0, total_r0_size = 0;
	int r1_size, r0_size;

	gettimeofday (&callmonoskolem_step_start_ms, NULL); 
	#endif

	// final_formula = polarity.formula
	Aig_Obj_t* final_formula;
	if(polarity == negated)
	{
		final_formula = createNot(formula, pub_aig_manager);
	}
	else //polarity == original
	{
		final_formula = formula;
	}
	assert(final_formula != NULL);

	// Let's find the variables to eliminate actually occuring in the formula
	set<string> support_final_formula;
	computeSupport(final_formula, support_final_formula, pub_aig_manager);
	set<string> varstoelim_in_final_formula;
	set_intersection(support_final_formula.begin(), support_final_formula.end(), Global_VariablesToEliminate_Set.begin(), Global_VariablesToEliminate_Set.end(),inserter(varstoelim_in_final_formula, varstoelim_in_final_formula.begin()));

	vector<Aig_Obj_t*> list_of_r1s; // list of r1's of variables to eliminate (order is as in Global_VariablesToEliminate)
	vector<Aig_Obj_t*> list_of_r0s; // list of r0's of variables to eliminate (order is as in Global_VariablesToEliminate)
	
	// Get the cannot be one sets, and cannot be zero sets
	for(list<string>::iterator list_it = Global_VariablesToEliminate.begin(); list_it != Global_VariablesToEliminate.end(); list_it++)
	{
		string variable_to_eliminate = *list_it;

		#ifdef DEBUG_SKOLEM
		cout << "\nvariable_to_eliminate = " << variable_to_eliminate << endl;
		#endif

		Aig_Obj_t* cannot_be_one_function; // ~final_formula [ variable_to_eliminate --> 1]
		Aig_Obj_t* cannot_be_zero_function; // ~final_formula [ variable_to_eliminate --> 0]
		Aig_Obj_t* skolem_function; // final_formula [ variable_to_eliminate --> 1]

		Aig_Obj_t* constant_zero;
		constant_zero = createFalse(pub_aig_manager); 
		assert(constant_zero != NULL);

		Aig_Obj_t* constant_one;
		constant_one = createTrue(pub_aig_manager); 
		assert(constant_one != NULL);

		skolem_function = ReplaceLeafByExpression(final_formula, variable_to_eliminate, constant_one, pub_aig_manager); 
		assert(skolem_function != NULL);

		cannot_be_one_function = createNot(skolem_function, pub_aig_manager); 
		assert(cannot_be_one_function != NULL);

		cannot_be_zero_function = createNot(ReplaceLeafByExpression(final_formula, variable_to_eliminate, constant_zero, pub_aig_manager), pub_aig_manager); 
		assert(cannot_be_zero_function != NULL);

		// connect to some output to avoid unwanted deletion
		Aig_Obj_t* cannot_be_one_function_CO = Aig_ObjCreateCo(pub_aig_manager, cannot_be_one_function ); 
		assert(cannot_be_one_function_CO != NULL);
		r1r0_cos_created.insert(cannot_be_one_function_CO);

		Aig_Obj_t* cannot_be_zero_function_CO = Aig_ObjCreateCo(pub_aig_manager, cannot_be_zero_function ); 
		assert(cannot_be_zero_function_CO != NULL);
		r1r0_cos_created.insert(cannot_be_zero_function_CO);			
			
		Aig_Obj_t* skolem_function_CO = Aig_ObjCreateCo(pub_aig_manager, skolem_function ); 
		assert(skolem_function_CO != NULL);
		intermediate_cos_created.insert(skolem_function_CO);

		list_of_r1s.push_back(cannot_be_one_function);
		list_of_r0s.push_back(cannot_be_zero_function);

		#ifdef DETAILED_RECORD_KEEP

		#ifdef PERFORM_SIZE_COMPUTATIONS_IN_PAR
		r1_size = computeSize(cannot_be_one_function, pub_aig_manager);
		r0_size = computeSize(cannot_be_zero_function, pub_aig_manager);
		#else
		r1_size = 0;
		r0_size = 0;
		#endif

		total_r1_size = total_r1_size + r1_size;
		total_r0_size = total_r0_size + r0_size;

		if(max_r1_size == -1)
		{
			max_r1_size = r1_size;
		}
		else if(max_r1_size < r1_size)
		{
			max_r1_size = r1_size;
		}
		if(max_r0_size == -1)
		{
			max_r0_size = r0_size;
		}
		else if(max_r0_size < r0_size)
		{
			max_r0_size = r0_size;
		}
		
				
		if(min_r1_size == -1)
		{
			min_r1_size = r1_size;
		}
		else if(min_r1_size > r1_size)
		{
			min_r1_size = r1_size;
		}
		if(min_r0_size == -1)
		{
			min_r0_size = r0_size;
		}
		else if(min_r0_size > r0_size)
		{
			min_r0_size = r0_size;
		}
		#endif


		#ifdef DEBUG_SKOLEM
		string cannot_be_one_file_name = "r1_";
		string cannot_be_zero_file_name = "r0_";
		
		char formula_char[100];
		sprintf(formula_char, "%p", formula);
		string formula_string(formula_char);
		if(polarity == negated)
		{
			formula_string += "n";
		}
		else
		{
			formula_string += "o";
		}

		cannot_be_one_file_name += formula_string;
		cannot_be_one_file_name += "_";
		cannot_be_zero_file_name += formula_string;
		cannot_be_zero_file_name += "_";
		
		cannot_be_one_file_name += variable_to_eliminate;
		cannot_be_one_file_name += ".v";
		cannot_be_zero_file_name += variable_to_eliminate;
		cannot_be_zero_file_name += ".v";

		writeFormulaToFile(pub_aig_manager, cannot_be_one_function, cannot_be_one_file_name);
		writeFormulaToFile(pub_aig_manager, cannot_be_zero_function, cannot_be_zero_file_name);
		#endif

		if(varstoelim_in_final_formula.find(variable_to_eliminate) != varstoelim_in_final_formula.end())
		{
			final_formula = ReplaceLeafByExpression(final_formula, variable_to_eliminate, skolem_function, pub_aig_manager);
			assert(final_formula != NULL); 
		}
		// otherwise don't change the final formula, as \exists variable_to_eliminate. (final_formula) is 
		// final_formula
		
	}// for each variable ends here

	// Enter into hash tables the entries
	// (polarity, formula) --> list_of_r1s and (polarity, formula) --> list_of_r0s
	// (original_polarity, original_formula) --> list_of_r1s and 
	// (original_polarity, original_formula) --> list_of_r0s

	insertIntoR0HashTable(polarity, formula, list_of_r0s);
	insertIntoR1HashTable(polarity, formula, list_of_r1s);
	
	if(polarity != original_polarity || formula != original_formula)
	{
		insertIntoR0HashTable(original_polarity, original_formula, list_of_r0s);
		insertIntoR1HashTable(original_polarity, original_formula, list_of_r1s);		
	}

	#ifdef DETAILED_RECORD_KEEP
	gettimeofday (&callmonoskolem_step_finish_ms, NULL);
	callmonoskolem_time = callmonoskolem_step_finish_ms.tv_sec * 1000 + callmonoskolem_step_finish_ms.tv_usec / 1000;
	callmonoskolem_time -= callmonoskolem_step_start_ms.tv_sec * 1000 + callmonoskolem_step_start_ms.tv_usec / 1000;
	
	total_time_in_callmonolithic = total_time_in_callmonolithic + callmonoskolem_time;

	string record_file;
	record_file = logfile_prefix;
	record_file += "skolem_function_generation_details.txt";
	FILE* record_fp = fopen(record_file.c_str(), "a+");
	assert(record_fp != NULL);

	if(!mask_printing_details_file)
	{
		fprintf(record_fp, "\nDetails of MonoSkolem Call#:%d(Depth from root = %d)\nTime = %llu\nmax r1 size = %d\tmin r1 size = %d\tavg r1 size = %f\nmax r0 size = %d\tmin r0 size = %d\tavg r0 size = %f\n", number_of_monoskolem_calls_on_arbitrary_boolean_formulas, depth_from_root, callmonoskolem_time, max_r1_size, min_r1_size, (float)total_r1_size/(float)Global_VariablesToEliminate_Set.size(), max_r0_size, min_r0_size, (float)total_r0_size/(float)Global_VariablesToEliminate_Set.size());
	}

	fclose(record_fp);	
	#endif

	if(prove_correctness_of_skolem_functions_of_arbitrary_boolean_formula_detailed_check)
	{
		// Create the Skolem functions			
		
		assert(list_of_r1s.size() == Global_VariablesToEliminate.size());

		vector<Aig_Obj_t*> skolem_functions_of_formula;
		for(int i = 0; i < list_of_r1s.size(); i++)
		{
			Aig_Obj_t* r1_i = list_of_r1s[i];
			assert(r1_i != NULL);

			Aig_Obj_t* skolem_i = createNot(r1_i, pub_aig_manager); 
			assert(skolem_i != NULL);

			skolem_functions_of_formula.push_back(skolem_i);		
		}

		// Perform reverse-substitution
		performReverseSubstitutionOfSkolemFunctions(skolem_functions_of_formula);

		
		// Check for exactness
		// First create F(psi(Y), Y)
		bool ensure_that_skolem_functions_are_on_y = true;
		
		map<string, Aig_Obj_t*> skolem_function_replacement_map;
		int i = 0;
		for(list<string>::iterator list_it = Global_VariablesToEliminate.begin(); list_it != Global_VariablesToEliminate.end(); list_it++)
		{
			string variable_to_eliminate = *list_it;
			
			Aig_Obj_t* skolem_i = skolem_functions_of_formula[i];
			assert(skolem_i != NULL);

			if(ensure_that_skolem_functions_are_on_y)
			{
				set<string> support_skolem_i;
				computeSupport(skolem_i, support_skolem_i, pub_aig_manager);
				
				set<string> varstoelim_in_support_skolem_i;
				set_intersection(support_skolem_i.begin(), support_skolem_i.end(), Global_VariablesToEliminate_Set.begin(), Global_VariablesToEliminate_Set.end(), inserter(varstoelim_in_support_skolem_i, varstoelim_in_support_skolem_i.begin()));

				if(!varstoelim_in_support_skolem_i.empty())				
				{
					cout << "\nSkolem function of variable " << variable_to_eliminate << " involves variables to be eliminated\n";
					assert(false);	
				}
			}

			skolem_function_replacement_map.insert(make_pair(variable_to_eliminate, skolem_i));
				
			i++;
		
		}// for each variable ends here	

		assert(skolem_function_replacement_map.size() > 0);

		Aig_Obj_t* result_of_qe_using_skolem_functions;
		result_of_qe_using_skolem_functions = replaceVariablesByFormulas(final_formula, skolem_function_replacement_map);	
		assert(result_of_qe_using_skolem_functions != NULL); // F(psi(Y), Y)	

		list<string> VariablesToEliminate_Copy;
		VariablesToEliminate_Copy = Global_VariablesToEliminate;

		Aig_Obj_t* equivalence_check; // ~F(psi(Y), Y) \wedge F(X, Y)
		equivalence_check = createAnd(createNot(result_of_qe_using_skolem_functions, pub_aig_manager), final_formula, pub_aig_manager);
		assert(equivalence_check != NULL);

		// Give to SAT-Solver
		unsigned long long int cnf_time;
		int formula_size;
		unsigned long long int simplification_time;
		map<string, int> Model_of_equivalence_check;
		bool result_of_equivalence_check;

		result_of_equivalence_check = isSat(pub_aig_manager, equivalence_check, Model_of_equivalence_check, cnf_time, formula_size, simplification_time);

		if(result_of_equivalence_check)
		{
			cout << "\nexists X.f => f[X --> psi] is NOT valid\n";
			cout << "\nCounterexample is\n";
			displayModelFromSATSolver(Model_of_equivalence_check);			
		}
		else
		{
			cout << "\nexists X.f => f[X --> psi] is valid\n";
		}

		string record_file;
		record_file = logfile_prefix;
		record_file += "skolem_function_generation_details.txt";
		FILE* record_fp = fopen(record_file.c_str(), "a+");
		assert(record_fp != NULL);

		if(result_of_equivalence_check)
		{
			fprintf(record_fp, "\n\nexists X.f(X,Y) = f'(psi,Y) is NOT valid; Skolem functions are NOT exact\n");
		}
		else
		{
			fprintf(record_fp, "\n\nexists X.f(X,Y) = f'(psi,Y) is valid; Skolem functions are exact\n");		

		}

		fclose(record_fp);

		if(result_of_equivalence_check) // not exact
		{
			assert(false);
		}
		
	}


	if(cleanup_after_each_step_in_arbitrary_boolean_combinations)
	{
		string step_name = "callMonoSkolem";
		cleanupAfterEachStepInArbitraryBooleanCombinations(step_name);
	}
	
}


void AIGBasedSkolem::computeCannotBeSetsInsideMonolithic(int var_to_elim_index)
{
	set<Aig_Obj_t*> cannot_be_one_set_for_var_to_elim_index;
	set<Aig_Obj_t*> cannot_be_zero_set_for_var_to_elim_index;

	#ifdef DEBUG_SKOLEM
	cout << "\ncomputing cannot be sets\n";
	#endif

	for(set<int>::iterator factor_it = FactorsWithVariable.begin(); factor_it != FactorsWithVariable.end(); factor_it++)
	{
		int factor_index = *factor_it;

		#ifdef DEBUG_SKOLEM
		cout << "\nfactor_index = " << factor_index << endl;
		#endif

		// Suppose j = factor_index
		// Let's compute ~co-factor-1_i_j and ~co-factor-0_i_j

		Aig_Obj_t* neg_cofactor_1;
		neg_cofactor_1 = computeNegatedCofactorOne(var_to_elim_index, factor_index); 
		assert(neg_cofactor_1 != NULL);
		// connecting to some output to avoid unwanted deletion
		Aig_Obj_t* neg_cofactor_1_CO = Aig_ObjCreateCo(pub_aig_manager, neg_cofactor_1 ); 
		assert(neg_cofactor_1_CO != NULL);	

		Aig_Obj_t* neg_cofactor_0;
		neg_cofactor_0 = computeNegatedCofactorZero(var_to_elim_index, factor_index); 
		assert(neg_cofactor_0 != NULL);	
		// connecting to some output to avoid unwanted deletion
		Aig_Obj_t* neg_cofactor_0_CO = Aig_ObjCreateCo(pub_aig_manager, neg_cofactor_0 ); 
		assert(neg_cofactor_0_CO != NULL);

		string cannot_be_one_string;
		Aig_Obj_t* cannot_be_one_object;
		allocateStringAndObjectToCannotBeDag(1, neg_cofactor_1, cannot_be_one_string, cannot_be_one_object);

		string cannot_be_zero_string;
		Aig_Obj_t* cannot_be_zero_object;
		allocateStringAndObjectToCannotBeDag(0, neg_cofactor_0, cannot_be_zero_string, cannot_be_zero_object);

		#ifdef DEBUG_SKOLEM
		show_cannot_be_string_to_cannot_be_object_map();
		show_cannot_be_object_to_cannot_be_dag_map();
		#endif

		// Insert the objects in respective cannot-be-sets
		cannot_be_one_set_for_var_to_elim_index.insert(cannot_be_one_object);
		cannot_be_zero_set_for_var_to_elim_index.insert(cannot_be_zero_object);

						
	}// for each factor ends here


	map<int, set<Aig_Obj_t*> >::iterator cannot_be_one_set_it = cannot_be_one_set.find(var_to_elim_index);
	assert(cannot_be_one_set_it == cannot_be_one_set.end());
	cannot_be_one_set.insert(make_pair(var_to_elim_index, cannot_be_one_set_for_var_to_elim_index));

	map<int, set<Aig_Obj_t*> >::iterator cannot_be_zero_set_it = cannot_be_zero_set.find(var_to_elim_index);
	assert(cannot_be_zero_set_it == cannot_be_zero_set.end());
	cannot_be_zero_set.insert(make_pair(var_to_elim_index, cannot_be_zero_set_for_var_to_elim_index));
	
}


void AIGBasedSkolem::insertIntoR0HashTable(call_type polarity, Aig_Obj_t* formula, vector<Aig_Obj_t*> &list_of_r0s)
{
	string key;	
	char formula_char[100];
	sprintf(formula_char, "%p", formula);
	string formula_string(formula_char);
	if(polarity == negated)
	{
		formula_string += "n";
	}
	else
	{
		formula_string += "o";
	}
	key = formula_string;

	#ifdef DEBUG_SKOLEM
	cout << "\nInserting entry for " << key << " in R0_map\n";
	#endif

	R0_map.insert(make_pair(key, list_of_r0s));			
}



void AIGBasedSkolem::insertIntoR1HashTable(call_type polarity, Aig_Obj_t* formula, vector<Aig_Obj_t*> &list_of_r1s)
{
	string key;	
	char formula_char[100];
	sprintf(formula_char, "%p", formula);
	string formula_string(formula_char);
	if(polarity == negated)
	{
		formula_string += "n";
	}
	else
	{
		formula_string += "o";
	}
	key = formula_string;

	#ifdef DEBUG_SKOLEM
	cout << "\nInserting entry for " << key << " in R1_map\n";
	#endif

	R1_map.insert(make_pair(key, list_of_r1s));			

}


void AIGBasedSkolem::callCegarSkolem(call_type original_polarity, Aig_Obj_t* original_formula, call_type polarity, Aig_Obj_t* formula, int depth_from_root)
{
	number_of_conjunctions_on_arbitrary_boolean_formulas++;

	#ifdef DETAILED_RECORD_KEEP
	struct timeval callcegarskolem_step_start_ms, callcegarskolem_step_finish_ms;
	unsigned long long int callcegarskolem_time;
	int max_r1_size = -1, max_r0_size = -1;
	int min_r1_size = -1, min_r0_size = -1;
	int total_r1_size = 0, total_r0_size = 0;
	int r1_size, r0_size;

	gettimeofday (&callcegarskolem_step_start_ms, NULL); 
	#endif

	// initialize the parameters needed before calling factorizedSkolemFunctionGenerator
	// as CegarSkolem on polarity.formula

	#ifdef DEBUG_PAR
	cout << "\nperform_cegar_on_arbitrary_boolean_formulas = " << perform_cegar_on_arbitrary_boolean_formulas;
	cout << "\ncluster_global_time_out_enabled = " << cluster_global_time_out_enabled;
	cout << "\navoid_cluster_global_time_out_at_top_node = " << avoid_cluster_global_time_out_at_top_node;
	cout << "\npolarity = " << polarity;
	cout << "\noriginal_polarity = " << original_polarity;
	cout << "\nformula = " << formula;
	cout << "\noriginal_formula = " << original_formula;
	cout << "\ninput_arbitrary_boolean_formula = " << input_arbitrary_boolean_formula;
	#endif

	// disable graceful timeout for the top-node if avoid_cluster_global_time_out_at_top_node
	// is enabled
	if(perform_cegar_on_arbitrary_boolean_formulas && cluster_global_time_out_enabled && avoid_cluster_global_time_out_at_top_node && polarity == original_polarity && formula == original_formula && polarity == original && formula == input_arbitrary_boolean_formula && !Aig_IsComplement(formula))
	{
		disableTimeOut_In_Cluster();
		#ifdef DEBUG_SKOLEM
		cout << "\nTIME-OUT DISABLED FOR THE TOP-NODE\n";
		#endif
	}

	vector<Aig_Obj_t*> list_of_r1s;
	vector<Aig_Obj_t*> list_of_r0s;

	if(checkGlobalTimeOut_In_Cluster()) //graceful-time-out: just disjoin the r1/r0's of children to
	// get the r1/r0's
	{
		//#ifdef DEBUG_PAR
		//cout << "\nWarning!!Global time-out inside the function AIGBasedSkolem::callCegarSkolem\n";
		//#endif
		cluster_global_timed_out = true; // cluster_global_timed_out flag set

		
		set<Aig_Obj_t*> Factors;
		assert(polarity == original);

		// Factors are the children
		Factors.insert(Aig_ObjChild0(formula));
		Factors.insert(Aig_ObjChild1(formula));	

		int factor_index = 1;
		map<int, vector<Aig_Obj_t*> > factor_index_to_list_of_r0s_map;
		map<int, vector<Aig_Obj_t*> > factor_index_to_list_of_r1s_map;

		for(set<Aig_Obj_t*>::iterator Factors_it = Factors.begin(); Factors_it != Factors.end(); Factors_it++)
		{
			Aig_Obj_t* given_factor;
			given_factor = *Factors_it;
			assert(given_factor != NULL);
				
			vector<Aig_Obj_t*> list_of_r0s_of_factor;
			vector<Aig_Obj_t*> list_of_r1s_of_factor;
			call_type factor_polarity = original;
				
			getEntryFromR0HashTable(factor_polarity, given_factor, list_of_r0s_of_factor);
			getEntryFromR1HashTable(factor_polarity, given_factor, list_of_r1s_of_factor);
				
			factor_index_to_list_of_r0s_map.insert(make_pair(factor_index, list_of_r0s_of_factor));
			factor_index_to_list_of_r1s_map.insert(make_pair(factor_index, list_of_r1s_of_factor));

			factor_index++;
		}//consider each factor ends here

		// We have list_of_r0s and list_of_r1s of each factor now
		// From these lists construct the final r0's and r1's

		int location_of_var_to_elim = 0;

		for(list<string>::iterator list_it = Global_VariablesToEliminate.begin(); list_it != Global_VariablesToEliminate.end(); list_it++)
		{
			string var_to_elim = *list_it;
		
			if(checkTimeOut()) // check for time-out
			{
				cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::callCegarSkolem\n";
				timed_out = true; // timed_out flag set
				return;
			}		

			#ifdef DEBUG_SKOLEM
			cout << "\nGetting cannot-be-1 and cannot-be-0 sets of " << var_to_elim << " from hash tables" << endl;
			#endif

			Aig_Obj_t* cannot_be_one_function;
			Aig_Obj_t* cannot_be_zero_function;
			set<Aig_Obj_t*> cannot_be_one_set_for_var_to_elim_index;
			set<Aig_Obj_t*> cannot_be_zero_set_for_var_to_elim_index;

			int factor_index = 1;
			for(set<Aig_Obj_t*>::iterator Factors_it = Factors.begin(); Factors_it != Factors.end(); Factors_it++)
			{
				#ifdef DEBUG_SKOLEM
				cout << "\nfactor_index = " << factor_index << endl;
				#endif

				map<int, vector<Aig_Obj_t*> >::iterator factor_index_to_list_of_r1s_map_it = factor_index_to_list_of_r1s_map.find(factor_index);
				assert(factor_index_to_list_of_r1s_map_it != factor_index_to_list_of_r1s_map.end());

				Aig_Obj_t* r1 = (factor_index_to_list_of_r1s_map_it->second)[location_of_var_to_elim];
		  		assert(r1 != NULL);		
		
		
				// connecting to some output to avoid unwanted deletion
				Aig_Obj_t* r1_CO = Aig_ObjCreateCo(pub_aig_manager, r1 ); 
				assert(r1_CO != NULL);
				intermediate_cos_created.insert(r1_CO);

				map<int, vector<Aig_Obj_t*> >::iterator factor_index_to_list_of_r0s_map_it = factor_index_to_list_of_r0s_map.find(factor_index);
				assert(factor_index_to_list_of_r0s_map_it != factor_index_to_list_of_r0s_map.end());

				Aig_Obj_t* r0 = (factor_index_to_list_of_r0s_map_it->second)[location_of_var_to_elim];
		  		assert(r0 != NULL);		
		
				// connecting to some output to avoid unwanted deletion
				Aig_Obj_t* r0_CO = Aig_ObjCreateCo(pub_aig_manager, r0 ); 
				assert(r0_CO != NULL);
				intermediate_cos_created.insert(r0_CO);
	
				// Insert the dags in respective cannot-be-sets
				cannot_be_one_set_for_var_to_elim_index.insert(r1);
				cannot_be_zero_set_for_var_to_elim_index.insert(r0);

				factor_index++;
			}// for each factor ends here

			assert(!cannot_be_one_set_for_var_to_elim_index.empty());
			cannot_be_one_function = createOr(cannot_be_one_set_for_var_to_elim_index, pub_aig_manager);
			assert(cannot_be_one_function != NULL);

			assert(!cannot_be_zero_set_for_var_to_elim_index.empty());
			cannot_be_zero_function = createOr(cannot_be_zero_set_for_var_to_elim_index, pub_aig_manager);
			assert(cannot_be_zero_function != NULL);
		
			// connect to some output to avoid unwanted deletion
			Aig_Obj_t* cannot_be_one_function_CO = Aig_ObjCreateCo(pub_aig_manager, cannot_be_one_function ); 
			assert(cannot_be_one_function_CO != NULL);
			r1r0_cos_created.insert(cannot_be_one_function_CO);

			Aig_Obj_t* cannot_be_zero_function_CO = Aig_ObjCreateCo(pub_aig_manager, cannot_be_zero_function ); 
			assert(cannot_be_zero_function_CO != NULL);
			r1r0_cos_created.insert(cannot_be_zero_function_CO);			
	
			list_of_r1s.push_back(cannot_be_one_function);
			list_of_r0s.push_back(cannot_be_zero_function);

			location_of_var_to_elim++;

			#ifdef DETAILED_RECORD_KEEP

			#ifdef PERFORM_SIZE_COMPUTATIONS_IN_PAR
			r1_size = computeSize(cannot_be_one_function, pub_aig_manager);
			r0_size = computeSize(cannot_be_zero_function, pub_aig_manager);
			#else
			r1_size = 0;
			r0_size = 0;
			#endif

			total_r1_size = total_r1_size + r1_size;
			total_r0_size = total_r0_size + r0_size;

			if(max_r1_size == -1)
			{
				max_r1_size = r1_size;
			}
			else if(max_r1_size < r1_size)
			{
				max_r1_size = r1_size;
			}
			if(max_r0_size == -1)
			{
				max_r0_size = r0_size;
			}
			else if(max_r0_size < r0_size)
			{
				max_r0_size = r0_size;
			}
		
				
			if(min_r1_size == -1)
			{
				min_r1_size = r1_size;
			}
			else if(min_r1_size > r1_size)
			{
				min_r1_size = r1_size;
			}
			if(min_r0_size == -1)
			{
				min_r0_size = r0_size;
			}
			else if(min_r0_size > r0_size)
			{
				min_r0_size = r0_size;
			}
			#endif

			#ifdef DEBUG_SKOLEM
			string cannot_be_one_file_name = "r1_";
			string cannot_be_zero_file_name = "r0_";
		
			char formula_char[100];
			sprintf(formula_char, "%p", formula);
			string formula_string(formula_char);
			if(polarity == negated)
			{
				formula_string += "n";
			}
			else
			{
				formula_string += "o";
			}

			cannot_be_one_file_name += formula_string;
			cannot_be_one_file_name += "_";
			cannot_be_zero_file_name += formula_string;
			cannot_be_zero_file_name += "_";
		
			cannot_be_one_file_name += var_to_elim;
			cannot_be_one_file_name += ".v";
			cannot_be_zero_file_name += var_to_elim;
			cannot_be_zero_file_name += ".v";

			writeFormulaToFile(pub_aig_manager, cannot_be_one_function, cannot_be_one_file_name);
			writeFormulaToFile(pub_aig_manager, cannot_be_zero_function, cannot_be_zero_file_name);
			#endif
		
		}// for each variable ends here

		// Enter into hash tables the entries
		// (polarity, formula) --> list_of_r1s and (polarity, formula) --> list_of_r0s
		// (original_polarity, original_formula) --> list_of_r1s and 
		// (original_polarity, original_formula) --> list_of_r0s

		insertIntoR0HashTable(polarity, formula, list_of_r0s);
		insertIntoR1HashTable(polarity, formula, list_of_r1s);
	
		if(polarity != original_polarity || formula != original_formula)
		{
			insertIntoR0HashTable(original_polarity, original_formula, list_of_r0s);
			insertIntoR1HashTable(original_polarity, original_formula, list_of_r1s);		
		}
	
	}//graceful-time-out
	else
	{

		//#ifdef DEBUG_PAR
		//cout << "\ntotal_time_in_compute_size = " << total_time_in_compute_size << endl;
		//#endif

		// setting variablestoeliminate and Factors
		list<string> VariablesToEliminate_Copy;
		VariablesToEliminate_Copy = Global_VariablesToEliminate;

		bool all_variables_to_eliminate_occure_in_formula;
		bool no_variables_to_eliminate_occure_in_formula;

		set<string> support_formula;
		computeSupport(formula, support_formula, pub_aig_manager);
		set<string> variables_to_eliminate_in_support_formula;
		set_intersection(support_formula.begin(), support_formula.end(), Global_VariablesToEliminate_Set.begin(), Global_VariablesToEliminate_Set.end(), inserter(variables_to_eliminate_in_support_formula, variables_to_eliminate_in_support_formula.begin()));

		if(variables_to_eliminate_in_support_formula.empty())//no variable to elimiate occure in formula
		{
			no_variables_to_eliminate_occure_in_formula = true;
			all_variables_to_eliminate_occure_in_formula = false;
		}
		else if(variables_to_eliminate_in_support_formula.size() == Global_VariablesToEliminate_Set.size()) // all variable to elimiate occure in formula
		{
			no_variables_to_eliminate_occure_in_formula = false;
			all_variables_to_eliminate_occure_in_formula = true;
		}
		else
		{
			no_variables_to_eliminate_occure_in_formula = false;
			all_variables_to_eliminate_occure_in_formula = false;
		}
	

		// To store r1 and r0 for variables NOT occuring in formula
		map<string, Aig_Obj_t*> map_of_r1s_of_free_variables;
		map<string, Aig_Obj_t*> map_of_r0s_of_free_variables;

		if(!no_variables_to_eliminate_occure_in_formula) // there are some variables to eliminate that occure in formula	
		{
			number_of_cegarskolem_calls_on_arbitrary_boolean_formulas++;

			set<Aig_Obj_t*> Factors;
			assert(polarity == original);

			// Factors are the children
			Factors.insert(Aig_ObjChild0(formula));
			Factors.insert(Aig_ObjChild1(formula));


			// setting parameters for CegarSkolem
			perform_reverse_substitution = false;	
			enable_cegar = true;
			use_bads_in_unified_cegar = false;
			use_cbzero_in_unified_cegar = false;
			use_assumptions_in_unified_cegar = false;
			accumulate_formulae_in_cbzero_in_cegar = true;	
			drop_free_factors = false; // It is important to set this, otherwise free
			// factors will be dropped, and we won't get exact result
			depth_from_root_in_cegarskolem_call_on_arbitrary_boolean_formulas = depth_from_root;

			if(avoid_sat_call_in_functional_forms && depth_from_root == 0)
			{
				internal_flag_to_avoid_sat_call_in_functional_forms = true;
			}
			else
			{
				internal_flag_to_avoid_sat_call_in_functional_forms = false;
			}

			#ifdef DETAILED_RECORD_KEEP
			struct timeval cegarskolem_step_start_ms, cegarskolem_step_finish_ms;
			unsigned long long int cegarskolem_time;
			gettimeofday (&cegarskolem_step_start_ms, NULL); 
			#endif
	
			// Let's call factorizedSkolemFunctionGenerator with these parameters
			// This will give r1 and r0 for variables occuring in Factors in global 
			// data-structures 

			//#ifdef DEBUG_PAR
			//cout << "\nfactorizedSkolemFunctionGenerator called\n";
			//#endif

			factorizedSkolemFunctionGenerator(Factors, VariablesToEliminate_Copy);

			#ifdef DETAILED_RECORD_KEEP
			gettimeofday (&cegarskolem_step_finish_ms, NULL);
			cegarskolem_time = cegarskolem_step_finish_ms.tv_sec * 1000 + cegarskolem_step_finish_ms.tv_usec / 1000;
			cegarskolem_time -= cegarskolem_step_start_ms.tv_sec * 1000 + cegarskolem_step_start_ms.tv_usec / 1000;
	
			total_time_in_cegarskolem = total_time_in_cegarskolem + cegarskolem_time;

			total_number_of_cegar_iterations_in_cegarskolem = total_number_of_cegar_iterations_in_cegarskolem + cegar_iteration_number;


			if(max_number_of_cegar_iterations_in_cegarskolem == -1)
			{
				max_number_of_cegar_iterations_in_cegarskolem = cegar_iteration_number;
			}
			else if(max_number_of_cegar_iterations_in_cegarskolem < cegar_iteration_number)
			{
				max_number_of_cegar_iterations_in_cegarskolem = cegar_iteration_number;
			}
			if(min_number_of_cegar_iterations_in_cegarskolem == -1)
			{
				min_number_of_cegar_iterations_in_cegarskolem = cegar_iteration_number;
			}
			else if(min_number_of_cegar_iterations_in_cegarskolem > cegar_iteration_number)
			{
				min_number_of_cegar_iterations_in_cegarskolem = cegar_iteration_number;
			}
			#endif	
		
		}

		if(checkTimeOut()) // check for time-out
		{
			#ifdef RECORD_KEEP
			string record_file;
			record_file = logfile_prefix;
			record_file += "skolem_function_generation_details.txt";
			FILE* record_fp = fopen(record_file.c_str(), "a+");
			assert(record_fp != NULL);

			fprintf(record_fp, "\nTime-out inside the function AIGBasedSkolem::factorizedSkolemFunctionGenerator\n");

			fclose(record_fp);
			#endif

			cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::callCegarSkolem\n";
			timed_out = true; // timed_out flag set
			return;
		}

		if(!all_variables_to_eliminate_occure_in_formula) // there are some variables to eliminate that does NOT occure in formula	
		{
			// To get r1 and r0 for variables NOT occuring in Factors
			getR1R0ForFreeVariablesInConjunction(formula, map_of_r1s_of_free_variables, map_of_r0s_of_free_variables);
		}

		
		// Get the cannot be one sets, and cannot be zero sets
		for(list<string>::iterator list_it = Global_VariablesToEliminate.begin(); list_it != Global_VariablesToEliminate.end(); list_it++)
		{
			string variable_to_eliminate = *list_it;
			int index_of_variable_to_eliminate = searchVarNameToVarIndexMap(var_name_to_var_index_map, variable_to_eliminate);

			#ifdef DEBUG_SKOLEM
			cout << "\nvariable_to_eliminate = " << variable_to_eliminate << "\tindex_of_variable_to_eliminate = " << index_of_variable_to_eliminate << endl;
			#endif

			Aig_Obj_t* cannot_be_one_function;
			Aig_Obj_t* cannot_be_zero_function;
		
			if(index_of_variable_to_eliminate == -1) // Factors free of variable_to_eliminate
			{
				map<string, Aig_Obj_t*>::iterator map_of_rs_it;
			
				map_of_rs_it = map_of_r1s_of_free_variables.find(variable_to_eliminate);
				assert(map_of_rs_it != map_of_r1s_of_free_variables.end());
				cannot_be_one_function = map_of_rs_it->second;
				assert(cannot_be_one_function != NULL);	
			
				map_of_rs_it = map_of_r0s_of_free_variables.find(variable_to_eliminate);
				assert(map_of_rs_it != map_of_r0s_of_free_variables.end());
				cannot_be_zero_function = map_of_rs_it->second;
				assert(cannot_be_zero_function != NULL);

				// connect to some output to avoid unwanted deletion
				Aig_Obj_t* cannot_be_one_function_CO = Aig_ObjCreateCo(pub_aig_manager, cannot_be_one_function ); 
				assert(cannot_be_one_function_CO != NULL);
				r1r0_cos_created.insert(cannot_be_one_function_CO);

				Aig_Obj_t* cannot_be_zero_function_CO = Aig_ObjCreateCo(pub_aig_manager, cannot_be_zero_function ); 
				assert(cannot_be_zero_function_CO != NULL);
				r1r0_cos_created.insert(cannot_be_zero_function_CO);
			}
			else // Factors not free of variable_to_eliminate; index_of_variable_to_eliminate gives the 
			// location of variable_to_eliminate in the Local Tables of factorizedSkolemFunctionGenerator
			// that stores r1's and r0's
			{
				set<Aig_Obj_t*> cannot_be_one_function_elements;
				set<Aig_Obj_t*> cannot_be_one_function_objects;
				map<int, set<Aig_Obj_t*> >::iterator cannot_be_one_set_it = cannot_be_one_set.find(index_of_variable_to_eliminate);
				assert(cannot_be_one_set_it != cannot_be_one_set.end());
				cannot_be_one_function_objects = cannot_be_one_set_it->second;

				for(set<Aig_Obj_t*>::iterator cannot_be_one_function_objects_it = cannot_be_one_function_objects.begin(); cannot_be_one_function_objects_it != cannot_be_one_function_objects.end(); cannot_be_one_function_objects_it++)
				{
					Aig_Obj_t* cannot_be_object = *cannot_be_one_function_objects_it;
					assert(cannot_be_object != NULL);

					map<Aig_Obj_t*, Aig_Obj_t*>::iterator cannot_be_object_to_cannot_be_dag_map_it = cannot_be_object_to_cannot_be_dag_map.find(cannot_be_object);
					Aig_Obj_t* cannot_be_dag = cannot_be_object_to_cannot_be_dag_map_it->second;
					assert(cannot_be_dag != NULL);
				
					cannot_be_one_function_elements.insert(cannot_be_dag);
				}

				assert(!cannot_be_one_function_elements.empty());
				cannot_be_one_function = createOr(cannot_be_one_function_elements, pub_aig_manager);
				assert(cannot_be_one_function != NULL);

				set<Aig_Obj_t*> cannot_be_zero_function_elements;
				set<Aig_Obj_t*> cannot_be_zero_function_objects;
				map<int, set<Aig_Obj_t*> >::iterator cannot_be_zero_set_it = cannot_be_zero_set.find(index_of_variable_to_eliminate);
				assert(cannot_be_zero_set_it != cannot_be_zero_set.end());
				cannot_be_zero_function_objects = cannot_be_zero_set_it->second;

				for(set<Aig_Obj_t*>::iterator cannot_be_zero_function_objects_it = cannot_be_zero_function_objects.begin(); cannot_be_zero_function_objects_it != cannot_be_zero_function_objects.end(); cannot_be_zero_function_objects_it++)
				{
					Aig_Obj_t* cannot_be_object = *cannot_be_zero_function_objects_it;
					assert(cannot_be_object != NULL);

					map<Aig_Obj_t*, Aig_Obj_t*>::iterator cannot_be_object_to_cannot_be_dag_map_it = cannot_be_object_to_cannot_be_dag_map.find(cannot_be_object);
					Aig_Obj_t* cannot_be_dag = cannot_be_object_to_cannot_be_dag_map_it->second;
					assert(cannot_be_dag != NULL);
				
					cannot_be_zero_function_elements.insert(cannot_be_dag);
				}

				assert(!cannot_be_zero_function_elements.empty());
				cannot_be_zero_function = createOr(cannot_be_zero_function_elements, pub_aig_manager);
				assert(cannot_be_zero_function != NULL);
			
				// connect to some output to avoid unwanted deletion
				Aig_Obj_t* cannot_be_one_function_CO = Aig_ObjCreateCo(pub_aig_manager, cannot_be_one_function ); 
				assert(cannot_be_one_function_CO != NULL);
				r1r0_cos_created.insert(cannot_be_one_function_CO);

				Aig_Obj_t* cannot_be_zero_function_CO = Aig_ObjCreateCo(pub_aig_manager, cannot_be_zero_function ); 
				assert(cannot_be_zero_function_CO != NULL);
				r1r0_cos_created.insert(cannot_be_zero_function_CO);			
			}

			list_of_r1s.push_back(cannot_be_one_function);
			list_of_r0s.push_back(cannot_be_zero_function);

			#ifdef DETAILED_RECORD_KEEP

			#ifdef PERFORM_SIZE_COMPUTATIONS_IN_PAR
			r1_size = computeSize(cannot_be_one_function, pub_aig_manager);
			r0_size = computeSize(cannot_be_zero_function, pub_aig_manager);
			#else
			r1_size = 0;
			r0_size = 0;
			#endif

			total_r1_size = total_r1_size + r1_size;
			total_r0_size = total_r0_size + r0_size;

			if(max_r1_size == -1)
			{
				max_r1_size = r1_size;
			}
			else if(max_r1_size < r1_size)
			{
				max_r1_size = r1_size;
			}
			if(max_r0_size == -1)
			{
				max_r0_size = r0_size;
			}
			else if(max_r0_size < r0_size)
			{
				max_r0_size = r0_size;
			}
		
				
			if(min_r1_size == -1)
			{
				min_r1_size = r1_size;
			}
			else if(min_r1_size > r1_size)
			{
				min_r1_size = r1_size;
			}
			if(min_r0_size == -1)
			{
				min_r0_size = r0_size;
			}
			else if(min_r0_size > r0_size)
			{
				min_r0_size = r0_size;
			}
			#endif


			#ifdef DEBUG_SKOLEM
			string cannot_be_one_file_name = "r1_";
			string cannot_be_zero_file_name = "r0_";
		
			char formula_char[100];
			sprintf(formula_char, "%p", formula);
			string formula_string(formula_char);
			if(polarity == negated)
			{
				formula_string += "n";
			}
			else
			{
				formula_string += "o";
			}

			cannot_be_one_file_name += formula_string;
			cannot_be_one_file_name += "_";
			cannot_be_zero_file_name += formula_string;
			cannot_be_zero_file_name += "_";
		
			cannot_be_one_file_name += variable_to_eliminate;
			cannot_be_one_file_name += ".v";
			cannot_be_zero_file_name += variable_to_eliminate;
			cannot_be_zero_file_name += ".v";

			writeFormulaToFile(pub_aig_manager, cannot_be_one_function, cannot_be_one_file_name);
			writeFormulaToFile(pub_aig_manager, cannot_be_zero_function, cannot_be_zero_file_name);
			#endif
		
		}// for each variable ends here

		// Enter into hash tables the entries
		// (polarity, formula) --> list_of_r1s and (polarity, formula) --> list_of_r0s
		// (original_polarity, original_formula) --> list_of_r1s and 
		// (original_polarity, original_formula) --> list_of_r0s

		insertIntoR0HashTable(polarity, formula, list_of_r0s);
		insertIntoR1HashTable(polarity, formula, list_of_r1s);
	
		if(polarity != original_polarity || formula != original_formula)
		{
			insertIntoR0HashTable(original_polarity, original_formula, list_of_r0s);
			insertIntoR1HashTable(original_polarity, original_formula, list_of_r1s);		
		}

		#ifdef DEBUG_PAR
		cout << "\ntotal_time_in_compute_size = " << total_time_in_compute_size << endl;
		#endif
	
		if(!no_variables_to_eliminate_occure_in_formula)
		{
			clearAllDataStructures();
			setParametersToDefaults();	
		}

	}//no graceful-time-out

	#ifdef DETAILED_RECORD_KEEP
	gettimeofday (&callcegarskolem_step_finish_ms, NULL);
	callcegarskolem_time = callcegarskolem_step_finish_ms.tv_sec * 1000 + callcegarskolem_step_finish_ms.tv_usec / 1000;
	callcegarskolem_time -= callcegarskolem_step_start_ms.tv_sec * 1000 + callcegarskolem_step_start_ms.tv_usec / 1000;
	
	total_time_in_callconjunction = total_time_in_callconjunction + callcegarskolem_time;

	string record_file;
	record_file = logfile_prefix;
	record_file += "skolem_function_generation_details.txt";
	FILE* record_fp = fopen(record_file.c_str(), "a+");
	assert(record_fp != NULL);

	if(!mask_printing_details_file)
	{
		fprintf(record_fp, "\nDetails of find_skolem_conjunction Call#:%d (Depth from root = %d)\nTime = %llu\nmax r1 size = %d\tmin r1 size = %d\tavg r1 size = %f\nmax r0 size = %d\tmin r0 size = %d\tavg r0 size = %f\n", number_of_conjunctions_on_arbitrary_boolean_formulas, depth_from_root, callcegarskolem_time, max_r1_size, min_r1_size, (float)total_r1_size/(float)Global_VariablesToEliminate_Set.size(), max_r0_size, min_r0_size, (float)total_r0_size/(float)Global_VariablesToEliminate_Set.size());
	}

	fclose(record_fp);	
	#endif

	if(prove_correctness_of_skolem_functions_of_arbitrary_boolean_formula_detailed_check)
	{
		// Create the Skolem functions			
		
		assert(list_of_r1s.size() == Global_VariablesToEliminate.size());

		vector<Aig_Obj_t*> skolem_functions_of_formula;
		for(int i = 0; i < list_of_r1s.size(); i++)
		{
			Aig_Obj_t* r1_i = list_of_r1s[i];
			assert(r1_i != NULL);

			Aig_Obj_t* skolem_i = createNot(r1_i, pub_aig_manager); 
			assert(skolem_i != NULL);

			skolem_functions_of_formula.push_back(skolem_i);		
		}

		// Perform reverse-substitution
		performReverseSubstitutionOfSkolemFunctions(skolem_functions_of_formula);

		
		// Check for exactness
		// First create F(psi(Y), Y)
		bool ensure_that_skolem_functions_are_on_y = true;
		
		map<string, Aig_Obj_t*> skolem_function_replacement_map;
		int i = 0;
		for(list<string>::iterator list_it = Global_VariablesToEliminate.begin(); list_it != Global_VariablesToEliminate.end(); list_it++)
		{
			string variable_to_eliminate = *list_it;
			
			Aig_Obj_t* skolem_i = skolem_functions_of_formula[i];
			assert(skolem_i != NULL);

			if(ensure_that_skolem_functions_are_on_y)
			{
				set<string> support_skolem_i;
				computeSupport(skolem_i, support_skolem_i, pub_aig_manager);
				
				set<string> varstoelim_in_support_skolem_i;
				set_intersection(support_skolem_i.begin(), support_skolem_i.end(), Global_VariablesToEliminate_Set.begin(), Global_VariablesToEliminate_Set.end(), inserter(varstoelim_in_support_skolem_i, varstoelim_in_support_skolem_i.begin()));

				if(!varstoelim_in_support_skolem_i.empty())				
				{
					cout << "\nSkolem function of variable " << variable_to_eliminate << " involves variables to be eliminated\n";
					assert(false);	
				}
			}

			skolem_function_replacement_map.insert(make_pair(variable_to_eliminate, skolem_i));
				
			i++;
		
		}// for each variable ends here	

		assert(skolem_function_replacement_map.size() > 0);

		Aig_Obj_t* result_of_qe_using_skolem_functions;
		result_of_qe_using_skolem_functions = replaceVariablesByFormulas(formula, skolem_function_replacement_map);	
		assert(result_of_qe_using_skolem_functions != NULL); // F(psi(Y), Y)	

		list<string> VariablesToEliminate_Copy;
		VariablesToEliminate_Copy = Global_VariablesToEliminate;

		Aig_Obj_t* equivalence_check; // ~F(psi(Y), Y) \wedge F(X, Y)
		equivalence_check = createAnd(createNot(result_of_qe_using_skolem_functions, pub_aig_manager), formula, pub_aig_manager);
		assert(equivalence_check != NULL);

		// Give to SAT-Solver
		unsigned long long int cnf_time;
		int formula_size;
		unsigned long long int simplification_time;
		map<string, int> Model_of_equivalence_check;
		bool result_of_equivalence_check;

		result_of_equivalence_check = isSat(pub_aig_manager, equivalence_check, Model_of_equivalence_check, cnf_time, formula_size, simplification_time);

		if(result_of_equivalence_check)
		{
			cout << "\nexists X.f => f[X --> psi] is NOT valid\n";
			cout << "\nCounterexample is\n";
			displayModelFromSATSolver(Model_of_equivalence_check);			
		}
		else
		{
			cout << "\nexists X.f => f[X --> psi] is valid\n";
		}

		string record_file;
		record_file = logfile_prefix;
		record_file += "skolem_function_generation_details.txt";
		FILE* record_fp = fopen(record_file.c_str(), "a+");
		assert(record_fp != NULL);

		if(result_of_equivalence_check)
		{
			fprintf(record_fp, "\n\nexists X.f(X,Y) = f'(psi,Y) is NOT valid; Skolem functions are NOT exact\n");
		}
		else
		{
			fprintf(record_fp, "\n\nexists X.f(X,Y) = f'(psi,Y) is valid; Skolem functions are exact\n");		

		}

		fclose(record_fp);

		if(result_of_equivalence_check) // not exact
		{
			assert(false);
		}
		
	}


	if(cleanup_after_each_step_in_arbitrary_boolean_combinations)
	{
		string step_name = "callCegarSkolem";
		cleanupAfterEachStepInArbitraryBooleanCombinations(step_name);
	}
	
}

	
Aig_Obj_t* AIGBasedSkolem::computeInitialSkolemFunctionsAndCannotBeSetsFromHashTableEntries(int var_to_elim_index, int location_of_var_to_elim, map<int, vector<Aig_Obj_t*> > &factor_index_to_list_of_r0s_map, map<int, vector<Aig_Obj_t*> > &factor_index_to_list_of_r1s_map)
{
	Aig_Obj_t* skolem_function;
	Aig_Obj_t* skolem_function_part1;
	Aig_Obj_t* skolem_function_part2;
	set<Aig_Obj_t*> skolem_function_part1_components;
	set<Aig_Obj_t*> skolem_function_part2_components;

	Aig_Obj_t* initial_cbzero_part_for_bad;
	Aig_Obj_t* initial_cbone_part_for_bad;

	// compute the elements in cb0_k and cb1_k
	set<Aig_Obj_t*> cannot_be_one_set_for_var_to_elim_index;
	set<Aig_Obj_t*> cannot_be_zero_set_for_var_to_elim_index;

	for(set<int>::iterator factor_it = FactorsWithVariable.begin(); factor_it != FactorsWithVariable.end(); factor_it++)
	{
		int factor_index = *factor_it;

		#ifdef DEBUG_SKOLEM
		cout << "\nfactor_index = " << factor_index << endl;
		#endif

		//#ifdef DEBUG_PAR
		//cout << "\nfactor_index = " << factor_index << endl;
		//#endif

		map<int, vector<Aig_Obj_t*> >::iterator factor_index_to_list_of_r1s_map_it = factor_index_to_list_of_r1s_map.find(factor_index);
		assert(factor_index_to_list_of_r1s_map_it != factor_index_to_list_of_r1s_map.end());

		//#ifdef DEBUG_PAR
		//cout << "\n(factor_index_to_list_of_r1s_map_it->second).size() = " << (factor_index_to_list_of_r1s_map_it->second).size() << endl;
		//#endif

		Aig_Obj_t* r1 = (factor_index_to_list_of_r1s_map_it->second)[location_of_var_to_elim];
  		assert(r1 != NULL);	

		//#ifdef DEBUG_PAR
		//cout << "\nr1 = " << r1 << endl;
		//cout << "\nsize(r1) = " << computeSize(r1, pub_aig_manager) << endl;
		//#endif	
		
		sizes_of_cannot_be_one_elements_of_variable.push_back(computeSize(r1, pub_aig_manager));

		// connecting to some output to avoid unwanted deletion
		Aig_Obj_t* r1_CO = Aig_ObjCreateCo(pub_aig_manager, r1 ); 
		assert(r1_CO != NULL);
		intermediate_cos_created.insert(r1_CO);

		//#ifdef DEBUG_PAR
		//cout << "\nr1_CO = " << r1_CO << endl;
		//#endif

		map<int, vector<Aig_Obj_t*> >::iterator factor_index_to_list_of_r0s_map_it = factor_index_to_list_of_r0s_map.find(factor_index);
		assert(factor_index_to_list_of_r0s_map_it != factor_index_to_list_of_r0s_map.end());

		//#ifdef DEBUG_PAR
		//cout << "\n(factor_index_to_list_of_r0s_map_it).size() = " << (factor_index_to_list_of_r0s_map_it->second).size() << endl;
		//#endif

		Aig_Obj_t* r0 = (factor_index_to_list_of_r0s_map_it->second)[location_of_var_to_elim];
  		assert(r0 != NULL);

		//#ifdef DEBUG_PAR
		//cout << "\nr0 = " << r0 << endl;
		//cout << "\nsize(r0) = " << computeSize(r0, pub_aig_manager) << endl;
		//#endif			
		
		sizes_of_cannot_be_zero_elements_of_variable.push_back(computeSize(r0, pub_aig_manager));

		// connecting to some output to avoid unwanted deletion
		Aig_Obj_t* r0_CO = Aig_ObjCreateCo(pub_aig_manager, r0 ); 
		assert(r0_CO != NULL);
		intermediate_cos_created.insert(r1_CO);
	
		//#ifdef DEBUG_PAR
		//cout << "\nr0_CO = " << r0_CO << endl;
		//#endif

		#ifdef DEBUG_SKOLEM
		writeFormulaToFile(pub_aig_manager, r1, "r1", ".v", var_to_elim_index, factor_index);	
		writeFormulaToFile(pub_aig_manager, r0, "r0", ".v", var_to_elim_index, factor_index);	
		#endif

		// Allocate strings and objects for the dags neg_cofactor_1 and neg_cofactor_0 

		string cannot_be_one_string;
		Aig_Obj_t* cannot_be_one_object;
		allocateStringAndObjectToCannotBeDag(1, r1, cannot_be_one_string, cannot_be_one_object);

		string cannot_be_zero_string;
		Aig_Obj_t* cannot_be_zero_object;
		allocateStringAndObjectToCannotBeDag(0, r0, cannot_be_zero_string, cannot_be_zero_object);

		#ifdef DEBUG_SKOLEM
		show_cannot_be_string_to_cannot_be_object_map();
		show_cannot_be_object_to_cannot_be_dag_map();
		#endif

		// Insert the objects in respective cannot-be-sets
		cannot_be_one_set_for_var_to_elim_index.insert(cannot_be_one_object);
		cannot_be_zero_set_for_var_to_elim_index.insert(cannot_be_zero_object);
		
		// Insert the r1 dag into the skolem_function_part1_components
		skolem_function_part1_components.insert(r1);						

		// Insert the r0 dag into the skolem_function_part2_components
		skolem_function_part2_components.insert(r0);
	}// for each factor ends here

	
	if(checkTimeOut()) // check for time-out
	{
		cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::computeInitialSkolemFunctionsAndCannotBeSetsFromHashTableEntries\n";
		timed_out = true; // timed_out flag set
		return NULL;
	}

	// insert in global tables
	map<int, set<Aig_Obj_t*> >::iterator cannot_be_one_set_it = cannot_be_one_set.find(var_to_elim_index);
	assert(cannot_be_one_set_it == cannot_be_one_set.end());
	cannot_be_one_set.insert(make_pair(var_to_elim_index, cannot_be_one_set_for_var_to_elim_index));

	map<int, set<Aig_Obj_t*> >::iterator cannot_be_zero_set_it = cannot_be_zero_set.find(var_to_elim_index);
	assert(cannot_be_zero_set_it == cannot_be_zero_set.end());
	cannot_be_zero_set.insert(make_pair(var_to_elim_index, cannot_be_zero_set_for_var_to_elim_index));

	// Let's compute the skolem_function
	// skolem_function is 
	//          disjunction of elements in cannot_be_one_set_for_var_to_elim_index \vee 
	//          negation of (disjunction of elements in cannot_be_one_set_for_var_to_elim_index)
	assert(!cannot_be_one_set_for_var_to_elim_index.empty());
	skolem_function_part1 = createOr(skolem_function_part1_components, pub_aig_manager);
	initial_cbone_part_for_bad = skolem_function_part1;
	skolem_function_part1 = createNot(skolem_function_part1, pub_aig_manager);
	assert(skolem_function_part1 != NULL);
	
	assert(!cannot_be_zero_set_for_var_to_elim_index.empty()); 
	skolem_function_part2 = createOr(skolem_function_part2_components, pub_aig_manager);
	initial_cbzero_part_for_bad = skolem_function_part2;
	assert(skolem_function_part2 != NULL);


	if(use_cbzero_in_unified_cegar)
	{
		skolem_function = createOr(skolem_function_part2, skolem_function_part1, pub_aig_manager);
	}
	else
	{
		skolem_function = skolem_function_part1;
	}
	
	
	assert(skolem_function != NULL);

	InitialSkolemFunctionSizeBeforeOptimization = computeSize(skolem_function, pub_aig_manager);

	if(use_dontcare_optimization_in_cegar)
	// optimize the skolem_function
	{
		// create Cb1_i \wedge Cb0_i

		// Cb1_i is disjunction of AIGs in cannot_be_one_set_for_var_to_elim_index, i.e. ~skolem_function_part1
		Aig_Obj_t* Cb1_part = createNot(skolem_function_part1, pub_aig_manager);

		// Cb0_i is disjunction of AIGs in cannot_be_zero_set_for_var_to_elim_index, i.e. skolem_function_part2
		Aig_Obj_t* Cb0_part = skolem_function_part2;

		Aig_Obj_t* dontcare_part = createAnd(Cb1_part, Cb0_part, pub_aig_manager);
		assert(dontcare_part != NULL);

		#ifdef DEBUG_SKOLEM
		writeFormulaToFile(pub_aig_manager, dontcare_part, "dontcare_part", ".v", var_to_elim_index, cegar_iteration_number);	
		writeFormulaToFile(pub_aig_manager, skolem_function, "unoptimized_skolem_function", ".v", var_to_elim_index, cegar_iteration_number);	
		#endif

		skolem_function = performDontCareOptimization(pub_aig_manager, skolem_function, dontcare_part);
		assert(skolem_function != NULL);
		
	}

	// connect to some output to avoid unwanted deletion
	Aig_Obj_t* skolem_function_part2_CO = Aig_ObjCreateCo(pub_aig_manager, skolem_function_part2 ); 
	assert(skolem_function_part2_CO != NULL);
	intermediate_cos_created.insert(skolem_function_part2_CO);

	Aig_Obj_t* skolem_function_CO = Aig_ObjCreateCo(pub_aig_manager, skolem_function ); 
	assert(skolem_function_CO != NULL);
	intermediate_cos_created.insert(skolem_function_CO);

	#ifdef DEBUG_SKOLEM
	cout << "\nabstract skolem_function computed\n";	
	#endif

	#ifdef PRINT_SKOLEM_FUNCTIONS
	string skolem_function_file_name = benchmark_name_without_extension;
	skolem_function_file_name += "_skolem_function";
	writeFormulaToFile(pub_aig_manager, skolem_function, skolem_function_file_name, ".v", var_to_elim_index, cegar_iteration_number);
	#endif

	// Enter into matrix
	insertIntoOneDimensionalMatrix(SkolemFunctions, number_of_vars_to_elim, var_to_elim_index, skolem_function, false);

	// Computing Badsets here
	if(var_to_elim_index < number_of_vars_to_elim) // No need to compute Bad_{n+1} 
	{
		Aig_Obj_t* bad_set_for_next_var;
		bad_set_for_next_var = createAnd(initial_cbzero_part_for_bad, initial_cbone_part_for_bad, pub_aig_manager);
		assert(bad_set_for_next_var != NULL);

		// connect to some output to avoid unwanted deletion
		Aig_Obj_t* bad_set_for_next_var_CO = Aig_ObjCreateCo(pub_aig_manager, bad_set_for_next_var ); 
		assert(bad_set_for_next_var_CO != NULL);
		intermediate_cos_created.insert(bad_set_for_next_var_CO);

		#ifdef DEBUG_SKOLEM
		cout << "\nbad_set_" << var_to_elim_index+1 << " computed\n";
		writeFormulaToFile(pub_aig_manager, bad_set_for_next_var, "bad_set", ".v", var_to_elim_index+1, cegar_iteration_number);	
		#endif

		// Enter into matrix
		insertIntoOneDimensionalMatrix(BadSets, number_of_vars_to_elim, var_to_elim_index+1, bad_set_for_next_var, false);
	}	
	
	if(checkTimeOut()) // check for time-out
	{
		cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::computeInitialSkolemFunctionsAndCannotBeSetsFromHashTableEntries\n";
		timed_out = true; // timed_out flag set
		return NULL;
	}	

	// Compute ICb0_k in terms of objects and as dag
	// These will be required while recomputing the Skolem functions
	// Let's compute these right now, since later on these sets will get changed

	// we already have ICb0_k dag; let's insert it
	map<int, Aig_Obj_t*>::iterator initial_cannot_be_zero_dags_it = initial_cannot_be_zero_dags.find(var_to_elim_index);
	assert(initial_cannot_be_zero_dags_it == initial_cannot_be_zero_dags.end());
	initial_cannot_be_zero_dags.insert(make_pair(var_to_elim_index, skolem_function_part2));
	
	// Let's compute the ICb0_k object
	Aig_Obj_t* initial_cannot_be_zero_object;
	assert(!cannot_be_zero_set_for_var_to_elim_index.empty());
	initial_cannot_be_zero_object = createOr(cannot_be_zero_set_for_var_to_elim_index, pub_aig_manager);
	assert(initial_cannot_be_zero_object != NULL);

	// connect to some output to avoid unwanted deletion
	Aig_Obj_t* initial_cannot_be_zero_object_CO = Aig_ObjCreateCo(pub_aig_manager, initial_cannot_be_zero_object ); 
	assert(initial_cannot_be_zero_object_CO != NULL);
	intermediate_cos_created.insert(initial_cannot_be_zero_object_CO);

	// let's insert it
	map<int, Aig_Obj_t*>::iterator initial_cannot_be_zero_objects_it = initial_cannot_be_zero_objects.find(var_to_elim_index);
	assert(initial_cannot_be_zero_objects_it == initial_cannot_be_zero_objects.end());
	initial_cannot_be_zero_objects.insert(make_pair(var_to_elim_index, initial_cannot_be_zero_object));
		
	return skolem_function;		
}



void AIGBasedSkolem::callDisjunction(call_type original_polarity, Aig_Obj_t* original_formula, call_type polarity, Aig_Obj_t* formula, int depth_from_root)
{
	number_of_disjunctions_on_arbitrary_boolean_formulas++;

	#ifdef DETAILED_RECORD_KEEP
	struct timeval calldisjunction_step_start_ms, calldisjunction_step_finish_ms;
	unsigned long long int calldisjunction_time;
	int max_r1_size = -1, max_r0_size = -1;
	int min_r1_size = -1, min_r0_size = -1;
	int total_r1_size = 0, total_r0_size = 0;
	int r1_size, r0_size;

	gettimeofday (&calldisjunction_step_start_ms, NULL); 
	#endif

	set<Aig_Obj_t*> Factors;
	vector<Aig_Obj_t*> list_of_r1s;
	vector<Aig_Obj_t*> list_of_r0s;

	
	if(perform_cegar_on_arbitrary_boolean_formulas && cluster_global_time_out_enabled && avoid_cluster_global_time_out_at_top_node && polarity == negated && formula == Aig_Regular(input_arbitrary_boolean_formula) && Aig_IsComplement(input_arbitrary_boolean_formula))//Time-out at lower level nodes, but the result should be exact
	// Hence call factorizedSkolemFunctionGenerator
	{
		disableTimeOut_In_Cluster();
		#ifdef DEBUG_SKOLEM
		cout << "\nTIME-OUT DISABLED FOR THE TOP-NODE\n";
		#endif

		// setting variablestoeliminate and Factors
		list<string> VariablesToEliminate_Copy;
		VariablesToEliminate_Copy = Global_VariablesToEliminate;

		bool all_variables_to_eliminate_occure_in_formula;
		bool no_variables_to_eliminate_occure_in_formula;

		set<string> support_formula;
		computeSupport(formula, support_formula, pub_aig_manager);
		set<string> variables_to_eliminate_in_support_formula;
		set_intersection(support_formula.begin(), support_formula.end(), Global_VariablesToEliminate_Set.begin(), Global_VariablesToEliminate_Set.end(), inserter(variables_to_eliminate_in_support_formula, variables_to_eliminate_in_support_formula.begin()));

		if(variables_to_eliminate_in_support_formula.empty())//no variable to elimiate occure in formula
		{
			no_variables_to_eliminate_occure_in_formula = true;
			all_variables_to_eliminate_occure_in_formula = false;
		}
		else if(variables_to_eliminate_in_support_formula.size() == Global_VariablesToEliminate_Set.size()) // all variable to elimiate occure in formula
		{
			no_variables_to_eliminate_occure_in_formula = false;
			all_variables_to_eliminate_occure_in_formula = true;
		}
		else
		{
			no_variables_to_eliminate_occure_in_formula = false;
			all_variables_to_eliminate_occure_in_formula = false;
		}
	

		// To store r1 and r0 for variables NOT occuring in formula
		map<string, Aig_Obj_t*> map_of_r1s_of_free_variables;
		map<string, Aig_Obj_t*> map_of_r0s_of_free_variables;

		if(!no_variables_to_eliminate_occure_in_formula) // there are some variables to eliminate that occure in formula	
		{
			number_of_cegarskolem_calls_on_arbitrary_boolean_formulas++;

			assert(polarity == negated);

			// Factors are the children
			Factors.insert(Aig_ObjChild0(formula));
			Factors.insert(Aig_ObjChild1(formula));


			// setting parameters for CegarSkolem
			perform_reverse_substitution = false;	
			enable_cegar = true;
			use_bads_in_unified_cegar = false;
			use_cbzero_in_unified_cegar = false;
			use_assumptions_in_unified_cegar = false;
			accumulate_formulae_in_cbzero_in_cegar = true;	
			drop_free_factors = false; // It is important to set this, otherwise free
			// factors will be dropped, and we won't get exact result
			depth_from_root_in_cegarskolem_call_on_arbitrary_boolean_formulas = depth_from_root;
			factorizedskolem_applied_on_disjunction = true;

			if(avoid_sat_call_in_functional_forms && depth_from_root == 0)
			{
				internal_flag_to_avoid_sat_call_in_functional_forms = true;
			}
			else
			{
				internal_flag_to_avoid_sat_call_in_functional_forms = false;
			}

			#ifdef DETAILED_RECORD_KEEP
			struct timeval cegarskolem_step_start_ms, cegarskolem_step_finish_ms;
			unsigned long long int cegarskolem_time;
			gettimeofday (&cegarskolem_step_start_ms, NULL); 
			#endif
	
			// Let's call factorizedSkolemFunctionGenerator with these parameters
			// This will give r1 and r0 for variables occuring in Factors in global 
			// data-structures 
			
			//#ifdef DEBUG_PAR
			//cout << "\nfactorizedSkolemFunctionGenerator called\n";
			//#endif		

			factorizedSkolemFunctionGenerator(Factors, VariablesToEliminate_Copy);

			#ifdef DETAILED_RECORD_KEEP
			gettimeofday (&cegarskolem_step_finish_ms, NULL);
			cegarskolem_time = cegarskolem_step_finish_ms.tv_sec * 1000 + cegarskolem_step_finish_ms.tv_usec / 1000;
			cegarskolem_time -= cegarskolem_step_start_ms.tv_sec * 1000 + cegarskolem_step_start_ms.tv_usec / 1000;
	
			total_time_in_cegarskolem = total_time_in_cegarskolem + cegarskolem_time;

			total_number_of_cegar_iterations_in_cegarskolem = total_number_of_cegar_iterations_in_cegarskolem + cegar_iteration_number;


			if(max_number_of_cegar_iterations_in_cegarskolem == -1)
			{
				max_number_of_cegar_iterations_in_cegarskolem = cegar_iteration_number;
			}
			else if(max_number_of_cegar_iterations_in_cegarskolem < cegar_iteration_number)
			{
				max_number_of_cegar_iterations_in_cegarskolem = cegar_iteration_number;
			}
			if(min_number_of_cegar_iterations_in_cegarskolem == -1)
			{
				min_number_of_cegar_iterations_in_cegarskolem = cegar_iteration_number;
			}
			else if(min_number_of_cegar_iterations_in_cegarskolem > cegar_iteration_number)
			{
				min_number_of_cegar_iterations_in_cegarskolem = cegar_iteration_number;
			}
			#endif	
		
		}

		if(checkTimeOut()) // check for time-out
		{
			#ifdef RECORD_KEEP
			string record_file;
			record_file = logfile_prefix;
			record_file += "skolem_function_generation_details.txt";
			FILE* record_fp = fopen(record_file.c_str(), "a+");
			assert(record_fp != NULL);

			fprintf(record_fp, "\nTime-out inside the function AIGBasedSkolem::factorizedSkolemFunctionGenerator\n");

			fclose(record_fp);
			#endif

			cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::callDisjunction\n";
			timed_out = true; // timed_out flag set
			return;
		}

		if(!all_variables_to_eliminate_occure_in_formula) // there are some variables to eliminate that does NOT occure in formula	
		{
			// To get r1 and r0 for variables NOT occuring in Factors
			getR1R0ForFreeVariablesInDisjunction(formula, map_of_r1s_of_free_variables, map_of_r0s_of_free_variables);
		}

		
		// Get the cannot be one sets, and cannot be zero sets
		for(list<string>::iterator list_it = Global_VariablesToEliminate.begin(); list_it != Global_VariablesToEliminate.end(); list_it++)
		{
			string variable_to_eliminate = *list_it;
			int index_of_variable_to_eliminate = searchVarNameToVarIndexMap(var_name_to_var_index_map, variable_to_eliminate);

			#ifdef DEBUG_SKOLEM
			cout << "\nvariable_to_eliminate = " << variable_to_eliminate << "\tindex_of_variable_to_eliminate = " << index_of_variable_to_eliminate << endl;
			#endif

			Aig_Obj_t* cannot_be_one_function;
			Aig_Obj_t* cannot_be_zero_function;
		
			if(index_of_variable_to_eliminate == -1) // Factors free of variable_to_eliminate
			{
				map<string, Aig_Obj_t*>::iterator map_of_rs_it;
			
				map_of_rs_it = map_of_r1s_of_free_variables.find(variable_to_eliminate);
				assert(map_of_rs_it != map_of_r1s_of_free_variables.end());
				cannot_be_one_function = map_of_rs_it->second;
				assert(cannot_be_one_function != NULL);	
			
				map_of_rs_it = map_of_r0s_of_free_variables.find(variable_to_eliminate);
				assert(map_of_rs_it != map_of_r0s_of_free_variables.end());
				cannot_be_zero_function = map_of_rs_it->second;
				assert(cannot_be_zero_function != NULL);

				// connect to some output to avoid unwanted deletion
				Aig_Obj_t* cannot_be_one_function_CO = Aig_ObjCreateCo(pub_aig_manager, cannot_be_one_function ); 
				assert(cannot_be_one_function_CO != NULL);
				r1r0_cos_created.insert(cannot_be_one_function_CO);

				Aig_Obj_t* cannot_be_zero_function_CO = Aig_ObjCreateCo(pub_aig_manager, cannot_be_zero_function ); 
				assert(cannot_be_zero_function_CO != NULL);
				r1r0_cos_created.insert(cannot_be_zero_function_CO);
			}
			else // Factors not free of variable_to_eliminate; index_of_variable_to_eliminate gives the 
			// location of variable_to_eliminate in the Local Tables of factorizedSkolemFunctionGenerator
			// that stores r1's and r0's
			{
				set<Aig_Obj_t*> cannot_be_one_function_elements;
				set<Aig_Obj_t*> cannot_be_one_function_objects;
				map<int, set<Aig_Obj_t*> >::iterator cannot_be_one_set_it = cannot_be_one_set.find(index_of_variable_to_eliminate);
				assert(cannot_be_one_set_it != cannot_be_one_set.end());
				cannot_be_one_function_objects = cannot_be_one_set_it->second;

				for(set<Aig_Obj_t*>::iterator cannot_be_one_function_objects_it = cannot_be_one_function_objects.begin(); cannot_be_one_function_objects_it != cannot_be_one_function_objects.end(); cannot_be_one_function_objects_it++)
				{
					Aig_Obj_t* cannot_be_object = *cannot_be_one_function_objects_it;
					assert(cannot_be_object != NULL);

					map<Aig_Obj_t*, Aig_Obj_t*>::iterator cannot_be_object_to_cannot_be_dag_map_it = cannot_be_object_to_cannot_be_dag_map.find(cannot_be_object);
					Aig_Obj_t* cannot_be_dag = cannot_be_object_to_cannot_be_dag_map_it->second;
					assert(cannot_be_dag != NULL);
				
					cannot_be_one_function_elements.insert(cannot_be_dag);
				}

				assert(!cannot_be_one_function_elements.empty());
				cannot_be_one_function = createOr(cannot_be_one_function_elements, pub_aig_manager);
				assert(cannot_be_one_function != NULL);

				set<Aig_Obj_t*> cannot_be_zero_function_elements;
				set<Aig_Obj_t*> cannot_be_zero_function_objects;
				map<int, set<Aig_Obj_t*> >::iterator cannot_be_zero_set_it = cannot_be_zero_set.find(index_of_variable_to_eliminate);
				assert(cannot_be_zero_set_it != cannot_be_zero_set.end());
				cannot_be_zero_function_objects = cannot_be_zero_set_it->second;

				for(set<Aig_Obj_t*>::iterator cannot_be_zero_function_objects_it = cannot_be_zero_function_objects.begin(); cannot_be_zero_function_objects_it != cannot_be_zero_function_objects.end(); cannot_be_zero_function_objects_it++)
				{
					Aig_Obj_t* cannot_be_object = *cannot_be_zero_function_objects_it;
					assert(cannot_be_object != NULL);

					map<Aig_Obj_t*, Aig_Obj_t*>::iterator cannot_be_object_to_cannot_be_dag_map_it = cannot_be_object_to_cannot_be_dag_map.find(cannot_be_object);
					Aig_Obj_t* cannot_be_dag = cannot_be_object_to_cannot_be_dag_map_it->second;
					assert(cannot_be_dag != NULL);
				
					cannot_be_zero_function_elements.insert(cannot_be_dag);
				}

				assert(!cannot_be_zero_function_elements.empty());
				cannot_be_zero_function = createOr(cannot_be_zero_function_elements, pub_aig_manager);
				assert(cannot_be_zero_function != NULL);
			
				// connect to some output to avoid unwanted deletion
				Aig_Obj_t* cannot_be_one_function_CO = Aig_ObjCreateCo(pub_aig_manager, cannot_be_one_function ); 
				assert(cannot_be_one_function_CO != NULL);
				r1r0_cos_created.insert(cannot_be_one_function_CO);

				Aig_Obj_t* cannot_be_zero_function_CO = Aig_ObjCreateCo(pub_aig_manager, cannot_be_zero_function ); 
				assert(cannot_be_zero_function_CO != NULL);
				r1r0_cos_created.insert(cannot_be_zero_function_CO);			
			}

			list_of_r1s.push_back(cannot_be_one_function);
			list_of_r0s.push_back(cannot_be_zero_function);

			#ifdef DETAILED_RECORD_KEEP

			#ifdef PERFORM_SIZE_COMPUTATIONS_IN_PAR
			r1_size = computeSize(cannot_be_one_function, pub_aig_manager);
			r0_size = computeSize(cannot_be_zero_function, pub_aig_manager);
			#else
			r1_size = 0;
			r0_size = 0;
			#endif

			total_r1_size = total_r1_size + r1_size;
			total_r0_size = total_r0_size + r0_size;

			if(max_r1_size == -1)
			{
				max_r1_size = r1_size;
			}
			else if(max_r1_size < r1_size)
			{
				max_r1_size = r1_size;
			}
			if(max_r0_size == -1)
			{
				max_r0_size = r0_size;
			}
			else if(max_r0_size < r0_size)
			{
				max_r0_size = r0_size;
			}
		
				
			if(min_r1_size == -1)
			{
				min_r1_size = r1_size;
			}
			else if(min_r1_size > r1_size)
			{
				min_r1_size = r1_size;
			}
			if(min_r0_size == -1)
			{
				min_r0_size = r0_size;
			}
			else if(min_r0_size > r0_size)
			{
				min_r0_size = r0_size;
			}
			#endif


			#ifdef DEBUG_SKOLEM
			string cannot_be_one_file_name = "r1_";
			string cannot_be_zero_file_name = "r0_";
		
			char formula_char[100];
			sprintf(formula_char, "%p", formula);
			string formula_string(formula_char);
			if(polarity == negated)
			{
				formula_string += "n";
			}
			else
			{
				formula_string += "o";
			}

			cannot_be_one_file_name += formula_string;
			cannot_be_one_file_name += "_";
			cannot_be_zero_file_name += formula_string;
			cannot_be_zero_file_name += "_";
		
			cannot_be_one_file_name += variable_to_eliminate;
			cannot_be_one_file_name += ".v";
			cannot_be_zero_file_name += variable_to_eliminate;
			cannot_be_zero_file_name += ".v";

			writeFormulaToFile(pub_aig_manager, cannot_be_one_function, cannot_be_one_file_name);
			writeFormulaToFile(pub_aig_manager, cannot_be_zero_function, cannot_be_zero_file_name);
			#endif
		
		}// for each variable ends here

		// Enter into hash tables the entries
		// (polarity, formula) --> list_of_r1s and (polarity, formula) --> list_of_r0s
		// (original_polarity, original_formula) --> list_of_r1s and 
		// (original_polarity, original_formula) --> list_of_r0s

		insertIntoR0HashTable(polarity, formula, list_of_r0s);
		insertIntoR1HashTable(polarity, formula, list_of_r1s);
	
		if(polarity != original_polarity || formula != original_formula)
		{
			insertIntoR0HashTable(original_polarity, original_formula, list_of_r0s);
			insertIntoR1HashTable(original_polarity, original_formula, list_of_r1s);		
		}
	
		if(!no_variables_to_eliminate_occure_in_formula)
		{
			clearAllDataStructures();
			setParametersToDefaults();	
		}
		
	} // calling factorizedSkolem at disjunction ends here
	else // usual code: just conjoin the r1/r0's
	{

		assert(polarity == negated);

		// Factors are the children
		Factors.insert(Aig_ObjChild0(formula));
		Factors.insert(Aig_ObjChild1(formula));	

		int factor_index = 1;
		map<int, vector<Aig_Obj_t*> > factor_index_to_list_of_r0s_map;
		map<int, vector<Aig_Obj_t*> > factor_index_to_list_of_r1s_map;

		for(set<Aig_Obj_t*>::iterator Factors_it = Factors.begin(); Factors_it != Factors.end(); Factors_it++)
		{
			Aig_Obj_t* given_factor;
			given_factor = *Factors_it;
			assert(given_factor != NULL);
				
			vector<Aig_Obj_t*> list_of_r0s_of_factor;
			vector<Aig_Obj_t*> list_of_r1s_of_factor;
			call_type factor_polarity = negated;
				
			getEntryFromR0HashTable(factor_polarity, given_factor, list_of_r0s_of_factor);
			getEntryFromR1HashTable(factor_polarity, given_factor, list_of_r1s_of_factor);
				
			factor_index_to_list_of_r0s_map.insert(make_pair(factor_index, list_of_r0s_of_factor));
			factor_index_to_list_of_r1s_map.insert(make_pair(factor_index, list_of_r1s_of_factor));

			factor_index++;
		}//consider each factor ends here

		// We have list_of_r0s and list_of_r1s of each factor now
		// From these lists construct the final r0's and r1's

		int location_of_var_to_elim = 0;

		for(list<string>::iterator list_it = Global_VariablesToEliminate.begin(); list_it != Global_VariablesToEliminate.end(); list_it++)
		{
			string var_to_elim = *list_it;
		
			if(checkTimeOut()) // check for time-out
			{
				cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::callDisjunction\n";
				timed_out = true; // timed_out flag set
				return;
			}		

			#ifdef DEBUG_SKOLEM
			cout << "\nGetting cannot-be-1 and cannot-be-0 sets of " << var_to_elim << " from hash tables" << endl;
			#endif

			Aig_Obj_t* cannot_be_one_function;
			Aig_Obj_t* cannot_be_zero_function;
			set<Aig_Obj_t*> cannot_be_one_set_for_var_to_elim_index;
			set<Aig_Obj_t*> cannot_be_zero_set_for_var_to_elim_index;

			int factor_index = 1;
			for(set<Aig_Obj_t*>::iterator Factors_it = Factors.begin(); Factors_it != Factors.end(); Factors_it++)
			{
				#ifdef DEBUG_SKOLEM
				cout << "\nfactor_index = " << factor_index << endl;
				#endif

				map<int, vector<Aig_Obj_t*> >::iterator factor_index_to_list_of_r1s_map_it = factor_index_to_list_of_r1s_map.find(factor_index);
				assert(factor_index_to_list_of_r1s_map_it != factor_index_to_list_of_r1s_map.end());

				Aig_Obj_t* r1 = (factor_index_to_list_of_r1s_map_it->second)[location_of_var_to_elim];
		  		assert(r1 != NULL);		
		
		
				// connecting to some output to avoid unwanted deletion
				Aig_Obj_t* r1_CO = Aig_ObjCreateCo(pub_aig_manager, r1 ); 
				assert(r1_CO != NULL);
				intermediate_cos_created.insert(r1_CO);

				map<int, vector<Aig_Obj_t*> >::iterator factor_index_to_list_of_r0s_map_it = factor_index_to_list_of_r0s_map.find(factor_index);
				assert(factor_index_to_list_of_r0s_map_it != factor_index_to_list_of_r0s_map.end());

				Aig_Obj_t* r0 = (factor_index_to_list_of_r0s_map_it->second)[location_of_var_to_elim];
		  		assert(r0 != NULL);		
		
				// connecting to some output to avoid unwanted deletion
				Aig_Obj_t* r0_CO = Aig_ObjCreateCo(pub_aig_manager, r0 ); 
				assert(r0_CO != NULL);
				intermediate_cos_created.insert(r0_CO);
	
				// Insert the dags in respective cannot-be-sets
				cannot_be_one_set_for_var_to_elim_index.insert(r1);
				cannot_be_zero_set_for_var_to_elim_index.insert(r0);

				factor_index++;
			}// for each factor ends here

			assert(!cannot_be_one_set_for_var_to_elim_index.empty());
			cannot_be_one_function = createAnd(cannot_be_one_set_for_var_to_elim_index, pub_aig_manager);
			assert(cannot_be_one_function != NULL);

			assert(!cannot_be_zero_set_for_var_to_elim_index.empty());
			cannot_be_zero_function = createAnd(cannot_be_zero_set_for_var_to_elim_index, pub_aig_manager);
			assert(cannot_be_zero_function != NULL);
		
			// connect to some output to avoid unwanted deletion
			Aig_Obj_t* cannot_be_one_function_CO = Aig_ObjCreateCo(pub_aig_manager, cannot_be_one_function ); 
			assert(cannot_be_one_function_CO != NULL);
			r1r0_cos_created.insert(cannot_be_one_function_CO);

			Aig_Obj_t* cannot_be_zero_function_CO = Aig_ObjCreateCo(pub_aig_manager, cannot_be_zero_function ); 
			assert(cannot_be_zero_function_CO != NULL);
			r1r0_cos_created.insert(cannot_be_zero_function_CO);			
	
			list_of_r1s.push_back(cannot_be_one_function);
			list_of_r0s.push_back(cannot_be_zero_function);

			location_of_var_to_elim++;

			#ifdef DETAILED_RECORD_KEEP

			#ifdef PERFORM_SIZE_COMPUTATIONS_IN_PAR
			r1_size = computeSize(cannot_be_one_function, pub_aig_manager);
			r0_size = computeSize(cannot_be_zero_function, pub_aig_manager);
			#else
			r1_size = 0;
			r0_size = 0;
			#endif

			total_r1_size = total_r1_size + r1_size;
			total_r0_size = total_r0_size + r0_size;

			if(max_r1_size == -1)
			{
				max_r1_size = r1_size;
			}
			else if(max_r1_size < r1_size)
			{
				max_r1_size = r1_size;
			}
			if(max_r0_size == -1)
			{
				max_r0_size = r0_size;
			}
			else if(max_r0_size < r0_size)
			{
				max_r0_size = r0_size;
			}
		
				
			if(min_r1_size == -1)
			{
				min_r1_size = r1_size;
			}
			else if(min_r1_size > r1_size)
			{
				min_r1_size = r1_size;
			}
			if(min_r0_size == -1)
			{
				min_r0_size = r0_size;
			}
			else if(min_r0_size > r0_size)
			{
				min_r0_size = r0_size;
			}
			#endif

			#ifdef DEBUG_SKOLEM
			string cannot_be_one_file_name = "r1_";
			string cannot_be_zero_file_name = "r0_";
		
			char formula_char[100];
			sprintf(formula_char, "%p", formula);
			string formula_string(formula_char);
			if(polarity == negated)
			{
				formula_string += "n";
			}
			else
			{
				formula_string += "o";
			}

			cannot_be_one_file_name += formula_string;
			cannot_be_one_file_name += "_";
			cannot_be_zero_file_name += formula_string;
			cannot_be_zero_file_name += "_";
		
			cannot_be_one_file_name += var_to_elim;
			cannot_be_one_file_name += ".v";
			cannot_be_zero_file_name += var_to_elim;
			cannot_be_zero_file_name += ".v";

			writeFormulaToFile(pub_aig_manager, cannot_be_one_function, cannot_be_one_file_name);
			writeFormulaToFile(pub_aig_manager, cannot_be_zero_function, cannot_be_zero_file_name);
			#endif
		
		}// for each variable ends here

		// Enter into hash tables the entries
		// (polarity, formula) --> list_of_r1s and (polarity, formula) --> list_of_r0s
		// (original_polarity, original_formula) --> list_of_r1s and 
		// (original_polarity, original_formula) --> list_of_r0s

		insertIntoR0HashTable(polarity, formula, list_of_r0s);
		insertIntoR1HashTable(polarity, formula, list_of_r1s);
	
		if(polarity != original_polarity || formula != original_formula)
		{
			insertIntoR0HashTable(original_polarity, original_formula, list_of_r0s);
			insertIntoR1HashTable(original_polarity, original_formula, list_of_r1s);		
		}

	}// usual code: just conjoin the r1/r0's ends here

	#ifdef DETAILED_RECORD_KEEP
	gettimeofday (&calldisjunction_step_finish_ms, NULL);
	calldisjunction_time = calldisjunction_step_finish_ms.tv_sec * 1000 + calldisjunction_step_finish_ms.tv_usec / 1000;
	calldisjunction_time -= calldisjunction_step_start_ms.tv_sec * 1000 + calldisjunction_step_start_ms.tv_usec / 1000;
	
	total_time_in_calldisjunction = total_time_in_calldisjunction + calldisjunction_time;


	string record_file;
	record_file = logfile_prefix;
	record_file += "skolem_function_generation_details.txt";
	FILE* record_fp = fopen(record_file.c_str(), "a+");
	assert(record_fp != NULL);

	if(!mask_printing_details_file)
	{
		fprintf(record_fp, "\nDetails of find_skolem_disjunction Call#:%d (Depth from root = %d)\nTime = %llu\nmax r1 size = %d\tmin r1 size = %d\tavg r1 size = %f\nmax r0 size = %d\tmin r0 size = %d\tavg r0 size = %f\n", number_of_disjunctions_on_arbitrary_boolean_formulas, depth_from_root, calldisjunction_time, max_r1_size, min_r1_size, (float)total_r1_size/(float)Global_VariablesToEliminate_Set.size(), max_r0_size, min_r0_size, (float)total_r0_size/(float)Global_VariablesToEliminate_Set.size());
	}

	fclose(record_fp);	
	#endif

	if(prove_correctness_of_skolem_functions_of_arbitrary_boolean_formula_detailed_check)
	{
		Aig_Obj_t* disjunction_formula = createNot(formula, pub_aig_manager);
		assert(disjunction_formula != NULL);

		// Create the Skolem functions			
		
		assert(list_of_r1s.size() == Global_VariablesToEliminate.size());

		vector<Aig_Obj_t*> skolem_functions_of_disjunction_formula;
		for(int i = 0; i < list_of_r1s.size(); i++)
		{
			Aig_Obj_t* r1_i = list_of_r1s[i];
			assert(r1_i != NULL);

			Aig_Obj_t* skolem_i = createNot(r1_i, pub_aig_manager); 
			assert(skolem_i != NULL);

			skolem_functions_of_disjunction_formula.push_back(skolem_i);		
		}

		vector<Aig_Obj_t*> skolem_functions_of_disjunction_formula_before_reverse_substitution;
		skolem_functions_of_disjunction_formula_before_reverse_substitution = skolem_functions_of_disjunction_formula;
		// Perform reverse-substitution
		performReverseSubstitutionOfSkolemFunctions(skolem_functions_of_disjunction_formula);

		
		// Check for exactness
		// First create F(psi(Y), Y)
		bool ensure_that_skolem_functions_are_on_y = true;
		
		map<string, Aig_Obj_t*> skolem_function_replacement_map;
		int i = 0;
		for(list<string>::iterator list_it = Global_VariablesToEliminate.begin(); list_it != Global_VariablesToEliminate.end(); list_it++)
		{
			string variable_to_eliminate = *list_it;
			
			Aig_Obj_t* skolem_i = skolem_functions_of_disjunction_formula[i];
			assert(skolem_i != NULL);

			if(ensure_that_skolem_functions_are_on_y)
			{
				set<string> support_skolem_i;
				computeSupport(skolem_i, support_skolem_i, pub_aig_manager);
				
				set<string> varstoelim_in_support_skolem_i;
				set_intersection(support_skolem_i.begin(), support_skolem_i.end(), Global_VariablesToEliminate_Set.begin(), Global_VariablesToEliminate_Set.end(), inserter(varstoelim_in_support_skolem_i, varstoelim_in_support_skolem_i.begin()));

				if(!varstoelim_in_support_skolem_i.empty())				
				{
					cout << "\nSkolem function of variable " << variable_to_eliminate << " involves variables to be eliminated\n";
					assert(false);	
				}
			}

			skolem_function_replacement_map.insert(make_pair(variable_to_eliminate, skolem_i));
				
			i++;
		
		}// for each variable ends here	


		// Printing to ensure correctness
		for(list<string>::iterator list_it = Global_VariablesToEliminate.begin(); list_it != Global_VariablesToEliminate.end(); list_it++)
		{
			string variable_to_eliminate = *list_it;
				
			Aig_Obj_t* my_skolem;
			my_skolem = skolem_function_replacement_map[variable_to_eliminate];

			string my_skolem_file_name = "original_problem_skolem_";
			my_skolem_file_name += variable_to_eliminate;
			my_skolem_file_name += ".v";
			writeFormulaToFile(pub_aig_manager, my_skolem, my_skolem_file_name);
		}
		// Printing to ensure correctness ends here

		assert(skolem_function_replacement_map.size() > 0);

		Aig_Obj_t* result_of_qe_using_skolem_functions;
		result_of_qe_using_skolem_functions = replaceVariablesByFormulas(disjunction_formula, skolem_function_replacement_map);	
		assert(result_of_qe_using_skolem_functions != NULL); // F(psi(Y), Y)

		// Printing to ensure correctness
		string result_of_qe_using_skolem_functions_file_name = "result_of_qe_using_skolem_functions.v";
		writeFormulaToFile(pub_aig_manager, result_of_qe_using_skolem_functions, result_of_qe_using_skolem_functions_file_name);
		// Printing to ensure correctness ends here	

		list<string> VariablesToEliminate_Copy;
		VariablesToEliminate_Copy = Global_VariablesToEliminate;

		Aig_Obj_t* equivalence_check; // ~F(psi(Y), Y) \wedge F(X, Y)
		equivalence_check = createAnd(createNot(result_of_qe_using_skolem_functions, pub_aig_manager), disjunction_formula, pub_aig_manager);
		assert(equivalence_check != NULL);

		// Give to SAT-Solver
		unsigned long long int cnf_time;
		int formula_size;
		unsigned long long int simplification_time;
		map<string, int> Model_of_equivalence_check;
		bool result_of_equivalence_check;

		result_of_equivalence_check = isSat(pub_aig_manager, equivalence_check, Model_of_equivalence_check, cnf_time, formula_size, simplification_time);

		if(result_of_equivalence_check)
		{
			cout << "\nexists X.f => f[X --> psi] is NOT valid\n";
			cout << "\nCounterexample is\n";
			displayModelFromSATSolver(Model_of_equivalence_check);			
		}
		else
		{
			cout << "\nexists X.f => f[X --> psi] is valid\n";
		}

		string record_file;
		record_file = logfile_prefix;
		record_file += "skolem_function_generation_details.txt";
		FILE* record_fp = fopen(record_file.c_str(), "a+");
		assert(record_fp != NULL);

		if(result_of_equivalence_check)
		{
			fprintf(record_fp, "\n\nexists X.f(X,Y) = f'(psi,Y) is NOT valid; Skolem functions are NOT exact\n");
		}
		else
		{
			fprintf(record_fp, "\n\nexists X.f(X,Y) = f'(psi,Y) is valid; Skolem functions are exact\n");		

		}

		fclose(record_fp);

		if(result_of_equivalence_check) // not exact
		{
			//Analysis to find the reason behind inexactness

			string problem_formula_file_name;
			problem_formula_file_name = "problem_formula.v";
			writeFormulaToFile(pub_aig_manager, disjunction_formula, problem_formula_file_name);

			string child1_problem_formula_file_name;
			child1_problem_formula_file_name = "child1_problem_formula.v";
			writeFormulaToFile(pub_aig_manager, Aig_ObjChild0(formula), child1_problem_formula_file_name);

			string child2_problem_formula_file_name;
			child2_problem_formula_file_name = "child2_problem_formula.v";
			writeFormulaToFile(pub_aig_manager, Aig_ObjChild1(formula), child2_problem_formula_file_name);

	
			// Let's see the truth values of the formulas
			map<string, bool> Model_of_equivalence_check_in_bool;
			for(map<string, int>::iterator Model_of_equivalence_check_it = Model_of_equivalence_check.begin(); Model_of_equivalence_check_it != Model_of_equivalence_check.end(); Model_of_equivalence_check_it++)
			{
				string variable_name = Model_of_equivalence_check_it->first;
				int variable_value = Model_of_equivalence_check_it->second;

				bool variable_value_bool;
				if(variable_value == 1)
				{
					variable_value_bool = true;
				}
				else
				{
					variable_value_bool = false;
				}

				Model_of_equivalence_check_in_bool.insert(make_pair(variable_name, variable_value_bool));				
			}

			Aig_Obj_t* child1_of_problem = createNot(Aig_ObjChild0(formula), pub_aig_manager); //F1(X, Y)
			Aig_Obj_t* child2_of_problem = createNot(Aig_ObjChild1(formula), pub_aig_manager); //F2(X, Y)
			
			Aig_Obj_t* qe_child1_of_problem;
			qe_child1_of_problem = replaceVariablesByFormulas(child1_of_problem, skolem_function_replacement_map);	
			assert(qe_child1_of_problem != NULL); // F1(psi(Y), Y)	

			Aig_Obj_t* qe_child2_of_problem;
			qe_child2_of_problem = replaceVariablesByFormulas(child2_of_problem, skolem_function_replacement_map);	
			assert(qe_child2_of_problem != NULL); // F2(psi(Y), Y)

			bool value_of_result_of_qe_using_skolem_functions = evaluateFormulaOfCi(result_of_qe_using_skolem_functions, Model_of_equivalence_check_in_bool);

			bool value_of_qe_child1_of_problem = evaluateFormulaOfCi(qe_child1_of_problem, Model_of_equivalence_check_in_bool);

			bool value_of_qe_child2_of_problem = evaluateFormulaOfCi(qe_child2_of_problem, Model_of_equivalence_check_in_bool);

			bool value_of_disjunction_formula = evaluateFormulaOfCi(disjunction_formula, Model_of_equivalence_check_in_bool);

			bool value_of_child1_of_problem = evaluateFormulaOfCi(child1_of_problem, Model_of_equivalence_check_in_bool);

			bool value_of_child2_of_problem = evaluateFormulaOfCi(child2_of_problem, Model_of_equivalence_check_in_bool);

			cout << "\nvalue_of_result_of_qe_using_skolem_functions = " << value_of_result_of_qe_using_skolem_functions << endl;

			cout << "\nvalue_of_qe_child1_of_problem = " << value_of_qe_child1_of_problem << endl;

			cout << "\nvalue_of_qe_child2_of_problem = " << value_of_qe_child2_of_problem << endl;

			cout << "\nvalue_of_disjunction_formula = " << value_of_disjunction_formula << endl;

			cout << "\nvalue_of_child1_of_problem = " << value_of_child1_of_problem << endl;

			cout << "\nvalue_of_child2_of_problem = " << value_of_child2_of_problem << endl;

			// Let's see F1(X, Y) for these values of Y under Skolem functions for X in F1(X, Y)
			// Also let's see F2(X, Y) for these values of Y under Skolem functions for X in F2(X, Y)
			int factor_under_consideration = 1;
			map<string, Aig_Obj_t*> skolem_function_replacement_map_of_factor1;
			map<string, Aig_Obj_t*> skolem_function_replacement_map_of_factor2;
			vector<Aig_Obj_t*> skolem_functions_of_factor1_before_reverse_substitution;
			vector<Aig_Obj_t*> skolem_functions_of_factor2_before_reverse_substitution;
			for(set<Aig_Obj_t*>::iterator Factors_it = Factors.begin(); Factors_it != Factors.end(); Factors_it++)
			{
				Aig_Obj_t* given_factor;
				given_factor = *Factors_it;
				assert(given_factor != NULL);
				
				vector<Aig_Obj_t*> list_of_r1s_of_factor;
				call_type factor_polarity = negated;
				
				getEntryFromR1HashTable(factor_polarity, given_factor, list_of_r1s_of_factor);
				
				vector<Aig_Obj_t*> skolem_functions_of_factor;
				for(int i = 0; i < list_of_r1s_of_factor.size(); i++)
				{
					Aig_Obj_t* r1_i = list_of_r1s_of_factor[i];
					assert(r1_i != NULL);

					Aig_Obj_t* skolem_i = createNot(r1_i, pub_aig_manager); 
					assert(skolem_i != NULL);

					skolem_functions_of_factor.push_back(skolem_i);		
				}

				if(factor_under_consideration == 1)
				{
					skolem_functions_of_factor1_before_reverse_substitution = skolem_functions_of_factor;
				}
				else if(factor_under_consideration == 2)
				{		
					skolem_functions_of_factor2_before_reverse_substitution = skolem_functions_of_factor;
				}
				else
				{
					assert(false);
				}

				performReverseSubstitutionOfSkolemFunctions(skolem_functions_of_factor);

				map<string, Aig_Obj_t*> skolem_function_replacement_map_of_factor;
				int index_of_var_in_factor = 0;
				for(list<string>::iterator list_it = Global_VariablesToEliminate.begin(); list_it != Global_VariablesToEliminate.end(); list_it++)
				{
					string variable_to_eliminate = *list_it;
					Aig_Obj_t* skolem_i = skolem_functions_of_factor[index_of_var_in_factor];
					assert(skolem_i != NULL);

					skolem_function_replacement_map_of_factor.insert(make_pair(variable_to_eliminate, skolem_i));
					index_of_var_in_factor++;
		
				}// for each variable ends here	

				Aig_Obj_t* neg_given_factor = createNot(given_factor, pub_aig_manager); 
				Aig_Obj_t* qe_neg_given_factor;
				qe_neg_given_factor = replaceVariablesByFormulas(neg_given_factor, skolem_function_replacement_map_of_factor);	
				assert(qe_neg_given_factor != NULL); 

				bool value_of_qe_neg_given_factor = evaluateFormulaOfCi(qe_neg_given_factor, Model_of_equivalence_check_in_bool);

				cout << "\nvalue_of_qe_neg_given_factor = " << value_of_qe_neg_given_factor << endl;

				if(factor_under_consideration == 1)
				{
					skolem_function_replacement_map_of_factor1 = skolem_function_replacement_map_of_factor;
				}
				else if(factor_under_consideration == 2)
				{		
					skolem_function_replacement_map_of_factor2 = skolem_function_replacement_map_of_factor;
				}
				else
				{
					assert(false);
				}
				
				factor_under_consideration++;

			}//consider each factor ends here

			map<string, bool> Model_of_equivalence_check_in_bool_on_y;
			cout << "\nModel_of_equivalence_check_in_bool_on_y\n";
			for(map<string, bool>::iterator Model_of_equivalence_check_in_bool_it = Model_of_equivalence_check_in_bool.begin(); Model_of_equivalence_check_in_bool_it != Model_of_equivalence_check_in_bool.end(); Model_of_equivalence_check_in_bool_it++)
			{
				string variable_name = Model_of_equivalence_check_in_bool_it->first;
				bool variable_value = Model_of_equivalence_check_in_bool_it->second;

				if(Global_VariablesToRemain_Set.find(variable_name) != Global_VariablesToRemain_Set.end())
				{
					Model_of_equivalence_check_in_bool_on_y.insert(make_pair(variable_name, variable_value));		
					cout << "\nvariable_name = " << variable_name << "\tvariable_value = " << variable_value;	
				}	
			}			


			int index_of_var_under_consideration = 0;
			for(list<string>::iterator list_it = Global_VariablesToEliminate.begin(); list_it != Global_VariablesToEliminate.end(); list_it++)
			{
				string variable_to_eliminate = *list_it;
				
				Aig_Obj_t* skolem_factor1;
				skolem_factor1 = skolem_function_replacement_map_of_factor1[variable_to_eliminate];

				Aig_Obj_t* skolem_factor2;
				skolem_factor2 = skolem_function_replacement_map_of_factor2[variable_to_eliminate];
	
				Aig_Obj_t* my_skolem;
				my_skolem = skolem_function_replacement_map[variable_to_eliminate];

				string my_skolem_file_name = "problem_skolem_";
				my_skolem_file_name += variable_to_eliminate;
				my_skolem_file_name += ".v";
				writeFormulaToFile(pub_aig_manager, my_skolem, my_skolem_file_name);
			
				bool value_of_skolem_factor1 = evaluateFormulaOfCi(skolem_factor1, Model_of_equivalence_check_in_bool_on_y);

				cout << "\nEvaluation of skolem_factor1 Done\n";

				bool value_of_skolem_factor2 = evaluateFormulaOfCi(skolem_factor2, Model_of_equivalence_check_in_bool_on_y);

				cout << "\nEvaluation of skolem_factor2 Done\n";

				bool value_of_my_skolem = evaluateFormulaOfCi(my_skolem, Model_of_equivalence_check_in_bool_on_y);
				
				cout << "\nEvaluation of my_skolem Done\n";
			
				Aig_Obj_t* skolem_factor1_bef;
				skolem_factor1_bef = skolem_functions_of_factor1_before_reverse_substitution[index_of_var_under_consideration];

				Aig_Obj_t* skolem_factor2_bef;
				skolem_factor2_bef = skolem_functions_of_factor2_before_reverse_substitution[index_of_var_under_consideration];
	
				Aig_Obj_t* my_skolem_bef;
				my_skolem_bef = skolem_functions_of_disjunction_formula_before_reverse_substitution[index_of_var_under_consideration];
			
				// Problem: Evaluating as below will use values of i obtained from the solver

				//bool value_of_skolem_factor1_bef = evaluateFormulaOfCi(skolem_factor1_bef, Model_of_equivalence_check_in_bool);

				//bool value_of_skolem_factor2_bef = evaluateFormulaOfCi(skolem_factor2_bef, Model_of_equivalence_check_in_bool);

				//bool value_of_my_skolem_bef = evaluateFormulaOfCi(my_skolem_bef, Model_of_equivalence_check_in_bool);

				//cout << "\nvar = " << variable_to_eliminate << "\tpsi_1(bef) = " << value_of_skolem_factor1_bef << "\tpsi_1 = " << value_of_skolem_factor1 << "\tpsi_2(bef) = " << value_of_skolem_factor2_bef << "\tpsi_2 = " << value_of_skolem_factor2 << "\tpsi(bef) = " << value_of_my_skolem_bef << "\tpsi = " << value_of_my_skolem;

				cout << "\nvar = " << variable_to_eliminate << "\tpsi_1 = " << value_of_skolem_factor1 << "\tpsi_2 = " << value_of_skolem_factor2 << "\tpsi = " << value_of_my_skolem;

				index_of_var_under_consideration++;
			}// for each variable ends here	

			assert(false);
		}// not exact ends here
		
	}


	if(cleanup_after_each_step_in_arbitrary_boolean_combinations)
	{
		string step_name = "callDisjunction";
		cleanupAfterEachStepInArbitraryBooleanCombinations(step_name);
	}
	
}


void AIGBasedSkolem::Skolem(call_type original_polarity, Aig_Obj_t* original_formula, int depth_from_root)
{
	#ifdef DEBUG_SKOLEM
	cout << endl;
	showNodeWithPolarity(original_polarity, original_formula);
	cout << " encountered\n";	
	#endif	

	if(existsInR1HashTable(original_polarity, original_formula)) // entry exists in HT
	{
		#ifdef DEBUG_SKOLEM
		cout << "\nEntry found in hash table\n";		
		#endif	

		#ifdef SH_DEBUG_SKOLEM
		cout << "\nSHETAL: Entry found in hash table for " << Aig_ObjId(Aig_Regular(original_formula)) << " call type " << original_polarity << endl;		
		#endif	

		return;
	}
	else
	{
		#ifdef DEBUG_SKOLEM
		cout << "\nNo entry found in hash table\n";		
		#endif	

		#ifdef SH_DEBUG_SKOLEM
		cout << "\nSHETAL: No entry found in hash table " << Aig_ObjId(Aig_Regular(original_formula)) << " call type " << original_polarity << endl;
		#endif

		call_type polarity;
		Aig_Obj_t* formula;
	
		if(Aig_IsComplement(original_formula)) // original_formula is negated
		{
			if(original_polarity == original)
			{
				polarity = negated;
			}
			else
			{
				polarity = original;
			}
		}
		else // original_formula is original
		{
			if(original_polarity == original)
			{
				polarity = original;
			}
			else
			{
				polarity = negated;
			}
		}

		formula = Aig_Regular(original_formula);

		// original_formula with original_polarity is the same as 
		// formula  with  polarity

		#ifdef DEBUG_SKOLEM
		cout << endl;
		showNodeWithPolarity(polarity, formula);
		cout << " obtained\n";	
		#endif	

		bool problem_instance_changed;
		if(polarity != original_polarity || formula != original_formula)
		{
			problem_instance_changed = true;
		}
		else
		{
			problem_instance_changed = false;
		}

		#ifdef DEBUG_SKOLEM
		if(problem_instance_changed)
		{
			cout << "\nProblem instance is changed\n";	
		}
		else
		{
			cout << "\nProblem instance is unchanged\n";	
		}
		#endif	

		if(problem_instance_changed && existsInR1HashTable(polarity, formula)) // entry exists in HT
		{
			#ifdef DEBUG_SKOLEM
			cout << "\nEntry found in hash table\n";		
			#endif

			#ifdef SH_DEBUG_SKOLEM
			cout << "\nSHETAL: Entry found in hash table for " << Aig_ObjId(Aig_Regular(formula)) << " call type " << polarity << " after problem instance changed " << endl;		
			#endif


			return;
		}
		else
		{
			#ifdef DEBUG_SKOLEM
			cout << "\nNo entry found in hash table\n";		
			#endif

			#ifdef SH_DEBUG_SKOLEM
			cout << "\nSHETAL: No entry found in hash table for " << Aig_ObjId(Aig_Regular(formula)) << " call type " << polarity << " after problem instance changed " << endl;				
			#endif

			#ifdef SH_DEBUG_SKOLEM
			attachCallDetailsInFile(polarity, formula, "skolem");
			#endif	

			if(formula->Type == AIG_OBJ_AND)
			{
				#ifdef DEBUG_SKOLEM
				showNodeWithPolarity(polarity, formula);
				cout << ":children = " << Aig_ObjChild0(formula) << ", " << Aig_ObjChild1(formula);
				cout << endl;		
				#endif

				if(polarity == original) // it is child1 \wedge child2
				{
					if(chooseToApplyMonoSkolem(formula))
					{
						#ifdef DEBUG_SKOLEM
						cout << "\nCalling callMonoSkolem on ";
						showNodeWithPolarity(polarity, formula);
						cout << endl;		
						#endif

						callMonoSkolem(original_polarity, original_formula, polarity, formula, depth_from_root);
					}
					else
					{

						#ifdef DEBUG_SKOLEM
						cout << "\nCalling callCegarSkolem on ";
						showNodeWithPolarity(polarity, formula);
						cout << ":children = " << Aig_ObjChild0(formula) << ", " << Aig_ObjChild1(formula);
						cout << endl;		
						#endif

						// call Skolem on the children 
						Skolem(polarity, Aig_ObjChild0(formula), depth_from_root+1);

						if(checkTimeOut()) // check for time-out
						{
							cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::Skolem\n";
							timed_out = true; // timed_out flag set
							return;
						}

						Skolem(polarity, Aig_ObjChild1(formula), depth_from_root+1);

						if(checkTimeOut()) // check for time-out
						{
							cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::Skolem\n";
							timed_out = true; // timed_out flag set
							return;
						}

						// call CegarSkolem on the results of calling Skolem on children 

						callCegarSkolem(original_polarity, original_formula, polarity, formula, depth_from_root);
					}
				}
				else // it is ~(child1 \wedge child2), i.e., ~child1 \vee ~child2
				{

					#ifdef DEBUG_SKOLEM
					cout << "\nCalling callDisjunction on ";
					showNodeWithPolarity(polarity, formula);
					cout << ":children = " << Aig_ObjChild0(formula) << ", " << Aig_ObjChild1(formula);
					cout << endl;		
					#endif	
					
					// call Skolem on the children 
					Skolem(polarity, Aig_ObjChild0(formula), depth_from_root+1);

					if(checkTimeOut()) // check for time-out
					{
						cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::Skolem\n";
						timed_out = true; // timed_out flag set
						return;
					}

					Skolem(polarity, Aig_ObjChild1(formula), depth_from_root+1);

					if(checkTimeOut()) // check for time-out
					{
						cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::Skolem\n";
						timed_out = true; // timed_out flag set
						return;
					}

					// call callDisjunction on the results of calling Skolem on children 
					

					callDisjunction(original_polarity, original_formula, polarity, formula, depth_from_root);
				}
			}
			else if(formula->Type == AIG_OBJ_CI || formula->Type == AIG_OBJ_CONST1)
			{
				#ifdef DEBUG_SKOLEM
				cout << "\nCalling callMonoSkolem on ";
				showNodeWithPolarity(polarity, formula);
				cout << endl;		
				#endif				

				callMonoSkolem(original_polarity, original_formula, polarity, formula, depth_from_root);
			}
			else
			{
				if(formula->Type == AIG_OBJ_CO)
				{
					cout << "\nAIG_OBJ_CO encountered at unexpected location\n";
					assert(false);
				}
				else
				{
					cout << "\nUnknown formula->Type encountered\n";	
					assert(false);
				}	
			}						
		}// (polarity, formula) does not exist in hash table
		
	}// (original_polarity, original_formula) does not exist in hash table
}


bool AIGBasedSkolem::existsInR0HashTable(call_type polarity, Aig_Obj_t* formula)
{
	string key;	
	char formula_char[100];
	sprintf(formula_char, "%p", formula);
	string formula_string(formula_char);
	if(polarity == negated)
	{
		formula_string += "n";
	}
	else
	{
		formula_string += "o";
	}
	key = formula_string;

	#ifdef DEBUG_SKOLEM
	cout << "\nChecking entry for " << key << " in R0_map\n";
	#endif

	map<string, vector<Aig_Obj_t*> >::iterator R0_map_it = R0_map.find(key);
	if(R0_map_it == R0_map.end())//entry does not exist
	{
		return false;
	}
	else
	{
		return true;
	}			
}


bool AIGBasedSkolem::existsInR1HashTable(call_type polarity, Aig_Obj_t* formula)
{
	string key;	
	char formula_char[100];
	sprintf(formula_char, "%p", formula);
	string formula_string(formula_char);
	if(polarity == negated)
	{
		formula_string += "n";
	}
	else
	{
		formula_string += "o";
	}
	key = formula_string;

	#ifdef DEBUG_SKOLEM
	cout << "\nChecking entry for " << key << " in R1_map\n";
	#endif

	map<string, vector<Aig_Obj_t*> >::iterator R1_map_it = R1_map.find(key);
	if(R1_map_it == R1_map.end())//entry does not exist
	{
		return false;
	}
	else
	{
		return true;
	}			
}


void AIGBasedSkolem::callSkolem(Aig_Obj_t* formula)
{	
	struct timeval callskolem_step_start_ms, callskolem_step_finish_ms;

	if(choose_to_apply_monoskolem_on_smaller_problem_instances)
	{
		// Apply DFS to find tree-size and varstoelim for all AND-
		// nodes in formula
		findTreeSizeAndVarsToElim(formula, pub_aig_manager);
	}
	
	#ifdef RECORD_KEEP
	string record_file;
	record_file = logfile_prefix;
	record_file += "skolem_function_generation_details.txt";
	FILE* record_fp = fopen(record_file.c_str(), "a+");
	assert(record_fp != NULL);

	int number_of_variables_in_formula;
	set<string> support_formula;
	computeSupport(formula, support_formula, pub_aig_manager);
	number_of_variables_in_formula = support_formula.size();
	int size_of_original_formula = computeSize(formula, pub_aig_manager);
	int number_of_variables_to_eliminate_in_formula = Global_VariablesToEliminate_Set.size();

	fprintf(record_fp, "\nsize of F(X,Y) = %d\n|X| = %d\n|X+Y| = %d\n", size_of_original_formula, number_of_variables_to_eliminate_in_formula, number_of_variables_in_formula);

	fclose(record_fp);


	string plot_file;
	plot_file = logfile_prefix;
	plot_file += "skolem_function_generation_details_to_plot.txt";
	FILE* plot_fp = fopen(plot_file.c_str(), "a+");
	assert(plot_fp != NULL);
	fprintf(plot_fp, "\n%s\t%s\t%s", benchmark_type.c_str(), benchmark_name.c_str(), machine.c_str());

	string algorithm_string = "arbitrary_boolean_combinations";
	fprintf(plot_fp, "\t%s", algorithm_string.c_str());
	fprintf(plot_fp, "\t%d\t%d\t%d", size_of_original_formula, number_of_variables_to_eliminate_in_formula, number_of_variables_in_formula);

	string order_string_to_print;
	if(order_of_elimination_of_variables == 0)
	{
		order_string_to_print = "alphabetical";	
	}
	else if(order_of_elimination_of_variables == 1)
	{
		order_string_to_print = "least-occurring-first";	
	}
	else if(order_of_elimination_of_variables == 2)
	{
		order_string_to_print = "externally-supplied";	
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
	else
	{
		cout << "\nUnsupported order\n";
		assert(false);
	}

	fprintf(plot_fp, "\t%s\t", order_string_to_print.c_str());

	fclose(plot_fp);
	#endif

	#ifdef DEBUG_SKOLEM
	writeFormulaToFile(pub_aig_manager, formula, "arbitrary_input_bool_formula", ".v", 0, 0);	
	#endif


	// Calling Skolem that finds r1's and r0's of all nodes 
	// in the formula in the HashTables

	call_type polarity = original;
	int depth_from_root = 0;
	Skolem(polarity, formula, depth_from_root);

	#ifdef DEBUG_SKOLEM
	if(checkIfResultsAreTimedOut_In_Cluster())//this is to check for graceful time-out
	{
		cout << "\nSkolem function generation finished. However results are not exact, but guaranteed over-approximate!! -- inexactness due to time-outs\n";
	}
	else
	{
		cout << "\nSkolem function generation finished.\n";
	}
	#endif

	if(checkTimeOut()) // check for time-out
	{
		#ifdef RECORD_KEEP
		string record_file;
		record_file = logfile_prefix;
		record_file += "skolem_function_generation_details.txt";
		FILE* record_fp = fopen(record_file.c_str(), "a+");
		assert(record_fp != NULL);

		fprintf(record_fp, "\nTime-out inside the function AIGBasedSkolem::Skolem\n");

		fclose(record_fp);
		#endif

		cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::callSkolem\n";
		timed_out = true; // timed_out flag set
		return;
		
	}


	// We have r1's and r0's in the HashTables
	// Let us create the Skolem functions

	// Get the r1's from the HashTable
				
	vector<Aig_Obj_t*> list_of_r1s_of_formula;
	obtainFromR1HashTable(polarity, formula, list_of_r1s_of_formula);

	// Get the Skolem functions by negating the r1's

	assert(list_of_r1s_of_formula.size() == Global_VariablesToEliminate.size());

	vector<Aig_Obj_t*> skolem_functions_of_formula;
	for(int i = 0; i < list_of_r1s_of_formula.size(); i++)
	{
		Aig_Obj_t* r1_i = list_of_r1s_of_formula[i];
		assert(r1_i != NULL);

		Aig_Obj_t* skolem_i = createNot(r1_i, pub_aig_manager); 
		assert(skolem_i != NULL);

		skolem_functions_of_formula.push_back(skolem_i);		
	}

	int i = 0;
	for(list<string>::iterator list_it = Global_VariablesToEliminate.begin(); list_it != Global_VariablesToEliminate.end(); list_it++)
	{
		string variable_to_eliminate = *list_it;
		
		#ifdef DEBUG_SKOLEM
		cout << "\nvariable_to_eliminate = " << variable_to_eliminate << endl;
		#endif

		Aig_Obj_t* skolem_i = skolem_functions_of_formula[i];
		assert(skolem_i != NULL);

		#ifdef RECORD_KEEP
		int final_skolem_function_size = computeSize(skolem_i, pub_aig_manager); // AIG Manager API Call
		skolem_function_sizes_before_reverse_substitution.push_back(final_skolem_function_size);
		sum_of_skolem_function_sizes = sum_of_skolem_function_sizes + final_skolem_function_size;

		if(max_skolem_function_size_before_reverse_substitution == -1)
		{
			max_skolem_function_size_before_reverse_substitution = final_skolem_function_size;
		}
		else if(max_skolem_function_size_before_reverse_substitution < final_skolem_function_size)
		{
			max_skolem_function_size_before_reverse_substitution = final_skolem_function_size;
		}
		if(min_skolem_function_size_before_reverse_substitution == -1)
		{
			min_skolem_function_size_before_reverse_substitution = final_skolem_function_size;
		}
		else if(min_skolem_function_size_before_reverse_substitution > final_skolem_function_size)
		{
			min_skolem_function_size_before_reverse_substitution = final_skolem_function_size;
		}
		#endif

		
		#ifdef DEBUG_SKOLEM
		string skolem_file_name = "skolemfunction_before_revsubstitution_";
		skolem_file_name += variable_to_eliminate;
		skolem_file_name += "_";
		skolem_file_name += logfile_prefix;
		skolem_file_name += ".v";
		writeFormulaToFile(pub_aig_manager, skolem_i, skolem_file_name);
		#endif

		i++;
		
	}// for each variable ends here

	gettimeofday (&callskolem_step_start_ms, NULL); 
	
	performReverseSubstitutionOfSkolemFunctions(skolem_functions_of_formula);

	gettimeofday (&callskolem_step_finish_ms, NULL);
	total_time_in_reverse_substitution_on_arbitrary_boolean_formulas = callskolem_step_finish_ms.tv_sec * 1000 + callskolem_step_finish_ms.tv_usec / 1000;
	total_time_in_reverse_substitution_on_arbitrary_boolean_formulas -= callskolem_step_start_ms.tv_sec * 1000 + callskolem_step_start_ms.tv_usec / 1000;

	if(checkTimeOut()) // check for time-out
	{
		#ifdef RECORD_KEEP
		string record_file;
		record_file = logfile_prefix;
		record_file += "skolem_function_generation_details.txt";
		FILE* record_fp = fopen(record_file.c_str(), "a+");
		assert(record_fp != NULL);

		fprintf(record_fp, "\nTime-out inside the function AIGBasedSkolem::performReverseSubstitutionOfSkolemFunctions\n");

		fclose(record_fp);
		#endif

		cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::callSkolem\n";
		timed_out = true; // timed_out flag set
		return;		
	}


	i = 0;
	for(list<string>::iterator list_it = Global_VariablesToEliminate.begin(); list_it != Global_VariablesToEliminate.end(); list_it++)
	{
		string variable_to_eliminate = *list_it;
		
		#ifdef DEBUG_SKOLEM
		cout << "\nvariable_to_eliminate = " << variable_to_eliminate << endl;
		#endif

		Aig_Obj_t* skolem_i = skolem_functions_of_formula[i];
		assert(skolem_i != NULL);

		#ifdef RECORD_KEEP
		int final_skolem_function_size = computeSize(skolem_i, pub_aig_manager); // AIG Manager API Call

		skolem_function_sizes_after_reverse_substitution.push_back(final_skolem_function_size);
		sum_of_skolem_function_sizes_after_reverse_substitution = sum_of_skolem_function_sizes_after_reverse_substitution + final_skolem_function_size;

		if(max_skolem_function_size_after_reverse_substitution == -1)
		{
			max_skolem_function_size_after_reverse_substitution = final_skolem_function_size;
		}
		else if(max_skolem_function_size_after_reverse_substitution < final_skolem_function_size)
		{
			max_skolem_function_size_after_reverse_substitution = final_skolem_function_size;
		}
		if(min_skolem_function_size_after_reverse_substitution == -1)
		{
			min_skolem_function_size_after_reverse_substitution = final_skolem_function_size;
		}
		else if(min_skolem_function_size_after_reverse_substitution > final_skolem_function_size)
		{
			min_skolem_function_size_after_reverse_substitution = final_skolem_function_size;
		}
		#endif
		
		#ifdef DEBUG_SKOLEM
		string skolem_file_name = "skolemfunction_after_revsubstitution_";
		skolem_file_name += variable_to_eliminate;
		skolem_file_name += "_";
		skolem_file_name += logfile_prefix;
		skolem_file_name += ".v";
		writeFormulaToFile(pub_aig_manager, skolem_i, skolem_file_name);
		#endif

		i++;
		
	}// for each variable ends here	

	
	// Proving correctness

	if(prove_correctness_of_skolem_functions_of_arbitrary_boolean_formula)
	{

		// First create F(psi(Y), Y)
		bool ensure_that_skolem_functions_are_on_y = true;
		
		map<string, Aig_Obj_t*> skolem_function_replacement_map;
		i = 0;
		for(list<string>::iterator list_it = Global_VariablesToEliminate.begin(); list_it != Global_VariablesToEliminate.end(); list_it++)
		{
			string variable_to_eliminate = *list_it;
			
			Aig_Obj_t* skolem_i = skolem_functions_of_formula[i];
			assert(skolem_i != NULL);

			if(ensure_that_skolem_functions_are_on_y)
			{
				set<string> support_skolem_i;
				computeSupport(skolem_i, support_skolem_i, pub_aig_manager);
				
				set<string> varstoelim_in_support_skolem_i;
				set_intersection(support_skolem_i.begin(), support_skolem_i.end(), Global_VariablesToEliminate_Set.begin(), Global_VariablesToEliminate_Set.end(), inserter(varstoelim_in_support_skolem_i, varstoelim_in_support_skolem_i.begin()));

				if(!varstoelim_in_support_skolem_i.empty())				
				{
					cout << "\nSkolem function of variable " << variable_to_eliminate << " involves variables to be eliminated\n";
					assert(false);	
				}
			}

			skolem_function_replacement_map.insert(make_pair(variable_to_eliminate, skolem_i));
				
			i++;
		
		}// for each variable ends here	

		assert(skolem_function_replacement_map.size() > 0);

		Aig_Obj_t* result_of_qe_using_skolem_functions;
		result_of_qe_using_skolem_functions = replaceVariablesByFormulas(input_arbitrary_boolean_formula, skolem_function_replacement_map);	
		assert(result_of_qe_using_skolem_functions != NULL); // F(psi(Y), Y)	

		list<string> VariablesToEliminate_Copy;
		VariablesToEliminate_Copy = Global_VariablesToEliminate;

		Aig_Obj_t* equivalence_check; // ~F(psi(Y), Y) \wedge F(X, Y)
		equivalence_check = createAnd(createNot(result_of_qe_using_skolem_functions, pub_aig_manager), input_arbitrary_boolean_formula, pub_aig_manager);
		assert(equivalence_check != NULL);

		// Give to SAT-Solver
		unsigned long long int cnf_time;
		int formula_size;
		unsigned long long int simplification_time;
		map<string, int> Model_of_equivalence_check;
		bool result_of_equivalence_check;

		bool use_incremental_solver = true;

		if(use_incremental_solver)
		{
			vector<Aig_Obj_t*> positive_assumptions;
			vector<Aig_Obj_t*> negative_assumptions;
			
			assert(IncrementalLabelCountForProvingCorrectness == 1);// first use should be HERE

			pSat_for_proving_correctness = sat_solver_new();
	
			result_of_equivalence_check = isExactnessCheckSatisfiable(pub_aig_manager, equivalence_check, Model_of_equivalence_check, cnf_time, formula_size, simplification_time, positive_assumptions, negative_assumptions, pSat_for_proving_correctness, IncrementalLabelTableForProvingCorrectness, IncrementalLabelCountForProvingCorrectness, Ci_name_to_Ci_label_mapForProvingCorrectness, Ci_label_to_Ci_name_mapForProvingCorrectness);
		
			sat_solver_delete(pSat_for_proving_correctness);
		}
		else // If this is used along with cleanup_after_each_step_in_arbitrary_boolean_combinations, then 
		// seg. fault can happen - note that isSat tries to derive cnf for the entire manager
		{
			result_of_equivalence_check = isSat(pub_aig_manager, equivalence_check, Model_of_equivalence_check, cnf_time, formula_size, simplification_time);

		}
		
		if(result_of_equivalence_check)
		{
			cout << "\nexists X.f => f[X --> psi] is NOT valid\n";
			cout << "\nCounterexample is\n";
			displayModelFromSATSolver(Model_of_equivalence_check);			
		}
		else
		{
			//cout << "\nexists X.f => f[X --> psi] is valid\n~exists X.f => ~f[X --> psi] is valid for any psi\nSkolem functions are exact\n";
			cout << "\nSkolem functions are exact\n";
		}

		string record_file;
		record_file = logfile_prefix;
		record_file += "skolem_function_generation_details.txt";
		FILE* record_fp = fopen(record_file.c_str(), "a+");
		assert(record_fp != NULL);

		if(result_of_equivalence_check)
		{
			fprintf(record_fp, "\n\nexists X.f(X,Y) = f'(psi,Y) is NOT valid; Skolem functions are NOT exact\n");
		}
		else
		{
			fprintf(record_fp, "\n\nexists X.f(X,Y) = f'(psi,Y) is valid; Skolem functions are exact\n");		

		}

		fclose(record_fp);
	
	}//if(prove_correctness_of_skolem_functions_of_arbitrary_boolean_formula) ends here


	if(use_for_qbf_satisfiability)
	{	
		// First create F(psi(Y), Y)
		map<string, Aig_Obj_t*> skolem_function_replacement_map;
		i = 0;
		for(list<string>::iterator list_it = Global_VariablesToEliminate.begin(); list_it != Global_VariablesToEliminate.end(); list_it++)
		{
			string variable_to_eliminate = *list_it;
			
			Aig_Obj_t* skolem_i = skolem_functions_of_formula[i];
			assert(skolem_i != NULL);

			skolem_function_replacement_map.insert(make_pair(variable_to_eliminate, skolem_i));		
			i++;		
		}// for each variable ends here	

		assert(skolem_function_replacement_map.size() > 0);

		Aig_Obj_t* result_of_qe_using_skolem_functions;
		result_of_qe_using_skolem_functions = replaceVariablesByFormulas(input_arbitrary_boolean_formula, skolem_function_replacement_map);	
		assert(result_of_qe_using_skolem_functions != NULL); // F(psi(Y), Y)	

		Aig_Obj_t* qbf_check; // ~F(psi(Y), Y)
		qbf_check = createNot(result_of_qe_using_skolem_functions, pub_aig_manager);
		assert(qbf_check != NULL);

		// Give to SAT-Solver
		unsigned long long int cnf_time;
		int formula_size;
		unsigned long long int simplification_time;
		map<string, int> Model_of_qbf_check;
		bool result_of_qbf_check;

		result_of_qbf_check = isSat(pub_aig_manager, qbf_check, Model_of_qbf_check, cnf_time, formula_size, simplification_time);

		if(result_of_qbf_check)
		{
			cout << "\nforall Y. exists X.f is false\n";
			cout << "\nCounterexample is\n";
			displayModelFromSATSolver(Model_of_qbf_check);			
		}
		else
		{
			cout << "\nforall Y. exists X.f is true\n";
		}

		string record_file;
		record_file = logfile_prefix;
		record_file += "skolem_function_generation_details.txt";
		FILE* record_fp = fopen(record_file.c_str(), "a+");
		assert(record_fp != NULL);

		if(result_of_qbf_check)
		{
			fprintf(record_fp, "\n\nforall Y. exists X.f is false\n");
		}
		else
		{
			fprintf(record_fp, "\n\nforall Y. exists X.f is true\n");		

		}

		fclose(record_fp);

	}//if(use_for_qbf_satisfiability) ends here
	
}


int AIGBasedSkolem::findLocationOfVariableInGlobalVariablesToEliminate(string var_to_elim)
{
	int location_of_var_to_elim = 0;
	for(list<string>::iterator Global_VariablesToEliminate_it = Global_VariablesToEliminate.begin(); Global_VariablesToEliminate_it != Global_VariablesToEliminate.end(); Global_VariablesToEliminate_it++)
	{
		if(*Global_VariablesToEliminate_it == var_to_elim)
		{
			return location_of_var_to_elim;
		}

		location_of_var_to_elim++;
	}
}



void AIGBasedSkolem::setParametersToDefaults()
{
	// Set all parameters to run Skolem function generator to default values
	perform_reverse_substitution = true;
	use_interpolant_as_skolem_function = false;
	
	enable_cegar = false;
	use_bads_in_unified_cegar = false;
	use_cbzero_in_unified_cegar = false;
	use_assumptions_in_unified_cegar = false;
	accumulate_formulae_in_cbzero_in_cegar = true;	

	internal_flag_to_avoid_sat_call_in_functional_forms = false;
	factorizedskolem_applied_on_disjunction = false;

	//NB: order_of_elimination_of_variables is kept as set [default value is 1] 	
}


void AIGBasedSkolem::getR1R0ForFreeVariablesInConjunction(Aig_Obj_t* formula, map<string, Aig_Obj_t*> &map_of_r1s, map<string, Aig_Obj_t*> &map_of_r0s)
{
	assert(formula != NULL);

	set<string> support;
	computeSupport(formula, support, pub_aig_manager);

	set<Aig_Obj_t*> Factors;
	// Factors are the children
	Factors.insert(Aig_ObjChild0(formula));
	Factors.insert(Aig_ObjChild1(formula));	

	int factor_index = 1;
	map<int, vector<Aig_Obj_t*> > factor_index_to_list_of_r0s_map;
	map<int, vector<Aig_Obj_t*> > factor_index_to_list_of_r1s_map;

	for(set<Aig_Obj_t*>::iterator Factors_it = Factors.begin(); Factors_it != Factors.end(); Factors_it++)
	{
		Aig_Obj_t* given_factor;
		given_factor = *Factors_it;
		assert(given_factor != NULL);
				
		vector<Aig_Obj_t*> list_of_r0s_of_factor;
		vector<Aig_Obj_t*> list_of_r1s_of_factor;
		call_type factor_polarity = original;
				
		getEntryFromR0HashTable(factor_polarity, given_factor, list_of_r0s_of_factor);
		getEntryFromR1HashTable(factor_polarity, given_factor, list_of_r1s_of_factor);
				
		factor_index_to_list_of_r0s_map.insert(make_pair(factor_index, list_of_r0s_of_factor));
		factor_index_to_list_of_r1s_map.insert(make_pair(factor_index, list_of_r1s_of_factor));

		factor_index++;
	}//consider each factor ends here

	// We have list_of_r0s and list_of_r1s of each factor now
	// From these lists construct the final r0's and r1's

	int location_of_var_to_elim = 0;

	for(list<string>::iterator list_it = Global_VariablesToEliminate.begin(); list_it != Global_VariablesToEliminate.end(); list_it++)
	{
		string var_to_elim = *list_it;

		if(support.find(var_to_elim) == support.end())//formula free of var_to_elim
		{
		
			#ifdef DEBUG_SKOLEM
			cout << "\nGetting cannot-be-1 and cannot-be-0 sets of " << var_to_elim << " from hash tables" << endl;
			#endif

			Aig_Obj_t* cannot_be_one_function;
			Aig_Obj_t* cannot_be_zero_function;
			set<Aig_Obj_t*> cannot_be_one_set_for_var_to_elim_index;
			set<Aig_Obj_t*> cannot_be_zero_set_for_var_to_elim_index;

			int factor_index = 1;
			for(set<Aig_Obj_t*>::iterator Factors_it = Factors.begin(); Factors_it != Factors.end(); Factors_it++)
			{
				#ifdef DEBUG_SKOLEM
				cout << "\nfactor_index = " << factor_index << endl;
				#endif

				map<int, vector<Aig_Obj_t*> >::iterator factor_index_to_list_of_r1s_map_it = factor_index_to_list_of_r1s_map.find(factor_index);
				assert(factor_index_to_list_of_r1s_map_it != factor_index_to_list_of_r1s_map.end());

				Aig_Obj_t* r1 = (factor_index_to_list_of_r1s_map_it->second)[location_of_var_to_elim];
		  		assert(r1 != NULL);		
		
		
				// connecting to some output to avoid unwanted deletion
				Aig_Obj_t* r1_CO = Aig_ObjCreateCo(pub_aig_manager, r1 ); 
				assert(r1_CO != NULL);
				intermediate_cos_created.insert(r1_CO);

				map<int, vector<Aig_Obj_t*> >::iterator factor_index_to_list_of_r0s_map_it = factor_index_to_list_of_r0s_map.find(factor_index);
				assert(factor_index_to_list_of_r0s_map_it != factor_index_to_list_of_r0s_map.end());

				Aig_Obj_t* r0 = (factor_index_to_list_of_r0s_map_it->second)[location_of_var_to_elim];
		  		assert(r0 != NULL);		
		
				// connecting to some output to avoid unwanted deletion
				Aig_Obj_t* r0_CO = Aig_ObjCreateCo(pub_aig_manager, r0 ); 
				assert(r0_CO != NULL);
				intermediate_cos_created.insert(r0_CO);
	
				// Insert the dags in respective cannot-be-sets
				cannot_be_one_set_for_var_to_elim_index.insert(r1);
				cannot_be_zero_set_for_var_to_elim_index.insert(r0);

				factor_index++;
			}// for each factor ends here

			assert(!cannot_be_one_set_for_var_to_elim_index.empty());
			cannot_be_one_function = createOr(cannot_be_one_set_for_var_to_elim_index, pub_aig_manager);
			assert(cannot_be_one_function != NULL);

			assert(!cannot_be_zero_set_for_var_to_elim_index.empty());
			cannot_be_zero_function = createOr(cannot_be_zero_set_for_var_to_elim_index, pub_aig_manager);
			assert(cannot_be_zero_function != NULL);
		
			// connect to some output to avoid unwanted deletion
			Aig_Obj_t* cannot_be_one_function_CO = Aig_ObjCreateCo(pub_aig_manager, cannot_be_one_function ); 
			assert(cannot_be_one_function_CO != NULL);
			intermediate_cos_created.insert(cannot_be_one_function_CO);

			Aig_Obj_t* cannot_be_zero_function_CO = Aig_ObjCreateCo(pub_aig_manager, cannot_be_zero_function ); 
			assert(cannot_be_zero_function_CO != NULL);			
			intermediate_cos_created.insert(cannot_be_zero_function_CO);
	
			map_of_r1s.insert(make_pair(var_to_elim, cannot_be_one_function));
			map_of_r0s.insert(make_pair(var_to_elim, cannot_be_zero_function));
		}//if formula free of var_to_elim ends here

		location_of_var_to_elim++;		
		
	}// for each variable ends here	
}

void AIGBasedSkolem::getEntryFromR0HashTable(call_type original_polarity, Aig_Obj_t* original_formula, vector<Aig_Obj_t*> &list_of_r0s)
{
	bool ExistsInHashTable = obtainFromR0HashTable(original_polarity, original_formula, list_of_r0s);

	if(ExistsInHashTable) // original entry exists in HT
	{
		return;
	}
	else
	{
		call_type polarity;
		Aig_Obj_t* formula;
	
		if(Aig_IsComplement(original_formula)) // original_formula is negated
		{
			if(original_polarity == original)
			{
				polarity = negated;
			}
			else
			{
				polarity = original;
			}
		}
		else // original_formula is original
		{
			if(original_polarity == original)
			{
				polarity = original;
			}
			else
			{
				polarity = negated;
			}
		}

		formula = Aig_Regular(original_formula);

		// original_formula with original_polarity is the same as 
		// formula  with  polarity

		bool problem_instance_changed;
		if(polarity != original_polarity || formula != original_formula)
		{
			problem_instance_changed = true;
		}
		else
		{
			problem_instance_changed = false;
		}

		if(problem_instance_changed) 
		{
			ExistsInHashTable = obtainFromR0HashTable(polarity, formula, list_of_r0s);

			if(ExistsInHashTable) // changed entry exists in HT
			{
				return;
			}
			else
			{
				assert(false);
			}
		}
		else // problem instance is unchanged. so why is original entry absent in HashTable?
		{
			assert(false);
		}

	}// original entry does not exist in HT	
}


bool AIGBasedSkolem::obtainFromR0HashTable(call_type polarity, Aig_Obj_t* formula, vector<Aig_Obj_t*> &list_of_r0s)
{
	string key;	
	char formula_char[100];
	sprintf(formula_char, "%p", formula);
	string formula_string(formula_char);
	if(polarity == negated)
	{
		formula_string += "n";
	}
	else
	{
		formula_string += "o";
	}
	key = formula_string;

	#ifdef DEBUG_SKOLEM
	cout << "\nExtracting entry for " << key << " from R0_map\n";
	#endif

	map<string, vector<Aig_Obj_t*> >::iterator R0_map_it = R0_map.find(key);
	if(R0_map_it == R0_map.end())//entry does not exist
	{
		#ifdef DEBUG_SKOLEM
		cout << "\nNo entry in R0_map\n";
		#endif
		return false;
	}
	else
	{
		list_of_r0s = R0_map_it->second;
		#ifdef DEBUG_SKOLEM
		cout << "\nEntry exists in R0_map\n";
		#endif
		return true;
	}			
}


void AIGBasedSkolem::getEntryFromR1HashTable(call_type original_polarity, Aig_Obj_t* original_formula, vector<Aig_Obj_t*> &list_of_r1s)
{
	bool ExistsInHashTable = obtainFromR1HashTable(original_polarity, original_formula, list_of_r1s);

	if(ExistsInHashTable) // original entry exists in HT
	{
		return;
	}
	else
	{
		call_type polarity;
		Aig_Obj_t* formula;
	
		if(Aig_IsComplement(original_formula)) // original_formula is negated
		{
			if(original_polarity == original)
			{
				polarity = negated;
			}
			else
			{
				polarity = original;
			}
		}
		else // original_formula is original
		{
			if(original_polarity == original)
			{
				polarity = original;
			}
			else
			{
				polarity = negated;
			}
		}

		formula = Aig_Regular(original_formula);

		// original_formula with original_polarity is the same as 
		// formula  with  polarity

		bool problem_instance_changed;
		if(polarity != original_polarity || formula != original_formula)
		{
			problem_instance_changed = true;
		}
		else
		{
			problem_instance_changed = false;
		}

		if(problem_instance_changed) 
		{
			ExistsInHashTable = obtainFromR1HashTable(polarity, formula, list_of_r1s);

			if(ExistsInHashTable) // changed entry exists in HT
			{
				return;
			}
			else
			{
				assert(false);
			}
		}
		else // problem instance is unchanged. so why is original entry absent in HashTable?
		{
			assert(false);
		}

	}// original entry does not exist in HT	
}



bool AIGBasedSkolem::obtainFromR1HashTable(call_type polarity, Aig_Obj_t* formula, vector<Aig_Obj_t*> &list_of_r1s)
{
	string key;	
	char formula_char[100];
	sprintf(formula_char, "%p", formula);
	string formula_string(formula_char);
	if(polarity == negated)
	{
		formula_string += "n";
	}
	else
	{
		formula_string += "o";
	}
	key = formula_string;

	#ifdef DEBUG_SKOLEM
	cout << "\nExtracting entry for " << key << " from R1_map\n";
	#endif

	map<string, vector<Aig_Obj_t*> >::iterator R1_map_it = R1_map.find(key);
	if(R1_map_it == R1_map.end())//entry does not exist
	{
		#ifdef DEBUG_SKOLEM
		cout << "\nNo entry in R1_map\n";
		#endif
		return false;
	}
	else
	{
		list_of_r1s = R1_map_it->second;
		#ifdef DEBUG_SKOLEM
		cout << "\nEntry exists in R1_map\n";
		#endif
		return true;
	}			
}



void AIGBasedSkolem::arbitraryBooleanBenchmarkGeneration(set<Aig_Obj_t*> &transition_function_factors, map<string, Aig_Obj_t*> &output_string_to_transition_function_parts, list<string> &VariablesToEliminate)
{
	int number_of_variables_to_eliminate = VariablesToEliminate.size();
	int original_no_of_cis = number_of_Cis;
		
	assert(!transition_function_factors.empty()); // each element is x_i' \equiv f_i(X, I)
	assert(!output_string_to_transition_function_parts.empty()); // each element is string x_i' --> f_i(X, I)
	
	map<string, Aig_Obj_t*> variable_to_skolem_function_map; // This stores x_i ---> true
	for(list<string>::iterator list_it = VariablesToEliminate.begin(); list_it != VariablesToEliminate.end(); list_it++)
	{
		string variable_to_eliminate = *list_it;

		Aig_Obj_t* skolem_function = createTrue(pub_aig_manager);
		assert(skolem_function != NULL);

		variable_to_skolem_function_map.insert(make_pair(variable_to_eliminate, skolem_function));			
	}
	
	// let's see output_string_to_transition_function_parts
	#ifdef DEBUG_SKOLEM
	cout << "\noutput_string_to_transition_function_parts\n";
	for(map<string, Aig_Obj_t*>::iterator map_it = output_string_to_transition_function_parts.begin(); map_it != output_string_to_transition_function_parts.end(); map_it++)
	{
		cout << endl << map_it->first << "\t" << map_it->second << endl;
		string transition_function_part_file_name = benchmark_name_without_extension;
		transition_function_part_file_name += "_";
		transition_function_part_file_name += map_it->first;
		transition_function_part_file_name += "_transition_function_part";
		writeFormulaToFile(pub_aig_manager, map_it->second, transition_function_part_file_name, ".v", 0, 0);
	}	
	#endif

	map<Aig_Obj_t*, Aig_Obj_t*> input_object_to_transition_function_parts;
	for(map<string, Aig_Obj_t*>::iterator map_it = output_string_to_transition_function_parts.begin(); map_it != output_string_to_transition_function_parts.end(); map_it++)
	{
		string latchout_name = map_it->first;
		int index_of_uscore = latchout_name.find_last_of("_");
	       	string latchout_part = latchout_name.substr(0, index_of_uscore);
		assert(latchout_part == "LATCHOUT");
		string location_str = latchout_name.substr(index_of_uscore+1);
		
		string latchin_name = "LATCHIN_";
		latchin_name += location_str;
	
		map<string, Aig_Obj_t*>::iterator Ci_name_to_Ci_object_map_it = Ci_name_to_Ci_object_map.find(latchin_name);
		assert(Ci_name_to_Ci_object_map_it != Ci_name_to_Ci_object_map.end());
		Aig_Obj_t* input_object = Ci_name_to_Ci_object_map_it->second;
		assert(input_object != NULL);
		
		input_object_to_transition_function_parts.insert(make_pair(input_object, map_it->second));
	}		

	#ifdef DEBUG_SKOLEM
	cout << "\ninput_object_to_transition_function_parts\n";
	int file_counter = 1;
	for(map<Aig_Obj_t*, Aig_Obj_t*>::iterator map_it = input_object_to_transition_function_parts.begin(); map_it != input_object_to_transition_function_parts.end(); map_it++)
	{
		string transition_function_part_file_name = benchmark_name_without_extension;
		transition_function_part_file_name += "_transition_function_part";
		writeFormulaToFile(pub_aig_manager, map_it->second, transition_function_part_file_name, ".v", 0, file_counter);

		string transition_function_name_file_name = benchmark_name_without_extension;
		transition_function_name_file_name += "_transition_function_name";
		writeFormulaToFile(pub_aig_manager, map_it->first, transition_function_name_file_name, ".v", 0, file_counter);

		file_counter++;
	}	
	#endif

	set<Aig_Obj_t*> all_bit_differing_from_true_components;
	// This has (f_1(X, I) \neq f_1(X, TRUE)) \vee \ldots \vee (f_m(X, I) \neq f_m(X, TRUE))
	set<Aig_Obj_t*> all_bit_differing_from_cycle_components;
	// This has (f_1(X, I) \neq x_1) \vee \ldots \vee (f_m(X, I) \neq x_m)

	int part_number = 1;
	int number_of_parts = input_object_to_transition_function_parts.size();
	for(map<Aig_Obj_t*, Aig_Obj_t*>::iterator map_it = input_object_to_transition_function_parts.begin(); map_it != input_object_to_transition_function_parts.end(); map_it++)
	{
		Aig_Obj_t* transition_function_part = map_it->second; // f_i(X, I)
		Aig_Obj_t* transition_function_name = map_it->first; // x_i

		Aig_Obj_t* transition_function_part_after_replacement;
		transition_function_part_after_replacement = replaceVariablesByFormulas(transition_function_part, variable_to_skolem_function_map);
		assert(transition_function_part_after_replacement != NULL); // f_i(x, true)

		Aig_Obj_t* single_bit_differing_from_true_component;
		single_bit_differing_from_true_component = createEquivalence(transition_function_part, transition_function_part_after_replacement, pub_aig_manager);
		assert(single_bit_differing_from_true_component != NULL); // f_i(X, I) \equiv f_i(x, G(X))

		Aig_Obj_t* single_bit_differing_from_cycle_component;
		single_bit_differing_from_cycle_component = createEquivalence(transition_function_part, transition_function_name, pub_aig_manager);
		assert(single_bit_differing_from_cycle_component != NULL); // f_i(X, I) \equiv x_i

		Aig_Obj_t* all_bit_differing_from_true_component = createNot(single_bit_differing_from_true_component, pub_aig_manager);
		assert(all_bit_differing_from_true_component != NULL); // f_i(X, I) \neq f_i(x, G(X))

		Aig_Obj_t* all_bit_differing_from_cycle_component = createNot(single_bit_differing_from_cycle_component, pub_aig_manager);
		assert(all_bit_differing_from_cycle_component != NULL); // f_i(X, I) \neq x_i

				
		all_bit_differing_from_true_components.insert(all_bit_differing_from_true_component);
		all_bit_differing_from_cycle_components.insert(all_bit_differing_from_cycle_component);

		part_number++;
	}

	Aig_Obj_t* all_bit_differing_from_true; // (f_1(X, I) \neq f_1(X, TRUE)) \vee \ldots \vee (f_m(X, I) \neq f_m(X, TRUE))
	Aig_Obj_t* all_bit_differing_from_cycle; // (f_1(X, I) \neq x_1) \vee \ldots \vee (f_m(X, I) \neq x_m)

	assert(all_bit_differing_from_true_components.size() > 0);
	all_bit_differing_from_true = createOr(all_bit_differing_from_true_components, pub_aig_manager);
	assert(all_bit_differing_from_true != NULL); 
	
	assert(all_bit_differing_from_cycle_components.size() > 0);
	all_bit_differing_from_cycle = createOr(all_bit_differing_from_cycle_components, pub_aig_manager);
	assert(all_bit_differing_from_cycle != NULL); 
	
	int no_of_cis_with_f_variables = number_of_Cis;
	int total_no_of_cis = number_of_Cis;

	#ifdef DEBUG_SKOLEM
	string all_bit_differing_from_true_file_name = benchmark_name_without_extension;
	all_bit_differing_from_true_file_name += "_all_bit_differing_from_true";
	writeFormulaToFile(pub_aig_manager, all_bit_differing_from_true, all_bit_differing_from_true_file_name, ".v", 0, 0);
	
	string all_bit_differing_from_cycle_file_name = benchmark_name_without_extension;
	all_bit_differing_from_cycle_file_name += "_all_bit_differing_from_cycle";
	writeFormulaToFile(pub_aig_manager, all_bit_differing_from_cycle, all_bit_differing_from_cycle_file_name, ".v", 0, 0);
	#endif
	
	// Printing in files	
	Aig_Obj_t* all_bit_differing_from_cycle_CO;
	all_bit_differing_from_cycle_CO = Aig_ObjCreateCo( pub_aig_manager, all_bit_differing_from_cycle );
	assert(all_bit_differing_from_cycle_CO != NULL);

	Aig_Man_t* all_bit_differing_from_cycle_aig_manager;
	all_bit_differing_from_cycle_aig_manager = simplifyUsingConeOfInfluence( pub_aig_manager, Aig_ManCoNum(pub_aig_manager)-1, 1 );
	assert(all_bit_differing_from_cycle_aig_manager != NULL);

	char verilog_file_char[100];
	string verilog_file = benchmark_name_without_extension;
	verilog_file += "_all_bit_differing_from_cycle";

	char pname[100];
	strcpy(pname, verilog_file.c_str());
	all_bit_differing_from_cycle_aig_manager->pName = pname;
	verilog_file += ".v";
	strcpy(verilog_file_char, verilog_file.c_str());

	writeCombinationalCircuitInVerilog(all_bit_differing_from_cycle_aig_manager, number_of_variables_to_eliminate, original_no_of_cis, no_of_cis_with_f_variables, total_no_of_cis, verilog_file_char, false );

	cout << "\nBenchmark file " << verilog_file << " written\n";

	Aig_Obj_t* all_bit_differing_from_true_CO;
	all_bit_differing_from_true_CO = Aig_ObjCreateCo( pub_aig_manager, all_bit_differing_from_true );
	assert(all_bit_differing_from_true_CO != NULL);

	Aig_Man_t* all_bit_differing_from_true_aig_manager;
	all_bit_differing_from_true_aig_manager = simplifyUsingConeOfInfluence( pub_aig_manager, Aig_ManCoNum(pub_aig_manager)-1, 1 );
	assert(all_bit_differing_from_true_aig_manager != NULL);

	verilog_file = benchmark_name_without_extension;
	verilog_file += "_all_bit_differing_from_true";

	strcpy(pname, verilog_file.c_str());
	all_bit_differing_from_true_aig_manager->pName = pname;
	verilog_file += ".v";
	strcpy(verilog_file_char, verilog_file.c_str());

	writeCombinationalCircuitInVerilog(all_bit_differing_from_true_aig_manager, number_of_variables_to_eliminate, original_no_of_cis, no_of_cis_with_f_variables, total_no_of_cis, verilog_file_char, false );
	
	cout << "\nBenchmark file " << verilog_file << " written\n";
}


void AIGBasedSkolem::Skolem_In_Cluster(int original_polarity_as_int, Aig_Obj_t* original_formula, int depth_from_root, vector<Aig_Obj_t*> &list_of_r1s, vector<Aig_Obj_t*> &list_of_r0s, int rank, bool top_level_block, bool prove_correctness_at_top_level_block, bool &r1r0s_computed_are_exact)
{
	#ifdef DEBUG_SKOLEM
	cout << "\nCalling Skolem\n";	
	#endif	

	#ifdef DEBUG_SKOLEM
	writeFormulaToFile(pub_aig_manager, original_formula, "original_formula", ".v", 0, 0);	
	#endif

	call_type original_polarity;
	if(original_polarity_as_int == 0)
	{
		original_polarity = original;
	}
	else if(original_polarity_as_int == 1)
	{
		original_polarity = negated;
	}
	else
	{
		assert(false);
	}

	#ifdef DEBUG_PAR
	printCallDetails_Across_ClusterNodes(original_polarity, original_formula, "Skolem", rank);
	#endif

	Skolem(original_polarity, original_formula, depth_from_root);

	#ifdef DEBUG_SKOLEM
	cout << "\nGetting the r0's and r1's from the hash tables\n";	
	#endif	

	getEntryFromR0HashTable(original_polarity, original_formula, list_of_r0s);
	getEntryFromR1HashTable(original_polarity, original_formula, list_of_r1s);

	#ifdef DEBUG_SKOLEM
	showListOfAigNodes(list_of_r0s, "list_of_r0s");
	showListOfAigNodes(list_of_r1s, "list_of_r1s");
	#endif

	assert(list_of_r1s.size() > 0);	
	assert(list_of_r0s.size() > 0);	

	#ifdef DEBUG_PAR
	printHashTableOperation_Across_ClusterNodes(original_polarity, original_formula, list_of_r1s, list_of_r0s, false, rank);
	#endif

	//#ifdef DEBUG_PAR
	if(checkIfResultsAreTimedOut_In_Cluster())
	{
		//cout << "\nResults from Skolem_In_Cluster are not exact!! -- inexactness due to time-outs\n";

		r1r0s_computed_are_exact = false;
	}
	else
	{
		//cout << "\nResults from Skolem_In_Cluster are exact\n";

		r1r0s_computed_are_exact = true;
	}
	//#endif

	if(top_level_block && prove_correctness_at_top_level_block)
	{
		vector<Aig_Obj_t*> skolem_functions_of_formula;
		for(int i = 0; i < list_of_r1s.size(); i++)
		{
			Aig_Obj_t* r1_i = list_of_r1s[i];
			assert(r1_i != NULL);

			Aig_Obj_t* skolem_i = createNot(r1_i, pub_aig_manager); 
			assert(skolem_i != NULL);

			skolem_functions_of_formula.push_back(skolem_i);		
		}

		performReverseSubstitutionOfSkolemFunctions(skolem_functions_of_formula);

		bool ensure_that_skolem_functions_are_on_y = true;
		
		map<string, Aig_Obj_t*> skolem_function_replacement_map;
		int skolem_index = 0;
		for(list<string>::iterator list_it = Global_VariablesToEliminate.begin(); list_it != Global_VariablesToEliminate.end(); list_it++)
		{
			string variable_to_eliminate = *list_it;
			
			Aig_Obj_t* skolem_i = skolem_functions_of_formula[skolem_index];
			assert(skolem_i != NULL);

			if(ensure_that_skolem_functions_are_on_y)
			{
				set<string> support_skolem_i;
				computeSupport(skolem_i, support_skolem_i, pub_aig_manager);
				
				set<string> varstoelim_in_support_skolem_i;
				set_intersection(support_skolem_i.begin(), support_skolem_i.end(), Global_VariablesToEliminate_Set.begin(), Global_VariablesToEliminate_Set.end(), inserter(varstoelim_in_support_skolem_i, varstoelim_in_support_skolem_i.begin()));

				if(!varstoelim_in_support_skolem_i.empty())				
				{
					cout << "\n\nSkolem function of variable " << variable_to_eliminate << " involves variables to be eliminated\n";
					assert(false);	
				}
			}

			skolem_function_replacement_map.insert(make_pair(variable_to_eliminate, skolem_i));
				
			skolem_index++;
		
		}// for each variable ends here	

		assert(skolem_function_replacement_map.size() > 0);

		Aig_Obj_t* formula_from_master;
		if(original_polarity_as_int == 0)//original
		{
			formula_from_master = original_formula;
		}
		else if(original_polarity_as_int == 1)//negated
		{
			formula_from_master = createNot(original_formula, pub_aig_manager);
		}
		else
		{
			assert(false);
		}

		Aig_Obj_t* result_of_qe_using_skolem_functions;
		result_of_qe_using_skolem_functions = replaceVariablesByFormulas(formula_from_master, skolem_function_replacement_map);	
		assert(result_of_qe_using_skolem_functions != NULL); // F(psi(Y), Y)	

		list<string> VariablesToEliminate_Copy;
		VariablesToEliminate_Copy = Global_VariablesToEliminate;

		Aig_Obj_t* equivalence_check; // ~F(psi(Y), Y) \wedge F(X, Y)
		equivalence_check = createAnd(createNot(result_of_qe_using_skolem_functions, pub_aig_manager), formula_from_master, pub_aig_manager);
		assert(equivalence_check != NULL);

		// Give to SAT-Solver
		unsigned long long int cnf_time;
		int formula_size;
		unsigned long long int simplification_time;
		map<string, int> Model_of_equivalence_check;
		bool result_of_equivalence_check;

		bool use_incremental_solver = true;

		if(use_incremental_solver)
		{
			vector<Aig_Obj_t*> positive_assumptions;
			vector<Aig_Obj_t*> negative_assumptions;
			
			assert(IncrementalLabelCountForProvingCorrectness == 1);// first use should be HERE

			pSat_for_proving_correctness = sat_solver_new();
	
			result_of_equivalence_check = isExactnessCheckSatisfiable(pub_aig_manager, equivalence_check, Model_of_equivalence_check, cnf_time, formula_size, simplification_time, positive_assumptions, negative_assumptions, pSat_for_proving_correctness, IncrementalLabelTableForProvingCorrectness, IncrementalLabelCountForProvingCorrectness, Ci_name_to_Ci_label_mapForProvingCorrectness, Ci_label_to_Ci_name_mapForProvingCorrectness);
		
			sat_solver_delete(pSat_for_proving_correctness);
		}
		else
		{
			result_of_equivalence_check = isSat(pub_aig_manager, equivalence_check, Model_of_equivalence_check, cnf_time, formula_size, simplification_time);
		}
		
		if(result_of_equivalence_check)
		{
			cout << "\nexists X.f => f[X --> psi] is NOT valid; Skolem functions are NOT exact\n";
			cout << "\nCounterexample is\n";
			displayModelFromSATSolver(Model_of_equivalence_check);			
		}
		else
		{
			cout << "\nexists X.f => f[X --> psi] is valid; Skolem functions are exact\n";
		}
	}//if(top_level_block && prove_correctness_at_top_level_block)
}

void AIGBasedSkolem::GetFromHashTable_In_Cluster(int original_polarity_as_int, Aig_Obj_t* original_formula, vector<Aig_Obj_t*> &list_of_r1s, vector<Aig_Obj_t*> &list_of_r0s, int rank)
{
	#ifdef DEBUG_SKOLEM
	cout << "\nGetting the r0's and r1's from the hash tables\n";	
	#endif

	call_type original_polarity;
	if(original_polarity_as_int == 0)
	{
		original_polarity = original;
	}
	else if(original_polarity_as_int == 1)
	{
		original_polarity = negated;
	}
	else
	{
		assert(false);
	}	

	getEntryFromR0HashTable(original_polarity, original_formula, list_of_r0s);
	getEntryFromR1HashTable(original_polarity, original_formula, list_of_r1s);
}


void AIGBasedSkolem::SetInHashTable_In_Cluster(int original_polarity_as_int, Aig_Obj_t* original_formula, vector<Aig_Obj_t*> &list_of_r1s, vector<Aig_Obj_t*> &list_of_r0s, int rank)
{
	#ifdef DEBUG_SKOLEM
	cout << "\nSetting the r0's and r1's in the hash tables\n";	
	#endif

	assert(list_of_r1s.size() > 0);	
	assert(list_of_r0s.size() > 0);	

	call_type original_polarity;
	if(original_polarity_as_int == 0)
	{
		original_polarity = original;
	}
	else if(original_polarity_as_int == 1)
	{
		original_polarity = negated;
	}
	else
	{
		assert(false);
	}	
	
	insertIntoR0HashTable(original_polarity, original_formula, list_of_r0s);
	insertIntoR1HashTable(original_polarity, original_formula, list_of_r1s);

	#ifdef DEBUG_PAR
	printCallDetails_Across_ClusterNodes(original_polarity, original_formula, "Set", rank);
	printHashTableOperation_Across_ClusterNodes(original_polarity, original_formula, list_of_r1s, list_of_r0s, true, rank);
	#endif

	call_type polarity;
	Aig_Obj_t* formula;
	
	if(Aig_IsComplement(original_formula)) // original_formula is negated
	{
		if(original_polarity == original)
		{
			polarity = negated;
		}
		else
		{
			polarity = original;
		}
	}
	else // original_formula is original
	{
		if(original_polarity == original)
		{
			polarity = original;
		}
		else
		{
			polarity = negated;
		}
	}

	formula = Aig_Regular(original_formula);

	// original_formula with original_polarity is the same as 
	// formula  with  polarity

	if(polarity != original_polarity || formula != original_formula)
	{
		insertIntoR0HashTable(polarity, formula, list_of_r0s);
		insertIntoR1HashTable(polarity, formula, list_of_r1s);	

		#ifdef DEBUG_PAR
		printCallDetails_Across_ClusterNodes(polarity, formula, "Set", rank);
		printHashTableOperation_Across_ClusterNodes(polarity, formula, list_of_r1s, list_of_r0s, true, rank);
		#endif	
	}
}



AIGBasedSkolem::AIGBasedSkolem(Abc_Ntk_t* Original_Abc_Network, Aig_Man_t* ext_aig_manager, int rank, int order_from_master, char* order_file_from_master, char* variable_file_from_master, int debug_level, int milking_cex_on, set<string> &non_occuring_variables_to_eliminate, list<string> &order_of_elimination)
{
	assert(Original_Abc_Network != NULL);

	// worker node
	//assert(rank != 0); Why not in master node?

	#ifdef DEBUG_PAR
		cout << "\n\nInterface-Message: INIT STARTED IN PROCESSOR WITH RANK " << rank << endl << endl;
	#endif

	#ifdef DEBUG_SKOLEM
		cout << "\norder_file_from_master = " << order_file_from_master << endl;	
	#endif

	// Let's get all the variable names and
	// Ci_name_to_Ci_number_map
	Abc_Obj_t* tempInputObj;
	int j = 0;
	vector<string> variable_names;
	Abc_NtkForEachCi(Original_Abc_Network, tempInputObj, j)
	{
		string variable_name = Abc_ObjName(tempInputObj);
		variable_names.push_back(variable_name);

		Ci_name_to_Ci_number_map.insert(make_pair(variable_name, j));
		number_of_Cis++;				
	} 

	#ifdef DEBUG_SKOLEM	//Commented for now - SS
	cout << endl << "Ci_name_to_Ci_number_map" << endl;
	for(map<string, int>::iterator map_it = Ci_name_to_Ci_number_map.begin(); map_it != Ci_name_to_Ci_number_map.end(); map_it++)
	{
		cout << map_it->first << "\t" << map_it->second << endl;
	}
	#endif

	pub_aig_manager = ext_aig_manager;
	
	// Get the root_of_conjunction
	assert(Aig_ManCoNum(pub_aig_manager) == 1);
	Aig_Obj_t* CO_aig_manager;
	CO_aig_manager = Aig_ManCo(pub_aig_manager, 0);
	assert(CO_aig_manager != NULL);

	Aig_Obj_t* root_of_conjunction;
	root_of_conjunction = Aig_ObjChild0(CO_aig_manager);	
	assert(root_of_conjunction != NULL);

	Aig_Obj_t* arbitrary_boolean_formula = root_of_conjunction;

	perform_cegar_on_arbitrary_boolean_formulas = true;

	if(debug_level == 0)
	{
		mask_printing_cegar_details = true;
		mask_printing_details_file = true;
	}
	else if(debug_level == 1)
	{
		mask_printing_cegar_details = true;
		mask_printing_details_file = false;
	}
	else if(debug_level == 2)
	{
		mask_printing_cegar_details = false;
		mask_printing_details_file = false;
	}

	if(milking_cex_on == 1)
	{
		generate_all_counterexamples_from_sat_call = true;
	}
	else
	{
		generate_all_counterexamples_from_sat_call = false;
	}

	cleanup_after_each_step_in_arbitrary_boolean_combinations = false;

	// Let's get variables to eliminate

	list<string> VariablesToEliminate;
	variables_to_eliminate_file_name = variable_file_from_master;
	obtainVariablesToEliminate(VariablesToEliminate);
	set<string> VariablesToEliminate_Set(VariablesToEliminate.begin(), VariablesToEliminate.end());

	// Let's get the IDs of the variables
	
	Aig_Obj_t* ciObj;
	vector<int> variable_ids;
	int i = 0;
	Aig_ManForEachCi(pub_aig_manager, ciObj, i )
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

	#ifdef ENABLE_FILE_PRINTING_IN_DEBUG_PAR
		string debug_file_for_root_of_conjunction = "root_of_conjunction_rank_";
		char rank_char[100];
		sprintf(rank_char, "%d", rank);
		string rank_string(rank_char);
		debug_file_for_root_of_conjunction += rank_string;	

		writeFormulaToFileWithNodeId(pub_aig_manager, arbitrary_boolean_formula, debug_file_for_root_of_conjunction);
	#endif

	
	// Get the order of elimination
	order_of_elimination_of_variables = order_from_master;
	if(order_of_elimination_of_variables == 2)//external order
	{
		variable_order_file_name = order_file_from_master;
	}
	fixOrderOfEliminationForArbitraryBooleanFormula(VariablesToEliminate, arbitrary_boolean_formula, pub_aig_manager);

	Global_VariablesToEliminate = VariablesToEliminate;
	order_of_elimination = VariablesToEliminate;
	copy(Global_VariablesToEliminate.begin(), Global_VariablesToEliminate.end(), inserter(Global_VariablesToEliminate_Set, Global_VariablesToEliminate_Set.begin()));

	set<string> support_arbitrary_boolean_formula;
	computeSupport(arbitrary_boolean_formula, support_arbitrary_boolean_formula, pub_aig_manager);
	set_difference(support_arbitrary_boolean_formula.begin(), support_arbitrary_boolean_formula.end(), Global_VariablesToEliminate_Set.begin(), Global_VariablesToEliminate_Set.end(),inserter(Global_VariablesToRemain_Set, Global_VariablesToRemain_Set.begin()));

	set_difference(VariablesToEliminate_Set.begin(), VariablesToEliminate_Set.end(), Global_VariablesToEliminate_Set.begin(), Global_VariablesToEliminate_Set.end(),inserter(non_occuring_variables_to_eliminate, non_occuring_variables_to_eliminate.begin()));

	input_arbitrary_boolean_formula = arbitrary_boolean_formula;

	#ifdef DEBUG_PAR
		cout << "\n\nInterface-Message: INIT FINISHED IN PROCESSOR WITH RANK " << rank << endl << endl;
	#endif
	
	#ifdef DEBUG_SKOLEM
		cout << " List of variables to eliminate" << endl;
		showList(VariablesToEliminate);	
	#endif		
}


void AIGBasedSkolem::showListOfAigNodes(vector<Aig_Obj_t*> &list_of_r, string whoami)
{	
	cout << endl << whoami << endl;
	for(int list_it = 0; list_it < list_of_r.size(); list_it++)
	{
		Aig_Obj_t* my_node = list_of_r[list_it];
		cout <<"node: " << my_node;
		if(Aig_IsComplement(my_node))
			cout << "\tcomplemented"<< "\tnode->id: ~" << Aig_ObjId(Aig_Regular(my_node)) << endl;
		else
			cout << "\toriginal"<< "\tnode->id: " << Aig_ObjId(my_node) << endl;		
	}
}


void AIGBasedSkolem::printHashTableOperation_Across_ClusterNodes(call_type polarity, Aig_Obj_t* formula, vector<Aig_Obj_t*> &list_of_r1s, vector<Aig_Obj_t*> &list_of_r0s, bool set_operation, int rank)
{
	string key;	


	char rank_char[100];
	sprintf(rank_char, "rank%d", rank);
	string rank_string(rank_char);	


	char formula_char[100];
	sprintf(formula_char, "%p", formula);
	string formula_string(formula_char);
	if(polarity == negated)
	{
		formula_string += "neg";
	}
	else
	{
		formula_string += "org";
	}
	

	char id_char[100];
	if(Aig_IsComplement(formula))
	{
		sprintf(id_char, "neg%d", Aig_ObjId(Aig_Regular(formula)));
	}
	else	
	{
		sprintf(id_char, "org%d", Aig_ObjId(formula));
	}
	string id_string(id_char);
	if(polarity == negated)
	{
		id_string += "neg";
	}
	else
	{
		id_string += "org";
	}
	

	string operation_string;
	if(set_operation)
	{
		operation_string = "set";
	}
	else
	{
		operation_string = "get";
	}	


	key = operation_string;
	key += "_";
	key += rank_string;
	key += "_";
	key += id_string;	
	key += "_";
	key += formula_string;	

	// Print the cannot be one sets, and cannot be zero sets
	#ifdef ENABLE_FILE_PRINTING_IN_DEBUG_PAR

	int cannot_be_function_index = 0;
	for(list<string>::iterator list_it = Global_VariablesToEliminate.begin(); list_it != Global_VariablesToEliminate.end(); list_it++)
	{
		string variable_to_eliminate = *list_it;
		
		Aig_Obj_t* cannot_be_one_function;
		Aig_Obj_t* cannot_be_zero_function;		
		
		cannot_be_one_function = list_of_r1s[cannot_be_function_index];
		cannot_be_zero_function = list_of_r0s[cannot_be_function_index];

		string cannot_be_one_file_name = key;
		cannot_be_one_file_name += "_";
		cannot_be_one_file_name += "r1_";
		cannot_be_one_file_name += variable_to_eliminate;
		cannot_be_one_file_name += ".v";

		string cannot_be_zero_file_name = key;
		cannot_be_zero_file_name += "_";
		cannot_be_zero_file_name += "r0_";		
		cannot_be_zero_file_name += variable_to_eliminate;
		cannot_be_zero_file_name += ".v";
		
		writeFormulaToFile(pub_aig_manager, cannot_be_one_function, cannot_be_one_file_name);
		writeFormulaToFile(pub_aig_manager, cannot_be_zero_function, cannot_be_zero_file_name);
		
		cannot_be_function_index++;
		
	}// for each variable ends here
	
	#endif	

	
	if(set_operation)
	{
		cout << "\n\nInterface-Message: SET R0 and R1 ENTRIES NODE-POLARITY = " << formula_string << " AND NODEID-POLARITY = " << id_string << " IN PROCESSOR WITH RANK = " << rank <<"; SEE FILES STARTING WITH " << key << " FOR DETAILS\n\n";		
	}
	else
	{
		cout << "\n\nInterface-Message: GOT R0 and R1 ENTRIES NODE-POLARITY = " << formula_string << " AND NODEID-POLARITY = " << id_string << " IN PROCESSOR WITH RANK = " << rank <<"; SEE FILES STARTING WITH " << key << " FOR DETAILS\n\n";			
	}	
}



void AIGBasedSkolem::printCallDetails_Across_ClusterNodes(call_type polarity, Aig_Obj_t* formula, string function_name, int rank)
{
	string key;	


	char rank_char[100];
	sprintf(rank_char, "rank%d", rank);
	string rank_string(rank_char);	


	char formula_char[100];
	sprintf(formula_char, "%p", formula);
	string formula_string(formula_char);
	if(polarity == negated)
	{
		formula_string += "neg";
	}
	else
	{
		formula_string += "org";
	}
	

	char id_char[100];
	if(Aig_IsComplement(formula))
	{
		sprintf(id_char, "neg%d", Aig_ObjId(Aig_Regular(formula)));
	}
	else	
	{
		sprintf(id_char, "org%d", Aig_ObjId(formula));
	}
	string id_string(id_char);
	if(polarity == negated)
	{
		id_string += "neg";
	}
	else
	{
		id_string += "org";
	}
	

	cout << endl << "\nInterface-Message: FUNCTION " << function_name << " CALLED FOR NODE-POLARITY = " << formula_string << " AND NODEID-POLARITY = " << id_string << " IN PROCESSOR WITH RANK = " << rank << endl << endl;
}


void AIGBasedSkolem::attachCallDetailsInFile(call_type polarity, Aig_Obj_t* formula, string function_name)
{
	char formula_char[100];
	sprintf(formula_char, "%p", formula);
	string formula_string(formula_char);
	if(polarity == negated)
	{
		formula_string += "neg";
	}
	else
	{
		formula_string += "org";
	}
	

	char id_char[100];
	if(Aig_IsComplement(formula))
	{
		sprintf(id_char, "neg%d", Aig_ObjId(Aig_Regular(formula)));
	}
	else	
	{
		sprintf(id_char, "org%d", Aig_ObjId(formula));
	}
	string id_string(id_char);
	if(polarity == negated)
	{
		id_string += "neg";
	}
	else
	{
		id_string += "org";
	}

	
	string call_file_name = logfile_prefix;
	call_file_name += "skolem_calls.txt";
	FILE* call_fp = fopen(call_file_name.c_str(), "a+");
	
	fprintf(call_fp,"%s\t%s\n", formula_string.c_str(), id_string.c_str());

	fclose(call_fp);	
}

/* Given a replacement map this function optimizes the map by removing entries in it that 
will not occur in the formula on which replacement is to be applied */
void AIGBasedSkolem::optimizeReplacementMap(map<string, Aig_Obj_t*> &replacement_map, Aig_Obj_t* source_formula, map<string, Aig_Obj_t*> &optimized_replacement_map)
{
	set<string> support_source_formula;
	computeSupport(source_formula, support_source_formula, pub_aig_manager);

	for(map<string, Aig_Obj_t*>::iterator replacement_map_it = replacement_map.begin(); replacement_map_it != replacement_map.end(); replacement_map_it++)
	{
		set<string>::iterator support_source_formula_it = support_source_formula.find(replacement_map_it->first);
		if(support_source_formula_it != support_source_formula.end()) // variable in replacement_map exists in source formula
		{
			//#ifdef DEBUG_SKOLEM
			//cout << "\nOptimized entry:  = " << replacement_map_it->first << "\tsize of rhs = " << computeSize(replacement_map_it->second, pub_aig_manager) << endl;
			//#ifdef DEBUG_SKOLEM

			optimized_replacement_map.insert(make_pair(replacement_map_it->first, replacement_map_it->second));
		}
	}
}


void AIGBasedSkolem::showReplacementMap(map<string, Aig_Obj_t*> &replacement_map, string whoami)
{
	cout << endl << whoami << endl;
	for(map<string, Aig_Obj_t*>::iterator replacement_map_it = replacement_map.begin(); replacement_map_it != replacement_map.end(); replacement_map_it++)
	{
		cout << "\nEntry: lhs = " << replacement_map_it->first << "\tsize of rhs = " << computeSize(replacement_map_it->second, pub_aig_manager) << endl;			
	}
	
}



void AIGBasedSkolem::showReplacementMap(map<string, Aig_Obj_t*> &replacement_map, string whoami, int call_count)
{
	cout << endl << whoami << endl;
	for(map<string, Aig_Obj_t*>::iterator replacement_map_it = replacement_map.begin(); replacement_map_it != replacement_map.end(); replacement_map_it++)
	{
		cout << "\nEntry: lhs = " << replacement_map_it->first << "\tsize of rhs = " << computeSize(replacement_map_it->second, pub_aig_manager) << endl;			
	}

	
	for(map<string, Aig_Obj_t*>::iterator replacement_map_it = replacement_map.begin(); replacement_map_it != replacement_map.end(); replacement_map_it++)
	{
		string aig_file_name = benchmark_name_without_extension;
		aig_file_name += "_replacement_map_failure_aig_expand_";	
		aig_file_name += replacement_map_it->first;
		writeFormulaToFile(pub_aig_manager, replacement_map_it->second, aig_file_name, ".v", 0, call_count);					
	}
	
}




bool AIGBasedSkolem::checkIfSkolemFunctionAtGivenIndexIsExact_using_Simulation(int correction_index, map<string, int> &Model_of_ExactnessCheck, map<int, Aig_Obj_t*> &Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX, map<int, Aig_Obj_t*> &Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX, list<string> &VariablesToEliminate, int number_of_solutions_generated_with_same_y)
{
	#ifdef RECORD_KEEP
	string record_file;
	record_file = logfile_prefix;
	record_file += "skolem_function_generation_details.txt";
	FILE* record_fp = fopen(record_file.c_str(), "a+");
	assert(record_fp != NULL);
	#endif

	assert(cegar_iteration_number > 0);
	assert(cegar_iteration_for_correction_index > 0); 
	
	if(use_assumptions_in_unified_cegar)
	{
		cout << "\nExtracting counterexamples using simulation is not supported when USE-ASSUMPTIONS-IN-UNIFIED-CEGAR is true\n";
		assert(false);
	}

	// 1) Add the refinement hints into CNF of the incremental solver
	#ifdef DEBUG_CEGAR
	if(Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX.empty() && Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX.empty())
	{
		cout << "\nRefinement hints are empty\n";
	}
	else
	{
		cout << "\nRefinement hints are NOT empty\n";
	}
	#endif

	#ifdef DEBUG_CEGAR
	show_present_refinement_hint(Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX, Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX);
	#endif

	Aig_Obj_t* delta_epsilon_i;

	// Create the dag for delta_epsilon_i:
	// for each o_j added in Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX
	// (o_j = dag_j) \wedge 
	// (Z_i_k = Z_i_{k+1} \wedge o_j)
	// also for each o_j added in Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX
	// (o_j = dag_j)
		
	Aig_Obj_t* Cb_part;
	set<Aig_Obj_t*> Cb_objects;

	Aig_Obj_t* Z_part;
	set<Aig_Obj_t*> Z_objects;

	for(map<int, Aig_Obj_t*>::iterator hint_it = Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX.begin(); hint_it != Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX.end(); hint_it++)
	{
		int destination = hint_it->first;
		Aig_Obj_t* new_cannot_be_one_object_at_destination = hint_it->second;

		map<Aig_Obj_t*, Aig_Obj_t*>::iterator cannot_be_object_to_cannot_be_dag_map_it = cannot_be_object_to_cannot_be_dag_map.find(new_cannot_be_one_object_at_destination);
		assert(cannot_be_object_to_cannot_be_dag_map_it != cannot_be_object_to_cannot_be_dag_map.end());
		Aig_Obj_t* new_cannot_be_one_dag_at_destination = cannot_be_object_to_cannot_be_dag_map_it->second;

		Aig_Obj_t* Cb_one_equivalence = createEquivalence(new_cannot_be_one_object_at_destination, new_cannot_be_one_dag_at_destination, pub_aig_manager);
		assert(Cb_one_equivalence != NULL);

		Cb_objects.insert(Cb_one_equivalence);

		
		int present_z_j_k_count = Z_variable_counter[destination];
		int next_z_j_k_count = present_z_j_k_count + 1;
		Z_variable_counter[destination] = next_z_j_k_count;

		string present_z_j_k_string = obtainZVariableString(destination, present_z_j_k_count); // obtain the string Z_{destination}_{present_z_j_k_count}
		Aig_Obj_t* present_z_j_k_object = obtainExistingObjectOfTemporaryVariableForIncrementalSolving(present_z_j_k_string);
		assert(present_z_j_k_object != NULL);
				
		string next_z_j_k_string = obtainZVariableString(destination, next_z_j_k_count); // obtain the string Z_{destination}_{next_z_j_k_count}
		Aig_Obj_t* next_z_j_k_object = obtainObjectOfTemporaryVariableForIncrementalSolving(next_z_j_k_string);
		assert(next_z_j_k_object != NULL);

		Aig_Obj_t* R_i_j_increment = createEquivalence(present_z_j_k_object, createAnd(createNot(new_cannot_be_one_object_at_destination, pub_aig_manager), next_z_j_k_object, pub_aig_manager), pub_aig_manager);
		assert(R_i_j_increment != NULL);

		Z_objects.insert(R_i_j_increment);
	}
		
		
	for(map<int, Aig_Obj_t*>::iterator hint_it = Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX.begin(); hint_it != Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX.end(); hint_it++)
	{
		int destination = hint_it->first;
		Aig_Obj_t* new_cannot_be_zero_object_at_destination = hint_it->second;

		map<Aig_Obj_t*, Aig_Obj_t*>::iterator cannot_be_object_to_cannot_be_dag_map_it = cannot_be_object_to_cannot_be_dag_map.find(new_cannot_be_zero_object_at_destination);
		assert(cannot_be_object_to_cannot_be_dag_map_it != cannot_be_object_to_cannot_be_dag_map.end());
		Aig_Obj_t* new_cannot_be_zero_dag_at_destination = cannot_be_object_to_cannot_be_dag_map_it->second;

		Aig_Obj_t* Cb_zero_equivalence = createEquivalence(new_cannot_be_zero_object_at_destination, new_cannot_be_zero_dag_at_destination, pub_aig_manager);
		assert(Cb_zero_equivalence != NULL);

		Cb_objects.insert(Cb_zero_equivalence);
	}
		
	if(Cb_objects.empty() && Z_objects.empty())
	{
		delta_epsilon_i = createTrue(pub_aig_manager);
	}
	else
	{		
		assert(!Cb_objects.empty());
		Cb_part = createAnd(Cb_objects, pub_aig_manager);
		assert(Cb_part != NULL);
		// connect to some output to avoid unwanted deletion
		Aig_Obj_t* Cb_part_CO = Aig_ObjCreateCo(pub_aig_manager, Cb_part ); 
		assert(Cb_part_CO != NULL);
		intermediate_cos_created.insert(Cb_part_CO);

		assert(!Z_objects.empty());
		Z_part = createAnd(Z_objects, pub_aig_manager);
		assert(Z_part != NULL);
		// connect to some output to avoid unwanted deletion
		Aig_Obj_t* Z_part_CO = Aig_ObjCreateCo(pub_aig_manager, Z_part ); 
		assert(Z_part_CO != NULL);
		intermediate_cos_created.insert(Z_part_CO);


		#ifdef DEBUG_SKOLEM
		string Cb_part_file_name = benchmark_name_without_extension;
		Cb_part_file_name += "_Cb_part";

		string Z_part_file_name = benchmark_name_without_extension;
		Z_part_file_name += "_Z_part";

		cout << "\nCb_part computed\n";
		cout << "\nZ_part computed\n";

		writeFormulaToFile(pub_aig_manager, Cb_part, Cb_part_file_name, ".v", cegar_iteration_number, number_of_solutions_generated_with_same_y);
		writeFormulaToFile(pub_aig_manager, Z_part, Z_part_file_name, ".v", cegar_iteration_number, number_of_solutions_generated_with_same_y);
		#endif

		delta_epsilon_i = createAnd(Cb_part, Z_part, pub_aig_manager);
	}

	assert(delta_epsilon_i != NULL);
	// connect to some output to avoid unwanted deletion
	Aig_Obj_t* delta_epsilon_i_CO = Aig_ObjCreateCo(pub_aig_manager, delta_epsilon_i ); 
	assert(delta_epsilon_i_CO != NULL);
	intermediate_cos_created.insert(delta_epsilon_i_CO);


	#ifdef DEBUG_CEGAR
	string delta_epsilon_i_file_name = benchmark_name_without_extension;
	delta_epsilon_i_file_name += "_delta_epsilon_i";
	cout << "\ndelta_epsilon_i computed\n";
	writeFormulaToFile(pub_aig_manager, delta_epsilon_i, delta_epsilon_i_file_name, ".v", cegar_iteration_number, number_of_solutions_generated_with_same_y);
	#endif

	#ifdef DEBUG_CEGAR
	cout << endl << "Adding clauses of delta_epsilon_i to SAT-Solver\n";
	#endif

	if(use_generic_sat_solver_interface)
	{
			if(sat_solver_used_in_cegar == "abc")
			{
				getIncrementAsCNF_and_AddToSolver(pub_aig_manager, delta_epsilon_i, pSat_for_exactness_check, IncrementalLabelTableForExactnessCheck, IncrementalLabelCountForExactnessCheck, Ci_name_to_Ci_label_mapForExactnessCheck, Ci_label_to_Ci_name_mapForExactnessCheck);

			}
			else // for other SAT solvers
			{
				assert(false);
			}	
	}
	else
	{
		addIncrementToExactnessCheck(pub_aig_manager, delta_epsilon_i, pSat_for_exactness_check, IncrementalLabelTableForExactnessCheck, IncrementalLabelCountForExactnessCheck, Ci_name_to_Ci_label_mapForExactnessCheck, Ci_label_to_Ci_name_mapForExactnessCheck);
	
	}

	// Perform simulation to check satisfiability of F(X, Y)

	#ifdef DETAILED_RECORD_KEEP
	unsigned long long int simulation_ms;
	struct timeval simulation_start_ms, simulation_finish_ms;
	gettimeofday (&simulation_start_ms, NULL); 	
	#endif

	bool f_is_sat = checkSatisfiabilityOfFunctionUsingSimulation(Model_of_ExactnessCheck, Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX, VariablesToEliminate);

	
	#ifdef DETAILED_RECORD_KEEP
	gettimeofday (&simulation_finish_ms, NULL);
	simulation_ms = simulation_finish_ms.tv_sec * 1000 + simulation_finish_ms.tv_usec / 1000;
	simulation_ms -= simulation_start_ms.tv_sec * 1000 + simulation_start_ms.tv_usec / 1000;
	total_time_in_simulation_to_replace_sat_in_cegar = total_time_in_simulation_to_replace_sat_in_cegar + simulation_ms;
	#endif

	#ifdef RECORD_KEEP
	if(!mask_printing_cegar_details)
	{
		fprintf(record_fp, "\n\n%d\t%d\t%llu(-,-)(-)", cegar_iteration_number, correction_index, simulation_ms);
	}

	fclose(record_fp);
	#endif


	#ifdef DEBUG_SKOLEM
	displayModelFromSATSolver(Model_of_ExactnessCheck);
	cout << endl << "f_is_sat = " << f_is_sat << endl;
	#endif

	if(f_is_sat)
	// f(x,y) is sat/true under Model_of_ExactnessCheck, i.e. ~f(x,y) is false, i.e. epsilon is false 
	{
		return false;
	}
	else // f(x,y) is unsat/false under Model_of_ExactnessCheck, i.e. ~f(x,y) is true, i.e. epsilon is true 
	{
		return true;
	}

}


Aig_Obj_t* AIGBasedSkolem::createSkolemFunction_In_Mu_Based_Scheme_With_Optimizations_With_Optional_ICb0(int destination)
{
	map<int, set<Aig_Obj_t*> >::iterator cannot_be_one_set_it = cannot_be_one_set.find(destination);
	assert(cannot_be_one_set_it != cannot_be_one_set.end());

	set<Aig_Obj_t*> cannot_be_one_set_objects = cannot_be_one_set_it->second;
	// let's find the corresponding dags

	Aig_Obj_t* skolem_function_part1;
	set<Aig_Obj_t*> skolem_function_part1_components;

	for(set<Aig_Obj_t*>::iterator cannot_be_one_set_objects_it = cannot_be_one_set_objects.begin(); cannot_be_one_set_objects_it != cannot_be_one_set_objects.end();  cannot_be_one_set_objects_it++)
	{
		Aig_Obj_t* cannot_be_object = *cannot_be_one_set_objects_it;
		assert(cannot_be_object != NULL);

		map<Aig_Obj_t*, Aig_Obj_t*>::iterator cannot_be_object_to_cannot_be_dag_map_it = cannot_be_object_to_cannot_be_dag_map.find(cannot_be_object);
		assert(cannot_be_object_to_cannot_be_dag_map_it != cannot_be_object_to_cannot_be_dag_map.end());
				
		Aig_Obj_t* cannot_be_dag = cannot_be_object_to_cannot_be_dag_map_it->second;
		assert(cannot_be_dag != NULL);
		
		skolem_function_part1_components.insert(cannot_be_dag);		
	}

	if(skolem_function_part1_components.empty()) // no condition under which it can't be 1
	// i.e. it can be 1 always
	{
		skolem_function_part1 = createTrue(pub_aig_manager);
	}
	else
	{
		skolem_function_part1 = createOr(skolem_function_part1_components, pub_aig_manager);
		skolem_function_part1 = createNot(skolem_function_part1, pub_aig_manager);
	}
	assert(skolem_function_part1 != NULL);
	
	map<int, Aig_Obj_t*>::iterator initial_cannot_be_zero_dags_it = initial_cannot_be_zero_dags.find(destination);
	assert(initial_cannot_be_zero_dags_it != initial_cannot_be_zero_dags.end());
	Aig_Obj_t* skolem_function_part2 = initial_cannot_be_zero_dags_it->second;
	
	
	Aig_Obj_t* skolem_function;
	skolem_function = createOr(createAnd(use_cbzero_in_unified_cegar_aig, skolem_function_part2, pub_aig_manager), skolem_function_part1, pub_aig_manager);	
	assert(skolem_function != NULL);

	return skolem_function;
}


bool AIGBasedSkolem::checkSatisfiabilityOfFunctionUsingSimulation(map<string, int> &Model_of_ExactnessCheck, map<int, Aig_Obj_t*> &Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX, list<string> &VariablesToEliminate)
{
	// First let's parse the model and get values of X variables, Y variables, 
	// X' variables, and cannot_be_string variables

	map<string, int> XValues; // XValues[x_variable] gives value of x_variable
	map<string, int> YValues; // YValues[y_variable] gives value of y_variable
	map<string, int> CannotBeStringValues; // CannotBeStringValues[cannot_be_string] gives its value
	map<string, int> XNewValues; // XNewValues[x_new_variable] gives value of x_new_variable

	for(map<string, int>::iterator model_it = Model_of_ExactnessCheck.begin(); model_it != Model_of_ExactnessCheck.end(); model_it++)
	{
		string variable_name = model_it->first;
		int variable_value = model_it->second;
		
		map<string, Aig_Obj_t*>::iterator cannot_be_string_to_cannot_be_object_map_it = cannot_be_string_to_cannot_be_object_map.find(variable_name);

		if(cannot_be_string_to_cannot_be_object_map_it != cannot_be_string_to_cannot_be_object_map.end()) // variable_name is eta/sigma
		{
			CannotBeStringValues.insert(make_pair(variable_name, variable_value));		
		}
		else if(variables_quantified.find(variable_name) != variables_quantified.end()) // variable_name is an X  variable
		{
			XValues.insert(make_pair(variable_name, variable_value));
		}
		else if(variables_not_quantified.find(variable_name) != variables_not_quantified.end()) // variable_name is a Y variable
		{
			YValues.insert(make_pair(variable_name, variable_value));
		}
		else
		{
			XNewValues.insert(make_pair(variable_name, variable_value));
		}
	}

	Model_of_ExactnessCheck.clear(); // No longer needed now


	#ifdef DEBUG_CEGAR
	cout << endl;
	for(map<string, int>::iterator XValues_it = XValues.begin(); XValues_it != XValues.end(); XValues_it++)
	{
		cout << endl << "XValues[" << XValues_it->first << "] = " << XValues_it->second;
	}
	cout << endl;
	for(map<string, int>::iterator XNewValues_it = XNewValues.begin(); XNewValues_it != XNewValues.end(); XNewValues_it++)
	{
		cout << endl << "XNewValues[" << XNewValues_it->first << "] = " << XNewValues_it->second;
	}
	cout << endl;
	for(map<string, int>::iterator YValues_it = YValues.begin(); YValues_it != YValues.end(); YValues_it++)
	{
		cout << endl << "YValues[" << YValues_it->first << "] = " << YValues_it->second;
	}
	cout << endl;
	for(map<string, int>::iterator CannotBeStringValues_it = CannotBeStringValues.begin(); CannotBeStringValues_it != CannotBeStringValues.end(); CannotBeStringValues_it++)
	{
		cout << endl << "CannotBeStringValues[" << CannotBeStringValues_it->first << "] = " << CannotBeStringValues_it->second;
	}
	cout << endl;		
	#endif

	
	// Then find the location from which we need to start reevaluating the XValues
	// This is the location of the maximum x_i in the Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX

	map<int, Aig_Obj_t*>::reverse_iterator Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX_rit = Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX.rbegin();
	int last_refined_location = Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX_rit->first;
	
	#ifdef DEBUG_CEGAR
	cout << endl << "last_refined_location = " << last_refined_location << endl;
	#endif

	// Now reevaluate the XValues x_{last_refined_location} ... x_{1} using 
	// the values of Y variables and XValues x_{n} ... x_{last_refined_location+1}
	// Just remember that the Skolem functions existing are r0[i] \vee ~r1[i]
	// What we want are Skolem functions of the form ~r1[i]	

	// We will use a common hash-table if use_common_hashtable_in_milking is true
	bool use_common_hashtable_in_milking = true;
	t_HashTable<int, bool> CommonEvaluationHashTableInMilking;

	map<string, bool> variable_to_value_map;
	for(map<string, int>::iterator yvalues_it = YValues.begin(); yvalues_it != YValues.end(); yvalues_it++)
	{
		bool bool_value;
		if(yvalues_it->second == 1)
		{
			bool_value = true;
		}
		else
		{
			bool_value = false;
		}

		variable_to_value_map.insert(make_pair(yvalues_it->first, bool_value));
		#ifdef DEBUG_SKOLEM
			cout << endl << yvalues_it->first << " --> " << bool_value << " inserted into variable_to_value_map\n";
		#endif
		Model_of_ExactnessCheck.insert(make_pair(yvalues_it->first, yvalues_it->second));
	}
	
	for(int var_to_elim_index = number_of_vars_to_elim; var_to_elim_index > last_refined_location; var_to_elim_index--)
	{
		string var_to_elim = searchVarIndexToVarNameMap(var_index_to_var_name_map, var_to_elim_index);
		map<string, int>::iterator xvalues_it = XValues.find(var_to_elim);
	
		bool bool_value;
		if(xvalues_it->second == 1)
		{
			bool_value = true;
		}
		else
		{
			bool_value = false;
		}

		variable_to_value_map.insert(make_pair(xvalues_it->first, bool_value));
		#ifdef DEBUG_SKOLEM
			cout << endl << xvalues_it->first << " --> " << bool_value << " inserted into variable_to_value_map\n";
		#endif
		Model_of_ExactnessCheck.insert(make_pair(xvalues_it->first, xvalues_it->second));
	}
	
	for(int var_to_elim_index = last_refined_location; var_to_elim_index >= 1; var_to_elim_index--)
	{
		// Obtain XValues[var_to_elim_index]
		string var_to_elim = searchVarIndexToVarNameMap(var_index_to_var_name_map, var_to_elim_index);

		#ifdef DEBUG_SKOLEM
			cout << endl << "Evaluating the Skolem function of " << var_to_elim << ", i.e., x[" << var_to_elim_index << "]" << endl;
		#endif

		// obtaining \psi_i
		Aig_Obj_t* skolem_function;
		bool use_the_existing_skolem_function = false;
		// Existing Skolem function is r0[i] \vee ~r1[i]
		// We need to compute Skolem function based on value of  
		// use_cbzero_in_unified_cegar_aig
		if(use_the_existing_skolem_function)
		{
			skolem_function = searchOneDimensionalMatrix(SkolemFunctions, number_of_vars_to_elim, var_to_elim_index);
		}
		else
		{
			skolem_function = createSkolemFunction_In_Mu_Based_Scheme_With_Optimizations_With_Optional_ICb0(var_to_elim_index);
		}
		assert(skolem_function != NULL); 

		#ifdef DEBUG_SKOLEM
		string skolem_function_file_name = benchmark_name_without_extension;
		skolem_function_file_name += "_skolem_function_used_in_simulation";
		writeFormulaToFile(pub_aig_manager, skolem_function, skolem_function_file_name, ".v", var_to_elim_index, cegar_iteration_number);
		#endif

		bool bool_value;
		if(use_common_hashtable_in_milking)
		{
			bool_value = evaluateFormulaOfCi_Efficient_With_Given_HashTable(skolem_function, variable_to_value_map, CommonEvaluationHashTableInMilking);
		}
		else if(true)
		{
			bool_value = evaluateFormulaOfCi_Efficient(skolem_function, variable_to_value_map);//This is more efficient
		}
		else
		{
			bool_value = evaluateFormulaOfCi(skolem_function, variable_to_value_map);//less efficient version
		}


		variable_to_value_map.insert(make_pair(var_to_elim, bool_value));	

		#ifdef DEBUG_SKOLEM
			cout << endl << var_to_elim << " --> " << bool_value << " inserted into variable_to_value_map\n";
		#endif

		if(bool_value)
		{
			Model_of_ExactnessCheck.insert(make_pair(var_to_elim, 1));	
		}
		else
		{
			Model_of_ExactnessCheck.insert(make_pair(var_to_elim, 0));
		}	
	}

	
	bool f_is_sat;
	if(use_common_hashtable_in_milking)
	{
		f_is_sat = evaluateFormulaOfCi_Efficient_With_Given_HashTable(conjunction_of_factors, variable_to_value_map, CommonEvaluationHashTableInMilking);
	}
	else if(true)
	{
		f_is_sat = evaluateFormulaOfCi_Efficient(conjunction_of_factors, variable_to_value_map);//This is more efficient
	}
	else
	{
		f_is_sat = evaluateFormulaOfCi(conjunction_of_factors, variable_to_value_map);//less efficient version
	}

	#ifdef DEBUG_CEGAR
	cout << endl << "f_is_sat = " << f_is_sat << endl;
	#endif

	if(f_is_sat)//~f is unsat; no model
	{
		Model_of_ExactnessCheck.clear();
	}
	else
	{
		// Note that we also need to add the XNewvalues, and reevaluate the r1[i]'s and r0[i]'s	

		for(map<string, int>::iterator XNewValues_it = XNewValues.begin(); XNewValues_it != XNewValues.end(); XNewValues_it++)
		{
			Model_of_ExactnessCheck.insert(make_pair(XNewValues_it->first, XNewValues_it->second));
		}

		for(map<string, Aig_Obj_t*>::iterator cannot_be_string_to_cannot_be_object_map_it = cannot_be_string_to_cannot_be_object_map.begin(); cannot_be_string_to_cannot_be_object_map_it != cannot_be_string_to_cannot_be_object_map.end(); cannot_be_string_to_cannot_be_object_map_it++)
		{
			string cannot_be_string = cannot_be_string_to_cannot_be_object_map_it->first;
			Aig_Obj_t* cannot_be_object = cannot_be_string_to_cannot_be_object_map_it->second;
			
			map<Aig_Obj_t*, Aig_Obj_t*>::iterator cannot_be_object_to_cannot_be_dag_map_it = cannot_be_object_to_cannot_be_dag_map.find(cannot_be_object);
			assert(cannot_be_object_to_cannot_be_dag_map_it != cannot_be_object_to_cannot_be_dag_map.end());
			Aig_Obj_t* cannot_be_dag = cannot_be_object_to_cannot_be_dag_map_it->second;

			bool bool_value;
			if(use_common_hashtable_in_milking)
			{
				bool_value = evaluateFormulaOfCi_Efficient_With_Given_HashTable(cannot_be_dag, variable_to_value_map, CommonEvaluationHashTableInMilking);
			}
			else if(true)
			{
				bool_value = evaluateFormulaOfCi_Efficient(cannot_be_dag, variable_to_value_map);//This is more efficient
			}
			else
			{
				bool_value = evaluateFormulaOfCi(cannot_be_dag, variable_to_value_map);//less efficient version
			}

			if(bool_value)
			{
				Model_of_ExactnessCheck.insert(make_pair(cannot_be_string, 1));	
			}
			else
			{
				Model_of_ExactnessCheck.insert(make_pair(cannot_be_string, 0));
			}
		}
		
	}

	return f_is_sat;	
}




bool AIGBasedSkolem::checkIfSkolemFunctionAtGivenIndexIsExact_using_Mu_Based_Scheme_With_Optimizations_For_Functional_Forms(int cegar_iteration_number, int correction_index, map<string, int> &Model_of_ExactnessCheck, map<int, Aig_Obj_t*> &Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX, map<int, Aig_Obj_t*> &Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX, list<string> &VariablesToEliminate)
{
	assert(benchmark_type == "factorization");	

	if(cegar_iteration_number == 0)
	{
		#ifdef DEBUG_CEGAR
		cout << "\nCase with cegar_iteration_number == 0 \n";
		#endif

		// First create epsilon_zero and add clauses arises from it into the SAT solver

		Aig_Obj_t* epsilon_zero;

		// correction_index must be number_of_vars_to_elim
		assert(correction_index == number_of_vars_to_elim);

		// Create the dag for epsilon_zero:
		

		// dag for epsilon_zero is: 

		// F(x_1',...,x_n',Y) \wedge

		// (B_1 \vee ... \vee B_{n-1}) \wedge (B_1 = dag for bad_1) \wedge ... (B_{n-1} = dag for bad_{n-1}) \wedge

		// (x_2 = psi_2) \wedge ... \wedge (x_n = psi_n) \wedge 
		
		// (eta_1 = dag for eta_1) \wedge ... \wedge (eta_l = dag for eta_l) \wedge
		// (sigma_1 = dag for sigma_1) \wedge ... \wedge (sigma_s = dag for sigma_s) \wedge
		// we need to consider eta's and sigma's of all x_i's

		// Let's first create dag for 
		// (eta_1 = dag for eta_1) \wedge ... \wedge (eta_l = dag for eta_l) \wedge
		// (sigma_1 = dag for sigma_1) \wedge ... \wedge (sigma_s = dag for sigma_s)
		// in Cb_part

		Aig_Obj_t* Cb_part;
		set<Aig_Obj_t*> Cb_objects;

		for(map<int, set<Aig_Obj_t*> >::iterator cannot_be_one_set_it = cannot_be_one_set.begin(); cannot_be_one_set_it != cannot_be_one_set.end(); cannot_be_one_set_it++)
		{
			int var_to_elim_index = cannot_be_one_set_it->first;
			
			set<Aig_Obj_t*> cannot_be_one_set_objects = cannot_be_one_set_it->second;
			// let's find the corresponding dags

			for(set<Aig_Obj_t*>::iterator cannot_be_one_set_objects_it = cannot_be_one_set_objects.begin(); cannot_be_one_set_objects_it != cannot_be_one_set_objects.end();  cannot_be_one_set_objects_it++)
			{
				Aig_Obj_t* cannot_be_object = *cannot_be_one_set_objects_it;
				assert(cannot_be_object != NULL);

				map<Aig_Obj_t*, Aig_Obj_t*>::iterator cannot_be_object_to_cannot_be_dag_map_it = cannot_be_object_to_cannot_be_dag_map.find(cannot_be_object);
				assert(cannot_be_object_to_cannot_be_dag_map_it != cannot_be_object_to_cannot_be_dag_map.end());
				
				Aig_Obj_t* cannot_be_dag = cannot_be_object_to_cannot_be_dag_map_it->second;
				assert(cannot_be_dag != NULL);
			
				Aig_Obj_t* Cb_equivalence = createEquivalence(cannot_be_object, cannot_be_dag, pub_aig_manager);
				Cb_objects.insert(Cb_equivalence);
			}	
		}

		for(map<int, set<Aig_Obj_t*> >::iterator cannot_be_zero_set_it = cannot_be_zero_set.begin(); cannot_be_zero_set_it != cannot_be_zero_set.end(); cannot_be_zero_set_it++)
		{
			int var_to_elim_index = cannot_be_zero_set_it->first;
			
			set<Aig_Obj_t*> cannot_be_zero_set_objects = cannot_be_zero_set_it->second;
			// let's find the corresponding dags

			for(set<Aig_Obj_t*>::iterator cannot_be_zero_set_objects_it = cannot_be_zero_set_objects.begin(); cannot_be_zero_set_objects_it != cannot_be_zero_set_objects.end();  cannot_be_zero_set_objects_it++)
			{
				Aig_Obj_t* cannot_be_object = *cannot_be_zero_set_objects_it;
				assert(cannot_be_object != NULL);

				map<Aig_Obj_t*, Aig_Obj_t*>::iterator cannot_be_object_to_cannot_be_dag_map_it = cannot_be_object_to_cannot_be_dag_map.find(cannot_be_object);
				assert(cannot_be_object_to_cannot_be_dag_map_it != cannot_be_object_to_cannot_be_dag_map.end());
				
				Aig_Obj_t* cannot_be_dag = cannot_be_object_to_cannot_be_dag_map_it->second;
				assert(cannot_be_dag != NULL);
			
				Aig_Obj_t* Cb_equivalence = createEquivalence(cannot_be_object, cannot_be_dag, pub_aig_manager);
				Cb_objects.insert(Cb_equivalence);
			}	
		}

		assert(!Cb_objects.empty());
		Cb_part = createAnd(Cb_objects, pub_aig_manager);
		assert(Cb_part != NULL);
		// connect to some output to avoid unwanted deletion
		Aig_Obj_t* Cb_part_CO = Aig_ObjCreateCo(pub_aig_manager, Cb_part ); 
		assert(Cb_part_CO != NULL);
		intermediate_cos_created.insert(Cb_part_CO);


		// Let's create dag for (x_2 = psi_2) \wedge ... \wedge (x_n = psi_n)
		// We need to add exact Skolem functions for Tsietin variables if apply_tsietin_encoding_on_benchmarks is true
		
		Aig_Obj_t* S_equivalence_part;
		set<Aig_Obj_t*> S_equivalence_objects;

		// we need to create psi_i as  disjunction of elements in initial_cannot_be_zero_objects[i] 
		// \vee negation of disjunction of elements in cannot-be-one-set[i]
		for(map<int, set<Aig_Obj_t*> >::iterator cannot_be_one_set_it = cannot_be_one_set.begin(); cannot_be_one_set_it != cannot_be_one_set.end(); cannot_be_one_set_it++)
		{
			int var_to_elim_index = cannot_be_one_set_it->first;

			if(apply_tsietin_encoding_on_benchmarks)
			{
				if(var_to_elim_index <= number_of_tsietin_variables)
				{
					#ifdef DEBUG_SKOLEM
					cout << endl << var_to_elim_index << " <= " << number_of_tsietin_variables <<", hence exact Skolem fuctions to be used\n";
					#endif
					continue; // no need to add abstract Skolem functions
				}
			}

			// obtaining dag for x_i
			string var_to_elim = searchVarIndexToVarNameMap(var_index_to_var_name_map, var_to_elim_index);

			map<string, Aig_Obj_t*>::iterator Ci_to_eliminate_name_to_Ci_to_eliminate_object_map_it = Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.find(var_to_elim);
			assert(Ci_to_eliminate_name_to_Ci_to_eliminate_object_map_it != Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.end());			
			Aig_Obj_t* var_to_elim_obj = Ci_to_eliminate_name_to_Ci_to_eliminate_object_map_it->second;

			// obtaining \psi_i_part2
			Aig_Obj_t* psi_i_part2;
			set<Aig_Obj_t*> psi_i_part2_components = cannot_be_one_set_it->second;
			if(psi_i_part2_components.empty())
			{
				psi_i_part2 = createTrue(pub_aig_manager);
			}
			else
			{
				psi_i_part2 = createOr(psi_i_part2_components, pub_aig_manager);
				psi_i_part2 = createNot(psi_i_part2, pub_aig_manager);
			}
			assert(psi_i_part2 != NULL);
			
			// initialize Z_variable_counter[var_to_elim_index] to 0
			Z_variable_counter.insert(make_pair(var_to_elim_index, 0));

			int z_i_count = Z_variable_counter[var_to_elim_index]; // 0 here
			
			string z_i_string = obtainZVariableString(var_to_elim_index, z_i_count); // obtain the string Z_{var_to_elim_index}_0

			// check if object for z_i_string is already existing; if yes return it; otherwise create, 
			// update temporary_variable_for_incremental_solving_to_object_map and return
			Aig_Obj_t* z_i_object = obtainObjectOfTemporaryVariableForIncrementalSolving(z_i_string);
			assert(z_i_object != NULL);

			psi_i_part2 = createAnd(psi_i_part2, z_i_object, pub_aig_manager);	
			assert(psi_i_part2 != NULL);		

		
			// obtaining \psi_i_part1
			Aig_Obj_t* psi_i_part1;

			map<int, Aig_Obj_t*>::iterator initial_cannot_be_zero_objects_it = initial_cannot_be_zero_objects.find(var_to_elim_index);
			assert(initial_cannot_be_zero_objects_it != initial_cannot_be_zero_objects.end());

			psi_i_part1 = initial_cannot_be_zero_objects_it->second;
			assert(psi_i_part1 != NULL);
			

			// obtaining \psi_i
			Aig_Obj_t* psi_i;
			psi_i = createOr(createAnd(use_cbzero_in_unified_cegar_aig, psi_i_part1, pub_aig_manager), psi_i_part2, pub_aig_manager);
			assert(psi_i != NULL);			

			Aig_Obj_t* S_equivalence_i = createEquivalence(var_to_elim_obj, psi_i, pub_aig_manager);

			if(true) //var_to_elim_index > 1 is sufficeint; but may need code change
			{
				S_equivalence_objects.insert(S_equivalence_i);	
			}
		}

		if(apply_tsietin_encoding_on_benchmarks)
		{
			for(int tsietin_location_index = 1; tsietin_location_index <= number_of_tsietin_variables; tsietin_location_index++)
			{
				// obtaining dag for x_i
				string var_to_elim = searchVarIndexToVarNameMap(var_index_to_var_name_map, tsietin_location_index);

				map<string, Aig_Obj_t*>::iterator Ci_to_eliminate_name_to_Ci_to_eliminate_object_map_it = Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.find(var_to_elim);
				assert(Ci_to_eliminate_name_to_Ci_to_eliminate_object_map_it != Ci_to_eliminate_name_to_Ci_to_eliminate_object_map.end());			
				Aig_Obj_t* var_to_elim_obj = Ci_to_eliminate_name_to_Ci_to_eliminate_object_map_it->second;

				// obtaining \psi_i
				Aig_Obj_t* psi_i;
				map<string, Aig_Obj_t*>::iterator tsietin_variable_to_exact_skolem_function_map_it = tsietin_variable_to_exact_skolem_function_map.find(var_to_elim);
				assert(tsietin_variable_to_exact_skolem_function_map_it != tsietin_variable_to_exact_skolem_function_map.end());

				psi_i = tsietin_variable_to_exact_skolem_function_map_it->second;
				assert(psi_i != NULL);			

				Aig_Obj_t* S_equivalence_i = createEquivalence(var_to_elim_obj, psi_i, pub_aig_manager);

				S_equivalence_objects.insert(S_equivalence_i);	

				#ifdef DEBUG_SKOLEM
				cout << endl << "Exact Skolem function used for x[" << tsietin_location_index << "] = " << var_to_elim << endl;
				#endif			

			}
		}
		
		if(S_equivalence_objects.empty())
		{
			S_equivalence_part = createTrue(pub_aig_manager);
		}
		else
		{
			S_equivalence_part = createAnd(S_equivalence_objects, pub_aig_manager);
		}
		assert(S_equivalence_part != NULL);

		// connect to some output to avoid unwanted deletion
		Aig_Obj_t* S_equivalence_part_CO = Aig_ObjCreateCo(pub_aig_manager, S_equivalence_part ); 
		assert(S_equivalence_part_CO != NULL);
		intermediate_cos_created.insert(S_equivalence_part_CO);


		// Let's create dag for
		// (B_1 = dag for bad_1) \wedge ... \wedge (B_{i} = dag for bad_{i})
		// We need to exclude Tsietin variables if apply_tsietin_encoding_on_benchmarks is true
		Aig_Obj_t* B_equivalence_part;
		set<Aig_Obj_t*> B_equivalence_objects;
		Aig_Obj_t* B_part;
		set<Aig_Obj_t*> B_objects;

		for(int bad_location_index = 1; bad_location_index <= number_of_vars_to_elim; bad_location_index++)
		{

			if(apply_tsietin_encoding_on_benchmarks)
			{
				if(bad_location_index <= number_of_tsietin_variables)
				{
					#ifdef DEBUG_SKOLEM
					cout << endl << bad_location_index << " <= " << number_of_tsietin_variables <<", hence exact Skolem fuctions to be used\n";
					#endif
					continue; // no need to add bads for these locations; Skolem functions already exact
				}
			}

			Aig_Obj_t* bad_set_obj;
			bad_set_obj = searchOneDimensionalMatrix(BadSets, number_of_vars_to_elim, bad_location_index);
			assert(bad_set_obj != NULL); 

			// Obtaining dag for bad_set_obj
			map<int, Aig_Obj_t*>::iterator B_i_index_to_B_i_object_map_iterator = B_i_index_to_B_i_object_map.find(bad_location_index);
			assert(B_i_index_to_B_i_object_map_iterator != B_i_index_to_B_i_object_map.end());
			Aig_Obj_t* B_obj = B_i_index_to_B_i_object_map_iterator->second;
			assert(B_obj != NULL); 

			B_objects.insert(B_obj);

			Aig_Obj_t* B_equivalence_i = createEquivalence(bad_set_obj, B_obj, pub_aig_manager);
			B_equivalence_objects.insert(B_equivalence_i);
			
		}

		assert(!B_equivalence_objects.empty());
		B_equivalence_part = createAnd(B_equivalence_objects, pub_aig_manager);
		assert(B_equivalence_part != NULL);
		// connect to some output to avoid unwanted deletion
		Aig_Obj_t* B_equivalence_part_CO = Aig_ObjCreateCo(pub_aig_manager, B_equivalence_part ); 
		assert(B_equivalence_part_CO != NULL);
		intermediate_cos_created.insert(B_equivalence_part_CO);

		Aig_Obj_t* negated_conjunction_of_factors = createNot(conjunction_of_factors, pub_aig_manager);
		assert(negated_conjunction_of_factors != NULL);

		// create aig for ite(use_bads_in_unified_cegar_aig, B_equivalence_part wedge disjunction_of_bad_symbols, negated_conjunction_of_factors)
		Aig_Obj_t* prevention_part;
		prevention_part = createIte(use_bads_in_unified_cegar_aig, createAnd(B_equivalence_part, disjunction_of_bad_symbols, pub_aig_manager), negated_conjunction_of_factors, pub_aig_manager);
		// connect to some output to avoid unwanted deletion
		Aig_Obj_t* prevention_part_CO = Aig_ObjCreateCo(pub_aig_manager, prevention_part ); 
		assert(prevention_part_CO != NULL);
		intermediate_cos_created.insert(prevention_part_CO);


		#ifdef DEBUG_SKOLEM
		string Cb_part_file_name = benchmark_name_without_extension;
		Cb_part_file_name += "_Cb_part";

		string S_equivalence_part_file_name = benchmark_name_without_extension;
		S_equivalence_part_file_name += "_S_equivalence_part";

		string B_equivalence_part_file_name = benchmark_name_without_extension;
		B_equivalence_part_file_name += "_B_equivalence_part";

		string prevention_part_file_name = benchmark_name_without_extension;
		prevention_part_file_name += "_prevention_part";

		cout << "\nCb_part computed\n";
		cout << "\nS_equivalence_part computed\n";
		cout << "\nB_equivalence_part computed\n";
		cout << "\nprevention_part computed\n";
		
		writeFormulaToFile(pub_aig_manager, Cb_part, Cb_part_file_name, ".v", cegar_iteration_number, 0);
		writeFormulaToFile(pub_aig_manager, S_equivalence_part, S_equivalence_part_file_name, ".v", cegar_iteration_number, 0);
		writeFormulaToFile(pub_aig_manager, B_equivalence_part, B_equivalence_part_file_name, ".v", cegar_iteration_number, 0);
		writeFormulaToFile(pub_aig_manager, prevention_part, prevention_part_file_name, ".v", cegar_iteration_number, 0);
		#endif	


		set<Aig_Obj_t*> epsilon_zero_objects;
		epsilon_zero_objects.insert(Cb_part);
		epsilon_zero_objects.insert(S_equivalence_part);
		epsilon_zero_objects.insert(prevention_part);
		epsilon_zero_objects.insert(renamed_conjunction_of_factors);
				

		epsilon_zero = createAnd(epsilon_zero_objects, pub_aig_manager);
		assert(epsilon_zero != NULL);
		// connect to some output to avoid unwanted deletion
		Aig_Obj_t* epsilon_zero_CO = Aig_ObjCreateCo(pub_aig_manager, epsilon_zero ); 
		assert(epsilon_zero_CO != NULL);
		intermediate_cos_created.insert(epsilon_zero_CO);

		if(Aig_IsComplement(epsilon_zero) && Aig_Regular(epsilon_zero) == createTrue(pub_aig_manager))
		// epsilon_zero is false
		{
			#ifdef DEBUG_CEGAR
			cout << "\nAIG for epsilon_zero is false; no need to call the sat-solver\n";
			#endif

			#ifdef RECORD_KEEP
			string record_file;
			record_file = logfile_prefix;
			record_file += "skolem_function_generation_details.txt";
			FILE* record_fp = fopen(record_file.c_str(), "a+");
			assert(record_fp != NULL);
	
			number_of_exactness_checking_in_cegar++;

			if(!mask_printing_cegar_details)
			{
				fprintf(record_fp, "\t0(0,0)(1)");
			}

			fclose(record_fp);
			#endif

			return true;
		}

		#ifdef DEBUG_CEGAR
		cout << endl << "Adding clauses of epsilon_zero to SAT-Solver\n";
		#endif

		if(use_generic_sat_solver_interface)
		{
			if(sat_solver_used_in_cegar == "abc")
			{
				getIncrementAsCNF_and_AddToSolver(pub_aig_manager, epsilon_zero, pSat_for_exactness_check, IncrementalLabelTableForExactnessCheck, IncrementalLabelCountForExactnessCheck, Ci_name_to_Ci_label_mapForExactnessCheck, Ci_label_to_Ci_name_mapForExactnessCheck);

			}
			else // for other SAT solvers
			{
				assert(false);
			}	
		}
		else
		{
			addIncrementToExactnessCheck(pub_aig_manager, epsilon_zero, pSat_for_exactness_check, IncrementalLabelTableForExactnessCheck, IncrementalLabelCountForExactnessCheck, Ci_name_to_Ci_label_mapForExactnessCheck, Ci_label_to_Ci_name_mapForExactnessCheck);

		}

		// Perform simulation/SAT call

		int number_of_simulations_done = 0;
		
		while(number_of_simulations_done <= number_of_simulations_before_sat_call_in_functional_forms)
		{
			
			if(number_of_simulations_done < number_of_simulations_before_sat_call_in_functional_forms) 				// Do simulation		
			{

				// Perform simulation to check satisfiability of F(X, Y)

				#ifdef DETAILED_RECORD_KEEP
				unsigned long long int simulation_ms;
				struct timeval simulation_start_ms, simulation_finish_ms;
				gettimeofday (&simulation_start_ms, NULL); 	
				#endif

				bool result_of_exactnesscheck = checkSatisfiabilityOfFunctionInFunctionalForms(Model_of_ExactnessCheck);

				#ifdef DETAILED_RECORD_KEEP
				gettimeofday (&simulation_finish_ms, NULL);
				simulation_ms = simulation_finish_ms.tv_sec * 1000 + simulation_finish_ms.tv_usec / 1000;
				simulation_ms -= simulation_start_ms.tv_sec * 1000 + simulation_start_ms.tv_usec / 1000;
				total_time_in_function_evaluation_to_replace_sat_in_cegar_in_functional_forms = total_time_in_function_evaluation_to_replace_sat_in_cegar_in_functional_forms + simulation_ms;
				#endif
			
					
				#ifdef RECORD_KEEP
				string record_file;
				record_file = logfile_prefix;
				record_file += "skolem_function_generation_details.txt";
				FILE* record_fp = fopen(record_file.c_str(), "a+");
				assert(record_fp != NULL);

				if(!mask_printing_cegar_details)
				{
					if(number_of_simulations_done == 0)
					{
						fprintf(record_fp, "\t%llu(-,-)(-)", simulation_ms);
					}
					else
					{
						fprintf(record_fp, "\n\n%d\t%d\t%llu(-,-)(-)", cegar_iteration_number, correction_index, simulation_ms);
					}
				}

				fclose(record_fp);
				#endif


				#ifdef DEBUG_SKOLEM
				displayModelFromSATSolver(Model_of_ExactnessCheck);
				cout << endl << "result_of_exactnesscheck = " << result_of_exactnesscheck << endl;
				#endif

				if(!result_of_exactnesscheck)
				// ExactnessCheck unsat i.e. skolem function at correction_index is exact
				{
					// we will need to do checks again
					number_of_simulations_done++;
				}
				else // skolem function at correction_index is inexact
				{
					return false;
				}
			}
			else // Do SAT
			{
				vector<Aig_Obj_t*> positive_assumptions_in_exactness_check;
				vector<Aig_Obj_t*> negative_assumptions_in_exactness_check;

			obtainAssumptionsInExactnessCheck_using_Generic_Skolem_Functions_With_Unified_Code_And_Incremental_Solving  (correction_index, positive_assumptions_in_exactness_check, negative_assumptions_in_exactness_check);
				//assert(positive_assumptions_in_exactness_check.size() != 0);
				//assert(negative_assumptions_in_exactness_check.size() != 0);

				epsilon_zero = createTrue(pub_aig_manager); //clauses are already added
				
				#ifdef DETAILED_RECORD_KEEP
				unsigned long long int solver_ms;
				struct timeval solver_start_ms, solver_finish_ms;
				gettimeofday (&solver_start_ms, NULL); 	
				#endif

				// Give to SAT-Solver and get unsat / sat with model
				unsigned long long int cnf_time;
				int formula_size;
				unsigned long long int simplification_time;
				bool result_of_exactnesscheck;
			
				if(use_generic_sat_solver_interface)
				{
					if(sat_solver_used_in_cegar == "abc")
					{
						result_of_exactnesscheck = getIncrementAsCNF_AddToSolver_and_CallSolver_With_Assumptions(pub_aig_manager, epsilon_zero, Model_of_ExactnessCheck, cnf_time, formula_size, simplification_time, positive_assumptions_in_exactness_check, negative_assumptions_in_exactness_check, pSat_for_exactness_check, IncrementalLabelTableForExactnessCheck, IncrementalLabelCountForExactnessCheck, Ci_name_to_Ci_label_mapForExactnessCheck, Ci_label_to_Ci_name_mapForExactnessCheck);

					}
					else // for other SAT solvers
					{
						assert(false);
					}	
				}
				else
				{

				 	result_of_exactnesscheck = isExactnessCheckSatisfiable(pub_aig_manager, epsilon_zero, Model_of_ExactnessCheck, cnf_time, formula_size, simplification_time, positive_assumptions_in_exactness_check, negative_assumptions_in_exactness_check, pSat_for_exactness_check, IncrementalLabelTableForExactnessCheck, IncrementalLabelCountForExactnessCheck, Ci_name_to_Ci_label_mapForExactnessCheck, Ci_label_to_Ci_name_mapForExactnessCheck);
		
				}
	
				#ifdef DETAILED_RECORD_KEEP
				gettimeofday (&solver_finish_ms, NULL);
				solver_ms = solver_finish_ms.tv_sec * 1000 + solver_finish_ms.tv_usec / 1000;
				solver_ms -= solver_start_ms.tv_sec * 1000 + solver_start_ms.tv_usec / 1000;

				if(!mask_printing_cegar_details)
				{
					cout << "\nsolver finished in " << solver_ms << " milliseconds\n";
				}

				total_time_in_smt_solver = total_time_in_smt_solver + solver_ms;
				total_time_in_exactness_checking_in_cegar = total_time_in_exactness_checking_in_cegar + solver_ms;
				number_of_exactness_checking_in_cegar++;
				#endif

				#ifdef RECORD_KEEP
				string record_file;
				record_file = logfile_prefix;
				record_file += "skolem_function_generation_details.txt";
				FILE* record_fp = fopen(record_file.c_str(), "a+");
				assert(record_fp != NULL);

				if(!mask_printing_cegar_details)
				{
					if(number_of_simulations_done == 0)
					{
						fprintf(record_fp, "\t%llu(%llu,%llu)(%d)", solver_ms, cnf_time, simplification_time, formula_size);
					}
					else
					{
						fprintf(record_fp, "\n\n%d\t%d\t%llu(%llu,%llu)(%d)", cegar_iteration_number, correction_index, solver_ms, cnf_time, simplification_time, formula_size);
					}
				}

				fclose(record_fp);
				#endif


				#ifdef DEBUG_SKOLEM
				displayModelFromSATSolver(Model_of_ExactnessCheck);
				cout << endl << "result_of_exactnesscheck = " << result_of_exactnesscheck << endl;
				#endif

				removeTemporaryVariablesFromModel(Model_of_ExactnessCheck);

				#ifdef DEBUG_SKOLEM
				cout << "\nModel after removing temporary variables\n";
				displayModelFromSATSolver(Model_of_ExactnessCheck);
				cout << endl << "result_of_exactnesscheck = " << result_of_exactnesscheck << endl;
				#endif
	
				if(!result_of_exactnesscheck)
				// ExactnessCheck unsat i.e. skolem function at correction_index is exact
				{
					return true;
				}
				else // skolem function at correction_index is inexact
				{
					return false;
				}
			}// Do SAT ends here
		}//while ends here
		
	} // if(cegar_iteration_number == 0) ends here
	else // if(cegar_iteration_number > 0)
	{
		assert(cegar_iteration_for_correction_index > 0); 

		#ifdef DEBUG_CEGAR
		cout << "\nCase with cegar_iteration_for_correction_index > 0 \n";

		if(Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX.empty() && Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX.empty())
		{
			cout << "\nRefinement hints are empty\n";
		}
		else
		{
			cout << "\nRefinement hints are NOT empty\n";
		}
		#endif

		#ifdef DEBUG_CEGAR
		show_present_refinement_hint(Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX, Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX);
		#endif

		Aig_Obj_t* delta_epsilon_i;

		// Create the dag for delta_epsilon_i:
		// for each o_j added in Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX
		// (o_j = dag_j) \wedge 
		// (Z_i_k = Z_i_{k+1} \wedge o_j) \wedge 
		
		Aig_Obj_t* Cb_part;
		set<Aig_Obj_t*> Cb_objects;

		Aig_Obj_t* Z_part;
		set<Aig_Obj_t*> Z_objects;

		for(map<int, Aig_Obj_t*>::iterator hint_it = Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX.begin(); hint_it != Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX.end(); hint_it++)
		{
			int destination = hint_it->first;
			Aig_Obj_t* new_cannot_be_one_object_at_destination = hint_it->second;

			map<Aig_Obj_t*, Aig_Obj_t*>::iterator cannot_be_object_to_cannot_be_dag_map_it = cannot_be_object_to_cannot_be_dag_map.find(new_cannot_be_one_object_at_destination);
			assert(cannot_be_object_to_cannot_be_dag_map_it != cannot_be_object_to_cannot_be_dag_map.end());
			Aig_Obj_t* new_cannot_be_one_dag_at_destination = cannot_be_object_to_cannot_be_dag_map_it->second;

			Aig_Obj_t* Cb_one_equivalence = createEquivalence(new_cannot_be_one_object_at_destination, new_cannot_be_one_dag_at_destination, pub_aig_manager);
			assert(Cb_one_equivalence != NULL);

			Cb_objects.insert(Cb_one_equivalence);

		
			int present_z_j_k_count = Z_variable_counter[destination];
			int next_z_j_k_count = present_z_j_k_count + 1;
			Z_variable_counter[destination] = next_z_j_k_count;

			string present_z_j_k_string = obtainZVariableString(destination, present_z_j_k_count); // obtain the string Z_{destination}_{present_z_j_k_count}
			Aig_Obj_t* present_z_j_k_object = obtainExistingObjectOfTemporaryVariableForIncrementalSolving(present_z_j_k_string);
			assert(present_z_j_k_object != NULL);
				
			string next_z_j_k_string = obtainZVariableString(destination, next_z_j_k_count); // obtain the string Z_{destination}_{next_z_j_k_count}
			Aig_Obj_t* next_z_j_k_object = obtainObjectOfTemporaryVariableForIncrementalSolving(next_z_j_k_string);
			assert(next_z_j_k_object != NULL);

			Aig_Obj_t* R_i_j_increment = createEquivalence(present_z_j_k_object, createAnd(createNot(new_cannot_be_one_object_at_destination, pub_aig_manager), next_z_j_k_object, pub_aig_manager), pub_aig_manager);
			assert(R_i_j_increment != NULL);

			Z_objects.insert(R_i_j_increment);
		}
		
		
		for(map<int, Aig_Obj_t*>::iterator hint_it = Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX.begin(); hint_it != Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX.end(); hint_it++)
		{
			int destination = hint_it->first;
			Aig_Obj_t* new_cannot_be_zero_object_at_destination = hint_it->second;

			map<Aig_Obj_t*, Aig_Obj_t*>::iterator cannot_be_object_to_cannot_be_dag_map_it = cannot_be_object_to_cannot_be_dag_map.find(new_cannot_be_zero_object_at_destination);
			assert(cannot_be_object_to_cannot_be_dag_map_it != cannot_be_object_to_cannot_be_dag_map.end());
			Aig_Obj_t* new_cannot_be_zero_dag_at_destination = cannot_be_object_to_cannot_be_dag_map_it->second;

			Aig_Obj_t* Cb_zero_equivalence = createEquivalence(new_cannot_be_zero_object_at_destination, new_cannot_be_zero_dag_at_destination, pub_aig_manager);
			assert(Cb_zero_equivalence != NULL);

			Cb_objects.insert(Cb_zero_equivalence);
		}
		
		if(Cb_objects.empty() && Z_objects.empty())
		{
			delta_epsilon_i = createTrue(pub_aig_manager);
		}
		else
		{		
			assert(!Cb_objects.empty());
			Cb_part = createAnd(Cb_objects, pub_aig_manager);
			assert(Cb_part != NULL);
			// connect to some output to avoid unwanted deletion
			Aig_Obj_t* Cb_part_CO = Aig_ObjCreateCo(pub_aig_manager, Cb_part ); 
			assert(Cb_part_CO != NULL);
			intermediate_cos_created.insert(Cb_part_CO);

			assert(!Z_objects.empty());
			Z_part = createAnd(Z_objects, pub_aig_manager);
			assert(Z_part != NULL);
			// connect to some output to avoid unwanted deletion
			Aig_Obj_t* Z_part_CO = Aig_ObjCreateCo(pub_aig_manager, Z_part ); 
			assert(Z_part_CO != NULL);
			intermediate_cos_created.insert(Z_part_CO);


			#ifdef DEBUG_SKOLEM
			string Cb_part_file_name = benchmark_name_without_extension;
			Cb_part_file_name += "_Cb_part";

			string Z_part_file_name = benchmark_name_without_extension;
			Z_part_file_name += "_Z_part";

			cout << "\nCb_part computed\n";
			cout << "\nZ_part computed\n";

			writeFormulaToFile(pub_aig_manager, Cb_part, Cb_part_file_name, ".v", cegar_iteration_number, 0);
			writeFormulaToFile(pub_aig_manager, Z_part, Z_part_file_name, ".v", cegar_iteration_number, 0);
			#endif

			delta_epsilon_i = createAnd(Cb_part, Z_part, pub_aig_manager);
		}

		assert(delta_epsilon_i != NULL);
		// connect to some output to avoid unwanted deletion
		Aig_Obj_t* delta_epsilon_i_CO = Aig_ObjCreateCo(pub_aig_manager, delta_epsilon_i ); 
		assert(delta_epsilon_i_CO != NULL);
		intermediate_cos_created.insert(delta_epsilon_i_CO);


		#ifdef DEBUG_CEGAR
		string delta_epsilon_i_file_name = benchmark_name_without_extension;
		delta_epsilon_i_file_name += "_delta_epsilon_i";
		cout << "\ndelta_epsilon_i computed\n";
		writeFormulaToFile(pub_aig_manager, delta_epsilon_i, delta_epsilon_i_file_name, ".v", cegar_iteration_number, 0);
		#endif

		#ifdef DEBUG_CEGAR
		cout << endl << "Adding clauses of delta_epsilon_i to SAT-Solver\n";
		#endif

		if(use_generic_sat_solver_interface)
		{
			if(sat_solver_used_in_cegar == "abc")
			{
				getIncrementAsCNF_and_AddToSolver(pub_aig_manager, delta_epsilon_i, pSat_for_exactness_check, IncrementalLabelTableForExactnessCheck, IncrementalLabelCountForExactnessCheck, Ci_name_to_Ci_label_mapForExactnessCheck, Ci_label_to_Ci_name_mapForExactnessCheck);

			}
			else // for other SAT solvers
			{
				assert(false);
			}	
		}
		else
		{
			addIncrementToExactnessCheck(pub_aig_manager, delta_epsilon_i, pSat_for_exactness_check, IncrementalLabelTableForExactnessCheck, IncrementalLabelCountForExactnessCheck, Ci_name_to_Ci_label_mapForExactnessCheck, Ci_label_to_Ci_name_mapForExactnessCheck);

		}

		int number_of_simulations_done = 0;
		
		while(number_of_simulations_done <= number_of_simulations_before_sat_call_in_functional_forms)
		{
			
			if(number_of_simulations_done < number_of_simulations_before_sat_call_in_functional_forms) 				// do simulation		
			{

				// Perform simulation to check satisfiability of F(X, Y)

				#ifdef DETAILED_RECORD_KEEP
				unsigned long long int simulation_ms;
				struct timeval simulation_start_ms, simulation_finish_ms;
				gettimeofday (&simulation_start_ms, NULL); 	
				#endif

				bool result_of_exactnesscheck = checkSatisfiabilityOfFunctionInFunctionalForms(Model_of_ExactnessCheck);

				#ifdef DETAILED_RECORD_KEEP
				gettimeofday (&simulation_finish_ms, NULL);
				simulation_ms = simulation_finish_ms.tv_sec * 1000 + simulation_finish_ms.tv_usec / 1000;
				simulation_ms -= simulation_start_ms.tv_sec * 1000 + simulation_start_ms.tv_usec / 1000;
				total_time_in_function_evaluation_to_replace_sat_in_cegar_in_functional_forms = total_time_in_function_evaluation_to_replace_sat_in_cegar_in_functional_forms + simulation_ms;
				#endif
			
					
				#ifdef RECORD_KEEP
				string record_file;
				record_file = logfile_prefix;
				record_file += "skolem_function_generation_details.txt";
				FILE* record_fp = fopen(record_file.c_str(), "a+");
				assert(record_fp != NULL);

				if(!mask_printing_cegar_details)
				{
					if(number_of_simulations_done == 0)
					{
						fprintf(record_fp, "\t%llu(-,-)(-)", simulation_ms);
					}
					else
					{
						fprintf(record_fp, "\n\n%d\t%d\t%llu(-,-)(-)", cegar_iteration_number, correction_index, simulation_ms);
					}
				}

				fclose(record_fp);
				#endif


				#ifdef DEBUG_SKOLEM
				displayModelFromSATSolver(Model_of_ExactnessCheck);
				cout << endl << "result_of_exactnesscheck = " << result_of_exactnesscheck << endl;
				#endif

				if(!result_of_exactnesscheck)
				// ExactnessCheck unsat i.e. skolem function at correction_index is exact
				{
					// we will need to do checks again
					number_of_simulations_done++;
				}
				else // skolem function at correction_index is inexact
				{
					return false;
				}
			}
			else // Do SAT
			{
				vector<Aig_Obj_t*> positive_assumptions_in_exactness_check;
				vector<Aig_Obj_t*> negative_assumptions_in_exactness_check;

			obtainAssumptionsInExactnessCheck_using_Generic_Skolem_Functions_With_Unified_Code_And_Incremental_Solving  (correction_index, positive_assumptions_in_exactness_check, negative_assumptions_in_exactness_check);
				//assert(positive_assumptions_in_exactness_check.size() != 0);
				//assert(negative_assumptions_in_exactness_check.size() != 0);

				delta_epsilon_i = createTrue(pub_aig_manager); //clauses are already added
				
				#ifdef DETAILED_RECORD_KEEP
				unsigned long long int solver_ms;
				struct timeval solver_start_ms, solver_finish_ms;
				gettimeofday (&solver_start_ms, NULL); 	
				#endif

				// Give to SAT-Solver and get unsat / sat with model
				unsigned long long int cnf_time;
				int formula_size;
				unsigned long long int simplification_time;
				bool result_of_exactnesscheck;

				if(use_generic_sat_solver_interface)
				{
					if(sat_solver_used_in_cegar == "abc")
					{
						result_of_exactnesscheck = getIncrementAsCNF_AddToSolver_and_CallSolver_With_Assumptions(pub_aig_manager, delta_epsilon_i, Model_of_ExactnessCheck, cnf_time, formula_size, simplification_time, positive_assumptions_in_exactness_check, negative_assumptions_in_exactness_check, pSat_for_exactness_check, IncrementalLabelTableForExactnessCheck, IncrementalLabelCountForExactnessCheck, Ci_name_to_Ci_label_mapForExactnessCheck, Ci_label_to_Ci_name_mapForExactnessCheck);

					}
					else // for other SAT solvers
					{
						assert(false);
					}	
				}
				else
				{

					result_of_exactnesscheck = isExactnessCheckSatisfiable(pub_aig_manager, delta_epsilon_i, Model_of_ExactnessCheck, cnf_time, formula_size, simplification_time, positive_assumptions_in_exactness_check, negative_assumptions_in_exactness_check, pSat_for_exactness_check, IncrementalLabelTableForExactnessCheck, IncrementalLabelCountForExactnessCheck, Ci_name_to_Ci_label_mapForExactnessCheck, Ci_label_to_Ci_name_mapForExactnessCheck);

				}
	
				#ifdef DETAILED_RECORD_KEEP
				gettimeofday (&solver_finish_ms, NULL);
				solver_ms = solver_finish_ms.tv_sec * 1000 + solver_finish_ms.tv_usec / 1000;
				solver_ms -= solver_start_ms.tv_sec * 1000 + solver_start_ms.tv_usec / 1000;

				if(!mask_printing_cegar_details)
				{
					cout << "\nsolver finished in " << solver_ms << " milliseconds\n";
				}

				total_time_in_smt_solver = total_time_in_smt_solver + solver_ms;
				total_time_in_exactness_checking_in_cegar = total_time_in_exactness_checking_in_cegar + solver_ms;
				number_of_exactness_checking_in_cegar++;
				#endif

				#ifdef RECORD_KEEP
				string record_file;
				record_file = logfile_prefix;
				record_file += "skolem_function_generation_details.txt";
				FILE* record_fp = fopen(record_file.c_str(), "a+");
				assert(record_fp != NULL);

				if(!mask_printing_cegar_details)
				{
					if(number_of_simulations_done == 0)
					{
						fprintf(record_fp, "\t%llu(%llu,%llu)(%d)", solver_ms, cnf_time, simplification_time, formula_size);
					}
					else
					{
						fprintf(record_fp, "\n\n%d\t%d\t%llu(%llu,%llu)(%d)", cegar_iteration_number, correction_index, solver_ms, cnf_time, simplification_time, formula_size);
					}
				}

				fclose(record_fp);
				#endif


				#ifdef DEBUG_SKOLEM
				displayModelFromSATSolver(Model_of_ExactnessCheck);
				cout << endl << "result_of_exactnesscheck = " << result_of_exactnesscheck << endl;
				#endif

				removeTemporaryVariablesFromModel(Model_of_ExactnessCheck);

				#ifdef DEBUG_SKOLEM
				cout << "\nModel after removing temporary variables\n";
				displayModelFromSATSolver(Model_of_ExactnessCheck);
				cout << endl << "result_of_exactnesscheck = " << result_of_exactnesscheck << endl;
				#endif
	
				if(!result_of_exactnesscheck)
				// ExactnessCheck unsat i.e. skolem function at correction_index is exact
				{
					return true;
				}
				else // skolem function at correction_index is inexact
				{
					return false;
				}
			}// Do SAT ends here
		}//while ends here
	} // if(cegar_iteration_for_correction_index > 0) ends here	
}


bool AIGBasedSkolem::checkSatisfiabilityOfFunctionInFunctionalForms(map<string, int> &Model_of_ExactnessCheck)
{
	assert(benchmark_type == "factorization");

	int number_of_x_y_variables = Global_VariablesToEliminate_Set.size();// no: of x variables + y variables		
	assert(number_of_x_y_variables % 2 == 0); // no: of x variables + y variables is even 
	int bits = number_of_x_y_variables/2;

	int maxbits_supported = (sizeof(unsigned long long int)*8) - 1;
	assert(bits < maxbits_supported);

	#ifdef DEBUG_SKOLEM
	cout << "\nbits = " << bits << "\tmaxbits_supported = " << maxbits_supported << endl;
	#endif

	srand(time(NULL));

	unsigned long long int min_word = 2;
	unsigned long long int modulus = findPower(bits);
	unsigned long long int max_word = modulus-1;

	#ifdef DEBUG_SKOLEM
	cout << "\nmin_word = " << min_word << "\tmax_word = " << max_word << "\tmodulus = " << modulus << endl;
	#endif

	unsigned long long int x_new_word = ((unsigned long long int) ((rand0to1) * max_word)) + min_word;
	unsigned long long int y_new_word = ((unsigned long long int) ((rand0to1) * max_word)) + min_word;
	unsigned long long int z_word = (x_new_word*y_new_word) % modulus;

	#ifdef DEBUG_SKOLEM
	cout << "\nx_new_word = " << x_new_word << "\ty_new_word = " << y_new_word << "\tz_word = " << z_word << endl;
	#endif

	string x_new_word_binary = convertDecimalToBitvectorWithProperWidth(x_new_word, bits);
	string y_new_word_binary = convertDecimalToBitvectorWithProperWidth(y_new_word, bits);
	string z_word_binary = convertDecimalToBitvectorWithProperWidth(z_word, bits);

	#ifdef DEBUG_SKOLEM
	cout << "\nx_new_word_binary = " << x_new_word_binary << "\ty_new_word_binary = " << y_new_word_binary << "\tz_word_binary = " << z_word_binary << endl;
	#endif

	map<string, bool> variable_to_value_map;

	// Get values for bits of x_new, y_new, and z
	for(int i = 0; i < bits; i++)
	{
		string x_new_bit = "x[";
		string y_new_bit = "y[";
		string z_bit = "z[";
		
		char i_char[100];
		sprintf(i_char, "%d", i);
		string i_string(i_char);
	
		x_new_bit += i_string;
		y_new_bit += i_string;
		z_bit += i_string;				
		
		x_new_bit += "]_new";
		y_new_bit += "]_new";
		z_bit += "]";

		int x_new_value, y_new_value, z_value;
		bool bool_z_value;

		if(x_new_word_binary[i] == '0')
		{
			x_new_value = 0;
		}
		else if(x_new_word_binary[i] == '1')
		{
			x_new_value = 1;
		}
		else
		{
			assert(false);
		}

		Model_of_ExactnessCheck.insert(make_pair(x_new_bit, x_new_value));

		if(y_new_word_binary[i] == '0')
		{
			y_new_value = 0;
		}
		else if(y_new_word_binary[i] == '1')
		{
			y_new_value = 1;
		}
		else
		{
			assert(false);
		}

		Model_of_ExactnessCheck.insert(make_pair(y_new_bit, y_new_value));


		if(z_word_binary[i] == '0')
		{
			z_value = 0;
			bool_z_value = false;
		}
		else if(z_word_binary[i] == '1')
		{
			z_value = 1;
			bool_z_value = true;
		}
		else
		{
			assert(false);
		}

		Model_of_ExactnessCheck.insert(make_pair(z_bit, z_value));
		variable_to_value_map.insert(make_pair(z_bit, bool_z_value));

		#ifdef DEBUG_SKOLEM
		cout << endl << x_new_bit << " = " << x_new_value;
		cout << endl << y_new_bit << " = " << y_new_value;
		cout << endl << z_bit << " = " << z_value;
		#endif
	}

	
	// Get values for bits of x and y
	
	map<int, bool> x_word_map;
	map<int, bool> y_word_map;

	for(int var_to_elim_index = number_of_vars_to_elim; var_to_elim_index >= 1; var_to_elim_index--)
	{
		// Obtain XValues[var_to_elim_index]
		string var_to_elim = searchVarIndexToVarNameMap(var_index_to_var_name_map, var_to_elim_index);

		string var_name;
		int var_index;
		var_name = getVariablenameAndVariableindexFromArrayReference(var_to_elim, var_index);
		assert(var_name == "x" || var_name == "y");

		#ifdef DEBUG_SKOLEM
		cout << "\nvar_to_elim = " << var_to_elim << "\tvar_name = " << var_name << "\tvar_index = " << var_index << endl;
		#endif
		
		// obtaining \psi_i
		Aig_Obj_t* skolem_function;
		bool use_the_existing_skolem_function = false;
		// Existing Skolem function is r0[i] \vee ~r1[i]
		// We need to compute Skolem function based on value of  
		// use_cbzero_in_unified_cegar_aig
		if(use_the_existing_skolem_function)
		{
			skolem_function = searchOneDimensionalMatrix(SkolemFunctions, number_of_vars_to_elim, var_to_elim_index);
		}
		else
		{
			skolem_function = createSkolemFunction_In_Mu_Based_Scheme_With_Optimizations_With_Optional_ICb0(var_to_elim_index);
		}
		assert(skolem_function != NULL); 

		#ifdef DEBUG_SKOLEM
		string skolem_function_file_name = benchmark_name_without_extension;
		skolem_function_file_name += "_skolem_function_used_in_function_simulation";
		writeFormulaToFile(pub_aig_manager, skolem_function, skolem_function_file_name, ".v", var_to_elim_index, cegar_iteration_number);
		#endif


		#ifdef DEBUG_SKOLEM
		unsigned long long int evaluation_ms;
		struct timeval evaluation_start_ms, evaluation_finish_ms;
		gettimeofday (&evaluation_start_ms, NULL); 	
		#endif

		bool bool_value;
		if(true)
		{
			bool_value = evaluateFormulaOfCi_Efficient(skolem_function, variable_to_value_map);//This is more efficient
		}
		else
		{
			bool_value = evaluateFormulaOfCi(skolem_function, variable_to_value_map);//less efficient version
		}

		#ifdef DEBUG_SKOLEM
		gettimeofday (&evaluation_finish_ms, NULL);
		evaluation_ms = evaluation_finish_ms.tv_sec * 1000 + evaluation_finish_ms.tv_usec / 1000;
		evaluation_ms -= evaluation_start_ms.tv_sec * 1000 + evaluation_start_ms.tv_usec / 1000;
		cout << "\nEvaluation of Skolem function of x_" << var_to_elim_index << " of size " << computeSize(skolem_function, pub_aig_manager) << " happened in " << evaluation_ms << " milliseconds\n";
		#endif
				

		#ifdef DEBUG_SKOLEM
		cout << "\nbool_value = " << bool_value << endl;
		#endif

		variable_to_value_map.insert(make_pair(var_to_elim, bool_value));	

		if(bool_value)
		{
			Model_of_ExactnessCheck.insert(make_pair(var_to_elim, 1));	
		}
		else
		{
			Model_of_ExactnessCheck.insert(make_pair(var_to_elim, 0));
		}	


		if(var_name == "x")
		{
			x_word_map.insert(make_pair(var_index, bool_value));
		}
		else
		{
			y_word_map.insert(make_pair(var_index, bool_value));
		}
	}

	#ifdef DEBUG_SKOLEM
	cout << "\nx_word_map\n";
	for(map<int, bool>::reverse_iterator x_word_map_rit = x_word_map.rbegin(); x_word_map_rit != x_word_map.rend(); ++x_word_map_rit)
	{
		cout << x_word_map_rit->first << "\t" << x_word_map_rit->second << endl;	
	}

	cout << "\ny_word_map\n";
	for(map<int, bool>::reverse_iterator y_word_map_rit = y_word_map.rbegin(); y_word_map_rit != y_word_map.rend(); ++y_word_map_rit)
	{
		cout << y_word_map_rit->first << "\t" << y_word_map_rit->second << endl;	
	}
	#endif

	unsigned long long int x_word = binaryMapToNumber(x_word_map);
	unsigned long long int y_word = binaryMapToNumber(y_word_map);

	unsigned long long int z_word_obtained = (x_word*y_word) % modulus;

	#ifdef DEBUG_SKOLEM
	cout << "\nx_word = " << x_word << "\ty_word = " << y_word << "\tz_word_obtained = " << z_word_obtained << endl;
	#endif
	
	if(x_word == 1 || y_word == 1 || z_word_obtained != z_word)
	{
		#ifdef DEBUG_SKOLEM
		cout << "\nepsilon is satisfiable\n";
		#endif

		if(!mask_printing_cegar_details)
		{
			cout << "\nFunctional simulation says that epsilon is satisfiable\n";
		}

		// We need values of cannot be objects also

		for(map<string, Aig_Obj_t*>::iterator cannot_be_string_to_cannot_be_object_map_it = cannot_be_string_to_cannot_be_object_map.begin(); cannot_be_string_to_cannot_be_object_map_it != cannot_be_string_to_cannot_be_object_map.end(); cannot_be_string_to_cannot_be_object_map_it++)
		{
			string cannot_be_string = cannot_be_string_to_cannot_be_object_map_it->first;
			Aig_Obj_t* cannot_be_object = cannot_be_string_to_cannot_be_object_map_it->second;
			
			map<Aig_Obj_t*, Aig_Obj_t*>::iterator cannot_be_object_to_cannot_be_dag_map_it = cannot_be_object_to_cannot_be_dag_map.find(cannot_be_object);
			assert(cannot_be_object_to_cannot_be_dag_map_it != cannot_be_object_to_cannot_be_dag_map.end());
			Aig_Obj_t* cannot_be_dag = cannot_be_object_to_cannot_be_dag_map_it->second;

			bool bool_value;
			if(true)
			{
				bool_value = evaluateFormulaOfCi_Efficient(cannot_be_dag, variable_to_value_map);//This is more efficient
			}
			else
			{
				bool_value = evaluateFormulaOfCi(cannot_be_dag, variable_to_value_map);//less efficient version
			}

			if(bool_value)
			{
				Model_of_ExactnessCheck.insert(make_pair(cannot_be_string, 1));	
			}
			else
			{
				Model_of_ExactnessCheck.insert(make_pair(cannot_be_string, 0));
			}
		}

		return true; // epsilon is satisfiable
	}		
	else
	{
		#ifdef DEBUG_SKOLEM
		cout << "\nepsilon is unsatisfiable\n";
		#endif

		if(!mask_printing_cegar_details)
		{
			cout << "\nFunctional simulation says that epsilon is unsatisfiable\n";
		}


		return false; // epsilon is unsatisfiable
	}
}



void AIGBasedSkolem::cleanupAfterEachStepInArbitraryBooleanCombinations(string step_name)
{
	#ifdef DEBUG_SKOLEM
	cout << endl << intermediate_cos_created.size() << " CO's to be deleted by AIGBasedSkolem::cleanupAfterEachStepInArbitraryBooleanCombinations() after " << step_name << endl;
	#endif

	for(set<Aig_Obj_t*>::iterator co_it = intermediate_cos_created.begin(); co_it != intermediate_cos_created.end(); co_it++)
	{
		Aig_Obj_t* co_to_be_deleted = *co_it;
		
		Aig_ObjDeletePo(pub_aig_manager, co_to_be_deleted);
	} 
	
	intermediate_cos_created.clear();

	int number_of_nodes_deleted = Aig_ManCleanup(pub_aig_manager);

	#ifdef DEBUG_SKOLEM
	cout << endl << number_of_nodes_deleted << " aig nodes deleted by Aig_ManCleanup in AIGBasedSkolem::cleanupAfterEachStepInArbitraryBooleanCombinations()\n";
	#endif	
}


void AIGBasedSkolem::cleanupMemoryInProcessor_In_Cluster(int rank)
{
	//#ifdef DEBUG_PAR
	//cout << "\n\nInterface-Message: cleanupMemoryInProcessor_In_Cluster CALLED IN PROCESSOR WITH RANK " << rank << endl << endl;
	//#endif

	bool delete_intermediate_cos_created = true;

	if(delete_intermediate_cos_created)
	{

		//#ifdef DEBUG_PAR
		//cout << endl << intermediate_cos_created.size() << " CO's to be deleted by cleanupMemoryInProcessor_In_Cluster" << endl;
		//#endif

		for(set<Aig_Obj_t*>::iterator co_it = intermediate_cos_created.begin(); co_it != intermediate_cos_created.end(); co_it++)
		{
			Aig_Obj_t* co_to_be_deleted = *co_it;
		
			Aig_ObjDeletePo(pub_aig_manager, co_to_be_deleted);
		} 
	
		intermediate_cos_created.clear();

	}

	bool delete_r1r0_cos_created = true;

	if(delete_r1r0_cos_created)
	{

		//#ifdef DEBUG_PAR
		//cout << endl << r1r0_cos_created.size() << " CO's to be deleted by cleanupMemoryInProcessor_In_Cluster" << endl;
		//#endif

		for(set<Aig_Obj_t*>::iterator co_it = r1r0_cos_created.begin(); co_it != r1r0_cos_created.end(); co_it++)
		{
			Aig_Obj_t* co_to_be_deleted = *co_it;
		
			Aig_ObjDeletePo(pub_aig_manager, co_to_be_deleted);
		} 
	
		r1r0_cos_created.clear();

		R0_map.clear();
		R1_map.clear();
	}

	bool delete_all_cos_created = false;

	if(delete_all_cos_created)//Don't try this option; causes memory corruption!!
	{
		
		set<Aig_Obj_t*> all_cos_created;

		for(int i = 1; i <= Aig_ManCoNum(pub_aig_manager)-1; i++)
		{
			Aig_Obj_t* co_to_be_deleted = Aig_ManCo(pub_aig_manager, i);
			all_cos_created.insert(co_to_be_deleted);
		}

		for(set<Aig_Obj_t*>::iterator co_it = all_cos_created.begin(); co_it != all_cos_created.end(); co_it++)
		{
			Aig_Obj_t* co_to_be_deleted = *co_it;		
			Aig_ObjDeletePo(pub_aig_manager, co_to_be_deleted);
		} 

		

		intermediate_cos_created.clear();
		r1r0_cos_created.clear();
		R0_map.clear();
		R1_map.clear();
	}


	bool apply_man_cleanup = true;

	if(apply_man_cleanup)
	{
		//#ifdef DEBUG_PAR
		//cout << endl << "Aig_ManCleanup called in cleanupMemoryInProcessor_In_Cluster\n";
		//#endif

		int number_of_nodes_deleted = Aig_ManCleanup(pub_aig_manager);

		//#ifdef DEBUG_PAR
		//cout << endl << number_of_nodes_deleted << " aig nodes deleted by Aig_ManCleanup in cleanupMemoryInProcessor_In_Cluster in Processor " << rank << "; remaining CI/CO/And are " << Aig_ManCiNum(pub_aig_manager) << " "  << Aig_ManCoNum(pub_aig_manager) << " " << Aig_ManAndNum(pub_aig_manager) << endl;
		//#endif
	}	

	// Delete the entries in r1r0_cos_created as well, along with the entries in the hashtables
	// used inside Skolem::Skolem(....)
}


void AIGBasedSkolem::getR1R0ForFreeVariablesInDisjunction(Aig_Obj_t* formula, map<string, Aig_Obj_t*> &map_of_r1s, map<string, Aig_Obj_t*> &map_of_r0s)
{
	assert(formula != NULL);

	set<string> support;
	computeSupport(formula, support, pub_aig_manager);

	set<Aig_Obj_t*> Factors;
	// Factors are the children
	Factors.insert(Aig_ObjChild0(formula));
	Factors.insert(Aig_ObjChild1(formula));	

	int factor_index = 1;
	map<int, vector<Aig_Obj_t*> > factor_index_to_list_of_r0s_map;
	map<int, vector<Aig_Obj_t*> > factor_index_to_list_of_r1s_map;

	for(set<Aig_Obj_t*>::iterator Factors_it = Factors.begin(); Factors_it != Factors.end(); Factors_it++)
	{
		Aig_Obj_t* given_factor;
		given_factor = *Factors_it;
		assert(given_factor != NULL);
				
		vector<Aig_Obj_t*> list_of_r0s_of_factor;
		vector<Aig_Obj_t*> list_of_r1s_of_factor;
		call_type factor_polarity = negated;
				
		getEntryFromR0HashTable(factor_polarity, given_factor, list_of_r0s_of_factor);
		getEntryFromR1HashTable(factor_polarity, given_factor, list_of_r1s_of_factor);
				
		factor_index_to_list_of_r0s_map.insert(make_pair(factor_index, list_of_r0s_of_factor));
		factor_index_to_list_of_r1s_map.insert(make_pair(factor_index, list_of_r1s_of_factor));

		factor_index++;
	}//consider each factor ends here

	// We have list_of_r0s and list_of_r1s of each factor now
	// From these lists construct the final r0's and r1's

	int location_of_var_to_elim = 0;

	for(list<string>::iterator list_it = Global_VariablesToEliminate.begin(); list_it != Global_VariablesToEliminate.end(); list_it++)
	{
		string var_to_elim = *list_it;

		if(support.find(var_to_elim) == support.end())//formula free of var_to_elim
		{
		
			#ifdef DEBUG_SKOLEM
			cout << "\nGetting cannot-be-1 and cannot-be-0 sets of " << var_to_elim << " from hash tables" << endl;
			#endif

			Aig_Obj_t* cannot_be_one_function;
			Aig_Obj_t* cannot_be_zero_function;
			set<Aig_Obj_t*> cannot_be_one_set_for_var_to_elim_index;
			set<Aig_Obj_t*> cannot_be_zero_set_for_var_to_elim_index;

			int factor_index = 1;
			for(set<Aig_Obj_t*>::iterator Factors_it = Factors.begin(); Factors_it != Factors.end(); Factors_it++)
			{
				#ifdef DEBUG_SKOLEM
				cout << "\nfactor_index = " << factor_index << endl;
				#endif

				map<int, vector<Aig_Obj_t*> >::iterator factor_index_to_list_of_r1s_map_it = factor_index_to_list_of_r1s_map.find(factor_index);
				assert(factor_index_to_list_of_r1s_map_it != factor_index_to_list_of_r1s_map.end());

				Aig_Obj_t* r1 = (factor_index_to_list_of_r1s_map_it->second)[location_of_var_to_elim];
		  		assert(r1 != NULL);		
		
		
				// connecting to some output to avoid unwanted deletion
				Aig_Obj_t* r1_CO = Aig_ObjCreateCo(pub_aig_manager, r1 ); 
				assert(r1_CO != NULL);
				intermediate_cos_created.insert(r1_CO);

				map<int, vector<Aig_Obj_t*> >::iterator factor_index_to_list_of_r0s_map_it = factor_index_to_list_of_r0s_map.find(factor_index);
				assert(factor_index_to_list_of_r0s_map_it != factor_index_to_list_of_r0s_map.end());

				Aig_Obj_t* r0 = (factor_index_to_list_of_r0s_map_it->second)[location_of_var_to_elim];
		  		assert(r0 != NULL);		
		
				// connecting to some output to avoid unwanted deletion
				Aig_Obj_t* r0_CO = Aig_ObjCreateCo(pub_aig_manager, r0 ); 
				assert(r0_CO != NULL);
				intermediate_cos_created.insert(r0_CO);
	
				// Insert the dags in respective cannot-be-sets
				cannot_be_one_set_for_var_to_elim_index.insert(r1);
				cannot_be_zero_set_for_var_to_elim_index.insert(r0);

				factor_index++;
			}// for each factor ends here

			assert(!cannot_be_one_set_for_var_to_elim_index.empty());
			cannot_be_one_function = createAnd(cannot_be_one_set_for_var_to_elim_index, pub_aig_manager);
			assert(cannot_be_one_function != NULL);

			assert(!cannot_be_zero_set_for_var_to_elim_index.empty());
			cannot_be_zero_function = createAnd(cannot_be_zero_set_for_var_to_elim_index, pub_aig_manager);
			assert(cannot_be_zero_function != NULL);
		
			// connect to some output to avoid unwanted deletion
			Aig_Obj_t* cannot_be_one_function_CO = Aig_ObjCreateCo(pub_aig_manager, cannot_be_one_function ); 
			assert(cannot_be_one_function_CO != NULL);
			intermediate_cos_created.insert(cannot_be_one_function_CO);

			Aig_Obj_t* cannot_be_zero_function_CO = Aig_ObjCreateCo(pub_aig_manager, cannot_be_zero_function ); 
			assert(cannot_be_zero_function_CO != NULL);			
			intermediate_cos_created.insert(cannot_be_zero_function_CO);
	
			map_of_r1s.insert(make_pair(var_to_elim, cannot_be_one_function));
			map_of_r0s.insert(make_pair(var_to_elim, cannot_be_zero_function));
		}//if formula free of var_to_elim ends here

		location_of_var_to_elim++;		
		
	}// for each variable ends here	
}



Aig_Obj_t* AIGBasedSkolem::computeInitialSkolemFunctionsAndCannotBeSetsFromHashTableEntriesForDisjunction(int var_to_elim_index, int location_of_var_to_elim, map<int, vector<Aig_Obj_t*> > &factor_index_to_list_of_r0s_map, map<int, vector<Aig_Obj_t*> > &factor_index_to_list_of_r1s_map)
{
	Aig_Obj_t* skolem_function;
	Aig_Obj_t* skolem_function_part1;
	Aig_Obj_t* skolem_function_part2;
	set<Aig_Obj_t*> skolem_function_part1_components;
	set<Aig_Obj_t*> skolem_function_part2_components;

	Aig_Obj_t* initial_cbzero_part_for_bad;
	Aig_Obj_t* initial_cbone_part_for_bad;

	// compute the elements in cb0_k and cb1_k
	set<Aig_Obj_t*> cannot_be_one_set_for_var_to_elim_index;
	set<Aig_Obj_t*> cannot_be_zero_set_for_var_to_elim_index;

	set<Aig_Obj_t*> dags_in_cannot_be_one_set_for_var_to_elim_index;
	set<Aig_Obj_t*> dags_in_cannot_be_zero_set_for_var_to_elim_index;

	for(set<int>::iterator factor_it = FactorsWithVariable.begin(); factor_it != FactorsWithVariable.end(); factor_it++)
	{
		int factor_index = *factor_it;

		#ifdef DEBUG_SKOLEM
		cout << "\nfactor_index = " << factor_index << endl;
		#endif

		map<int, vector<Aig_Obj_t*> >::iterator factor_index_to_list_of_r1s_map_it = factor_index_to_list_of_r1s_map.find(factor_index);
		assert(factor_index_to_list_of_r1s_map_it != factor_index_to_list_of_r1s_map.end());

		Aig_Obj_t* r1 = (factor_index_to_list_of_r1s_map_it->second)[location_of_var_to_elim];
  		assert(r1 != NULL);	

		// connecting to some output to avoid unwanted deletion
		Aig_Obj_t* r1_CO = Aig_ObjCreateCo(pub_aig_manager, r1 ); 
		assert(r1_CO != NULL);
		intermediate_cos_created.insert(r1_CO);

		dags_in_cannot_be_one_set_for_var_to_elim_index.insert(r1);

		

		map<int, vector<Aig_Obj_t*> >::iterator factor_index_to_list_of_r0s_map_it = factor_index_to_list_of_r0s_map.find(factor_index);
		assert(factor_index_to_list_of_r0s_map_it != factor_index_to_list_of_r0s_map.end());

		Aig_Obj_t* r0 = (factor_index_to_list_of_r0s_map_it->second)[location_of_var_to_elim];
  		assert(r0 != NULL);

		// connecting to some output to avoid unwanted deletion
		Aig_Obj_t* r0_CO = Aig_ObjCreateCo(pub_aig_manager, r0 ); 
		assert(r0_CO != NULL);
		intermediate_cos_created.insert(r0_CO);

		dags_in_cannot_be_zero_set_for_var_to_elim_index.insert(r0);
		
	}// for each factor ends here

	Aig_Obj_t* element_in_cannot_be_one_set_for_var_to_elim_index;
	element_in_cannot_be_one_set_for_var_to_elim_index = createAnd(dags_in_cannot_be_one_set_for_var_to_elim_index, pub_aig_manager);
	assert(element_in_cannot_be_one_set_for_var_to_elim_index != NULL);

	// connecting to some output to avoid unwanted deletion
	Aig_Obj_t* element_in_cannot_be_one_set_for_var_to_elim_index_CO = Aig_ObjCreateCo(pub_aig_manager, element_in_cannot_be_one_set_for_var_to_elim_index ); 
	assert(element_in_cannot_be_one_set_for_var_to_elim_index_CO != NULL);
	intermediate_cos_created.insert(element_in_cannot_be_one_set_for_var_to_elim_index_CO);
	
	
	Aig_Obj_t* element_in_cannot_be_zero_set_for_var_to_elim_index;
	element_in_cannot_be_zero_set_for_var_to_elim_index = createAnd(dags_in_cannot_be_zero_set_for_var_to_elim_index, pub_aig_manager);
	assert(element_in_cannot_be_zero_set_for_var_to_elim_index != NULL);

	// connecting to some output to avoid unwanted deletion
	Aig_Obj_t* element_in_cannot_be_zero_set_for_var_to_elim_index_CO = Aig_ObjCreateCo(pub_aig_manager, element_in_cannot_be_zero_set_for_var_to_elim_index ); 
	assert(element_in_cannot_be_zero_set_for_var_to_elim_index_CO != NULL);
	intermediate_cos_created.insert(element_in_cannot_be_zero_set_for_var_to_elim_index_CO);
	

	sizes_of_cannot_be_one_elements_of_variable.push_back(computeSize(element_in_cannot_be_one_set_for_var_to_elim_index, pub_aig_manager));

	sizes_of_cannot_be_zero_elements_of_variable.push_back(computeSize(element_in_cannot_be_zero_set_for_var_to_elim_index, pub_aig_manager));

	#ifdef DEBUG_SKOLEM
	writeFormulaToFile(pub_aig_manager, element_in_cannot_be_one_set_for_var_to_elim_index, "r1", ".v", var_to_elim_index, 0);	
	writeFormulaToFile(pub_aig_manager, element_in_cannot_be_zero_set_for_var_to_elim_index, "r0", ".v", var_to_elim_index, 0);	
	#endif

	// Allocate strings and objects  

	string cannot_be_one_string;
	Aig_Obj_t* cannot_be_one_object;
	allocateStringAndObjectToCannotBeDag(1, element_in_cannot_be_one_set_for_var_to_elim_index, cannot_be_one_string, cannot_be_one_object);

	string cannot_be_zero_string;
	Aig_Obj_t* cannot_be_zero_object;
	allocateStringAndObjectToCannotBeDag(0, element_in_cannot_be_zero_set_for_var_to_elim_index, cannot_be_zero_string, cannot_be_zero_object);

	#ifdef DEBUG_SKOLEM
	show_cannot_be_string_to_cannot_be_object_map();
	show_cannot_be_object_to_cannot_be_dag_map();
	#endif

	// Insert the objects in respective cannot-be-sets
	cannot_be_one_set_for_var_to_elim_index.insert(cannot_be_one_object);
	cannot_be_zero_set_for_var_to_elim_index.insert(cannot_be_zero_object);
		
	// Insert the r1 dag into the skolem_function_part1_components
	skolem_function_part1_components.insert(element_in_cannot_be_one_set_for_var_to_elim_index);			

	// Insert the r0 dag into the skolem_function_part2_components
	skolem_function_part2_components.insert(element_in_cannot_be_zero_set_for_var_to_elim_index);	

	
	if(checkTimeOut()) // check for time-out
	{
		cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::computeInitialSkolemFunctionsAndCannotBeSetsFromHashTableEntriesForDisjunction\n";
		timed_out = true; // timed_out flag set
		return NULL;
	}

	// insert in global tables
	map<int, set<Aig_Obj_t*> >::iterator cannot_be_one_set_it = cannot_be_one_set.find(var_to_elim_index);
	assert(cannot_be_one_set_it == cannot_be_one_set.end());
	cannot_be_one_set.insert(make_pair(var_to_elim_index, cannot_be_one_set_for_var_to_elim_index));

	map<int, set<Aig_Obj_t*> >::iterator cannot_be_zero_set_it = cannot_be_zero_set.find(var_to_elim_index);
	assert(cannot_be_zero_set_it == cannot_be_zero_set.end());
	cannot_be_zero_set.insert(make_pair(var_to_elim_index, cannot_be_zero_set_for_var_to_elim_index));

	// Let's compute the skolem_function
	// skolem_function is 
	//          disjunction of elements in cannot_be_one_set_for_var_to_elim_index \vee 
	//          negation of (disjunction of elements in cannot_be_one_set_for_var_to_elim_index)
	assert(!cannot_be_one_set_for_var_to_elim_index.empty());
	skolem_function_part1 = createOr(skolem_function_part1_components, pub_aig_manager);
	initial_cbone_part_for_bad = skolem_function_part1;
	skolem_function_part1 = createNot(skolem_function_part1, pub_aig_manager);
	assert(skolem_function_part1 != NULL);
	
	assert(!cannot_be_zero_set_for_var_to_elim_index.empty()); 
	skolem_function_part2 = createOr(skolem_function_part2_components, pub_aig_manager);
	initial_cbzero_part_for_bad = skolem_function_part2;
	assert(skolem_function_part2 != NULL);


	if(use_cbzero_in_unified_cegar)
	{
		skolem_function = createOr(skolem_function_part2, skolem_function_part1, pub_aig_manager);
	}
	else
	{
		skolem_function = skolem_function_part1;
	}
		
	assert(skolem_function != NULL);

	InitialSkolemFunctionSizeBeforeOptimization = computeSize(skolem_function, pub_aig_manager);

	if(use_dontcare_optimization_in_cegar)
	// optimize the skolem_function
	{
		// create Cb1_i \wedge Cb0_i

		// Cb1_i is disjunction of AIGs in cannot_be_one_set_for_var_to_elim_index, i.e. ~skolem_function_part1
		Aig_Obj_t* Cb1_part = createNot(skolem_function_part1, pub_aig_manager);

		// Cb0_i is disjunction of AIGs in cannot_be_zero_set_for_var_to_elim_index, i.e. skolem_function_part2
		Aig_Obj_t* Cb0_part = skolem_function_part2;

		Aig_Obj_t* dontcare_part = createAnd(Cb1_part, Cb0_part, pub_aig_manager);
		assert(dontcare_part != NULL);

		#ifdef DEBUG_SKOLEM
		writeFormulaToFile(pub_aig_manager, dontcare_part, "dontcare_part", ".v", var_to_elim_index, cegar_iteration_number);	
		writeFormulaToFile(pub_aig_manager, skolem_function, "unoptimized_skolem_function", ".v", var_to_elim_index, cegar_iteration_number);	
		#endif

		skolem_function = performDontCareOptimization(pub_aig_manager, skolem_function, dontcare_part);
		assert(skolem_function != NULL);
		
	}

	// connect to some output to avoid unwanted deletion
	Aig_Obj_t* skolem_function_part2_CO = Aig_ObjCreateCo(pub_aig_manager, skolem_function_part2 ); 
	assert(skolem_function_part2_CO != NULL);
	intermediate_cos_created.insert(skolem_function_part2_CO);

	Aig_Obj_t* skolem_function_CO = Aig_ObjCreateCo(pub_aig_manager, skolem_function ); 
	assert(skolem_function_CO != NULL);
	intermediate_cos_created.insert(skolem_function_CO);

	#ifdef DEBUG_SKOLEM
	cout << "\nabstract skolem_function computed\n";	
	#endif

	#ifdef PRINT_SKOLEM_FUNCTIONS
	string skolem_function_file_name = benchmark_name_without_extension;
	skolem_function_file_name += "_skolem_function";
	writeFormulaToFile(pub_aig_manager, skolem_function, skolem_function_file_name, ".v", var_to_elim_index, cegar_iteration_number);
	#endif

	// Enter into matrix
	insertIntoOneDimensionalMatrix(SkolemFunctions, number_of_vars_to_elim, var_to_elim_index, skolem_function, false);

	// Computing Badsets here
	if(var_to_elim_index < number_of_vars_to_elim) // No need to compute Bad_{n+1} 
	{
		Aig_Obj_t* bad_set_for_next_var;
		bad_set_for_next_var = createAnd(initial_cbzero_part_for_bad, initial_cbone_part_for_bad, pub_aig_manager);
		assert(bad_set_for_next_var != NULL);

		// connect to some output to avoid unwanted deletion
		Aig_Obj_t* bad_set_for_next_var_CO = Aig_ObjCreateCo(pub_aig_manager, bad_set_for_next_var ); 
		assert(bad_set_for_next_var_CO != NULL);
		intermediate_cos_created.insert(bad_set_for_next_var_CO);

		#ifdef DEBUG_SKOLEM
		cout << "\nbad_set_" << var_to_elim_index+1 << " computed\n";
		writeFormulaToFile(pub_aig_manager, bad_set_for_next_var, "bad_set", ".v", var_to_elim_index+1, cegar_iteration_number);	
		#endif

		// Enter into matrix
		insertIntoOneDimensionalMatrix(BadSets, number_of_vars_to_elim, var_to_elim_index+1, bad_set_for_next_var, false);
	}	
	
	if(checkTimeOut()) // check for time-out
	{
		cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::computeInitialSkolemFunctionsAndCannotBeSetsFromHashTableEntriesForDisjunction\n";
		timed_out = true; // timed_out flag set
		return NULL;
	}	

	// Compute ICb0_k in terms of objects and as dag
	// These will be required while recomputing the Skolem functions
	// Let's compute these right now, since later on these sets will get changed

	// we already have ICb0_k dag; let's insert it
	map<int, Aig_Obj_t*>::iterator initial_cannot_be_zero_dags_it = initial_cannot_be_zero_dags.find(var_to_elim_index);
	assert(initial_cannot_be_zero_dags_it == initial_cannot_be_zero_dags.end());
	initial_cannot_be_zero_dags.insert(make_pair(var_to_elim_index, skolem_function_part2));
	
	// Let's compute the ICb0_k object
	Aig_Obj_t* initial_cannot_be_zero_object;
	assert(!cannot_be_zero_set_for_var_to_elim_index.empty());
	initial_cannot_be_zero_object = createOr(cannot_be_zero_set_for_var_to_elim_index, pub_aig_manager);
	assert(initial_cannot_be_zero_object != NULL);

	// connect to some output to avoid unwanted deletion
	Aig_Obj_t* initial_cannot_be_zero_object_CO = Aig_ObjCreateCo(pub_aig_manager, initial_cannot_be_zero_object ); 
	assert(initial_cannot_be_zero_object_CO != NULL);
	intermediate_cos_created.insert(initial_cannot_be_zero_object_CO);

	// let's insert it
	map<int, Aig_Obj_t*>::iterator initial_cannot_be_zero_objects_it = initial_cannot_be_zero_objects.find(var_to_elim_index);
	assert(initial_cannot_be_zero_objects_it == initial_cannot_be_zero_objects.end());
	initial_cannot_be_zero_objects.insert(make_pair(var_to_elim_index, initial_cannot_be_zero_object));
		
	return skolem_function;		
}



void AIGBasedSkolem::skolemFunctionGeneratorUsingRsynth(list<string> &VariablesToEliminate)
{
	unsigned long long int total_ms;
	struct timeval total_start_ms, total_finish_ms;
	gettimeofday (&total_start_ms, NULL);

	#ifdef DEUBG_SKOLEM
	cout << "\nVariablesToEliminate\n";
	showList(VariablesToEliminate); 
	#endif

	set<string> VariablesToEliminate_Set(VariablesToEliminate.begin(), VariablesToEliminate.end());

	assert(Aig_ManCoNum(pub_aig_manager) == 1);
	Aig_Obj_t* CO_pub_aig_manager;
	CO_pub_aig_manager = Aig_ManCo(pub_aig_manager, 0);
	assert(CO_pub_aig_manager != NULL);

	string cnf_file = benchmark_name;
	cnf_file += "_rsynth.cnf";

	string output_variables_file = benchmark_name;
	output_variables_file += "_rsynth.vars";

	unsigned long long int con_ms;
	struct timeval con_start_ms, con_finish_ms;
	gettimeofday (&con_start_ms, NULL); 	

	convertToRsynthQDimacs(CO_pub_aig_manager, VariablesToEliminate_Set, pub_aig_manager, cnf_file, output_variables_file);

	gettimeofday (&con_finish_ms, NULL);
   	con_ms = con_finish_ms.tv_sec * 1000 + con_finish_ms.tv_usec / 1000;
   	con_ms -= con_start_ms.tv_sec * 1000 + con_start_ms.tv_usec / 1000;
	//cout << "\nConversion to DIMACS happened in " << con_ms << " milliseconds\n";


	// Here, add the code to call rsynth and collecting the results

	gettimeofday (&total_finish_ms, NULL);
   	total_ms = total_finish_ms.tv_sec * 1000 + total_finish_ms.tv_usec / 1000;
   	total_ms -= total_start_ms.tv_sec * 1000 + total_start_ms.tv_usec / 1000;
	//cout << "\nTotal time = " << total_ms << " milliseconds\n";	
}



void AIGBasedSkolem::interractiveSolver(Aig_Obj_t* formula, list<string> &VariablesToEliminate, set<string> &VariablesToRemain, vector<Aig_Obj_t*> &list_of_initial_r1s, vector<Aig_Obj_t*> &list_of_initial_r0s)
{
	// We need to solve formula i.e. F(X, Y), where VariablesToEliminate = X,
	// VariablesToRemain = Y, and list_of_initial_r1s, list_of_initial_r0s
	// are the list of r1's and r0's ordered as per VariablesToEliminate

	assert(VariablesToEliminate.size() == list_of_initial_r1s.size());
	assert(VariablesToEliminate.size() == list_of_initial_r0s.size());

	// Initializations

	// 1) Initialize variables_quantified, and variables_not_quantified
	copy(VariablesToEliminate.begin(), VariablesToEliminate.end(), inserter(variables_quantified, variables_quantified.begin()));
	variables_not_quantified = VariablesToRemain;

	#ifdef DEBUG_INTERRACTIVE_SOLVER
	// print the sets of variables and the formula
	#endif

	// 2) create the var_name_to_var_index_map and var_index_to_var_name_map
	int var_index = 1;
	for(list<string>::iterator list_it = VariablesToEliminate.begin(); list_it != VariablesToEliminate.end(); list_it++)
	{
		insertIntoVarNameToVarIndexMap(var_name_to_var_index_map, *list_it, var_index);
		insertIntoVarIndexToVarNameMap(var_index_to_var_name_map, var_index, *list_it);

		#ifdef DEBUG_INTERRACTIVE_SOLVER
		cout << "(" << *list_it << ", " << var_index << ") inserted into maps "<< endl;
		#endif	

		var_index++;
	}

	
	// 3) Insert initial r1/r0's in proper data-structures
	number_of_vars_to_elim = VariablesToEliminate.size();
	for(int var_to_elim_index = 1; var_to_elim_index <= number_of_vars_to_elim; var_to_elim_index++)
	{
		Aig_Obj_t* element_in_cannot_be_one_set;
		element_in_cannot_be_one_set = list_of_initial_r1s[var_to_elim_index-1];
		assert(element_in_cannot_be_one_set != NULL);

		Aig_Obj_t* element_in_cannot_be_zero_set;
		element_in_cannot_be_zero_set = list_of_initial_r0s[var_to_elim_index-1];
		assert(element_in_cannot_be_zero_set != NULL);

		// Allocate strings and objects  
		string cannot_be_one_string;
		Aig_Obj_t* cannot_be_one_object;
		allocateStringAndObjectToCannotBeDag(1, element_in_cannot_be_one_set, cannot_be_one_string, cannot_be_one_object);

		string cannot_be_zero_string;
		Aig_Obj_t* cannot_be_zero_object;
		allocateStringAndObjectToCannotBeDag(0, element_in_cannot_be_zero_set, cannot_be_zero_string, cannot_be_zero_object);

		#ifdef DEBUG_INTERRACTIVE_SOLVER
		show_cannot_be_string_to_cannot_be_object_map();
		show_cannot_be_object_to_cannot_be_dag_map();
		#endif

		// Insert the objects in respective cannot-be-sets
		set<Aig_Obj_t*> cannot_be_one_set_for_var_to_elim_index;
		set<Aig_Obj_t*> cannot_be_zero_set_for_var_to_elim_index;

		cannot_be_one_set_for_var_to_elim_index.insert(cannot_be_one_object);
		cannot_be_zero_set_for_var_to_elim_index.insert(cannot_be_zero_object);
				
		// insert in global tables
		map<int, set<Aig_Obj_t*> >::iterator cannot_be_one_set_it = cannot_be_one_set.find(var_to_elim_index);
		assert(cannot_be_one_set_it == cannot_be_one_set.end());
		cannot_be_one_set.insert(make_pair(var_to_elim_index, cannot_be_one_set_for_var_to_elim_index));

		map<int, set<Aig_Obj_t*> >::iterator cannot_be_zero_set_it = cannot_be_zero_set.find(var_to_elim_index);
		assert(cannot_be_zero_set_it == cannot_be_zero_set.end());
		cannot_be_zero_set.insert(make_pair(var_to_elim_index, cannot_be_zero_set_for_var_to_elim_index));

		map<int, Aig_Obj_t*>::iterator initial_cannot_be_zero_dags_it = initial_cannot_be_zero_dags.find(var_to_elim_index);
		assert(initial_cannot_be_zero_dags_it == initial_cannot_be_zero_dags.end());
		initial_cannot_be_zero_dags.insert(make_pair(var_to_elim_index, element_in_cannot_be_zero_set));	
	}	
		
	
	// CEGAR Loop	

	int correction_index = number_of_vars_to_elim; 
	cegar_iteration_for_correction_index = 0;
	map<string, int> Model_of_ExactnessCheck;
	map<int, Aig_Obj_t*> Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX;
	map<int, Aig_Obj_t*> Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX;	

	while(true)
	{

		// Get a Y-value from the user 
		map<string, int> YValues; // YValues[y_variable] gives value of y_variable
		getYValuesFromUser(YValues);

		bool epsilon_is_sat_for_given_y;
		// check if epsilon is satisfiable for the given y
		epsilon_is_sat_for_given_y = checkIfEpsilonIsSat_For_Given_Y_using_Simulation(formula, YValues, Model_of_ExactnessCheck, number_of_vars_to_elim);	

		if(!epsilon_is_sat_for_given_y) //epsilon is unsat
		// Skolem functions are correct; Give the X-values to user
		{
			giveXValuesToUser(VariablesToEliminate, Model_of_ExactnessCheck);
		}
		else // epsilon is sat; we need to refine the Skolem functions to 
		// eliminate the cases for this given Y and then give the X-values to user
		{
			
			bool epsilon_remains_sat_for_given_y = true;

			while(epsilon_remains_sat_for_given_y)
			{
				// From the model of exactness check, refine the r1/r0's
				refineSkolemFunctions_using_Mu_Based_Scheme_With_Optimizations(correction_index, Model_of_ExactnessCheck, Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX, Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX); 

				// Then find the location from which we need to start reevaluating the XValues
				// This is the location of the maximum x_i in the 
				// Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX

				map<int, Aig_Obj_t*>::reverse_iterator Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX_rit = Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX.rbegin();
				int last_refined_location = Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX_rit->first;
	
				#ifdef DEBUG_CEGAR
				cout << endl << "last_refined_location = " << last_refined_location << endl;
				#endif

				// Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX,..., 
				// are not needed -- let's clear them
				Refinement_Hint_Of_CannotBe_One_To_Eliminate_This_CEX.clear();
				Refinement_Hint_Of_CannotBe_Zero_To_Eliminate_This_CEX.clear();

				cegar_iteration_number++;
				cegar_iteration_for_correction_index++;

				// check if epsilon remains satisfiable 
				// after adding this refinement hint
				
				Model_of_ExactnessCheck.clear();
				epsilon_remains_sat_for_given_y = checkIfEpsilonIsSat_For_Given_Y_using_Simulation(formula, YValues, Model_of_ExactnessCheck, last_refined_location);				
			}

			// epsilon is unsat for the given y; hence for the given y,
			// the values of X from the Skolem functions are correct
			
			giveXValuesToUser(VariablesToEliminate, Model_of_ExactnessCheck);

		}// epsilon is sat ends here

	}// while(true) ends here

}// function ends here



void AIGBasedSkolem::getYValuesFromUser(map<string, int> &YValues)
{
	cout << "\nPress any key to start entering values for y-variables\n";
	char c = getchar();
	
	for(set<string>::iterator vit = variables_not_quantified.begin(); vit != variables_not_quantified.end();  vit++)
	{
		cout << "\nEnter value for " << *vit << endl;
		
		int value_y;
		scanf("%d", &value_y);
		assert(value_y == 1 || value_y == 0);
		YValues.insert(make_pair(*vit, value_y));		
	}
}
				

void AIGBasedSkolem::giveXValuesToUser(list<string> &VariablesToEliminate, map<string, int> &Model_of_ExactnessCheck)
{
	cout << "\nValues of X variables are\n";

	for(list<string>::iterator vit = VariablesToEliminate.begin(); vit != VariablesToEliminate.end(); vit++)
	{
		string x_variable = *vit;
		map<string, int>::iterator mit = Model_of_ExactnessCheck.find(x_variable);
		assert(mit != Model_of_ExactnessCheck.end());
		cout << x_variable << "\t" << mit->second << endl;
	}
}


bool AIGBasedSkolem::checkIfEpsilonIsSat_For_Given_Y_using_Simulation(Aig_Obj_t* formula, map<string, int> &YValues, map<string, int> &Model_of_ExactnessCheck, int last_refined_location)
{
	map<string, int> XValues; // XValues[x_variable] gives value of x_variable
	
	for(map<string, int>::iterator model_it = Model_of_ExactnessCheck.begin(); model_it != Model_of_ExactnessCheck.end(); model_it++)
	{
		string variable_name = model_it->first;
		int variable_value = model_it->second;
		
		if(variables_quantified.find(variable_name) != variables_quantified.end()) // variable_name is an X  variable
		{
			XValues.insert(make_pair(variable_name, variable_value));
		}		
	}


	Model_of_ExactnessCheck.clear(); 

	#ifdef DEBUG_CEGAR
	cout << endl;
	for(map<string, int>::iterator XValues_it = XValues.begin(); XValues_it != XValues.end(); XValues_it++)
	{
		cout << endl << "XValues[" << XValues_it->first << "] = " << XValues_it->second;
	}
	cout << endl;
	for(map<string, int>::iterator YValues_it = YValues.begin(); YValues_it != YValues.end(); YValues_it++)
	{
		cout << endl << "YValues[" << YValues_it->first << "] = " << YValues_it->second;
	}
	cout << endl;
	#endif

	
	// We need to reevaluate all the XValues, i.e., x_{last_refined_location} ... x_{1} using 
	// the values of Y variables.  
	// Just remember that the Skolem functions existing are r0[i] \vee ~r1[i]
	// What we want are Skolem functions of the form ~r1[i]	

	t_HashTable<int, bool> CommonEvaluationHashTableInMilking;

	map<string, bool> variable_to_value_map;
	// First set the Y-values in variable_to_value_map
	for(map<string, int>::iterator yvalues_it = YValues.begin(); yvalues_it != YValues.end(); yvalues_it++)
	{
		bool bool_value;
		if(yvalues_it->second == 1)
		{
			bool_value = true;
		}
		else
		{
			bool_value = false;
		}

		variable_to_value_map.insert(make_pair(yvalues_it->first, bool_value));
		#ifdef DEBUG_SKOLEM
			cout << endl << yvalues_it->first << " --> " << bool_value << " inserted into variable_to_value_map\n";
		#endif
		Model_of_ExactnessCheck.insert(make_pair(yvalues_it->first, yvalues_it->second));
	}

	for(int var_to_elim_index = number_of_vars_to_elim; var_to_elim_index > last_refined_location; var_to_elim_index--)
	{
		string var_to_elim = searchVarIndexToVarNameMap(var_index_to_var_name_map, var_to_elim_index);
		map<string, int>::iterator xvalues_it = XValues.find(var_to_elim);
	
		bool bool_value;
		if(xvalues_it->second == 1)
		{
			bool_value = true;
		}
		else
		{
			bool_value = false;
		}

		variable_to_value_map.insert(make_pair(xvalues_it->first, bool_value));
		#ifdef DEBUG_SKOLEM
			cout << endl << xvalues_it->first << " --> " << bool_value << " inserted into variable_to_value_map\n";
		#endif
		Model_of_ExactnessCheck.insert(make_pair(xvalues_it->first, xvalues_it->second));
	}
	
	
	// Now let's evaluate x_{last_refined_location} ... x_{1}	
	for(int var_to_elim_index = last_refined_location; var_to_elim_index >= 1; var_to_elim_index--)
	{
		// Obtain XValues[var_to_elim_index]
		string var_to_elim = searchVarIndexToVarNameMap(var_index_to_var_name_map, var_to_elim_index);

		// obtaining \psi_i
		Aig_Obj_t* skolem_function = createSkolemFunction_In_Mu_Based_Scheme_With_Optimizations_With_Optional_ICb0(var_to_elim_index);
		assert(skolem_function != NULL); 

		#ifdef DEBUG_SKOLEM
		string skolem_function_file_name = benchmark_name_without_extension;
		skolem_function_file_name += "_skolem_function_used_in_simulation";
		writeFormulaToFile(pub_aig_manager, skolem_function, skolem_function_file_name, ".v", var_to_elim_index, cegar_iteration_number);
		#endif

		bool bool_value;
		bool_value = evaluateFormulaOfCi_Efficient_With_Given_HashTable(skolem_function, variable_to_value_map, CommonEvaluationHashTableInMilking);
		variable_to_value_map.insert(make_pair(var_to_elim, bool_value));	

		#ifdef DEBUG_SKOLEM
			cout << endl << var_to_elim << " --> " << bool_value << " inserted into variable_to_value_map\n";
		#endif

		if(bool_value)
		{
			Model_of_ExactnessCheck.insert(make_pair(var_to_elim, 1));	
		}
		else
		{
			Model_of_ExactnessCheck.insert(make_pair(var_to_elim, 0));
		}	
	}

	
	bool f_is_sat;
	f_is_sat = evaluateFormulaOfCi_Efficient_With_Given_HashTable(formula, variable_to_value_map, CommonEvaluationHashTableInMilking);

	#ifdef DEBUG_CEGAR
	cout << endl << "f_is_sat = " << f_is_sat << endl;
	#endif

	if(f_is_sat) // f(x,y) is sat/true under Model_of_ExactnessCheck, i.e. ~f(x,y) is false, i.e. epsilon is false 
	{
		// We don't clear the x, y values here; need to show to user.

		return false;
	}
	else // f(x,y) is unsat/false under Model_of_ExactnessCheck, i.e. ~f(x,y) is true, i.e. epsilon is true
	{
		// Note that we also need to reevaluate the r1[i]'s and r0[i]'s	

		for(map<string, Aig_Obj_t*>::iterator cannot_be_string_to_cannot_be_object_map_it = cannot_be_string_to_cannot_be_object_map.begin(); cannot_be_string_to_cannot_be_object_map_it != cannot_be_string_to_cannot_be_object_map.end(); cannot_be_string_to_cannot_be_object_map_it++)
		{
			string cannot_be_string = cannot_be_string_to_cannot_be_object_map_it->first;
			Aig_Obj_t* cannot_be_object = cannot_be_string_to_cannot_be_object_map_it->second;
			
			map<Aig_Obj_t*, Aig_Obj_t*>::iterator cannot_be_object_to_cannot_be_dag_map_it = cannot_be_object_to_cannot_be_dag_map.find(cannot_be_object);
			assert(cannot_be_object_to_cannot_be_dag_map_it != cannot_be_object_to_cannot_be_dag_map.end());
			Aig_Obj_t* cannot_be_dag = cannot_be_object_to_cannot_be_dag_map_it->second;

			bool bool_value;
			bool_value = evaluateFormulaOfCi_Efficient_With_Given_HashTable(cannot_be_dag, variable_to_value_map, CommonEvaluationHashTableInMilking);
			
			if(bool_value)
			{
				Model_of_ExactnessCheck.insert(make_pair(cannot_be_string, 1));	
			}
			else
			{
				Model_of_ExactnessCheck.insert(make_pair(cannot_be_string, 0));
			}
		}

		return true;
		
	}
}



void AIGBasedSkolem::callInterractiveSolver(Aig_Obj_t* formula)
{	
	if(choose_to_apply_monoskolem_on_smaller_problem_instances)
	{
		// Apply DFS to find tree-size and varstoelim for all AND-
		// nodes in formula
		findTreeSizeAndVarsToElim(formula, pub_aig_manager);
	}
	
	#ifdef DEBUG_SKOLEM
	writeFormulaToFile(pub_aig_manager, formula, "arbitrary_input_bool_formula", ".v", 0, 0);	
	#endif


	// Calling Skolem to find r1 and r0's of top-node
	
	perform_cegar_on_arbitrary_boolean_formulas = true;
	call_type polarity = original;
	int depth_from_root = 0;
	Skolem(polarity, formula, depth_from_root);

	#ifdef DEBUG_SKOLEM
	if(checkIfResultsAreTimedOut_In_Cluster())//this is to check for graceful time-out
	{
		cout << "\nr1's and r0's from AIGBasedSkolem::Skolem are not exact, but guaranteed under-approximate!! -- inexactness due to time-outs\n";
	}
	else
	{
		cout << "\nr1's and r0's from AIGBasedSkolem::Skolem are exact\n";
	}
	#endif

	if(checkTimeOut()) // check for time-out
	{
		cout << "\nWarning!!Time-out inside the function AIGBasedSkolem::callInterractiveSolver\n";
		timed_out = true; // timed_out flag set
		return;
		
	}


	// We have r1's and r0's in the HashTables (Can be under-approximate in general)
	// Get the r1's and r0's from the HashTable
				
	vector<Aig_Obj_t*> list_of_r1s_of_formula;
	obtainFromR1HashTable(polarity, formula, list_of_r1s_of_formula);

	vector<Aig_Obj_t*> list_of_r0s_of_formula;
	obtainFromR0HashTable(polarity, formula, list_of_r0s_of_formula);

	assert(list_of_r1s_of_formula.size() == Global_VariablesToEliminate.size());
	assert(list_of_r0s_of_formula.size() == Global_VariablesToEliminate.size());

	interractiveSolver(formula, Global_VariablesToEliminate, Global_VariablesToRemain_Set, list_of_r1s_of_formula, list_of_r0s_of_formula);
	
}


bool AIGBasedSkolem::checkIfSkolemFunctionsObtainedAreCorrect(Aig_Obj_t* formula, list<string> &VariablesToEliminate_Order, vector<Aig_Obj_t*> &skolem_functions_of_formula)
{
	bool ensure_that_skolem_functions_are_on_y = true;
	
	set<string> VariablesToEliminate_Set;
	copy(VariablesToEliminate_Order.begin(), VariablesToEliminate_Order.end(), inserter(VariablesToEliminate_Set, VariablesToEliminate_Set.begin()));	
	
	map<string, Aig_Obj_t*> skolem_function_replacement_map;
	int skolem_index = 0;
	for(list<string>::iterator list_it = VariablesToEliminate_Order.begin(); list_it != VariablesToEliminate_Order.end(); list_it++)
	{
		string variable_to_eliminate = *list_it;
			
		Aig_Obj_t* skolem_i = skolem_functions_of_formula[skolem_index];
		assert(skolem_i != NULL);

		if(ensure_that_skolem_functions_are_on_y)
		{
			set<string> support_skolem_i;
			computeSupport(skolem_i, support_skolem_i, pub_aig_manager);
				
			set<string> varstoelim_in_support_skolem_i;
			set_intersection(support_skolem_i.begin(), support_skolem_i.end(), VariablesToEliminate_Set.begin(), VariablesToEliminate_Set.end(), inserter(varstoelim_in_support_skolem_i, varstoelim_in_support_skolem_i.begin()));

			if(!varstoelim_in_support_skolem_i.empty())				
			{
				cout << "\n\nSkolem function of variable " << variable_to_eliminate << " involves variables to be eliminated\n";
				assert(false);	
			}
		}

		skolem_function_replacement_map.insert(make_pair(variable_to_eliminate, skolem_i));
				
		skolem_index++;
		
	}// for each variable ends here	

	assert(skolem_function_replacement_map.size() > 0);

	Aig_Obj_t* result_of_qe_using_skolem_functions;
	result_of_qe_using_skolem_functions = replaceVariablesByFormulas(formula, skolem_function_replacement_map);	
	assert(result_of_qe_using_skolem_functions != NULL); // F(psi(Y), Y)	

	Aig_Obj_t* equivalence_check; // ~F(psi(Y), Y) \wedge F(X, Y)
	equivalence_check = createAnd(createNot(result_of_qe_using_skolem_functions, pub_aig_manager), formula, pub_aig_manager);
	assert(equivalence_check != NULL);

	// Give to SAT-Solver
	unsigned long long int cnf_time;
	int formula_size;
	unsigned long long int simplification_time;
	map<string, int> Model_of_equivalence_check;
	bool result_of_equivalence_check;

	bool use_incremental_solver = true;

	if(use_incremental_solver)
	{
		vector<Aig_Obj_t*> positive_assumptions;
		vector<Aig_Obj_t*> negative_assumptions;
			
		assert(IncrementalLabelCountForProvingCorrectness == 1);// first use should be HERE

		pSat_for_proving_correctness = sat_solver_new();
	
		result_of_equivalence_check = isExactnessCheckSatisfiable(pub_aig_manager, equivalence_check, Model_of_equivalence_check, cnf_time, formula_size, simplification_time, positive_assumptions, negative_assumptions, pSat_for_proving_correctness, IncrementalLabelTableForProvingCorrectness, IncrementalLabelCountForProvingCorrectness, Ci_name_to_Ci_label_mapForProvingCorrectness, Ci_label_to_Ci_name_mapForProvingCorrectness);
		
		sat_solver_delete(pSat_for_proving_correctness);
	}
	else
	{
		result_of_equivalence_check = isSat(pub_aig_manager, equivalence_check, Model_of_equivalence_check, cnf_time, formula_size, simplification_time);
	}
		
	if(result_of_equivalence_check)
	{
		cout << "\nexists X.f => f[X --> psi] is NOT valid; Skolem functions are NOT exact\n";
		cout << "\nCounterexample is\n";
		displayModelFromSATSolver(Model_of_equivalence_check);	
		return false;		
	}
	else
	{
		cout << "\nexists X.f => f[X --> psi] is valid; Skolem functions are exact\n";
		return true;
	}	

}


void AIGBasedSkolem::setParametersOfSeqCegarToDefaults()
{
	R0_map.clear();
	R1_map.clear();

	number_of_cegarskolem_calls_on_arbitrary_boolean_formulas = 0;
	number_of_monoskolem_calls_on_arbitrary_boolean_formulas = 0;
 	number_of_disjunctions_on_arbitrary_boolean_formulas = 0; 
 	number_of_conjunctions_on_arbitrary_boolean_formulas = 0;
 	skolem_function_sizes_before_reverse_substitution.clear();
	total_time_in_reverse_substitution_on_arbitrary_boolean_formulas = 0;
 	total_time_in_callconjunction = 0;
 	total_time_in_calldisjunction = 0;
 	total_time_in_callmonolithic = 0;
 	total_time_in_cegarskolem = 0;
 	min_skolem_function_size_after_reverse_substitution = -1;
 	max_skolem_function_size_after_reverse_substitution = -1;
 	min_skolem_function_size_before_reverse_substitution = -1;
 	max_skolem_function_size_before_reverse_substitution = -1;
 	total_number_of_cegar_iterations_in_cegarskolem = 0;
 	max_number_of_cegar_iterations_in_cegarskolem = -1;
 	min_number_of_cegar_iterations_in_cegarskolem = -1;
 	depth_from_root_in_cegarskolem_call_on_arbitrary_boolean_formulas = -1;
 	total_time_in_ordering_for_arbitrary_boolean_combinations = 0;

	IncrementalLabelTableForProvingCorrectness.clear();
	IncrementalLabelCountForProvingCorrectness = 1;
 	Ci_name_to_Ci_label_mapForProvingCorrectness.clear(); 
 	Ci_label_to_Ci_name_mapForProvingCorrectness.clear(); 

	TreeSizesOfNodes.clear();
 	VarsToElimOfNodes.clear();

	cumulative_time_in_true_sat_solving_in_cegar = 0;
 	cumulative_time_in_false_sat_solving_in_cegar = 0;
 	cumulative_time_in_sat_solving_in_cegar = 0;
 	total_time_in_simulation_to_replace_sat_in_cegar = 0;
 	cumulative_time_in_simulation_to_replace_sat_in_cegar = 0;
 	total_time_in_function_evaluation_to_replace_sat_in_cegar_in_functional_forms = 0;
 
	intermediate_cos_created.clear();
 	intermediate_cis_created.clear();
 	r1r0_cos_created.clear();	

}



void AIGBasedSkolem::cleanupDatastructuresAndSetParametersOfSeqCegarToDefaults()
{
	number_of_cegarskolem_calls_on_arbitrary_boolean_formulas = 0;
	number_of_monoskolem_calls_on_arbitrary_boolean_formulas = 0;
 	number_of_disjunctions_on_arbitrary_boolean_formulas = 0; 
 	number_of_conjunctions_on_arbitrary_boolean_formulas = 0;
 	skolem_function_sizes_before_reverse_substitution.clear();
	total_time_in_reverse_substitution_on_arbitrary_boolean_formulas = 0;
 	total_time_in_callconjunction = 0;
 	total_time_in_calldisjunction = 0;
 	total_time_in_callmonolithic = 0;
 	total_time_in_cegarskolem = 0;
 	min_skolem_function_size_after_reverse_substitution = -1;
 	max_skolem_function_size_after_reverse_substitution = -1;
 	min_skolem_function_size_before_reverse_substitution = -1;
 	max_skolem_function_size_before_reverse_substitution = -1;
 	total_number_of_cegar_iterations_in_cegarskolem = 0;
 	max_number_of_cegar_iterations_in_cegarskolem = -1;
 	min_number_of_cegar_iterations_in_cegarskolem = -1;
 	depth_from_root_in_cegarskolem_call_on_arbitrary_boolean_formulas = -1;
 	total_time_in_ordering_for_arbitrary_boolean_combinations = 0;

	IncrementalLabelTableForProvingCorrectness.clear();
	IncrementalLabelCountForProvingCorrectness = 1;
 	Ci_name_to_Ci_label_mapForProvingCorrectness.clear(); 
 	Ci_label_to_Ci_name_mapForProvingCorrectness.clear(); 

	TreeSizesOfNodes.clear();
 	VarsToElimOfNodes.clear();

	cumulative_time_in_true_sat_solving_in_cegar = 0;
 	cumulative_time_in_false_sat_solving_in_cegar = 0;
 	cumulative_time_in_sat_solving_in_cegar = 0;
 	total_time_in_simulation_to_replace_sat_in_cegar = 0;
 	cumulative_time_in_simulation_to_replace_sat_in_cegar = 0;
 	total_time_in_function_evaluation_to_replace_sat_in_cegar_in_functional_forms = 0;
 
	bool delete_intermediate_cos_created = true;

	if(delete_intermediate_cos_created)
	{

		#ifdef DEBUG_SKOLEM
		cout << endl << intermediate_cos_created.size() << " intermediate CO's to be deleted by AIGBasedSkolem::cleanupDatastructuresAndSetParametersOfSeqCegarToDefaults()" << endl;
		#endif

		for(set<Aig_Obj_t*>::iterator co_it = intermediate_cos_created.begin(); co_it != intermediate_cos_created.end(); co_it++)
		{
			Aig_Obj_t* co_to_be_deleted = *co_it;
		
			Aig_ObjDeletePo(pub_aig_manager, co_to_be_deleted);
		} 		

	}

	bool delete_r1r0_cos_created = true;

	if(delete_r1r0_cos_created)
	{

		#ifdef DEBUG_SKOLEM
		cout << endl << r1r0_cos_created.size() << " r1r0 CO's to be deleted by AIGBasedSkolem::cleanupDatastructuresAndSetParametersOfSeqCegarToDefaults()" << endl;
		#endif

		for(set<Aig_Obj_t*>::iterator co_it = r1r0_cos_created.begin(); co_it != r1r0_cos_created.end(); co_it++)
		{
			Aig_Obj_t* co_to_be_deleted = *co_it;
		
			Aig_ObjDeletePo(pub_aig_manager, co_to_be_deleted);
		} 
			

	}

	
	bool apply_man_cleanup = true;

	if(apply_man_cleanup)
	{
		#ifdef DEBUG_SKOLEM
		cout << endl << "Aig_ManCleanup called in AIGBasedSkolem::cleanupDatastructuresAndSetParametersOfSeqCegarToDefaults()\n";
		#endif

		int number_of_nodes_deleted = Aig_ManCleanup(pub_aig_manager);

		#ifdef DEBUG_SKOLEM
		cout << endl << number_of_nodes_deleted << " aig nodes deleted by Aig_ManCleanup in AIGBasedSkolem::cleanupDatastructuresAndSetParametersOfSeqCegarToDefaults(); remaining CI/CO/And are " << Aig_ManCiNum(pub_aig_manager) << " "  << Aig_ManCoNum(pub_aig_manager) << " " << Aig_ManAndNum(pub_aig_manager) << endl;
		#endif
	}


	R0_map.clear();
	R1_map.clear();
	intermediate_cis_created.clear();
	intermediate_cos_created.clear();
	r1r0_cos_created.clear();	

	// Delete the entries in r1r0_cos_created as well, along with the entries in the hashtables
	// used inside Skolem::Skolem(....)	
	
}



Aig_Obj_t* AIGBasedSkolem::findNewPartInFailureConditionDagUsingUnrolling(int &number_of_state_elements, map<int, string> &idName, list<string> &output_names, map<string, Aig_Obj_t*> &output_name_to_replaced_factor, map<Aig_Obj_t*, Aig_Obj_t*> &Output_Object_to_RHS_of_PrimaryOutputs, map<string, Aig_Obj_t*> &variable_to_skolem_function_map, int iterations_of_loop, ABC* abcObj, Abc_Frame_t* abcFrame)
{
	for(map<Aig_Obj_t*, Aig_Obj_t*>::iterator map_it = Output_Object_to_RHS_of_PrimaryOutputs.begin(); map_it != Output_Object_to_RHS_of_PrimaryOutputs.end(); map_it++)
	{
		Aig_Obj_t* output_obj = map_it->first;
		Aig_Obj_t* output = map_it->second;
				
		Aig_Obj_t* output_after_replacement;
		output_after_replacement = replaceVariablesByFormulas(output, variable_to_skolem_function_map);
		assert(output_after_replacement != NULL);
				
		map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(output_obj->Id);
		assert(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end());
		string output_name = Ci_id_to_Ci_name_map_it->second;

		assert(output_name.find(CIRCUITOUTPREFIX) != string::npos);

		int first_location = output_name.find_last_of("_");
		string first_index_string = output_name.substr(first_location+1);
		output_name = "primaryout_";
		output_name += first_index_string;

		Aig_Obj_t* output_after_replacement_CO = Aig_ObjCreateCo( pub_aig_manager, output_after_replacement ); 
		assert(output_after_replacement_CO != NULL);

		idName.insert(make_pair(output_after_replacement_CO->Id, output_name));			

		#ifdef DEBUG_SKOLEM
		cout << "\nInserted entry for " << output_name << " into  idName" << endl;		
		#endif	
	}

	#ifdef DEBUG_SKOLEM
	cout << "\nPrimary outputs added to idName" << endl;		
	#endif
			
	output_names.sort(compare_tsietin);

	number_of_state_elements = output_names.size();

	for(list<string>::iterator output_names_it = output_names.begin(); output_names_it != output_names.end(); output_names_it++)
	{
		string output_name = *output_names_it;
		map<string, Aig_Obj_t*>::iterator output_name_to_replaced_factor_it = output_name_to_replaced_factor.find(output_name);
		Aig_Obj_t* factor_after_replacement = output_name_to_replaced_factor_it->second;

		// factor after replacement is formula for a latchout
		Aig_Obj_t* factor_after_replacement_CO = Aig_ObjCreateCo( pub_aig_manager, factor_after_replacement ); 
		assert(factor_after_replacement_CO != NULL);

		idName.insert(make_pair(factor_after_replacement_CO->Id, output_name));

		#ifdef DEBUG_SKOLEM
		cout << "\nInserted entry for " << factor_after_replacement_CO->Id << " , " << output_name << " into  idName" << endl;		
		#endif

	}

	#ifdef DEBUG_SKOLEM
	cout << "\nOutputs added to idName" << endl;		
	#endif

	int i;
	Aig_Obj_t * pObj;
	Aig_ManForEachPiSeq(pub_aig_manager, pObj, i)
	{
		map<int, string>::iterator Ci_id_to_Ci_name_map_it = Ci_id_to_Ci_name_map.find(pObj->Id);
		assert(Ci_id_to_Ci_name_map_it != Ci_id_to_Ci_name_map.end());
		string input_name = Ci_id_to_Ci_name_map_it->second;

		if(input_name.find(LATCHPREFIX) != string::npos)
		{
			int first_location = input_name.find_last_of("_");
			string first_index_string = input_name.substr(first_location+1);
			input_name = "state_";
			input_name += first_index_string;

			idName.insert(make_pair(pObj->Id, input_name));

			#ifdef DEBUG_SKOLEM
			cout << "\nInserted entry for " << input_name << " into  idName" << endl;		
			#endif
		}
	}

	#ifdef DEBUG_SKOLEM
	cout << "\nInputs added to idName" << endl;		
	#endif

	#ifdef DEBUG_SKOLEM
	cout << "\nIdnames created" << endl;		
	#endif

	#ifdef DEBUG_SKOLEM
	cout << "\nidName.size() == " << idName.size();
	cout << "\toutput_names.size() == " << output_names.size();
	cout << "\toutput_name_to_replaced_factor.size() == " << output_name_to_replaced_factor.size() << endl;	
	showMap(idName, "idName");
	#endif
			
	Abc_Ntk_t* component_network = obtainNetworkFromFragmentOfAIGWithIdNames(pub_aig_manager, idName);
	//Abc_NtkMakeSequential(component_network, Abc_NtkPoNum(component_network));
	Abc_NtkMakeSequential(component_network, number_of_state_elements);
			
	// Let's look at the network
	abcFrame->pNtkCur = Abc_NtkDup(component_network);

	char verilog_file_char[100];
	string verilog_file = benchmark_name_without_extension;
	char iterations_of_loop_char[10];
	sprintf(iterations_of_loop_char, "%d", iterations_of_loop);
	string iterations_of_loop_string(iterations_of_loop_char);
	verilog_file += "_component";
	verilog_file += iterations_of_loop_string;
	verilog_file += ".v";

	string command = "write ";
	command += verilog_file;

	cout << command << endl;		
	if (abcObj->comExecute(abcFrame, command))
	{
		cout << "cannot execute command " << command << endl;
		assert(false);
	}

	assert(false);

}
