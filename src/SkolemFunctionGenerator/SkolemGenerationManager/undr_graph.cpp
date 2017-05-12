/***************************************************************************
FileName : undr_graph.cpp

SystemName: ParSyn : Parallel Boolean Funciton Synthesis Tool/ Parallel Skolem Function Generation Tool.

Authors: Ajith John
 
Affliation: IIT Bombay

Description: This file along with undr_graph.hpp defines class UndrGraph, an implementation of undirected graphs
************************************************************/

#include "undr_graph.hpp"

UndrGraph::UndrGraph(int V)
{
    assert(V > 0);

    this->V = V;
    for(int i = 0; i < V; i++)
    {
	list<int> adj_list;
	adj.push_back(adj_list);
    }

}

 
bool UndrGraph::edgeExists(int v, int w)
{
    list<int>::iterator i;
    for (i = adj[v].begin(); i != adj[v].end(); ++i)
    {
	if (*i == w)
	{
		return true;
	}
    }
    
    return false;
}


void UndrGraph::addEdge(int v, int w)
{
    assert(v >= 0 && v < V);
    assert(w >= 0 && w < V);

    if(!edgeExists(v, w))
    {
	    adj[v].push_back(w); // Add w to v’s list.
	    adj[w].push_back(v); // Add v to w’s list.

	    #ifdef DEBUG_UNDRGRAPH
	    cout << "\nEdge created between " << v << " and " << w << endl;
	    #endif
    }
    else
    {
	   #ifdef DEBUG_UNDRGRAPH
	   cout << "\nEdge already exists between " << v << " and " << w << endl;
	   #endif
    } 
}


int UndrGraph::degree(int v)
{
	return adj[v].size();
}



// A recursive function that uses visited[] and parent to detect
// cycle in subgraph reachable from vertex v.
bool UndrGraph::isCyclicUtil(int v, vector<bool> &visited, int parent, set<int> &disabled_nodes)
{
    // Mark the current node as visited
    visited[v] = true;
 
    // Recur for all the vertices adjacent to this vertex
    list<int>::iterator i;
    for (i = adj[v].begin(); i != adj[v].end(); ++i)
    {
	// If an adjacent is disabled, don't consider it
	if(disabled_nodes.find(*i) != disabled_nodes.end())
	{
		continue;
	}
        // If an adjacent is not visited, then recur for that adjacent
        if (!visited[*i])
        {
           if (isCyclicUtil(*i, visited, v, disabled_nodes))
              return true;
        }
 
        // If an adjacent is visited and not parent of current vertex,
        // then there is a cycle.
        else if (*i != parent)
	{
           return true;
	}
    }
    return false;
}
 
// Returns true if the graph contains a cycle, else false.
bool UndrGraph::isCyclic(set<int> &disabled_nodes)
{
    // Mark all the vertices as not visited and not part of recursion
    // stack
    vector<bool> visited;
    for(int i = 0; i < V; i++)
    {
	visited.push_back(false);
    }
 
 
    // Call the recursive helper function to detect cycle in different
    // DFS trees
    for (int u = 0; u < V; u++)
        if (disabled_nodes.find(u) == disabled_nodes.end() && !visited[u]) // Don't recur for u if it is already visited or is disabled
          if (isCyclicUtil(u, visited, -1, disabled_nodes))
             return true;
 
    return false;
}



bool UndrGraph::isFVS(set<int> &fvs)
{
	if(!isCyclic(fvs))
	{
		return true;
	}
	else
	{
		return false;
	}
}


bool UndrGraph::findSemiDisjointCycleUtil(int v, vector<bool> &visited, int parent, list<int> &semi_disjoint_cycle, stack<int> &mystack)
{
    #ifdef DEBUG_UNDRGRAPH
    cout << "\nNode " << v << " encountered\n";
    #endif

    visited[v] = true;
    mystack.push(v);
 
    // Recur for all the vertices adjacent to this vertex
    list<int>::iterator i;
    for (i = adj[v].begin(); i != adj[v].end(); ++i)
    {

	#ifdef DEBUG_UNDRGRAPH
	cout << "\nv = " << v << "\ti = " << *i << "\n";
	#endif

        // If an adjacent is not visited, then recur for that adjacent
        if (!visited[*i])
        {
	   #ifdef DEBUG_UNDRGRAPH
	   cout << "\n" << *i << "is not visited; recursively calling on it\n";
	   #endif

           if (findSemiDisjointCycleUtil(*i, visited, v, semi_disjoint_cycle, mystack))
	   {
	      mystack.pop();
              return true;
	   }
        }//// If an adjacent is not visited ends here 
        // If an adjacent is visited and not parent of current vertex,
        // then there is possibly cycle.
        else if (*i != parent)
	{
	   #ifdef DEBUG_UNDRGRAPH
	   cout << "\n*i != parent\n";
	   #endif

	   // obtain cycle by going into the stack upto *i
	   list<int> cycle;
	   bool cycle_encountered = obtainCycleFromStack(mystack, cycle, *i);

	   if(cycle_encountered)
	   {
		   #ifdef DEBUG_UNDRGRAPH
		   cout << "\nCycle encountered\n";
		   #endif

		   if(cycleIsSemidisjoint(cycle))
		   {
			#ifdef DEBUG_UNDRGRAPH
			cout << "\nCycle is semi-disjoint\n";
			#endif

			// copy the semidisjoint-cycle in semi_disjoint_cycle
			semi_disjoint_cycle = cycle;
			mystack.pop();
			return true;
		   }//if(cycleIsSemidisjoint(cycle)) ends here
		   else
		   {
			#ifdef DEBUG_UNDRGRAPH
			cout << "\nCycle is NOT semi-disjoint\n";
			#endif
		   }// else of if(cycleIsSemidisjoint(cycle)) ends here
	   }//if(cycle_encountered) ends here
	   else
	   {
		#ifdef DEBUG_UNDRGRAPH
		cout << "\nIt is NOT a cycle\n";
		#endif
	   }// else of if(cycle_encountered) ends here  

        }//if (*i != parent) ends here
        else
	{
	  #ifdef DEBUG_UNDRGRAPH
	  cout << "\n*i == parent && *i is visited\n";
	  #endif
	}

    }
    
    #ifdef DEBUG_UNDRGRAPH
    cout << "\nmystack.top() = " << mystack.top() << endl;
    #endif

    mystack.pop();
    return false;
}



bool UndrGraph::obtainCycleFromStack(stack<int> &mystack, list<int> &cycle, int end)
{
        bool cycle_encountered;

	stack<int> temp_stack;
	while(!mystack.empty())
	{
		int node = mystack.top();
		if(node == end)
		{
			break;
		}
		else
		{
			mystack.pop();
	
			cycle.push_back(node);
			temp_stack.push(node);	
		}		
	}
	cycle.push_back(end);

	if(mystack.empty()) // we emptied out the stack; no end found; i.e. cycle not correct
	{
		cycle_encountered = false;
	}
	else if(mystack.top() == end) // cycle encountered
	{
		cycle_encountered = true;
	}

	// put the elements back into mystack
	while(!temp_stack.empty())
	{
		int node = temp_stack.top();
		temp_stack.pop();
		mystack.push(node);			
	}

	#ifdef DEBUG_UNDRGRAPH
	if(cycle_encountered)
	{
		cout << "\nCycle found is: ";
		list<int>::iterator i;
		for (i = cycle.begin(); i != cycle.end(); ++i)
	    	{
			cout << *i << ", ";
		}
		cout << endl;
	}
	else
	{
		cout << "\nIt is not a cycle\n";
	}
	#endif

	return cycle_encountered;
	
}


bool UndrGraph::cycleIsSemidisjoint(list<int> &cycle)
{
	int number_of_nodes_with_high_degree = 0;

	list<int>::iterator i;
	for (i = cycle.begin(); i != cycle.end(); ++i)
    	{
		if(degree(*i) < 2)
		{
			cout << "\nSemiDisjointCycle finding tried on Unclean Graph\n";
			assert(false);
		}		
		else if(degree(*i) > 2)
		{
			number_of_nodes_with_high_degree++;
		}
	}

	if(number_of_nodes_with_high_degree <= 1)
	{
		return true;
	}
	else
	{
		return false;
	}
}

 

bool UndrGraph::findSemiDisjointCycle(list<int> &semi_disjoint_cycle)
{
    // Mark all the vertices as not visited and not part of recursion
    // stack
    vector<bool> visited;
    for(int i = 0; i < V; i++)
    {
	visited.push_back(false);
    }
 
 
    stack<int> mystack;
    for (int u = 0; u < V; u++)
    {
	#ifdef DEBUG_UNDRGRAPH
	cout << "\nroot_node_u = " << u << endl;
	#endif

        if (!visited[u]) // Don't recur for u if it is already visited
	{
	  assert(mystack.empty());

          if (findSemiDisjointCycleUtil(u, visited, -1, semi_disjoint_cycle, mystack))
             return true;
	}
    }
 
    return false;
}


void UndrGraph::findNeighbours(int v, set<int> &neighbours)
{
    list<int>::iterator i;
    for (i = adj[v].begin(); i != adj[v].end(); ++i)
    {
	neighbours.insert(*i);
    }	
}


bool UndrGraph::empty()
{
	bool graph_is_empty = true;
	for(int i = 0; i < V; i++)
	{
		if(degree(i) != 0)
		{
			graph_is_empty = false;
		}
	}
	return graph_is_empty;	
}
 

void UndrGraph::cleanup()
{
	set<int> nodes_to_delete;
	// nodes to delete = nodes with degree as 1
	for(int i = 0; i < V; i++)
	{
		if(degree(i) == 1)
		{
			nodes_to_delete.insert(i);
		}
	}

	#ifdef DEBUG_UNDRGRAPH
	showMySet(nodes_to_delete, "nodes_to_delete");
	#endif

	while(!nodes_to_delete.empty())
	{
		// find neighbours of nodes to delete
		set<int> neighbours;
		for(set<int>::iterator node_it = nodes_to_delete.begin(); node_it != nodes_to_delete.end(); node_it++)
		{
			int node = *node_it;
			set<int> neighbours_of_node;
			findNeighbours(node, neighbours_of_node);
			assert(neighbours_of_node.size() == 1);

			set_union(neighbours.begin(), neighbours.end(), neighbours_of_node.begin(), neighbours_of_node.end(),inserter(neighbours, neighbours.begin()));
		}

		#ifdef DEBUG_UNDRGRAPH
		showMySet(neighbours, "neighbours");
		#endif

		// delete the nodes to delete
		for(set<int>::iterator node_it = nodes_to_delete.begin(); node_it != nodes_to_delete.end(); node_it++)
		{
			int node = *node_it;
			#ifdef DEBUG_UNDRGRAPH	
			cout << "\nDeleting node " << node << endl;
			#endif
			deleteVertex(node);
		}		
		nodes_to_delete.clear();

		#ifdef DEBUG_UNDRGRAPH	
		cout << "\nNode deletion done" << endl;
		#endif		

		// nodes to delete = neighbours of deleted nodes with degree as 1
		for(set<int>::iterator node_it = neighbours.begin(); node_it != neighbours.end(); node_it++)
		{
			int neighbour = *node_it;
			if(degree(neighbour) == 1)
			{
				nodes_to_delete.insert(neighbour);
			}
		}

		#ifdef DEBUG_UNDRGRAPH
		showMySet(nodes_to_delete, "nodes_to_delete");
		#endif
	}//while(!nodes_to_delete.empty()) ends here
}


void UndrGraph::deleteVertex(int v)
{
	set<int> neighbours;
	findNeighbours(v, neighbours);

	#ifdef DEBUG_UNDRGRAPH
	cout << "\nv = " << v << endl;
	showMySet(neighbours, "neighbours");
	#endif

	for(set<int>::iterator neighbours_it = neighbours.begin(); neighbours_it != neighbours.end(); neighbours_it++)
	{
		int w = *neighbours_it;
		bool edge_exists = deleteEdge(v, w);
		assert(edge_exists);
	}	
}


bool UndrGraph::deleteEdge(int v, int w)
{

	#ifdef DEBUG_UNDRGRAPH
	cout << "\ndeleting edge between " << v << " and " << w << endl;
	#endif

	bool one_side_edge_exists = false;

	list<int>::iterator i;
    	for (i = adj[v].begin(); i != adj[v].end(); ++i)
    	{
		if (*i == w)
		{
			one_side_edge_exists = true;
			break;
		}
   	}
	if(one_side_edge_exists)
	{
		adj[v].erase(i);
	}

	bool other_side_edge_exists = false;
	list<int>::iterator j;
    	for (j = adj[w].begin(); j != adj[w].end(); ++j)
    	{
		if (*j == v)
		{
			other_side_edge_exists = true;
			break;
		}
   	}
	if(other_side_edge_exists)
	{
		adj[w].erase(j);
	}

	assert(one_side_edge_exists == other_side_edge_exists);

	return one_side_edge_exists;		
}


void UndrGraph::showGraph()
{
	cout << "\n\nPresent graph is";
	for(int i = 0; i < V; i++)
	{
		cout << "\n\nVertex: " << i << "\nAdjacent vertices: ";

		set<int> neighbours;
		findNeighbours(i, neighbours);
		for(set<int>::iterator neighbours_it = neighbours.begin(); neighbours_it != neighbours.end(); neighbours_it++)
		{
			int w = *neighbours_it;
			cout << w << ",";
		}
	}

	if(V == weight.size())
	{
		for(int i = 0; i < V; i++)
		{
			cout << "\n\nVertex: " << i << "\thas weight " << weight[i];
		}
	}	
}


void UndrGraph::initializeWeights(double wt)
{
	for(int i = 0; i < V; i++)
	{
		weight.push_back(wt);
	}
}


void UndrGraph::findCandidateFVS(set<int> &candidate_fvs, stack<int> &fvs_stack)
{
	initializeWeights(1); // forall v. weight(v) = 1
	candidate_fvs.clear(); // candidate_fvs = {}

	#ifdef DEBUG_UNDRGRAPH
	cout << "\nAfter initialization\n";
	showGraph();
	#endif

	cleanup();

	#ifdef DEBUG_UNDRGRAPH
	cout << "\nAfter first cleanup\n";
	showGraph();
	#endif

	while(!empty())
	{
		#ifdef DEBUG_UNDRGRAPH
		cout << "\nGraph is NOT empty\n";
		#endif

		list<int> semi_disjoint_cycle;
		bool semi_disjoint_cycle_exists = findSemiDisjointCycle(semi_disjoint_cycle);

		if(semi_disjoint_cycle_exists)
		{
			#ifdef DEBUG_UNDRGRAPH
			showMyList(semi_disjoint_cycle, "semi_disjoint_cycle");
			#endif

			assert(semi_disjoint_cycle.size() >= 3);

			// gamma = minimum among the weights of vertices in semi_disjoint_cycle
			list<int>::iterator it = semi_disjoint_cycle.begin();
			double gamma = weight[*it];
			it++;
			for(;it != semi_disjoint_cycle.end(); it++)
			{
				if(weight[*it] < gamma)
				{
					gamma = weight[*it];
				}
			}

			#ifdef DEBUG_UNDRGRAPH
			cout << "\ngamma = " << gamma << endl;
			#endif
			
			// weight of each vertex v in semi_disjoint_cycle becomes present weight - gamma
			it = semi_disjoint_cycle.begin();
			for(;it != semi_disjoint_cycle.end(); it++)
			{
				weight[*it] = weight[*it] - gamma;
			}

			#ifdef DEBUG_UNDRGRAPH
			cout << "\nAfter changing weights\n";
			showGraph();
			#endif
			
		}//if(semi_disjoint_cycle_exists) ends here
		else
		{
			#ifdef DEBUG_UNDRGRAPH
			cout << "\nNo semi-disjoint cycle found\n";
			#endif
			
			// gamma = minimum among (weight(u)/(degree(u)-1)) for each vertex u in the graph
			double gamma = (double)ULONG_MAX; // some large number to initialize
			for(int u = 0; u < V; u++)
			{
				int d_u = degree(u);
				if(d_u == 0) // deleted node
				{
					continue;
				}
				assert(d_u >= 2); // graph is clean

				double my_gamma = weight[u]/(double)(d_u-1);
				if(my_gamma < gamma)
				{
					gamma = my_gamma;
				}
			}
			
			#ifdef DEBUG_UNDRGRAPH
			cout << "\ngamma = " << gamma << endl;
			#endif

			// weight of each vertex u in the graph becomes present weight - gamma.(d_u-1)
			for(int u = 0; u < V; u++)
			{
				int d_u = degree(u);
				if(d_u == 0) // deleted node
				{
					continue;
				}
				assert(d_u >= 2); // graph is clean

				weight[u] = weight[u] - (gamma * (double)(d_u-1));
			}

			#ifdef DEBUG_UNDRGRAPH
			cout << "\nAfter changing weights\n";
			showGraph();
			#endif
			
		}//else of if(semi_disjoint_cycle_exists) ends here

		#ifdef DEBUG_UNDRGRAPH
		cout << "\nDeleting vertices with zero weight\n";
		#endif

		// find vertices with zero weight
		set<int> vertices_with_zero_weight;
		for(int u = 0; u < V; u++)
		{
			if(degree(u) == 0) // deleted node
			{
				continue;
			}	
			
			if(weight[u] == 0)
			{
				vertices_with_zero_weight.insert(u);				
			}
		}

		// delete vertices with zero weight and add into candidate_fvs and fvs_stack
		for(set<int>::iterator vertex_it = vertices_with_zero_weight.begin(); vertex_it != vertices_with_zero_weight.end(); vertex_it++)
		{
			int u = *vertex_it;
			candidate_fvs.insert(u);
			fvs_stack.push(u);
			
			deleteVertex(u);
		}

		#ifdef DEBUG_UNDRGRAPH
		cout << "\nAfter deletion of vertices with zero weight\n";
		showGraph();
		showMySet(candidate_fvs, "candidate_fvs");
		#endif

		// again cleanup
		cleanup();

		#ifdef DEBUG_UNDRGRAPH
		cout << "\nAfter cleanup\n";
		#endif		

	}//while(!empty()) ends here

	#ifdef DEBUG_UNDRGRAPH
	cout << "\nGraph is empty\n";
	showMySet(candidate_fvs, "candidate_fvs");
	#endif
}


void UndrGraph::showMySet(set<int> &integer_set, string who_am_i)
{
	cout << endl << endl << who_am_i << endl << endl;

	for(set<int>::iterator integer_it = integer_set.begin(); integer_it != integer_set.end(); integer_it++)
	{
		cout << *integer_it << ", ";
	}

	cout << endl;

}


void UndrGraph::showMyList(list<int> &integer_list, string who_am_i)
{
	cout << endl << endl << who_am_i << endl << endl;

	for(list<int>::iterator integer_it = integer_list.begin(); integer_it != integer_list.end(); integer_it++)
	{
		cout << *integer_it << ", ";
	}

	cout << endl;

}


int UndrGraph::size()
{
	return V;
}


bool UndrGraph::deadNodes(set<int> &dead_nodes)
{
	dead_nodes.clear();
	bool graph_is_empty = true;

	for(int i = 0; i < V; i++)
	{
		if(degree(i) == 0)
		{
			dead_nodes.insert(i);
		}
		else
		{
			graph_is_empty = false;
		}
	}

	return graph_is_empty;	
}


void UndrGraph::findFarthestNodeInTree(int current, int parent, int depth, int &deepest, int &maximum_depth, vector<bool> &visited)
{
    if(depth > maximum_depth)
    {
	maximum_depth = depth;
	deepest = current;
    }

    // Mark the current node as visited
    visited[current] = true;
 
    // Recur for all the vertices adjacent to this vertex
    list<int>::iterator i;
    for (i = adj[current].begin(); i != adj[current].end(); ++i)
    {
        if (*i != parent)
        {
        	  findFarthestNodeInTree(*i, current, depth+1, deepest, maximum_depth, visited);
        } 
    }
}


bool UndrGraph::locateCentreNodeInAPathInTree(int current, int parent, int diameter, int path_end, int &centre, stack<int> &path_stack)
{
    path_stack.push(current);

    if(current == path_end)//path found!!
    {
	// get the middle node in the path
	while(diameter > 0)
	{
		assert(!path_stack.empty());
		path_stack.pop();
		diameter = diameter - 1;
	}

	assert(!path_stack.empty());
	centre = path_stack.top();
	return true;
    }
    else
    {
 
    	// Recur for all the vertices adjacent to this vertex
    	list<int>::iterator i;
    	for (i = adj[current].begin(); i != adj[current].end(); ++i)
    	{
        	if (*i != parent)
        	{
        	  	if(locateCentreNodeInAPathInTree(*i, current, diameter, path_end, centre, path_stack))
		  	{
				return true;
		  	}
        	} 
    	}

    	path_stack.pop();
    	return false;
    }
}


int UndrGraph::findCentreNodeOfTree(int u, vector<bool> &visited)
{
	int v;
	int distance_from_u_to_v;

	#ifdef DEBUG_UNDRGRAPH
	cout << "\nu = " << u << endl;
	#endif
	
	v = u;
	distance_from_u_to_v = 0;
	findFarthestNodeInTree(u, -1, 0, v, distance_from_u_to_v, visited);

	#ifdef DEBUG_UNDRGRAPH
	cout << "\nv = " << v << "\tdistance_from_u_to_v = " << distance_from_u_to_v << endl;
	#endif

	int w;
	int distance_from_v_to_w;	

	w = v;
	distance_from_v_to_w = 0;
	findFarthestNodeInTree(v, -1, 0, w, distance_from_v_to_w, visited);	

	#ifdef DEBUG_UNDRGRAPH
	cout << "\nw = " << w << "\tdistance_from_v_to_w = " << distance_from_v_to_w << endl;
	#endif

	int diameter = distance_from_v_to_w/2;

	#ifdef DEBUG_UNDRGRAPH
	cout << "\ndiameter = " << diameter << endl;
	#endif

	stack<int> path_stack;
	int centre;
	bool centre_found = locateCentreNodeInAPathInTree(v, -1, diameter, w, centre, path_stack);
	assert(centre_found);

	#ifdef DEBUG_UNDRGRAPH
	cout << "\ncentre = " << centre << endl;
	#endif
	
	return centre;
}
 

