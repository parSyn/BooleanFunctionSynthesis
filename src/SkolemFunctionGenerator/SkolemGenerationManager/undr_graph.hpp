/***************************************************************************
FileName : undr_graph.hpp

SystemName: ParSyn : Parallel Boolean Funciton Synthesis Tool/ Parallel Skolem Function Generation Tool.

Description: This file along with undr_graph.cpp defines class UndrGraph, an implementation of undirected graphs

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

#ifndef UNDRGRAPH_HPP
#define	UNDRGRAPH_HPP

#include <iostream>
#include <list>
#include <vector>
#include <stack>
#include <set>
#include <algorithm>
#include <assert.h>
#include <limits.h>

//#define DEBUG_UNDRGRAPH

using namespace std;

// Class for an undirected graph
class UndrGraph
{
    int V;    // No. of vertices
    vector< list<int> > adj;    // Vector of adjacency lists
    vector< double > weight; // weights of vertices
    
    bool isCyclicUtil(int v, vector<bool> &visited, int parent, set<int> &disabled_nodes);
    bool findSemiDisjointCycleUtil(int v, vector<bool> &visited, int parent, list<int> &semi_disjoint_cycle, stack<int> &mystack);
    bool edgeExists(int v, int w); // returns true if edge exists between v and w
    bool obtainCycleFromStack(stack<int> &mystack, list<int> &cycle, int end);
    bool cycleIsSemidisjoint(list<int> &cycle);
    void findNeighbours(int v, set<int> &neighbours);
    bool deleteEdge(int v, int w);
    void initializeWeights(double wt); // set the weights of all vertices to wt
    void showMySet(set<int> &integer_set, string who_am_i);
    void showMyList(list<int> &integer_list, string who_am_i);
    
public:
    UndrGraph(int V);   // Constructor
    void addEdge(int v, int w);   // to add an edge to graph
    bool isCyclic(set<int> &disabled_nodes);   // returns true if there is a cycle
    bool isFVS(set<int> &fvs);   // returns true if the parameter is an fvs
    bool findSemiDisjointCycle(list<int> &semi_disjoint_cycle); // finds a semi-disjoint cycle in semi_disjoint_cycle; returns false if semi-disjoint cycle does not exist
    void cleanup();
    void showGraph();
    bool empty();  
    void findCandidateFVS(set<int> &candidate_fvs, stack<int> &fvs_stack); // first loop in Bafna's algorithm to find FVS 
    int degree(int v);
    void deleteVertex(int v);

    int size();
    bool deadNodes(set<int> &dead_nodes); // find the dead nodes i.e. nodes with no edges in the graph. returns true if all the nodes are dead; else returns false
    int findCentreNodeOfTree(int u, vector<bool> &visited);  
    bool locateCentreNodeInAPathInTree(int current, int parent, int diameter, int path_end, int &centre, stack<int> &path_stack);
    void findFarthestNodeInTree(int current, int parent, int depth, int &deepest, int &maximum_depth, vector<bool> &visited); 
};

#endif	/* UNDRGRAPH_HPP */
