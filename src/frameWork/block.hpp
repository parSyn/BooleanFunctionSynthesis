/***************************************************************************************************************

FileName: Block.hpp
SystemName: ParSyn : Parallel Boolean Funciton Synthesis Tool/ Parallel Skolem Function Generation Tool.

Authors: Shetal Shah and Ajith John 
 
Affliation: IIT Bombay

Description: The file contains the code pertaining to a block : A block is a set of one or more nodes of a DAG. It is the basic unit of computation for 
Parallel Synthesis tool

************************************************************/
#include <iostream>
#include <string.h>
#include <set>

using namespace std;
class Block 
{
protected:
   int  Id;	
    int root;

public :
    set<int> dependsOnBlocks;	
  //  set<int> dependsOnNodes;
    set<int> dependeeBlocks;
    set<int> processedDependents;
    set<int> notSentResultYet;

//The following data structures are used by the master node. In worker nodes they are empty
    vector<unsigned char> and_r1;
    vector<unsigned char> and_r0;
    vector<unsigned char> or_r1;
    vector<unsigned char> or_r0;
   
   set<int> processHasResult;	//Contains the list of processors that  already have the results of this block

	Block()
	{
    		static int idcounter = 0; 
		Id = idcounter ++;
		//root = -1;
	}

	void clearBlock()
	{
		dependsOnBlocks.clear();
		dependeeBlocks.clear();
		processedDependents.clear();
		notSentResultYet.clear();
		and_r1.clear();
		and_r0.clear();
		or_r1.clear();
		or_r0.clear();
	}

	void setRoot (int r ) { root = r; } // cout << " setting root of block " << Id << " as " << root << endl; };

	void addDependentBlock (int d) { dependsOnBlocks.insert (d); } // cout << "inserting " << d.getRoot() << " in dependsOn " << root << endl;  } 
	void removeDependentBlock (int d) { dependsOnBlocks.erase(d); } 
	bool noDependentBlocks ( ) { return dependsOnBlocks.empty ();}
	int numDependents () { return dependsOnBlocks.size();}
	
	void printDependentBlocks() const
	{
		cout << " dependent blocks for block id " << Id << " @ root " << root << " : " ;
		cout << " size " << dependsOnBlocks.size();
 
		for (std::set<int>::iterator it=dependsOnBlocks.begin(); it!=dependsOnBlocks.end(); ++it)
		{
			std::cout << ' ' << (*it);
		}
		cout << endl;
	}
	void printProcessedDependents() const
	{
		cout << " processed dependent for block id " << Id << " @ root " << root << " : " ;
		cout << " size " << processedDependents.size() << " " ;
 
		for (std::set<int>::iterator it=processedDependents.begin(); it!=processedDependents.end(); ++it)
		{
			cout << ' ' << (*it);
		}
		cout << endl;
	}

	int getId ()	{ return Id; }
	int getRoot () { 
	        return root; }

	void addDependeeBlock (int d) { dependeeBlocks.insert (d); } 
	void removeDependeeBlock (int d) { dependeeBlocks.erase(d); }
	bool anyPendingDependeeBlocks ( ) { return dependeeBlocks.empty ();}
	int numDependees ()	{return dependeeBlocks.size();}
	bool operator< (const Block &b1) const { return Id < b1.Id;}
	void store_and_r1 (vector<unsigned char>& v) { and_r1 = v;}
	void store_and_r0 (vector<unsigned char>& v) { and_r0 = v;}
	void store_or_r1 (vector<unsigned char>& v) { or_r1 = v;}
	void store_or_r0 (vector<unsigned char>& v) { or_r0 = v;}
	int get_and_r1_size ( ) {return and_r1.size();}
	int get_and_r0_size ( ) {return and_r0.size();}
	int get_or_r1_size ( ) {return or_r1.size();}
	int get_or_r0_size ( ) {return or_r0.size();}

};

ostream& operator<<(ostream& os, Block& b) 
{
	os <<  " root " << b.getRoot() << endl;
	return os;
}
