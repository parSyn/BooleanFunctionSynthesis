/***************************************************************************
FileName : main.cc

SystemName: ParSyn : Parallel Boolean Funciton Synthesis Tool/ Parallel Skolem Function Generation Tool.
Boolean Function Synthesis and Skolem Function Generation are essentially the same problems :). Both terms are used in the code

Description: This file contains the code to synthesize boolean functions in parallel - specifically it contains the code required to schedule the computation of r0 and r1 sets of each node of the AIG on worker nodes.

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

#include <iostream>
#include <fstream>
#include <string.h>
#include <set>
#include<map>
#include<queue>
#include <boost/mpi.hpp>
#include<boost/serialization/serialization.hpp>
#include<boost/serialization/vector.hpp>
#include <assert.h>
#include<time.h>
#include "block.hpp"

//Required to call Sequential Boolean Function Generator code
#include "AIGBasedSkolem.hpp"

//#define VERBOSE
//#define PREPROCESS_INFO
//#define PRINT_STATISTICS
//#define VERIFY_SKOLEM
//#define CONVERT_DEBUG
//#define USE_GIA
//#define SCHED_DEBUG
//#define ENCODE_DEBUG
//#define COMM_DEBUG
#define MEM_OPT
//#define PRINT_TOTAL_TIME_BREAKUP
//#define RUN_AS_SEQUENTIAL
//#define DEBUG_PRINT_SK

using namespace std;
namespace mpi=boost::mpi;
using namespace mpi;

enum message_tags {process_block, result_data_and_r1, result_data_and_r0, result_data_or_r1, result_data_or_r0, store_data, store_data_and_r1, store_data_and_r0, store_data_or_r1, store_data_or_r0, finalize};
//Reason for so many result_data and store_data tags is because async mpi with serialization does not work if you have multiple outstanding sends and recvs with the same tags between the same 2 nodes.
//I kept getting a message truncation error. For more see http://stackoverflow.com/questions/21889426/boostmpi-throws-mpi-err-truncate-on-multiple-isend-irecv-transfers-with-same-t
extern "C"
{
#include "src/base/abc/abc.h"
#include "src/base/main/mainInt.h"
#include "src/aig/aig/aig.h"
#include "src/aig/gia/gia.h"
#include "src/aig/gia/giaAig.h"
void   Abc_Start();
void   Abc_Stop();
Abc_Frame_t* Abc_FrameGetGlobalFrame();
int Cmd_CommandExecute( Abc_Frame_t * pAbc, const char* Command );
Aig_Man_t * Abc_NtkToDar(Abc_Ntk_t *pNtk, int, int);
void Aig_ManShow(Aig_Man_t *pAig, int , Vec_Ptr_t *);

}

int readCleanAig(Abc_Frame_t * pAbc, const char* pFileName)
{
    
    char Command[1000];

   
#ifdef USE_GIA
    sprintf( Command, "&r %s ", pFileName );
#else
    sprintf( Command, "read %s ", pFileName );
#endif
    if ( Cmd_CommandExecute( pAbc, Command ) )
    {
        fprintf( stdout, "Cannot execute command \"%s\".\n", Command );
        return 1;
    }

    

#ifdef USE_GIA
    sprintf( Command, "&st;    &scl ");
#else
    sprintf( Command, "strash -c ");
#endif
    if ( Cmd_CommandExecute( pAbc, Command ) )
    {
        fprintf( stdout, "Cannot execute command \"%s\".\n", Command );
        return 1;
    }
    
#ifdef USE_GIA
    sprintf( Command, "&b; &syn4; &b" );	//resyn2

#else
//    sprintf( Command, "fraig;  balance; rewrite -l; refactor -l; balance; rewrite -l; rewrite -lz; balance; refactor -lz; rewrite -lz; balance; print_stats" );	//resyn2

    sprintf( Command, "fraig; balance; rewrite -l; rewrite -lz; balance; rewrite -lz; balance; rewrite -l; refactor -l; balance; rewrite -l; rewrite -lz; balance; refactor -lz; rewrite -lz; balance " );	//fraig, resyn, resyn2
#endif
    if ( Cmd_CommandExecute( pAbc, Command ) )
    {
        fprintf( stdout, "Cannot execute command \"%s\".\n", Command );
        return 1;
    }
    return 0;
}
void printVector (vector<unsigned char> v, string name)
{
	cout << name << ":" ;
	for (unsigned int i = 0; i < v.size(); i++)
		cout << "  " << (unsigned) v[i] ;
	cout << endl;

}
void Io_WriteAigerEncode( vector<unsigned char>& pBuffer, unsigned int x )	//Copied from ABC - ioWriteAiger.c
{
    unsigned char ch;
#ifdef ENCODE_DEBUG
    cout << " Representing  " << x << " as " ;
#endif
    while (x & ~0x7f)
    {
        ch = (x & 0x7f) | 0x80;
	pBuffer.push_back(ch);

#ifdef ENCODE_DEBUG
	cout <<  " " << (unsigned) ch;
#endif
      //  pBuffer[Pos++] = ch;
        x >>= 7;
    }
    ch = x;
    pBuffer.push_back(ch);
#ifdef ENCODE_DEBUG
    cout <<  " " <<(unsigned) ch << endl;
#endif
   // pBuffer[Pos++] = ch;
}

/* Do a dfs on pObj. Add nodes as you encounter them in the reverse direction (bottom-up) */

void encodeAigObj_rec (Aig_Man_t * p, Aig_Obj_t* pObj, bool isRoot,  vector<unsigned char>& subTreeAig)
{

  unsigned int uLit = Aig_ObjToLit(pObj);

   if(Aig_IsComplement(pObj))
	pObj = Aig_Regular(pObj);

   assert (!Aig_ObjIsCo(pObj));
	
//Node has appeared before. Or is a ci or is const1.
    if ( Aig_ObjIsTravIdCurrent(p, pObj) || Aig_ObjIsCi(pObj) || Aig_ObjIsConst1(pObj))	//No need to list the CI's. The CI's will be the same across all nodes.
    {
	if (isRoot)
	{
		Io_WriteAigerEncode(subTreeAig, uLit + 2);

		Io_WriteAigerEncode(subTreeAig, 0);	//Indicating that it is a single literal
    		if (Aig_ObjIsCi(pObj) || Aig_ObjIsConst1(pObj))	
    			Aig_ObjSetTravIdCurrent(p, pObj);
#ifdef ENCODE_DEBUG
	cout << "Added @ " <<  " [" << uLit << "," << 0 << "]" << endl;
#endif
	}

	return;
    }

    Aig_ObjSetTravIdCurrent(p, pObj);

    assert(Aig_ObjIsNode(pObj));

    encodeAigObj_rec(p, Aig_ObjFanin0(pObj), false, subTreeAig);
    encodeAigObj_rec(p, Aig_ObjFanin1(pObj), false, subTreeAig);

    Io_WriteAigerEncode(subTreeAig, uLit + 2);

        unsigned int uLit0 = Aig_ObjToLit(Aig_ObjChild0(pObj));
        unsigned int uLit1 = Aig_ObjToLit(Aig_ObjChild1(pObj));
        if ( uLit1 > uLit0 )
        {
            unsigned int Temp = uLit0;
            uLit0 = uLit1;
            uLit1 = Temp;
        }
	
	assert (uLit > uLit0);
	assert (uLit0 > uLit1);
	
	Io_WriteAigerEncode(subTreeAig, (unsigned) uLit - uLit0);
	Io_WriteAigerEncode(subTreeAig, (unsigned) uLit0 - uLit1);
	
#ifdef ENCODE_DEBUG
	cout << "Added @ " <<  " [" << uLit << "," << uLit0 << ","<< uLit1 <<"]" << endl;
#endif
}


int Io_ReadAigerDecode( vector<unsigned char>& pBuffer, int& index)
{
    unsigned x = 0, i = 0;
    unsigned char ch;

//    while ((ch = getnoneofch (file)) & 0x80)
    while ((ch = pBuffer[index++]) & 0x80)
        x |= (ch & 0x7f) << (7 * i++);

    int val = x | (ch << (7 * i));
#ifdef CONVERT_DEBUG
    cout << " Returning val " << val << endl;
#endif
    return val;
}
//Very convoluted. Converts a vector of ints to a vector of Aig_Obj_t. Deserialization
void convertIntArrayToAigObj (Aig_Man_t* pMan, vector<unsigned char> &subTreeAig, vector<Aig_Obj_t*>& rootVec, vector<Aig_Obj_t*>& createdCos, bool isSkolem)
{
//	printVector (subTreeAig, "convert");
	int i = 0;
	Aig_Obj_t *pObjC1,*pObj, *pObjC0;
	
	map<int, Aig_Obj_t *> intNodeMap;
	
	int cLit0, cLit1, lit, posLit;

	int nElems = subTreeAig.size();

	bool c0Comp = false, c1Comp = false;
	while (i < nElems)
	{
	       
	       c0Comp = false;
	       c1Comp = false;

	       lit = Io_ReadAigerDecode(subTreeAig, i) - 2; 	//Currently, this node will not be complemented

	       assert (lit >= 0);
	       cLit0 =Io_ReadAigerDecode(subTreeAig, i); 	//Difference between lhs and rhs0
	      // cLit0 = subTreeAig[i++];
#ifdef CONVERT_DEBUG
		cout << "Processing " ;
		cout << "[ " << lit << "," << cLit0 << "]" << endl;
#endif
		
		if ((lit & 1 ) > 0)
			posLit = lit - 1;
		else
			posLit = lit;

		if (cLit0 == 0)	//The node is an CI or const1 or a node which has been seen earlier
		{
			if (intNodeMap.count (posLit) > 0)
				pObj = intNodeMap[posLit];	//Node seen earlier
			else
				pObj = Aig_ObjFromLit(pMan, posLit);	
/*
			if (posLit == 0)
			{
				assert(Aig_ObjIsConst1(pObj));
				if (lit > 0)
					cout << " The literal is false " << endl;
			}
*/
			assert (pObj != NULL);
			if (intNodeMap.count (posLit) ==0)
				intNodeMap[posLit] = pObj;	//The object is always indexed on the positive literal.

			if (posLit != lit)
				pObj = Aig_Not(pObj);
		}
		else
		{
		       cLit0 = lit - cLit0;
	
		       cLit1 = cLit0 - Io_ReadAigerDecode(subTreeAig, i); 	
	#ifdef CONVERT_DEBUG
			cout << "Resulting [cLit0, cLit1] " << cLit0 << "," << cLit1;
	#endif
			if ((cLit0 & 1) > 0) 	//Child 0 is a complement
			{
				cLit0 --;	
				c0Comp = true;
			}

			if (intNodeMap.count(cLit0) > 0)
			{
				pObjC0 = intNodeMap[cLit0];
	#ifdef CONVERT_DEBUG
				cout << " Found child0 in intNodeMap " << Aig_ObjId(pObjC0) << endl;
	#endif
			}
			else
			{
				pObjC0 = Aig_ObjFromLit(pMan, cLit0);
	#ifdef CONVERT_DEBUG
				cout << " Found child0 in Aig " << Aig_ObjId(pObjC0) << endl;
	#endif
			}
					
		       //cLit1 =Io_ReadAigerDecode(subTreeAig, i) + lit; 	
			
			if ((cLit1 & 1 ) > 0) 	//Child 0 is a complement
			{
				cLit1 --;	
				c1Comp = true;
			}

			if (intNodeMap.count(cLit1) > 0)
			{
				pObjC1 = intNodeMap[cLit1];
	#ifdef CONVERT_DEBUG
				cout << "cLit1 = " << cLit1 << ".  Found child1 in intNodeMap " << Aig_ObjId(pObjC1) << endl;
	#endif
			}
			else
			{
				pObjC1 = Aig_ObjFromLit(pMan, cLit1);
	#ifdef CONVERT_DEBUG
				cout << "cLit1 = " << cLit1 << " Found child1 in Aig " << Aig_ObjId(pObjC1) << endl;
	#endif
			}
			if (c0Comp) { pObjC0 = Aig_Not(pObjC0); } // cout << " Child0 is complemented " << endl;
			if (c1Comp) {pObjC1 = Aig_Not(pObjC1);  } //cout << " Child1 is complemented " << endl; 

			pObj = Aig_And(pMan, pObjC0, pObjC1);	//Check if lit is positive?


			intNodeMap[posLit] = pObj;	//The object is always indexed on the positive literal.

			if (posLit != lit)
				pObj = Aig_Not(pObj);

	#ifdef CONVERT_DEBUG
			int pObjId = Aig_ObjId(pObj);
			cout << " Added " << pObjId << " to  intNodeMap " << posLit << endl;

			cout <<  Aig_ObjToLit (pObj) << " is the literal for " << lit << " AigObjID " << pObjId << endl;
	#endif
		}
		int old_index = i;
	       if( Io_ReadAigerDecode(subTreeAig, i) == 1)
	       {
			assert (pObj != NULL);

			if (isSkolem)
			{
				Aig_ObjCreateCo(pMan, Aig_Not(pObj));//If skolem functions are to be generated then create Co with \neg r1
				rootVec.push_back(Aig_Not(pObj));	
			}
			else
			{
				createdCos.push_back(Aig_ObjCreateCo(pMan, pObj));
				rootVec.push_back(pObj);	
			}
#ifdef CONVERT_DEBUG
			cout << "Added " << Aig_ObjId(Aig_Regular(pObj)) << " into the vector. Size " << rootVec.size() <<  endl;
#endif
	       }
	       else
			i= old_index;
	}

    // add
}

void encodeAigObj (Aig_Man_t* p, vector<Aig_Obj_t*>& rootArr,  vector<unsigned char>& subTreeAig)
{
	Aig_Obj_t *pObj;

	Aig_ManIncrementTravId( p );
	Aig_ObjSetTravIdCurrent( p, Aig_ManConst1(p) );

	for (std::vector<Aig_Obj_t* >::iterator vit = rootArr.begin() ; vit != rootArr.end(); ++vit)
	{
		pObj = *vit;

    		encodeAigObj_rec( p, pObj, true, subTreeAig);	//Added
		subTreeAig.push_back( 1 );
	}

//Checking for correctness of the encoding /decoding functions
/*
	vector<Aig_Obj_t *> tempVec;
	Aig_Obj_t * pObj1;
	convertIntArrayToAigObj(p, subTreeAig,  tempVec);
	assert (tempVec.size() == rootArr.size());
	for (unsigned int i = 0; i < tempVec.size(); i++)
	{
		if ( rootArr[i] == tempVec[i])
			cout << "The nodes match @ " << i;
		else
		{
			if (Aig_IsComplement(rootArr[i]))
			{
				if (Aig_IsComplement(tempVec[i]))
					cout << " Original node " <<Aig_ObjId( Aig_Regular (rootArr[i])) << " Converted Node " << Aig_ObjId( Aig_Regular (tempVec[i])) << endl;
				else
					cout << " Expecting Negated " << Aig_ObjId( Aig_Regular (rootArr[i])) << " but got " << Aig_ObjId(tempVec[i]) << endl;
			}
			else
				cout << " Expecting " << Aig_ObjId( Aig_Regular (rootArr[i])) << " but got " << Aig_ObjId(tempVec[i]) << endl;
		}
	}
*/

}

/* This function can be used to set different block sizes.  flag = true => take total number of ands (ignore the ors as they are cheap) and calculate the blocksize */
int determineBlockSize (Aig_Man_t *p, int totalBlocks, int numAnds, int numOrs, bool trueAnds)
{
	//int totalNodesWithSharing = numAnds + numOrs; 	//This may not contain all the numAnds and  numOrs as the dfs is still happening.
	int totalAndNodes = Aig_ManAndNum(p);	
	
//	assert (numAnds + numOrs == totalAndNodes);

	int  blockSize1 = (totalAndNodes)/ totalBlocks;
	int blockSize2 = (numAnds)/ totalBlocks;
/* if MPI scheduling works properly, one decide on blocks based on # and nodes rather than total blocks */
		
	return  trueAnds ? blockSize2 : blockSize1;
}
	
void createVariableMap (char* orderFileName, map<string, int>& varNamesVec)
{

	std::ifstream infile(orderFileName);	
	
	string varName;
	int index = 0;
	while (infile >> varName)
	{
		//cout << varName;
		varNamesVec.insert(std::pair<string, int>( varName, index));
		index ++;
	}
	infile.close();

}


void createVariableMap (list<string> &order_of_elimination, map<string, int>& varNamesVec)
{

	string varName;
	int index = 0;
	for (list<string>::iterator order_it = order_of_elimination.begin(); order_it != order_of_elimination.end(); order_it++)
	{
		varName = *order_it;
		//cout << varName;
		varNamesVec.insert(std::pair<string, int>( varName, index));
		index ++;
	}
}


void dfsAndMark_rec( Aig_Man_t * p, Aig_Obj_t * pObj, bool pushNegation, int *markArray,  int & numAnds, int & numOrs)
{
    //clock_t start_clock = clock();
    bool isComp = Aig_IsComplement(pObj);

    if (isComp)
    	pObj = Aig_Regular (pObj);

    assert (pObj);

    int nodeId = Aig_ObjId(pObj);


    if ( Aig_ObjIsTravIdCurrent(p, pObj) )	//Is the node shared? Check if you would like to make a block
    {
	
	if (markArray[nodeId] == 2)	//Already marked it as both. No need to traverse the subtree again
		return;

	

	if (isComp ^ pushNegation) // a exor b - The two negatives cancel each other or if both are positive
	{
		if (markArray[ nodeId] == 0)
		{	
		 	markArray[nodeId] = 2;
			numOrs ++;
			pushNegation = true;
	        }	//If marked as an or node, mark as an and and or node
		else
			return;
	}
	else
	{

	     	if(markArray[nodeId] == 1)
	     	{ 
			markArray[nodeId] = 2;
			numAnds ++;
			pushNegation = false;
	     	}
		else
		    return;
	}
	//Or node is cheap and hence we are more interested in the number of And nodes.
       // return;
    }
    else
    {
	   Aig_ObjSetTravIdCurrent(p, pObj);

	    if ( Aig_ObjIsCo(pObj) )
	    {

		dfsAndMark_rec( p, Aig_ObjChild0(pObj), isComp, markArray, numAnds, numOrs);
		return;
	    }

	   if (pushNegation ^ isComp)
	   {
	   	markArray[nodeId] = 1;
		numOrs ++;
	   }
	   else
		numAnds ++;
	
	    pushNegation = pushNegation ^ isComp;

   }
     if ( Aig_ObjIsCi(pObj) )
	return;

    dfsAndMark_rec( p, Aig_ObjChild0(pObj), pushNegation, markArray,  numAnds, numOrs);
    dfsAndMark_rec( p, Aig_ObjChild1(pObj), pushNegation, markArray,  numAnds, numOrs);

}
/**Function************************************************************

  Synopsis    [ DFS traversal and marking nodes as and & or.  Taken from Abc 

  Description []
               
  SideEffects []

  SeeAlso     []


This function does a dfs Walk and marks a node as an and node, or node or both.
markArray = 0 => and Node
markArray = 1 => or Node
markArray = 2 => both Node

if the node functions as an and node (through any parent), numAnds++
*/

void dfsAndMark(Aig_Man_t * p, int *markArray, int & numAnds, int & numOrs)
{
    Aig_Obj_t * pObj;
    int i;
    Aig_ManIncrementTravId( p );
    Aig_ObjSetTravIdCurrent( p, Aig_ManConst1(p) );

    Aig_ManForEachCo( p, pObj, i )
    	dfsAndMark_rec( p, pObj, false, markArray, numAnds, numOrs);
#ifdef VERBOSE
    cout << " numAnds = " << numAnds << " numOrs " << numOrs <<  "NumBoth " << (numAnds + numOrs) - (Aig_ManObjNum(p) -1) << endl;
#endif
}

/*Create new block */

void genNewBlock(int root, map<int, Block>& blockMap)
{
	Block b;
	b.setRoot (root);
	blockMap.insert (std::pair<int, Block>(root, b));
#ifdef PREPROCESS_INFO
	cout << " created new block  with root as " << b.getRoot();
#endif
}

/*Traverses the AIG and creates blocks */

void createBlocks_rec( Aig_Man_t * p, Aig_Obj_t *pObj,   int blockSize,  map <int, Block>& blockMap, int *numDescendentsBelowNode, int *numAndsBelowNode, int *markArray, int use_g_ands)
{

    assert (! Aig_ObjIsCo(pObj)); //Cannot be a CO node

    assert (! Aig_IsComplement(pObj));

    if ( Aig_ObjIsTravIdCurrent(p, pObj) )	//Is the node shared? Check if you would like to make a block
    {
	return;
     }

    Aig_ObjSetTravIdCurrent(p, pObj);

    int nodeId = Aig_ObjId(pObj);

    if (Aig_ObjIsCi(pObj))
    {
	   numDescendentsBelowNode[nodeId] = 0;
	   numAndsBelowNode[nodeId] = 0;
	   //hitleaf = true;
	   if (blockSize == 1 && (! use_g_ands))
	   {
		genNewBlock(nodeId,  blockMap);
	//	leafBlocks ++;
	   }
	   return;
    }

    assert( Aig_ObjIsNode(pObj) );


    createBlocks_rec( p, Aig_ObjFanin0(pObj),  blockSize, blockMap, numDescendentsBelowNode, numAndsBelowNode, markArray, use_g_ands);
    createBlocks_rec( p, Aig_ObjFanin1(pObj),   blockSize, blockMap, numDescendentsBelowNode, numAndsBelowNode, markArray, use_g_ands);


    numDescendentsBelowNode[nodeId] = numDescendentsBelowNode[ Aig_ObjFaninId0(pObj)]+ numDescendentsBelowNode[Aig_ObjFaninId1(pObj)];
    numAndsBelowNode[nodeId] = numAndsBelowNode[ Aig_ObjFaninId0(pObj)]+ numAndsBelowNode[Aig_ObjFaninId1(pObj)];

     numDescendentsBelowNode[nodeId] ++;

    if (markArray[nodeId] != 1)
	numAndsBelowNode[nodeId] ++;
		
  //bool newblock = false;
#ifdef PREPROCESS_INFO

    cout << " Number of ors below node " << nodeId << " is " << numDescendentsBelowNode[nodeId] << endl;
    cout << " Number of ands below node " << nodeId << " is " << numAndsBelowNode[nodeId] << endl;
#endif

   int numNodesBelow; //, cBlockSize = blockSize;

   if (use_g_ands)
	numNodesBelow = numAndsBelowNode[nodeId] ;
   else
	numNodesBelow = numDescendentsBelowNode[nodeId];

   /* if( hitleaf) 
   {
	cBlockSize = numNodesLeafBlocks;
	hitleaf = false;
	leafBlocks ++;
   }
   else
	cBlockSize = blockSize;
*/
    
  if(numNodesBelow >= blockSize ) 
  {
	genNewBlock(nodeId,  blockMap);
//	newblock = true;
 // }
  // if( newblock)
   //{
	   numDescendentsBelowNode[nodeId] = 0;
	   numAndsBelowNode[nodeId] = 0;
   }
	    
}
/* A dfs walk to create blocks when returning  (bottom up). Currently, a block is created for each node in the AIG  */

void createBlocks( Aig_Man_t * p, int blockSize,   map<int, Block>& blockMap, int *numDescendentsBelowNode, int *numAndsBelowNode, int * markArray, set <int>& top_lev_blocks, int use_g_ands)
{
    Aig_Obj_t * pObj;
    int i, id;

    Aig_ManIncrementTravId( p );
    Aig_ObjSetTravIdCurrent( p, Aig_ManConst1(p) );
    //int leafBlocks = 0;
  //  bool hitleaf = false;
    Aig_ManForEachCo( p, pObj, i )
    {
    	createBlocks_rec( p, Aig_ObjFanin0(pObj), blockSize,  blockMap, numDescendentsBelowNode, numAndsBelowNode,  markArray, use_g_ands);
	id = Aig_ObjFaninId0(pObj);
	genNewBlock(id, blockMap);
	top_lev_blocks.insert (id);
#ifdef VERBOSE
	cout << " Added " << id  << " to top level blocks " << endl;
#endif
    }

#ifdef VERBOSE
   cout << " No. of blocks created " << blockMap.size() << endl; // ". No of leaf Blocks created " << leafBlocks << endl;
   cout << " No. of top level blocks " << top_lev_blocks.size() << endl;
#endif
}

void addDependentInfo (Block& par, Block& child)
{
	par.addDependentBlock(child.getRoot());
	child.addDependeeBlock(par.getRoot());
#ifdef PREPROCESS_INFO
	cout << " Adding " << par << " as dependent on " << child;
#endif
}
/* Collect Dependencies between blocks */

void collectDependencyInfo_rec (Aig_Man_t *p, Aig_Obj_t *pObj, Block& currentBlock, map<int, Block>& blockMap)
{
//Assumption : node is always regular

    assert (! Aig_IsComplement(pObj));

    if ( Aig_ObjIsTravIdCurrent(p, pObj) )	//Is the node shared? Check if you would like to make a block
	return;

    Aig_ObjSetTravIdCurrent(p, pObj);

    assert (!  Aig_ObjIsCo(pObj));

    if (Aig_ObjIsCi(pObj))
        return;

    Aig_Obj_t *child;
    int nodeId;

    assert( Aig_ObjIsNode(pObj) );

    child = Aig_ObjFanin0(pObj);
    nodeId = Aig_ObjId(child);

//Check if child0 is a root
    if(blockMap.count(nodeId) > 0) 	//This is the root of another block
    {
	addDependentInfo (currentBlock, blockMap[nodeId]);
	collectDependencyInfo_rec(p, child, blockMap[nodeId], blockMap);
    }
    else
	collectDependencyInfo_rec(p, child, currentBlock,  blockMap);

//Check if child1 is root
    child = Aig_ObjFanin1(pObj);
    nodeId = Aig_ObjId(child);
    if( blockMap.count(nodeId) > 0) //Is child root of another block? 
    {
	addDependentInfo (currentBlock, blockMap[nodeId]);
	collectDependencyInfo_rec(p, child, blockMap[nodeId], blockMap);
    }
    else
	collectDependencyInfo_rec(p, child, currentBlock,  blockMap);
}

void collectDependencyInfo (Aig_Man_t *p,  map<int, Block>& blockMap)
{
    Aig_Obj_t * pObj;
    int i;

    Aig_ManIncrementTravId( p );
    Aig_ObjSetTravIdCurrent( p, Aig_ManConst1(p) );
    Aig_ManForEachCo( p, pObj, i )
	collectDependencyInfo_rec(p, Aig_ObjFanin0(pObj), blockMap[Aig_ObjFaninId0(pObj)], blockMap);
	
}


/* The code for the master to assign blocks to the workers and ensure that the results of the children blocks are sent  */
void assignBlocktoProcess(communicator& world, queue<int>& processBlocks, queue<int>& freeProcess, int* currProcessBlockMap, int& numMesgSent, map<int, Block>& blockMap, int *markArray, bool sendResult, double& commTime, int& cntDummy)
{
	int p, process;
	clock_t start_comm_time; 
	while (!freeProcess.empty() && (! processBlocks.empty()))
	{
		p = processBlocks.front ();
		processBlocks.pop();
		process = freeProcess.front();
		freeProcess.pop();

		start_comm_time = clock();

		world.send(process, process_block, p);	

		commTime += ((double) (clock() - start_comm_time)/CLOCKS_PER_SEC);
#ifdef COMM_DEBUG 
		cout << " Sending " << p << " and " << markArray[p] << " to " << process << endl;
#endif

		currProcessBlockMap[process] = p;
		numMesgSent ++;
		
		
		bool and_node, or_node, send_Dummy;
//Send result of dependent nodes to process */
		if(sendResult)
		{
			vector<int> dummy;
			assert (dummy.size() == 0);
			boost::mpi::request req0, req1[2], req2[2];
			//Send result of the blocks this node depends on. 
			set <int> * pd = & (blockMap[p].processedDependents);
			
			for (set<int>::iterator bit=pd->begin(); bit!=pd->end(); ++bit)
			{
				Block *bptr = &blockMap[*bit];
				//result[1] = *bit;  
				and_node = false;	
				or_node = false;
				send_Dummy = false;
				
//Commented out these two lines - so that dummy is not sent.
				//if (bptr->processHasResult.count(process) != 0)	//Process already has results of the block pointed to by bptr;
				//	send_Dummy = true;

				if (markArray[*bit] != 1)	
					and_node = true;
					
				if(markArray[*bit] > 0)
					or_node = true;
					
				world.send(process, store_data, *bit);	//Send the result of dependent blocks to the dependee block.
				
				if (and_node)
				{
		start_comm_time = clock();

					if (send_Dummy)
					{
						req1[0] = world.isend(process, store_data_and_r1, dummy);
						req1[1] = world.isend(process, store_data_and_r0, dummy);
#ifdef COMM_DEBUG
					cout << " Sent dummy " << *bit << " and result " << " to " << process << endl;
#endif
					}
					else	
					{
						req1[0] = world.isend(process, store_data_and_r1, bptr->and_r1);
						req1[1] = world.isend(process, store_data_and_r0, bptr->and_r0);
#ifdef COMM_DEBUG
					cout << " Sent dependent's " << *bit << " and result "  << " to " << process;
					cout << " size of r0  "  << bptr->get_and_r0_size() << " size of r1 " << bptr->get_and_r1_size()  << " to " << process << endl;
#endif
					}
		commTime += ((double) (clock() - start_comm_time)/CLOCKS_PER_SEC);
					//printVector ( bptr->and_r1, " r1 ");
					//printVector ( bptr->and_r0, " r0 ");
				}
				if (or_node)
				{
					
		start_comm_time = clock();
					if (send_Dummy)
					{
						req2[0] = world.isend(process, store_data_or_r1, dummy);
						req2[1] = world.isend(process, store_data_or_r0, dummy);
#ifdef COMM_DEBUG
						cout << " Sent dummy " << *bit << " or result " << " to " << process << endl;
#endif
					}
					else	
					{
						req2[0] = world.isend(process, store_data_or_r1, bptr->or_r1);
						req2[1] = world.isend(process, store_data_or_r0, bptr->or_r0);
#ifdef COMM_DEBUG
						cout << " Sent dependent's " << *bit << " or result " <<  " to " << process;
						cout << " size of r0  "  << bptr->or_r0.size() << " size of r1 " << bptr->or_r1.size()  << " to " << process;
#endif
					}

		commTime += ((double) (clock() - start_comm_time)/CLOCKS_PER_SEC);
				}
				if(! send_Dummy)
					bptr->processHasResult.insert(process);	//Process already has results of the block pointed to by bptr;
				else
					cntDummy ++;

				if(and_node)
				{
					boost::mpi::wait_all (req1, req1 + 2);
				}
				if(or_node)
				{
					boost::mpi::wait_all (req2, req2 + 2);
				}
			//Sent Data to p. Remember this
				bptr->notSentResultYet.erase (p);
				if (bptr->notSentResultYet.empty())	
				{
//To reduce memory footprint - delete r0's and r1's when not need. Ideally delete block.
						//cout << " Block " << *bit << " no longer needed. Can be deleted " << endl;	
#ifdef MEM_OPT
					bptr->clearBlock();
#endif 
				}
			}
		}

	}
}

void printSkolemFunctionsToFile (Abc_Ntk_t *pNtk, Aig_Man_t *pAig, map<int,Block>& blockMap, int *markArray, AIGBasedSkolem * aigbs, char * orderFileName, char * aigFileName, bool solvedAtMaster, set<string> &non_occuring_variables_to_eliminate, list<string> &order_of_elimination, bool perform_reverse_substitution_before_printing)
{
		//Dump Skolem functions of the topmost node into a file
		vector<Aig_Obj_t*> list_of_r1_roots;

		map<string, int> varNameMap;
		//createVariableMap (orderFileName, varNameMap); // commented by Ajith John
		createVariableMap (order_of_elimination, varNameMap); // added by Ajith John

		//assert (Aig_ManCoNum(pAig) == 1);
		Aig_Obj_t *pFanin = Aig_ObjFanin0(Aig_ManCo(pAig, 0));
		Block *bptr = &blockMap[Aig_ObjId(pFanin)];
		vector<Aig_Obj_t*> createdCos;
//Instead if the code below- you will need 
		if (! solvedAtMaster)
		{
			if (bptr-> and_r1.size() > 0)
				convertIntArrayToAigObj (pAig, bptr->and_r1, list_of_r1_roots, createdCos, true);
			if (bptr-> or_r1.size() > 0)
				convertIntArrayToAigObj (pAig, bptr->or_r1, list_of_r1_roots,  createdCos, true);
		}
		else
		{
			//Get list of r1 roots From Hash Table
		}

		if(perform_reverse_substitution_before_printing)
			aigbs->performReverseSubstitutionOfSkolemFunctions(list_of_r1_roots) ;	//Perform Reverse Substitution

		// Added by Ajith John
		set<string> support_of_skolem;
		for(int i = 0; i < list_of_r1_roots.size(); i++)
		{
			Aig_Obj_t* skolem_i = list_of_r1_roots[i];

			#ifdef DEBUG_PRINT_SK
			writeFormulaToFile(pAig, skolem_i, "final_sk_function", ".v", i, 0);	
			#endif

			set<string> support_skolem_i;
			computeSupport(skolem_i, support_skolem_i, pAig);
			set_union(support_of_skolem.begin(), support_of_skolem.end(), support_skolem_i.begin(), support_skolem_i.end(),inserter(support_of_skolem, support_of_skolem.begin()));				
		}
		// Added by Ajith John ends here

		Vec_Ptr_t * vCis = Vec_PtrAlloc(Aig_ManCiNum(pAig));
		Vec_Ptr_t * vCos = Vec_PtrAlloc(Aig_ManCoNum(pAig));

#ifdef DEBUG_PRINT_SK
		cout << " No. of Pis at the master node " << Aig_ManCiNum(pAig) << " No. of Cos at the master node " << Aig_ManCoNum(pAig) << endl;
#endif

		vector<string> Ci_name_list;// Added by Ajith John
		vector<string> Co_name_list;// Added by Ajith John
		for ( int i = 0; i < Abc_NtkPiNum(pNtk); i++)
		{
#ifdef DEBUG_PRINT_SK
			cout << "Writing Co at location " << i  << endl;
#endif
			char* nm = Abc_ObjName( Abc_NtkPi(pNtk, i));
			string snm (nm);
				
			if (varNameMap.count (snm) > 0)	//if variable is eliminated
			{
				int index = varNameMap[snm];
				Vec_PtrPush (vCos,  Aig_ObjCreateCo(pAig, list_of_r1_roots[index]));;
#ifdef DEBUG_PRINT_SK
				cout << "Writing Co " << snm << " at location " << i  << endl;
#endif
				Co_name_list.push_back(snm);
			}
			else if(non_occuring_variables_to_eliminate.find(snm) != non_occuring_variables_to_eliminate.end())// snm is an output which is non-occurring
			{
				Vec_PtrPush (vCos,  Aig_ObjCreateCo(pAig, Aig_ManConst1(pAig)));;
#ifdef DEBUG_PRINT_SK
				cout << "Writing Co " << snm << " as TRUE at location " << i  << endl;
#endif
				Co_name_list.push_back(snm);
			}
			else if(support_of_skolem.find(snm) == support_of_skolem.end()) // Added by Ajith John
			{
#ifdef DEBUG_PRINT_SK
				cout << "Avoiding " << snm << " at location " << i  << endl;
#endif			
			}
			else	//if variable not eliminated
			{
				Vec_PtrPush (vCis,  Aig_ManCi(pAig, i ));
#ifdef DEBUG_PRINT_SK
				cout << "Writing Ci " << snm << " at location " << i  << endl;
#endif
				Ci_name_list.push_back(snm);
			}
		}

	
		
		Aig_Man_t * pNew = Aig_ManDupSimpleDfsPart(pAig, vCis, vCos);
		
		string fileName(aigFileName);
		fileName = fileName.substr(fileName.find_last_of("/") + 1);  //Get the file name;
		fileName.erase(fileName.find ("."), string::npos); //This contains the code for the raw file name;
		fileName.append("_sk.v"); //This contains the code for the raw file name;
		//Aig_ManDumpVerilog (pNew, (char*) fileName.c_str());

		writeCombinationalCircuitInVerilog( pNew, (char*) fileName.c_str(), Ci_name_list, Co_name_list); // Added by Ajith John
		list_of_r1_roots.clear();
		Vec_PtrFree(vCis);
		Vec_PtrFree(vCos);
		Aig_ManStop (pNew);	
		
}
		
//After timeout, call skolem in cluster at the master
////Currently not used - using this will remove the advantage of parallelism if timeout is very small.

void atMasterAfterTimeOut (Aig_Man_t *pAig, map<int,Block>& blockMap, int *markArray, AIGBasedSkolem * aigbs, set<int> & top_lev_blocks)
{
		// build the r1, r0 sets for each block whose results the master node has
		vector<Aig_Obj_t*> createdCos;
		for (std::map<int,Block>::iterator it=blockMap.begin(); it!=blockMap.end(); ++it)
		{
		//	std::cout << it->first << " => " << it->second ;
			if (!(it->second.and_r1.empty())  )	//Block has results
			{
				assert (! it->second.and_r1.empty());
				vector<Aig_Obj_t*> list_of_and_r1s;
				vector<Aig_Obj_t*> list_of_and_r0s;
				convertIntArrayToAigObj (pAig, it->second.and_r1, list_of_and_r1s, createdCos, false);
				convertIntArrayToAigObj (pAig, it->second.and_r0, list_of_and_r0s, createdCos, false);
				aigbs->SetInHashTable_In_Cluster (0,  Aig_ManObj(pAig, it->first), list_of_and_r1s, list_of_and_r0s, 0);
			}
			if (! it->second.or_r1.empty())
			{
				assert (! it->second.or_r1.empty());
				vector<Aig_Obj_t*> list_of_or_r1s;
				vector<Aig_Obj_t*> list_of_or_r0s;
				convertIntArrayToAigObj (pAig, it->second.or_r0, list_of_or_r1s,  createdCos, false);
				convertIntArrayToAigObj (pAig, it->second.or_r0, list_of_or_r0s,  createdCos, false);
				aigbs->SetInHashTable_In_Cluster (1,  Aig_ManObj(pAig, it->first), list_of_or_r1s, list_of_or_r0s, 0);	//world.rank = 0
			}

			it->second.clearBlock();	
			//cout << " Cleared Block " << it->first << endl;
		}

		assert (top_lev_blocks.size() == 1);	// if > 1, then send rest of the blocks to the worker nodes so that skolem functions are computed in parallel
		for (std::set<int>::iterator sit=top_lev_blocks.begin(); sit!=top_lev_blocks.end(); ++sit)
		{
			vector<Aig_Obj_t*> list_of_r1s;
			vector<Aig_Obj_t*> list_of_r0s;
			bool r1r0s_exact;
			bool verify = true;
			//bool top_lev = false;

		 	std::cout << ' ' << *sit;
			 int typeofNode = markArray[*sit] ;
			// assert that markArray of top level block is 0 or 1. (Not 2)
			 assert (typeofNode < 2);	//Not really required in the code. Just added it for correctness
			Aig_Obj_t *pObj = Aig_ManObj(pAig, *sit);
			
			// Call skolem in cluster for the top level block
		         if (typeofNode == 1)
				aigbs->Skolem_In_Cluster(1, pObj, 0, list_of_r1s, list_of_r0s, 0, true, verify, r1r0s_exact);	//Currently depth_from_root = 0; world.rank = 0
			 else	
				aigbs->Skolem_In_Cluster(0, pObj, 0, list_of_r1s, list_of_r0s, 0, true, verify, r1r0s_exact);	//Currently depth_from_root = 0; world.rank = 0
		}
		
}


/* Code which executes at the master node. The master node takes care of scheduling different blocks on different processors */
void masterCode (communicator& world, Aig_Man_t *pAig, map<int,Block>& blockMap, int *markArray, AIGBasedSkolem * aigbs, set<int> & top_lev_blocks, double timeOutTime, bool &solvedAtMaster)			
{
	queue<int> processBlocks; 
	set<int> remainingBlocks;

	clock_t start_comm_time, start_wait_time; 
	double commTime = 0.0, waitTime = 0.0;
	
#ifdef RUN_AS_SEQUENTIAL

	assert (top_lev_blocks.size() == 1);
	for (std::set<int>::iterator sit=top_lev_blocks.begin(); sit!=top_lev_blocks.end(); ++sit)
			processBlocks.push(*sit);
#else
	for (std::map<int,Block>::iterator it=blockMap.begin(); it!=blockMap.end(); ++it)
	{
		if (it->second.noDependentBlocks())	
			processBlocks.push (it->second.getRoot());
		else
			remainingBlocks.insert(it->second.getRoot());
	}
#endif


		

	int i, cntDummy = 0;

	int currProcessBlockMap [world.size() - 1];
	queue<int> freeProcess;
	for (i = 1; i < world.size(); i++)
		freeProcess.push (i);

	int numMesgSent = 0;
	int numMesgRecv = 0;
		//assign blocks that can be processed to the worker processes
	//double timeOutExactTime = ( clock() / (double) CLOCKS_PER_SEC)  + timeOutTime ;// timeOutTime is in seconds
#ifdef VERBOSE
	cout << "Initally: No. of blocks in ProcessBlocks Queue " << processBlocks.size() << ". Remaining blocks " << remainingBlocks.size() << endl;
	cout << "Current time " << clock() << "Time out time " << ( clock() / (double) CLOCKS_PER_SEC)  + timeOutTime ; 
#endif

	assignBlocktoProcess(world, processBlocks, freeProcess, currProcessBlockMap, numMesgSent, blockMap, markArray, false, commTime, cntDummy);

	//  assign  the next block in the queue to the source 
	// send the result_data to the source, if any

	//once numprocess sends = numblocks
	 //	free all queues;
	// once numprocess recvs = numblocks
		//send finalize mesg

	int d;
	int blockRoot;

	boost::mpi::request req1[2], req2[2];
	while (numMesgRecv < numMesgSent)
	{
		vector<unsigned char> r1, r11 ;
		vector<unsigned char> r0, r01;

		boost::mpi::status s  = world.probe();
		
	//	boost::mpi::status s = ireq.wait();
		if (s.tag() == result_data_and_r1 || s.tag() == result_data_or_r1)  // Receive the packet of data
		{
//Receive R1 and R0
			start_comm_time = clock();
			req1[0] = world.irecv(s.source(), s.tag(), r1);	
			
			if(s.tag() == result_data_and_r1)
				req1[1] = world.irecv(s.source(), result_data_and_r0, r0);
			else 
				req1[1] = world.irecv(s.source(), result_data_or_r0, r0);
				
			commTime += ((double) (clock() - start_comm_time)/CLOCKS_PER_SEC);

			blockRoot = currProcessBlockMap[s.source()];
			(blockMap[blockRoot]).processHasResult.insert(s.source());

			if (markArray[blockRoot] == 2)
			{
				start_comm_time = clock();
				req2[0] = world.irecv(s.source(), result_data_or_r1, r11);	
				req2[1] = world.irecv(s.source(), result_data_or_r0, r01);
				commTime += ((double) (clock() - start_comm_time)/CLOCKS_PER_SEC);
			}



		//get result from source
			numMesgRecv ++;

			//add source to the freeprocess queue 
			freeProcess.push (s.source());
// Recompute Dependency informations; add blocks which can now be processed in the process Queue	
			for (set<int>::iterator bmit=blockMap[blockRoot].dependeeBlocks.begin(); bmit!=blockMap[blockRoot].dependeeBlocks.end(); ++bmit)
			{
				d = *bmit;	//The root of the dependee block
				Block *dependee =  &blockMap[d];
				dependee->processedDependents.insert(blockRoot);	//Should be int or block? See which is more convenient
				blockMap[blockRoot].notSentResultYet.insert(d);	//Results not sent yet to dependee
				dependee->removeDependentBlock(blockRoot);

				int root = dependee->getRoot();
				
	#ifdef SCHED_DEBUG
				cout << " Dependee " << root << " is no longer dependent on "  << blockRoot;
				cout << " No of. Dependents of " << root << " still remaining " << dependee->numDependents();
	#endif
				if (dependee->noDependentBlocks())
				{
					remainingBlocks.erase(root);
					processBlocks.push(root);
	#ifdef SCHED_DEBUG
					cout << " Dependee " << root << " is added to processBlocks. size of remaining blocks is "  << remainingBlocks.size();
	#endif
				}
			}

//	Store the results in the block
			start_comm_time = clock();
			start_wait_time = clock();

			boost::mpi::wait_all (req1, req1 +2);	//wait for the result_data to come
			if (markArray[blockRoot] == 2)
				boost::mpi::wait_all (req2, req2 +2);

			commTime += ((double) (clock() - start_comm_time)/CLOCKS_PER_SEC);
			waitTime += ((double) (clock() - start_wait_time)/CLOCKS_PER_SEC);

//store the result - so that it can be passed on to the dependents when required
			if (markArray[blockRoot] == 0)	//and_node
			{	
				blockMap[blockRoot].store_and_r1( r1);
				blockMap[blockRoot].store_and_r0( r0);
			}
			if (markArray[blockRoot] == 1)	//or_node
			{	
				blockMap[blockRoot].store_or_r1( r1);
				blockMap[blockRoot].store_or_r0( r0);
			}
			if (markArray[blockRoot] == 2)	//both and and or node
			{

				blockMap[blockRoot].store_and_r1( r1);
				blockMap[blockRoot].store_and_r0( r0);

				blockMap[blockRoot].store_or_r1( r11);
				blockMap[blockRoot].store_or_r0( r01);
			}

			//cout << " Finished Receiving data from " << s.source() << endl;	
	   }
//	   if ((clock() / (double) CLOCKS_PER_SEC) < timeOutExactTime)
	   	assignBlocktoProcess(world, processBlocks, freeProcess, currProcessBlockMap, numMesgSent, blockMap, markArray, true, commTime, cntDummy);
 		
#ifdef VERBOSE
	cout << " Current No. of free processes : " << freeProcess.size() << " No. of blocks in Process Queue " << processBlocks.size() << " No. of remaining blocks "  << remainingBlocks.size() << endl;
	if (!freeProcess.empty())
		cout << freeProcess.size() << " Processes waiting for a block. "  << endl;
		
#endif
	}
	if (remainingBlocks.empty())
	{
//		cout << " Time to say goodbye " << endl;
		cout << " Skolem functions successfully generated " << endl;
//		cout << "numMesgsSent " << numMesgSent << " numMesgsReceived " << numMesgRecv << endl;
//		cout << "No. of (nodes) dummy r1s and r0s sent " << cntDummy << endl;
		
		assert (numMesgSent == numMesgRecv);
	}
	else
	{
//Currently not used
		if (timeOutTime > 0)
		{
			cout << " Current Time " << (clock() / (double) CLOCKS_PER_SEC) << endl;
			//processBlocks.clear();	//Will have to pop each block out
			remainingBlocks.clear();
			atMasterAfterTimeOut (pAig, blockMap, markArray, aigbs, top_lev_blocks);
		        solvedAtMaster = true;
			
		}
		else
			cerr << " Error - not all blocks processed! " << endl;
	}

	start_comm_time = clock();
	for (i = 1; i < world.size(); i++)
	{
		world.send(i, finalize, 0);
	}
		commTime += ((double) (clock() - start_comm_time)/CLOCKS_PER_SEC);
#ifdef PRINT_TOTAL_TIME_BREAKUP
		cerr << " Total Time taken To communicate at Master Node  " << commTime << " seconds. " << endl;
#endif
	return ;	
}			
/* Code at the worker node 
// get the block to be processed.
				// if block has dependents
				// wait for data from the master for each of the dependees
				// deserialize and store in the r0, r1 hashtable
				//	call Skolem
				// seriablize the pass the result to the master
*/
void workerCode (communicator & world, Aig_Man_t * pAig, map<int,Block> blockMap, int *markArray, AIGBasedSkolem * aigbs, set<int> & top_lev_blocks)
{

	int p, i;
	clock_t start_proc_time, start_comm_time, start_wait_time,  start_idle_time;
	double proc_time = 0.0; 
	double comm_time = 0.0;
	double wait_time = 0.0;
	double idle_time = 0.0;

	// Added by Ajith
	unsigned long long int step_ms;
	struct timeval step_start_ms, step_finish_ms;
	// Added by Ajith ends here

#ifdef PRINT_STATISTICS
	clock_t clock1, clock2;
#endif
#ifdef PRINT_TOTAL_TIME_BREAKUP
	clock_t total_time;
	total_time = clock();
#endif
	while (1)
	{
		start_idle_time = clock()	;
#ifdef VERBOSE
		cout << " Waiting for a message at " << world.rank() << ". Time " << ((double) clock()/CLOCKS_PER_SEC) << endl;
#endif
		boost::mpi::status msg = world.probe();
		if (msg.tag() == process_block) 
		{
  // Receive the packet of data
			start_comm_time = clock();
			world.recv(msg.source(), msg.tag(), p);	
			comm_time += ((double) (clock() - start_comm_time)/CLOCKS_PER_SEC);

			idle_time += ((double) (clock() - start_idle_time)/CLOCKS_PER_SEC);
				
			int nodeType =  markArray[p]; 
			Aig_Obj_t *pObj = Aig_ManObj(pAig, p);
#ifdef VERBOSE
			cout << " Received Block process Message " << p << " at" << world.rank() << ". Wait Time " << (((double) clock() - start_idle_time)/CLOCKS_PER_SEC) << " Node type " << nodeType << endl;
#endif

			int d_size = blockMap[p].dependsOnBlocks.size(); //Using dependsOnBlocks as this data structure is not changed at the worker node. 

			//int result, result1[2], result2[2];	//result1[0] = call_type //result1[1] = id of the  node this block is dependent on

			int d_id;
	//Get and set result of blocks that this block depends on
			boost::mpi::request req0, req1[2], req2[2];
				vector<Aig_Obj_t*> createdCos;

			start_comm_time = clock();

			//Delete next line once the problem is solved -SS
#ifdef RUN_AS_SEQUENTIAL
			d_size = 0;
#endif
			for (i = 0; i < d_size; i++)
			{
				vector<unsigned char> list_of_d_r1s_int;
				vector<Aig_Obj_t*> list_of_d_r1s;
				vector<unsigned char> list_of_d_r0s_int;
				vector<Aig_Obj_t*> list_of_d_r0s;

				vector<unsigned char> list_of_d_r1s_int1;
				vector<Aig_Obj_t*> list_of_d_r11s;
				vector<unsigned char> list_of_d_r0s_int1;
				vector<Aig_Obj_t*> list_of_d_r01s;

				//req0 = 
				world.recv(msg.source(), store_data,  d_id);	//Send the result of dependent blocks to the dependee block.
			//	req0.wait();
				
	#ifdef COMM_DEBUG
				cout << " Received store data  " <<  msg.source()  << endl; 
	#endif
				//d_id = result1[1];
				assert (d_id < Aig_ManObjNum(pAig));
				
				if (markArray[d_id] != 1)
				{
					req1[0] = world.irecv(msg.source(), store_data_and_r1, list_of_d_r1s_int);	//Send the result of dependent blocks to the dependee block.
					req1[1] = world.irecv(msg.source(), store_data_and_r0, list_of_d_r0s_int);	//Send the result of dependent blocks to the dependee block.
				}

				if(markArray[d_id] > 0)	//both and and or ndoe
				{
					req2[0] = world.irecv(msg.source(), store_data_or_r1, list_of_d_r1s_int1);	//Send the result of dependent blocks to the dependee block.
					req2[1] = world.irecv(msg.source(), store_data_or_r0, list_of_d_r0s_int1);	//Send the result of dependent blocks to the dependee block.
				}
		
				start_wait_time = clock();	
				if (markArray[d_id] != 1)	//And node or both and and or node
				{
					req1[0].wait();
					wait_time += ((double) (clock() - start_wait_time)/CLOCKS_PER_SEC);

					if (list_of_d_r1s_int.size () > 0)
						convertIntArrayToAigObj (pAig, list_of_d_r1s_int, list_of_d_r1s, createdCos, false);


					start_wait_time = clock();	
					req1[1].wait();
					wait_time += ((double) (clock() - start_wait_time)/CLOCKS_PER_SEC);

					if (list_of_d_r0s_int.size () > 0)
						convertIntArrayToAigObj (pAig, list_of_d_r0s_int, list_of_d_r0s, createdCos, false);

	#ifdef COMM_DEBUG
				cout << "Received r1 from "  << msg.source() << " size " << list_of_d_r1s_int.size() << endl;
				cout << "Received r0 from "  << msg.source() << " size " << list_of_d_r0s_int.size() << endl;
	#endif
					if (list_of_d_r1s_int.size () > 0)
					{
				//		cout << " Setting in Hashtable for " << Aig_ObjId(Aig_ManObj(pAig, d_id)) << " polarity " << markArray[d_id] << " size of r1, r0" << list_of_d_r1s.size() << ","  << list_of_d_r0s.size() << endl;
						aigbs->SetInHashTable_In_Cluster (0,  Aig_ManObj(pAig, d_id), list_of_d_r1s, list_of_d_r0s, world.rank());
					}
				}	
				if(markArray[d_id] > 0)	// or node or both 
				{
					start_wait_time = clock();	
			//		req0.wait();
					wait_time += ((double) (clock() - start_wait_time)/CLOCKS_PER_SEC);
					//assert (result2[1] < Aig_ManObjNum(pAig));
			
					start_wait_time = clock();	
					req2[0].wait();
					wait_time += ((double) (clock() - start_wait_time)/CLOCKS_PER_SEC);
					if (list_of_d_r1s_int1.size () > 0)
						convertIntArrayToAigObj (pAig, list_of_d_r1s_int1, list_of_d_r11s, createdCos, false);

					start_wait_time = clock();	
					req2[1].wait();
					wait_time += ((double) (clock() - start_wait_time)/CLOCKS_PER_SEC);
					if (list_of_d_r0s_int1.size () > 0)
						convertIntArrayToAigObj (pAig, list_of_d_r0s_int1, list_of_d_r01s, createdCos, false);
	#ifdef COMM_DEBUG
				cout << " Setting in Hashtable for " << Aig_ObjId(Aig_ManObj(pAig, d_id)) << " polarity " << markArray[d_id] << "size of r0, r1" << list_of_d_r11s.size() << "," << list_of_d_r01s.size() << endl;

	#endif
					if (list_of_d_r1s_int1.size () > 0)
					{
						aigbs->SetInHashTable_In_Cluster (1,  Aig_ManObj(pAig, d_id), list_of_d_r11s, list_of_d_r01s, world.rank());
					}
				}

			}
			comm_time += ((double) (clock() - start_comm_time)/CLOCKS_PER_SEC);
	#ifdef PRINT_STATISTICS
			cout << " Time taken by processor " << world.rank() << " receive dependent's  data and convert it "  << p << " is " << ((double) (clock() - start_comm_time)/CLOCKS_PER_SEC) << " seconds." << endl; 
	#endif
		//Call Skolem for this block - depending on the node Type.	
			vector<unsigned char> list_of_and_r1s_int;
			vector<Aig_Obj_t*> list_of_and_r1s;
			vector<unsigned char> list_of_and_r0s_int;
			vector<Aig_Obj_t*> list_of_and_r0s;

			vector<unsigned char> list_of_or_r1s_int;
			vector<Aig_Obj_t*> list_of_or_r1s;
			vector<unsigned char> list_of_or_r0s_int;
			vector<Aig_Obj_t*> list_of_or_r0s;

			bool and_node = false;
			bool or_node = false;

			if (nodeType != 1)
				and_node = true;
			if (nodeType > 0)
				or_node = true;
			
			bool verify = false;
			bool top_lev = false;
			bool r1r0s_exact;

	#ifdef VERIFY_SKOLEM
			verify = true;
	#endif
			if (top_lev_blocks.count(p) > 0)
				top_lev = true;

			if (and_node)
			{
				start_proc_time = clock();
				gettimeofday (&step_start_ms, NULL);// Added by Ajith

				aigbs->Skolem_In_Cluster(0, pObj, 0, list_of_and_r1s, list_of_and_r0s, world.rank(), top_lev, verify, r1r0s_exact);	//Currently depth_from_root = 0

				gettimeofday (&step_finish_ms, NULL);// Added by Ajith starts here
   				step_ms = step_finish_ms.tv_sec * 1000 + step_finish_ms.tv_usec / 1000;
   				step_ms -= step_start_ms.tv_sec * 1000 + step_start_ms.tv_usec / 1000;// Added by Ajith ends here
				
				proc_time += ((double) (clock() - start_proc_time)/CLOCKS_PER_SEC);
	#ifdef PRINT_STATISTICS
			cout << " Time taken by processor " << world.rank() << " to generate Skolem functions for and "  << p << " is " << ((double) (clock() - start_proc_time)/CLOCKS_PER_SEC) << " seconds, i.e., " << step_ms << " milliseconds" << endl; 
	#endif
				start_comm_time = clock();
				encodeAigObj(pAig, list_of_and_r1s, list_of_and_r1s_int);
				req1[0] = world.isend(msg.source(), result_data_and_r1, list_of_and_r1s_int);

				encodeAigObj(pAig, list_of_and_r0s, list_of_and_r0s_int);
				req1[1] = world.isend(msg.source(), result_data_and_r0, list_of_and_r0s_int);
	#ifdef PRINT_STATISTICS
			cout << " Time taken by processor " << world.rank() << " to 'and' encode Skolem functions "  << p << " is " << ((double) (clock() - start_comm_time)/CLOCKS_PER_SEC) << " seconds." << endl; 
	#endif

			comm_time += ((double) (clock() - start_comm_time)/CLOCKS_PER_SEC);
			}
			if(or_node)
			{
				start_proc_time = clock();
				gettimeofday (&step_start_ms, NULL);// Added by Ajith

				aigbs->Skolem_In_Cluster(1, pObj, 0, list_of_or_r1s, list_of_or_r0s, world.rank(), top_lev, verify, r1r0s_exact);	//Currently depth_from_root = 0

				gettimeofday (&step_finish_ms, NULL);// Added by Ajith starts here
   				step_ms = step_finish_ms.tv_sec * 1000 + step_finish_ms.tv_usec / 1000;
   				step_ms -= step_start_ms.tv_sec * 1000 + step_start_ms.tv_usec / 1000;// Added by Ajith ends here
				
				proc_time += ((double) (clock() - start_proc_time)/CLOCKS_PER_SEC);
	#ifdef PRINT_STATISTICS
			cout << " Time taken by processor " << world.rank() << " to generate Skolem functions for or "  << p << " is " << ((double) (clock() - start_proc_time)/CLOCKS_PER_SEC) << " seconds, i.e., " << step_ms << " milliseconds" << endl;
	#endif
			start_comm_time = clock();
			
				//if (nodeType == 1)
				//{
				encodeAigObj(pAig, list_of_or_r1s, list_of_or_r1s_int);
				req2[0] = world.isend(msg.source(), result_data_or_r1, list_of_or_r1s_int);
				encodeAigObj(pAig, list_of_or_r0s, list_of_or_r0s_int);
				req2[1] = world.isend(msg.source(), result_data_or_r0, list_of_or_r0s_int);
			//	}
			comm_time += ((double) (clock() - start_comm_time)/CLOCKS_PER_SEC);

	#ifdef PRINT_STATISTICS
			cout << " Time taken by processor " << world.rank() << " to 'or' encode Skolem functions "  << p << " is " << ((double) (clock() - start_comm_time)/CLOCKS_PER_SEC) << " seconds." << endl; 
	#endif
			}
			start_wait_time = clock();
			if(and_node)
			{
				boost::mpi::wait_all (req1,  req1 +2);
			}
			if(or_node )
			{
				boost::mpi::wait_all (req2, req2 + 2);
			}
			wait_time += ((double) (clock() - start_wait_time)/CLOCKS_PER_SEC);
			comm_time += ((double) (clock() - start_wait_time)/CLOCKS_PER_SEC);

			aigbs->cleanupMemoryInProcessor_In_Cluster (world.rank());

/* Added extra by SS to reduce memory map */

			bool delete_created_cos = true;

			if(delete_created_cos)
			{

				for(vector<Aig_Obj_t*>::iterator co_it = createdCos.begin(); co_it != createdCos.end(); co_it++)
				{
					Aig_Obj_t* co_to_be_deleted = *co_it;
				
					Aig_ObjDeletePo(pAig, co_to_be_deleted);
				} 
		
				createdCos.clear();
			}

	      }
		if(msg.tag() == finalize)
		{
			idle_time += ((double) (clock() - start_idle_time)/CLOCKS_PER_SEC);

#ifdef PRINT_TOTAL_TIME_BREAKUP
			cerr << " Time taken by processor After Preprocessing  " << world.rank() << "  is " << ((double) (clock() - total_time)/CLOCKS_PER_SEC) << " seconds." << endl; 
			cerr << " Total Time taken by processor in Skolem Function Generation  " << world.rank() << "  is " << proc_time << " seconds." << endl; 
			cerr << " Total Time taken by processor " << world.rank() << " in Communication(Including Encoding/Decoding)  " << world.rank() << "  is " << comm_time << " seconds." << endl; 
			cerr << " Total Time taken by processor " << world.rank() << " in Waiting (Isend/IRecv) " << world.rank() << "  is " << wait_time << " seconds." << endl; 
			cerr << " Total Idle time for processor " << world.rank() << " is "  << idle_time << endl;
#endif
#ifdef VERBOSE
			cout << " @ Processor " << world.rank() << " Num AIG Nodes are (CI/CO/And) " << Aig_ManCiNum(pAig) << " "  << Aig_ManCoNum(pAig) << " " << Aig_ManAndNum(pAig) << endl;
#endif

			return;
		}
	}
}



void printSkolemFunctionSizesToFile (Aig_Man_t *pAig, map<int,Block>& blockMap, AIGBasedSkolem* aigbs, char * aigFileName, bool solvedAtMaster, bool perform_reverse_substitution_before_printing)
{
		unsigned long long int sum__skolem_function_sizes__after = 0;
		unsigned long long int sum__skolem_function_sizes__before = 0;
		float avg__skolem_function_sizes__after;
		float avg__skolem_function_sizes__before;

		vector<Aig_Obj_t*> list_of_r1_roots;

		Aig_Obj_t *pFanin = Aig_ObjFanin0(Aig_ManCo(pAig, 0));
		Block *bptr = &blockMap[Aig_ObjId(pFanin)];
		vector<Aig_Obj_t*> createdCos;
	
		if (! solvedAtMaster)
		{
			if (bptr-> and_r1.size() > 0)
				convertIntArrayToAigObj (pAig, bptr->and_r1, list_of_r1_roots, createdCos, true);
			if (bptr-> or_r1.size() > 0)
				convertIntArrayToAigObj (pAig, bptr->or_r1, list_of_r1_roots,  createdCos, true);
		}
		else
		{
			//Get list of r1 roots From Hash Table
		}

		#ifdef DEBUG_SKOLEM
		cout << endl;
		#endif

		for(int i = 0; i < list_of_r1_roots.size(); i++)
		{
			Aig_Obj_t* skolem_i = list_of_r1_roots[i];
			int skolem_i_size = computeSize(skolem_i, pAig); 
			#ifdef DEBUG_SKOLEM
			cout << skolem_i_size << "\t";
			#endif
			sum__skolem_function_sizes__before = sum__skolem_function_sizes__before + skolem_i_size;			
		}

		avg__skolem_function_sizes__before = (float)sum__skolem_function_sizes__before/(float)list_of_r1_roots.size();

		if(perform_reverse_substitution_before_printing)
			aigbs->performReverseSubstitutionOfSkolemFunctions(list_of_r1_roots) ;	//Perform Reverse Substitution
		#ifdef DEBUG_SKOLEM
		cout << endl;
		#endif

		for(int i = 0; i < list_of_r1_roots.size(); i++)
		{
			Aig_Obj_t* skolem_i = list_of_r1_roots[i];
			int skolem_i_size = computeSize(skolem_i, pAig); 
			#ifdef DEBUG_SKOLEM
			cout << skolem_i_size << "\t";
			#endif
			sum__skolem_function_sizes__after = sum__skolem_function_sizes__after + skolem_i_size;			
		}
		
		avg__skolem_function_sizes__after = (float)sum__skolem_function_sizes__after/(float)list_of_r1_roots.size();

		string fileName(aigFileName);
		fileName = fileName.substr(fileName.find_last_of("/") + 1);  //Get the file name;
		fileName.erase(fileName.find ("."), string::npos); //This contains the code for the raw file name;
		fileName.append("_size.dat"); 

		FILE* size_fp = fopen(fileName.c_str(), "w");
		assert(size_fp != NULL);	
		fprintf(size_fp, "%s\t%f\t%f\n", aigFileName, avg__skolem_function_sizes__before, avg__skolem_function_sizes__after);

		fclose(size_fp);		
}

/* Main function */


int main( int argc, char* argv[])
{
	environment env; 	//This initializes the MPI Environment
	communicator world;	//Creates a communicator between all the processes
	
	char* aigFileName;
	char* orderFileName, *varNameFile;
	int numAndsPerBlock;
	int numBlocks;
	int var_order = 1;
	int use_genuine_ands = 0;
	double timeOutTime = 0;
	int debug_level = 0;
	int milking_cex_on = 0;
	int print_skolem_functions = 0;//New argument added by Ajith
	bool negOutputOfF = false;
        set<string> non_occuring_variables_to_eliminate; // added by Ajith
	list<string> order_of_elimination; // added by Ajith

	char *typeOfBenchmark;
clock_t start_clock, end_clock;
	start_clock = clock();

	//double preTime, commTime;

	if (argc < 2)
	{
		cout << "Usage : parSyn input_file_name  variable_name_file variable_order variable_order_file timeOutTime print_skolem_functions compute_for_neg_F" << endl;
	//	cout << "Usage : parSF aig_file_name variable_order_file_name timeOutTime  print_skolem_functions" << endl;
//		cout << " use_genuine_ands = 1, uses only the number of genuine ands when creating blocks.  0 uses aig nodes" << endl;
		cout << endl << " Options:" << endl;
		cout <<  "1. input_file_name:  name of circuit containing the original formula in aiger or verilog format" << endl;
		cout << "2. var_name_file : file containing the names of the (output) variables. These are the variables whose Skolem functions are to be generated" << endl;
		cout << "3. variable_order :  an int which indicates which ordering to use for the input variables -  0:lexicographic, 1: least occurring first; 2:	external" << endl;
	       cout << "\n4. variable_order_file: file containing the variable order. This is ignored if variable order is 0 or 1" << endl;
		cout << "5. timeOutTime :  in seconds. timeOutTime = 0 implies that exact skolem functions will not computed at intermediate nodes" << endl;
	//	cout << "factorization/generated - for now use factorization for factorization benchmarks; generated for the remaining benchmarks" << endl;
	//	cout << " debug_level = 0 for minium verbosity and debug_level = 2 for maximum verbosity" << endl;
	//	cout << " milking_cex_on = 1 for milking counterexamples and milking_cex_on = 0 for disabling milking" << endl;
		cout << "6. print_skolem_functions = 1 for printing the skolem functions in file; 0 otherwise" << endl;
		cout << "7. Compute skolem functions for neg F (where F is the input circuit) : 1 :yes ; 0: no " << endl;

		exit (1);
	}
	else
	{

		aigFileName = argv[1];
		varNameFile = argv[2];
		var_order = atoi(argv[3]);
		orderFileName = argv[4];
		numAndsPerBlock = 1 ; // atoi(argv[3]);
		use_genuine_ands = 0 ; // atoi(argv[4]);
		timeOutTime = atof(argv[5]);
		
	//	typeOfBenchmark = "generated";

	//	debug_level = atoi(argv[5]);
	//	milking_cex_on = atoi(argv[6]);
		print_skolem_functions = atoi(argv[6]);
		if(atoi(argv[7]) == 1)
			negOutputOfF = true;
			
	}

	if (world.rank() == 0)
	{
		cout << " No. of cores = " << world.size() <<  endl;
		cout << " Starting preprocessing on " << aigFileName << endl; 
	}
#ifdef PRINT_TOTAL_TIME_BREAKUP
	clock_t start_pre_time;
	start_pre_time = clock();
#endif

#ifdef PRINT_STATISTICS
	clock_t clock1, clock2;
	clock1 = clock();
#endif
	Abc_Frame_t* pAbc;
	Abc_Start();
	pAbc = Abc_FrameGetGlobalFrame();
	if (readCleanAig (pAbc, (const char*) aigFileName))
	{
	    cerr << "Reading file not sucessful, Exiting " << endl;
	    exit (-1);
	}
	//else
	//	cout << endl << aigFileName << " was read successfully. " << endl;



	if (numBlocks == 0)
		numBlocks ++;
Aig_Man_t * pAig;
//#ifdef USE_GIA
       // Gia_Man_t *pGia  =  Abc_FrameGetGia (pAbc);
//	pAig = Gia_ManToAigSimple( pAbc->pGia );

//#else
        Abc_Ntk_t* pNtk =  Abc_FrameReadNtk (pAbc);

int negflag = 0;

if(negOutputOfF)    //Temporary Hack added for ReactSyn benchmarks - SS
{
    //Aig_Man_t *pAig_original = Abc_NtkToDar( pNtk, 0, 0);//temporary addition by Ajith
    //Aig_ManDumpVerilog (pAig_original, "original.v");//temporary addition by Ajith

    Abc_Obj_t* pCo = Abc_NtkPo(pNtk,0);
    Abc_Obj_t* pFanin = Abc_ObjChild0(pCo);

    assert (Abc_ObjRegular(pFanin));

    negflag = Abc_ObjFaninC0(pCo);

    Abc_ObjDeleteFanin(pCo, Abc_ObjFanin0(pCo));

    if (negflag)

                Abc_ObjAddFanin(pCo, pFanin);    

    else

        	Abc_ObjAddFanin(pCo,  Abc_ObjNot(pFanin)); 
}

	pAig = Abc_NtkToDar( pNtk, 0, 0);

	//Aig_ManDumpVerilog (pAig, "changed.v");//temporary addition by Ajith

	//Find what function Ajith uses to create an Aig Manager. Use the same one
//#endif

	if (Aig_ManNodeNum(pAig) == 0)
	{
		cerr << " This aig has no and nodes! Output is a constant? " << endl;
		Aig_ManStop( pAig );
		Abc_Stop();
	 	exit(1);	
	}
//Calculate the number of ands - copied from Abc_NtkPrintStats

#ifdef PRINT_STATISTICS
		clock2 = clock();
		cout << " Time taken by processor " << world.rank() << " create the AIG " << ((double) (clock2 - clock1)/CLOCKS_PER_SEC) << " seconds. " << endl;
		clock1 = clock2;
#endif

        int numDescendentsBelowNode[Aig_ManObjNum(pAig)];
        int numAndsBelowNode[Aig_ManObjNum(pAig)];
    	int markArray[Aig_ManObjNum (pAig)];	//By default all nodes are and nodes and all leaves are regular.
	map<int, Block> blockMap;
	int numAnds = 0;
	int numOrs = 0;

	fill (numDescendentsBelowNode, numDescendentsBelowNode+Aig_ManObjNum(pAig), 0);	
	fill (numAndsBelowNode, numDescendentsBelowNode+Aig_ManObjNum(pAig), 0);	
	fill (markArray, markArray+Aig_ManObjNum(pAig), 0);	
	
//Mark internal nodes as and / or nodes
	dfsAndMark( pAig, markArray,  numAnds, numOrs);

//determine how blocksize -# ands in the block

	if (numAndsPerBlock <= 0)
		numAndsPerBlock = 1;

#ifdef PRINT_STATISTICS
		clock2 = clock();
		cout << " Time taken by processor " << world.rank() << " to mark Nodes and determine block size " << ((double) (clock2 - clock1)/CLOCKS_PER_SEC) << " seconds. " << endl;
#endif
//Create  the blocks
//Many possiblities - no. of nodes, no. of and nodes, fanout of the root
//Right now using # of and nodes.

	set <int> top_lev_blocks;
	createBlocks(pAig, numAndsPerBlock, blockMap, numDescendentsBelowNode, numAndsBelowNode, markArray, top_lev_blocks, use_genuine_ands);


#ifdef PRINT_STATISTICS
			clock1 = clock();
			cout << " Time taken by processor " << world.rank() << " to mark create blocks " << ((double) (clock1 - clock2)/CLOCKS_PER_SEC) << " seconds. " << endl;
#endif

	if (blockMap.size() > 1)
		collectDependencyInfo (pAig, blockMap);

#ifdef PRINT_STATISTICS
			clock2 = clock();
			cout << " Time taken by processor " << world.rank() << " to collect dependency info " << ((double) (clock2 - clock1)/CLOCKS_PER_SEC) << " seconds. " << endl;
#endif
//Collecting Statistics
#ifdef PRINT_STATISTICS
double avg_size = 0;

int zero_blocks = 0;
int size_1_blocks = 0;
int sz;

		for (std::map<int,Block>::iterator it=blockMap.begin(); it!=blockMap.end(); ++it)
		{
			sz = 	it->second.dependsOnBlocks.size();
			if (sz == 0)
				zero_blocks ++;
			else if (sz == 1)
				size_1_blocks ++;
			else
				avg_size += sz;
		}

		cout << " I/p: No. of Ands per block " << numAndsPerBlock << "  No. of zero blocks " << zero_blocks << ". No of 1 blocks : " << size_1_blocks << " . Total # Blocks " << blockMap.size() << endl;
		cout << "Average number of dependents = " << avg_size/ (blockMap.size() - (zero_blocks + size_1_blocks)) << endl;
#endif

//Collecting Statistics ends

#ifdef PRINT_TOTAL_TIME_BREAKUP
	cerr << " Time taken by processor " << world.rank() << " to preprocess " << ((double) (clock() - start_pre_time )/CLOCKS_PER_SEC) << " seconds. " << endl;
	cerr << " #Blocks " << blockMap.size() << "." << endl;
#endif
	

	if (world.rank() == 0)
		cout << " Preprocessing Done. Starting Skolem Function Generation. " << endl;

	AIGBasedSkolem* AIGBasedSkolemObj;
	 //AIGBasedSkolemObj = new AIGBasedSkolem(pNtk, pAig, world.rank(), orderFileName, typeOfBenchmark, debug_level, milking_cex_on);
	 AIGBasedSkolemObj = new AIGBasedSkolem(pNtk, pAig,  world.rank(), var_order, orderFileName, varNameFile, debug_level, milking_cex_on, non_occuring_variables_to_eliminate, order_of_elimination);
	if(world.rank()==0)	//Process 0 generates components (opt) and sends the name of the component i to a process i to start simulation
	{
#ifdef SCHED_DEBUG
		cout << " printing dependency blocks " << endl;

		for (std::map<int,Block>::iterator it=blockMap.begin(); it!=blockMap.end(); ++it)
		{
			std::cout << it->first << " => " << it->second ;
			it->second.printDependentBlocks();	
		}
#endif
		bool solvedAtMaster = false;
		startGlobalTimer_In_Cluster(timeOutTime);
		masterCode(world, pAig, blockMap, markArray, AIGBasedSkolemObj, top_lev_blocks, timeOutTime, solvedAtMaster);	//Master node does scheduling of the blocks between processors. Also sends result data across blocks.

		bool print_skolem_function_sizes = true;
		bool perform_reverse_substitution_before_printing = true;
		if(print_skolem_function_sizes)
			printSkolemFunctionSizesToFile (pAig, blockMap, AIGBasedSkolemObj, aigFileName, solvedAtMaster, perform_reverse_substitution_before_printing);

		if(print_skolem_functions == 1)	
			printSkolemFunctionsToFile (pNtk, pAig, blockMap, markArray, AIGBasedSkolemObj, orderFileName, aigFileName, solvedAtMaster, non_occuring_variables_to_eliminate, order_of_elimination, perform_reverse_substitution_before_printing);
	}
	else 	//Processors other than rank 0 do skolem function generation on the blocks
	{
		//Call init for setting the timeout parameter
		// Added by Ajith
		startGlobalTimer_In_Cluster(timeOutTime);
		// Added by Ajith ends here

		workerCode(world, pAig, blockMap, markArray, AIGBasedSkolemObj, top_lev_blocks);
	}
		
//Cleanup
    	Aig_ManStop( pAig );
	Abc_Stop();
//Return
	end_clock = clock();
//Write results to a dat file - this is for easy plotting of results.	
	if (world.rank() ==0)
	{
		string fileName(aigFileName);
		fileName = fileName.substr(fileName.find_last_of("/") + 1);  //Get the file name;
		fileName.erase(fileName.find ("."), string::npos); //This contains the code for the raw file name;
		fileName.append(".dat"); //This contains the code for the raw file name;
		ofstream myfile;
  		myfile.open ((const char*) fileName.c_str(), std::ios::app);
  		myfile << aigFileName << " " << ((double) (end_clock - start_clock)/CLOCKS_PER_SEC) << " " << timeOutTime << " " << endl;
  		myfile.close();	
		cerr << " Total Time taken  " << ((double) (end_clock - start_clock)/CLOCKS_PER_SEC) << " seconds. " << endl;
	}
	return 0;
}



