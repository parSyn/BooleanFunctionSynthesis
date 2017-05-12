/***************************************************************************
FileName : AbcApi.hpp

SystemName: ParSyn : Parallel Boolean Funciton Synthesis Tool/ Parallel Skolem Function Generation Tool.

Authors: Dinesh Chattani, Ajith John
 
Affliation: IIT Bombay

Description: This file along with AbcApi.cpp defines class ABC, as interface with ABC tool
************************************************************/

#ifndef ABCAPI_H
#define	ABCAPI_H

//#define DEBUG_EXECUTE // Debug option for comExecute function

#include<iostream>
#include<vector>
#include<cstring>
#include<sstream>
#include<map>
#include <sys/time.h>

using namespace std;

extern "C"
{
#include "base/abc/abc.h"
#include "base/main/mainInt.h"
#include "base/cmd/cmd.h"
#include "base/abc/abc.h"
#include "misc/nm/nmInt.h"
#include "sat/cnf/cnf.h" // Added by Ajith John on 22 April 2014
#include "sat/bsat/satStore.h" // Added by Ajith John on 22 April 2014
#include "sat/bsat/satSolver2.h" // Added by Ajith John on 30 September 2014
#include "opt/mfs/mfs.h" // Added by Ajith John on 12 January 2015
#include "opt/mfs/mfsInt.h" // Added by Ajith John on 12 January 2015
#include "bool/kit/kit.h" // Added by Ajith John on 12 January 2015

    Aig_Man_t * Abc_NtkToDar(Abc_Ntk_t * pNtk, int fExors, int fRegisters);
    Abc_Ntk_t * Abc_NtkDarCleanupAig(Abc_Ntk_t * pNtk, int fCleanupPis, int fCleanupPos, int fVerbose);
    Abc_Ntk_t * Abc_NtkFromAigPhase(Aig_Man_t * pMan);
}

class ABC
{
private:
    Abc_Frame_t* gFrameObj;
    static ABC *singleton;
protected:
    ABC();

public:
    static unsigned long long int nameSuffixCount;

    /**
     * will return the instance of ABC object
     * @return 
     */
    static ABC* getSingleton()
    {
        if (singleton == NULL)
        {
            singleton = new ABC();
        }
        return singleton;
    }

    /**
     * This will give frame of ABC so as to run ABC commands from program
     * @return 
     */
    Abc_Frame_t*& getAbcFrame()
    {
        return gFrameObj;
    }

    /**
     * Executes the given command 
     * @param pAbc
     * @param command
     * @return 
     */
    int comExecute(Abc_Frame_t * pAbc, string command)
    {
	#ifdef DEBUG_EXECUTE
        cout << endl << "Executing " << command << endl;
	unsigned long long int execution_ms;
	struct timeval exec_start_ms, exec_finish_ms;
	gettimeofday (&exec_start_ms, NULL);
	#endif

        int ret_value = Cmd_CommandExecute(pAbc, (char*) command.c_str());

	#ifdef DEBUG_EXECUTE
	gettimeofday (&exec_finish_ms, NULL);
	execution_ms = exec_finish_ms.tv_sec * 1000 + exec_finish_ms.tv_usec / 1000;
	execution_ms -= exec_start_ms.tv_sec * 1000 + exec_start_ms.tv_usec / 1000;
	cout << "Executed in " << execution_ms << " milli seconds" << endl;
	#endif
	
	return ret_value;
    }

  
    ~ABC()
    {
        //Abc_Stop();
    }
};


#endif	/* ABCAPI_H */

