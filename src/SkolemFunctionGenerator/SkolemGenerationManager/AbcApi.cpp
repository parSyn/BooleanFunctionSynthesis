/***************************************************************************
FileName : AbcApi.cpp

SystemName: ParSyn : Parallel Boolean Funciton Synthesis Tool/ Parallel Skolem Function Generation Tool.

Authors: Dinesh Chattani, Ajith John
 
Affliation: IIT Bombay

Description: This file along with AbcApi.hpp defines class ABC, as interface with ABC tool
************************************************************/

#include <map>
#include "AbcApi.hpp"
#include "helper.hpp"


unsigned long long int ABC::nameSuffixCount;
ABC* ABC::singleton; //=NULL;

ABC::ABC()
{
    #ifdef DEBUG_SKOLEM
    cout << "starting ABC" << endl;
    #endif
    Abc_Start();
    gFrameObj = Abc_FrameAllocate();
    gFrameObj = Abc_FrameGetGlobalFrame();

//Removing dependency on abc.rc = SS */
/*    string command = "source abc.rc";
    if (comExecute(gFrameObj, command))
    {
        cout << "Cannot execute command " << command << endl;
    }
    else
    {
	#ifdef DEBUG_SKOLEM
        cout << "loaded alias file" << endl;
	#endif
    }

*/


}




