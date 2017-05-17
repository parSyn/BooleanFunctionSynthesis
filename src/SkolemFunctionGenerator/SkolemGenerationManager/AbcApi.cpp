/***************************************************************************
FileName : AbcApi.cpp

SystemName: ParSyn : Parallel Boolean Funciton Synthesis Tool/ Parallel Skolem Function Generation Tool.

Description: This file along with AbcApi.hpp defines class ABC, as interface with ABC tool

Copyright (C) 2017  Shetal Shah, Ajith John and Dinesh Chattani

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




