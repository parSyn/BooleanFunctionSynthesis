export MPIC = mpic++ 	
export CC = g++	
export ABC_PATH = ${HOME}/abc_latest/alanmi-abc-376aefd8fcdc
#export ABC_PATH = ${HOME}/abc
#export ABC_PATH = ${HOME}/ABC/alanmi-abc-376aefd8fcdc
export ABC_INCLUDES = -I$(ABC_PATH) -I$(ABC_PATH)/src
export LIBS = -lm -lpthread $(ABC_PATH)/libabc.a -lreadline -ldl -lrt 
#export LIBS = -lm -ldl -lreadline -lpthread -lrt $(ABC_PATH)/libabc.a
export B_INCLUDE = -I/usr/include
export BOOST_MPI_LIBS = /usr/lib/libboost_mpi.a /usr/lib/libboost_serialization.a
#export B_INCLUDE = -I/usr/local/include
#export BOOST_MPI_LIBS = /usr/local/lib/libboost_mpi.a /usr/local/lib/libboost_serialization.a
export OPTFLAGS = -g -DLIN64 -O  
export CFLAGS = -c #-Wall # -Wno-unused-function 

TOPTARGETS := all clean

SUBDIRS := SkolemFunctionGenerator/HashTableManager SkolemFunctionGenerator/SkolemGenerationManager/ SkolemFunctionGenerator/Main frameWork 

$(TOPTARGETS): $(SUBDIRS)
$(SUBDIRS):
	$(MAKE) -C $@ $(MAKECMDGOALS)

.PHONY: $(TOPTARGETS) $(SUBDIRS)

