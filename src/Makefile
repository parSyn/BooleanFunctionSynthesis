export MPIC = mpic++ 	
export CC = g++	
export ABC_PATH = ${HOME}/abc.latest/abc
export ABC_INCLUDES = -I$(ABC_PATH) -I$(ABC_PATH)/src
export LIBS = -lm -lpthread -lreadline -ldl -lrt -L${ABC_PATH} -labc 
export BOOST_PATH =${HOME}/boost_1_68_0
export B_INCLUDE = -I${BOOST_PATH}/boost
export BOOST_MPI_LIBS = -L${BOOST_PATH}/stage/lib  -lboost_mpi -lboost_serialization
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

