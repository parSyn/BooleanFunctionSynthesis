OPT_FLAGS_MORE = -g -DQE -DSKOLEM 

HM_DIR = ../HashTableManager

build : AbcApi.o helper.o AIGBasedSkolem.o undr_graph.o  

AbcApi.o: AbcApi.cpp AbcApi.hpp helper.o
	$(CC) $(OPTFLAGS) $(OPT_FLAGS_MORE)  -o $@  $(CFLAGS) AbcApi.cpp  -I $(ABC_INCLUDES)  -I$(HM_DIR) 
	
helper.o:helper.cpp helper.hpp
	$(CC) $(OPTFLAGS) $(OPT_FLAGS_MORE) -o $@ $(CFLAGS) helper.cpp  -I $(ABC_INCLUDES) -I$(HM_DIR)
	
AIGBasedSkolem.o:AIGBasedSkolem.cpp AIGBasedSkolem.hpp helper.o AbcApi.o undr_graph.o
	$(CC) $(OPTFLAGS) $(OPT_FLAGS_MORE) -o $@  $(CFLAGS)  AIGBasedSkolem.cpp  $(ABC_INCLUDES) -I$(HM_DIR)

undr_graph.o:undr_graph.cpp undr_graph.hpp
	$(CC) $(OPTFLAGS)  $(OPT_FLAGS_MORE) -o $@ $(CFLAGS) undr_graph.cpp

clean:
	rm -rf *.o 
