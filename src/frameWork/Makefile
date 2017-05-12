SK_PATH = ../SkolemFunctionGenerator

HM_DIR = $(SK_PATH)/HashTableManager
SK_DIR = $(SK_PATH)/SkolemGenerationManager

SK_INCLUDE = -I$(HM_DIR) -I$(SK_DIR) 

BIN_DIR = ../../bin


OBJS = $(HM_DIR)/HashTable_WithStandardKeys.o  $(SK_DIR)/AbcApi.o  $(SK_DIR)/helper.o  $(SK_DIR)/AIGBasedSkolem.o $(SK_DIR)/undr_graph.o

all: $(BIN_DIR)/parSyn

$(BIN_DIR)/parSyn: main.o $(ABCLIB)$ $(OBJS) 
	$(MPIC)$  -g  -o $@ $<  $(OBJS) $(LIBS)$ $(BOOST_MPI_LIBS) 

main.o: main.cc
	$(MPIC)$ $ $(B_INCLUDE) $(ABC_INCLUDES) $(SK_INCLUDE) $(OPTFLAGS) $(CFLAGS) $< -o $@

clean:
	rm -f $(BIN_DIR)/parSyn *.o
