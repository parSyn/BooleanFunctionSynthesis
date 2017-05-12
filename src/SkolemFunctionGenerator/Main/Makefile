HM_DIR = ../HashTableManager
SK_DIR = ../SkolemGenerationManager
BIN_DIR = ../../../bin

SK_INCLUDE :=  -I$(HM_DIR) -I$(SK_DIR)

OBJS = main.o $(HM_DIR)/HashTable_WithStandardKeys.o $(SK_DIR)/AbcApi.o $(SK_DIR)/helper.o $(SK_DIR)/AIGBasedSkolem.o $(SK_DIR)/undr_graph.o

$(BIN_DIR)/SkolemFunctionGenerator: $(OBJS)
	$(CC) $(OPTFLAGS) -o $@ $(OBJS) $(LIBS)

main.o : main.cc
	$(CC) $(OPTFLAGS) $(ABC_INCLUDES) $(SK_INCLUDE) $(CFLAGS) $< -o $@  

clean:
	rm -f main.o $(BIN_DIR)/SkolemFunctionGenerator

