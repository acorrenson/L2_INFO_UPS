# compilateur vhdl
GHDL = ghdl

.PHONY: all
all: test


test: test_mux2_1 test_mux4_1

# ====================================
# Test de l'entitee mux2_1
test_mux2_1: mux2_1.o test_mux2_1.o
	${GHDL} -e test_mux2_1
	./test_mux2_1 --vcd=test_mux2_1.vcd

test_mux2_1.o: test_mux2_1.vhd
	${GHDL} -a test_mux2_1.vhd
# ====================================


# ====================================
# Test de l'entitée mux4_1
test_mux4_1: mux4_1.o mux2_1.o test_mux4_1.o
	${GHDL} -e test_mux4_1 
	./test_mux4_1 --vcd=test_mux4_1.vcd

test_mux4_1.o: test_mux4_1.vhd
	${GHDL} -a test_mux4_1.vhd
# ====================================


# ====================================
# Compilation des sources en objets
mux4_1.o: mux4_1.vhd
	${GHDL} -a mux4_1.vhd


mux2_1.o: mux2_1.vhd
	${GHDL} -a mux2_1.vhd
# ====================================


.PHONY: clean
clean:
	rm -rf *.o test_mux4_1 test_mux2_1