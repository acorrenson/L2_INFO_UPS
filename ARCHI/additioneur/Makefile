# compilateur vhdl
GHDL = ghdl

.PHONY: all
all: test

test: test_additionneur_1

# ====================================
# Test de l'entitée additionneur_1
test_additionneur_1: additionneur_1.o
	${GHDL} -e test_additionneur_1
	./test_additionneur_1 --vcd=test_additionneur_1.vcd
# ====================================


# ====================================
# Compilation des sources en objets
additionneur_1.o: additionneur_1.vhd
	${GHDL} -a additionneur_1.vhd
# ====================================


.PHONY: clean
clean:
	rm -rf *.o test_additionneur_1.vcd test_demi_additionneur_1