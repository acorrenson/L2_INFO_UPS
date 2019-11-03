
all: test

test: bascule_d_test
	./$^ --vcd=$^.vcd

bascule_d_test: bascule-d.o
	ghdl -e $@

bascule-d.o: bascule-d.vhd
	ghdl -a $^

clean:
	rm *.vcd *.o bascule_d_test