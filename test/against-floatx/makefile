.PHONY: clean all

all: test.out fma_test.out

test.o: test.cpp
	g++ -std=c++14 test.cpp -I../../third-party/FloatX/src -g -c -o test.o

test.out: test.o
	g++ -std=c++14 test.o -o test.out

fma_test.out: fma_test.cpp
	g++ -std=c++14 fma_test.cpp -I../../third-party/FloatX/src -o fma_test.out

clean:
	rm test.o test.out

