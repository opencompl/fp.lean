.PHONY: clean all

all: test.out fma_test.out

test.o: test.cpp
	g++ -std=c++11 -O2 test.cpp -I../../third-party/ -g -c -o test.o

test.out: test.o ../../third-party/symfpu/symfpu.a
	g++ -std=c++11 -O2 ../../third-party/symfpu/symfpu.a ../../third-party/symfpu/baseTypes/simpleExecutable.o test.o -o test.out

fma_test.o: fma_test.cpp
	g++ -std=c++11 fma_test.cpp -I../../third-party/ -g -c -o fma_test.o

fma_test.out: fma_test.o
	g++ -std=c++11 ../../third-party/symfpu/symfpu.a ../../third-party/symfpu/baseTypes/simpleExecutable.o fma_test.o -o fma_test.out
	
../../third-party/symfpu/symfpu.a:
	cd ../../third-party/symfpu && make

clean:
	rm test.o test.out

