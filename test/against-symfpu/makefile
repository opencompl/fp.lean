.PHONY: clean all

all: test.out

test.o: test.cpp
	g++ -std=c++11 test.cpp -I../../third-party/ -g -c -o test.o

test.out: test.o ../../third-party/symfpu/symfpu.a
	g++ -std=c++11 ../../third-party/symfpu/symfpu.a ../../third-party/symfpu/baseTypes/simpleExecutable.o test.o -o test.out

../../third-party/symfpu/symfpu.a:
	cd ../../third-party/symfpu && make

clean:
	rm test.o test.out

