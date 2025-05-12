.PHONY: clean all

all: test.out

test.o: test.cpp
	g++ -std=c++11 test.cpp -I../../third-party/FloatX/src -g -c -o test.o

test.out: test.o
	g++ -std=c++11 test.o -o test.out

clean:
	rm test.o test.out

