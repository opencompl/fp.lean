include ../flags
CXXFLAGS+=-I../../
ALL=simpleExecutable.o

.PHONY : all

all : $(ALL)

%.o : %.cpp
	$(CXX) $(CXXFLAGS) -g -c $^ -o $@

