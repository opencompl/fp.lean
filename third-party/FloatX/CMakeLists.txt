cmake_minimum_required(VERSION 3.1)
project(FloatX)

option(BUILD_TESTS "Generate build files for unit tests" OFF)
option(BUILD_EXHAUSTIVE_TESTS "Generate build files for exhaustive tests" OFF)
option(DEVEL_TOOLS "Include development tools in build system" ON)
option(BUILD_EXAMPLES "Build examples in the example/ directory" ON)

set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_STANDARD 11)

add_subdirectory(third_party)  # third party tools and libraries

add_library(floatx INTERFACE)
target_include_directories(floatx INTERFACE src/)

if(BUILD_TESTS OR BUILD_EXHAUSTIVE_TESTS)
    enable_testing()
endif()

if(BUILD_TESTS)
    add_subdirectory(test)
endif()

if(BUILD_EXHAUSTIVE_TESTS)
    add_subdirectory(testx)
endif()

if(BUILD_EXAMPLES)
    add_subdirectory(examples)
endif()
