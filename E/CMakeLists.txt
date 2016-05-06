cmake_minimum_required(VERSION 3.4)
project(satori)

find_package(CGAL REQUIRED)

include(${CGAL_USE_FILE})

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O0 -std=gnu++11 -Wall -g3 -fsanitize=undefined")

add_definitions(-DDEBUG)

set(SOURCE_FILES main.cpp)
add_executable(solution ${SOURCE_FILES})
add_executable(gen gen.cpp)
#add_executable(runner runner.cpp)
add_executable(t test.cpp)