cmake_minimum_required(VERSION 3.8)
project(transduction CXX)
add_compile_options(-g -Wall -Wextra -Wpedantic -O3)

add_subdirectory(lib)

add_library(transduction INTERFACE)
target_include_directories(transduction INTERFACE ${CMAKE_CURRENT_SOURCE_DIR}/include)
target_link_libraries(transduction INTERFACE aig)

add_executable(tra ${CMAKE_CURRENT_SOURCE_DIR}/test/tra.cpp)
target_link_libraries(tra transduction nextbdd)

add_executable(rantra ${CMAKE_CURRENT_SOURCE_DIR}/test/rantra.cpp)
target_link_libraries(rantra transduction nextbdd)
