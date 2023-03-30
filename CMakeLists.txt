cmake_minimum_required(VERSION 3.8)
project(transduction CXX)
add_compile_options(-g -Wall -Wextra -Wpedantic -O3)

add_subdirectory(lib)

file(GLOB FILENAMES ${CMAKE_CURRENT_SOURCE_DIR}/src/*.cpp)
add_library(transduction ${FILENAMES})
target_include_directories(transduction PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/include)
target_link_libraries(transduction nextbdd aig)

add_executable(tra ${CMAKE_CURRENT_SOURCE_DIR}/test/main.cpp)
target_link_libraries(tra transduction)
