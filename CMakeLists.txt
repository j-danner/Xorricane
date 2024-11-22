cmake_minimum_required(VERSION 3.12)

# set the project name
project(xnf_cdcl_solver VERSION 0.3.0)

# specify the C++ standard
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

if(CMAKE_BUILD_TYPE)
else()
    set(CMAKE_BUILD_TYPE "Release")
endif()

# options
option(VERBOSITY "compile with verbosity outputs" ON)
if(VERBOSITY OR CMAKE_BUILD_TYPE STREQUAL "Debug") 
    add_definitions(-DVERBOSITY)
endif()

#static linking to libstdc++ and libgcc in case of Release build; otherwise give warnings!
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -W -Wall -Wextra -Wswitch -Wsign-compare -ffast-math -static-libgcc -static-libstdc++ -pthread" )# -ftree-vectorizer-verbose=5 -Weffc++")
set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -ftree-loop-vectorize -DNDEBUG")
set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -fasynchronous-unwind-tables -D_GLIBCXX_ASSERTIONS")# -D_FORTIFY_SOURCE=2 

#find jemalloc for linking
find_package(PkgConfig REQUIRED QUIET)
pkg_check_modules(JEMALLOC QUIET jemalloc)
if(JEMALLOC_FOUND)
    pkg_search_module(JEMALLOC REQUIRED jemalloc)
    message("jemalloc found!")
    include_directories(${JEMALLOC_INCLUDE_DIRS})
    set(EXTRA_LIBS ${EXTRA_LIBS} ${JEMALLOC_LIBRARIES})
    #set(EXTRA_INCLUDES ${EXTRA_INCLUDES} ${JEMALLOC_INCLUDE_DIRS})
    add_definitions(-DUSING_JEMALLOC)
else()
    message("jemalloc not found! (optional)")
endif()


# add subdirectories
add_subdirectory(src)

# add the main executable
add_executable(xnf_cdcl_solver src/main.cpp src/argparse/argparse.hpp)

# link libs to xnf_cdcl_solver
target_link_libraries(xnf_cdcl_solver PUBLIC ${EXTRA_LIBS} PRIVATE solver)
target_include_directories(xnf_cdcl_solver PUBLIC "${PROJECT_BINARY_DIR}" ${EXTRA_INCLUDES})

include(CheckCXXCompilerFlag)
CHECK_CXX_COMPILER_FLAG("-march=native" COMPILER_SUPPORTS_MARCH_NATIVE)
if(COMPILER_SUPPORTS_MARCH_NATIVE)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -march=native -mtune=native")
endif()

# get m4ri library 
configure_file(CMakeLists.txt.m4ri m4ri-download/CMakeLists.txt)
execute_process(COMMAND "${CMAKE_COMMAND}" -G "${CMAKE_GENERATOR}" .
    WORKING_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/m4ri-download"
)
execute_process(COMMAND "${CMAKE_COMMAND}" --build .
    WORKING_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/m4ri-download"
)

find_library(m4ri_library m4ri "${CMAKE_CURRENT_BINARY_DIR}/m4ri-src/.libs")

if(NOT m4ri_library)
    message(FATAL_ERROR "m4ri library not found!")
endif()


# set up unit tests with Catch2 - if found
find_package(Catch2 3 QUIET)
if(Catch2_FOUND)
    message("Catch2 found!")
    set_property(GLOBAL PROPERTY CTEST_TARGETS_ADDED ON)
    include(CTest)
    include(Catch)
    # These tests can use the Catch2-provided main
    add_executable(testing tests/test_xlit.cpp tests/test_xlit_watch.cpp tests/test_xcls_watch.cpp tests/test_xsys.cpp tests/test_solve.cpp)
    target_link_libraries(testing PUBLIC ${EXTRA_LIBS} PRIVATE solver Catch2::Catch2WithMain)
    target_include_directories(testing PUBLIC "${PROJECT_BINARY_DIR}" ${EXTRA_INCLUDES})
    catch_discover_tests(testing)
    enable_testing()
else()
    message("Catch 2 not found!")
endif()

# set up micro-benchmarks with google-bench
find_package(benchmark QUIET)
if(benchmark_FOUND)
    message("benchmark lib found!")
    add_executable(bench tests/benchmark.cpp)
    target_link_libraries(bench PUBLIC ${EXTRA_LIBS} PRIVATE benchmark::benchmark solver)
    target_include_directories(bench PUBLIC "${PROJECT_BINARY_DIR}" ${EXTRA_INCLUDES})
else()
    message("benchmark lib not found!")
endif()

get_filename_component(BENCH_FILES "../benchmarks" ABSOLUTE CACHE)
add_definitions(-DBENCH_FILES="${BENCH_FILES}")



#add compile definitions to forward compile information to program
add_compile_definitions(__CMAKE_CXX_COMPILER_ID="${CMAKE_CXX_COMPILER_ID}")
add_compile_definitions(__CMAKE_CXX_COMPILER_VERSION="${CMAKE_CXX_COMPILER_VERSION}")
add_compile_definitions(__CMAKE_CXX_STANDARD="${CMAKE_CXX_STANDARD}")
string(TOUPPER ${CMAKE_BUILD_TYPE} CMAKE_BUILD_TYPE_UPPER)
add_compile_definitions(__CMAKE_CXX_FLAGS="${CMAKE_CXX_FLAGS} ${CMAKE_CXX_FLAGS_${CMAKE_BUILD_TYPE_UPPER}}")

add_compile_definitions(__PROJECT_NAME="${PROJECT_NAME}")
add_compile_definitions(__PROJECT_VERSION="${PROJECT_VERSION}")

