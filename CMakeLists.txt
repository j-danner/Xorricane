cmake_minimum_required(VERSION 3.17)

# set the project name
project(xorricane VERSION 0.4.2.9)

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

#set warnings and other default compiler options
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -W -Wall -Wextra -Wswitch -Wsign-compare -ffast-math -pthread" )# -ftree-vectorizer-verbose=5 -Weffc++")
set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -DNDEBUG")
set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -fasynchronous-unwind-tables -D_GLIBCXX_ASSERTIONS")# -D_FORTIFY_SOURCE=2 

#find jemalloc for linking
find_package(PkgConfig REQUIRED QUIET)
pkg_check_modules(JEMALLOC QUIET jemalloc)
if(JEMALLOC_FOUND)
    pkg_search_module(JEMALLOC REQUIRED jemalloc)
    message("jemalloc found!")
    include_directories(${JEMALLOC_INCLUDE_DIRS})
    execute_process(COMMAND jemalloc-config --libdir OUTPUT_VARIABLE JEMALLOC_LIBDIR OUTPUT_STRIP_TRAILING_WHITESPACE)
    execute_process(COMMAND jemalloc-config --libs OUTPUT_VARIABLE JEMALLOC_LIBS OUTPUT_STRIP_TRAILING_WHITESPACE)
    #link to static jemalloc -- libjemalloc_pic.a is the only one availabe on my arch system..
    set(EXTRA_LIBS ${EXTRA_LIBS} ${JEMALLOC_LIBDIR}/libjemalloc_pic.a ${JEMALLOC_LIBS})
    #link to dynamic jemalloc
    #set(EXTRA_LIBS ${EXTRA_LIBS} ${JEMALLOC_LIBRARIES})
    add_definitions(-DUSING_JEMALLOC)
else()
    message("jemalloc not found! (optional)")
endif()

#find ccache for faster dev-builds
find_program(CCACHE_FOUND ccache)
if (CCACHE_FOUND)
  if ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "GNU")
    # without this compiler messages in `make` backend would be uncolored
    set(CMAKE_CXX_FLAGS  "${CMAKE_CXX_FLAGS} -fdiagnostics-color=auto")
  endif()
  set_property(GLOBAL PROPERTY RULE_LAUNCH_COMPILE "ccache")
  set_property(GLOBAL PROPERTY RULE_LAUNCH_LINK "ccache")
endif()

# add subdirectories
add_subdirectory(src)

# add the main executable
add_executable(xorricane src/main.cpp src/argparse/argparse.hpp)

# link libs to xorricane
target_link_libraries(xorricane PUBLIC ${EXTRA_LIBS} PRIVATE solver)
target_include_directories(xorricane PUBLIC "${PROJECT_BINARY_DIR}" ${EXTRA_INCLUDES})

#static option -- use with caution! leads to segv on algattack...
option(STATIC "compile statically linked solver" OFF)
if(STATIC) 
    target_link_options(xorricane PUBLIC -static-libstdc++ -static-libgcc -static)
endif()

##enable march native
include(CheckCXXCompilerFlag)
CHECK_CXX_COMPILER_FLAG("-march=native" COMPILER_SUPPORTS_MARCH_NATIVE)
if(COMPILER_SUPPORTS_MARCH_NATIVE)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -march=native -mtune=native")
endif()


# set up unit tests with Catch2 - if found
find_package(Catch2 3 QUIET)
if(Catch2_FOUND)
    message("Catch2 found!")
    include(Catch)
    # These tests can use the Catch2-provided main
    add_executable(testing
        tests/test_cls_watch.cpp
        tests/test_impl_graph.cpp 
        tests/test_lin_sys_lazy.cpp
        tests/test_lin_sys.cpp
        tests/test_lineral_watch.cpp
        tests/test_lineral.cpp
        tests/test_solve.cpp
    )
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

