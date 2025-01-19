
# get m4ri library 
configure_file(CMakeLists.txt.m4ri m4ri-download/CMakeLists.txt)
execute_process(COMMAND "${CMAKE_COMMAND}" -G "${CMAKE_GENERATOR}" .
    WORKING_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/m4ri-download"
)
execute_process(COMMAND "${CMAKE_COMMAND}" --build .
    WORKING_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/m4ri-download"
)
#find_library(M4RI_LIBRARY NAMES m4ri) //load locally installed library -- not working as we need the latest git-fixes!
find_library(M4RI_LIBRARY NAMES m4ri PATHS "${CMAKE_CURRENT_BINARY_DIR}/m4ri-src/.libs" NO_DEFAULT_PATH)
if(NOT M4RI_LIBRARY)
    message(FATAL_ERROR "m4ri library could not be built!")
endif()


#setup library for linerals
add_library(
    lineral
    STATIC
    #misc
    misc.hpp
    #lineral
    lineral.hpp
    lineral.cpp
    cls.hpp
    #lin_sys
    lin_sys.hpp
    lin_sys.cpp 
    #rang - library for colours in terminal
    rang/rang.hpp
)

#find and set up boost
set(Boost_USE_STATIC_LIBS ON)
set(Boost_USE_MULTITHREADED OFF)
set(Boost_USE_STATIC_RUNTIME OFF)
find_package(Boost 1.67 COMPONENTS container REQUIRED)
message(STATUS "Boost version: ${Boost_VERSION}")

target_include_directories(lineral PUBLIC ${Boost_INCLUDE_DIRS} ${CMAKE_CURRENT_BINARY_DIR}/m4ri-src)
target_link_libraries(lineral PUBLIC ${EXTRA_LIBS} ${M4RI_LIBRARY})


##build cryptominisatlib
configure_file("${CMAKE_CURRENT_SOURCE_DIR}/cryptominisat/src/GitSHA1.cpp.in" "${CMAKE_CURRENT_BINARY_DIR}/cryptominisat/GitSHA1.cpp" @ONLY)
configure_file("${CMAKE_CURRENT_SOURCE_DIR}/cryptominisat/src/GitSHA1.h" "${CMAKE_CURRENT_BINARY_DIR}/cryptominisat/src/GitSHA1.h")

set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} ${CMAKE_CURRENT_SOURCE_DIR}/cryptominisat/cmake)
find_package(GMP REQUIRED)
include_directories( SYSTEM ${GMP_INCLUDE_DIR} )
# Needed for PicoSAT trace generation
add_definitions( -DTRACE )
# main files for lib
add_library(cms
    STATIC
    cryptominisat/src/constants.h
    cryptominisat/src/cnf.cpp
    cryptominisat/src/probe.cpp
    cryptominisat/src/oracle_use.cpp
    cryptominisat/src/backbone.cpp
    cryptominisat/src/frat.cpp
    cryptominisat/src/propengine.cpp
    cryptominisat/src/varreplacer.cpp
    cryptominisat/src/clausecleaner.cpp
    cryptominisat/src/occsimplifier.cpp
    cryptominisat/src/gatefinder.cpp
    cryptominisat/src/subsumestrengthen.cpp
    cryptominisat/src/clauseallocator.cpp
    cryptominisat/src/sccfinder.cpp
    cryptominisat/src/solverconf.cpp
    cryptominisat/src/distillerlong.cpp
    cryptominisat/src/distillerlitrem.cpp
    cryptominisat/src/distillerbin.cpp
    cryptominisat/src/distillerlongwithimpl.cpp
    cryptominisat/src/str_impl_w_impl.cpp
    cryptominisat/src/solutionextender.cpp
    cryptominisat/src/completedetachreattacher.cpp
    cryptominisat/src/searcher.cpp
    cryptominisat/src/solver.cpp
    cryptominisat/src/hyperengine.cpp
    cryptominisat/src/subsumeimplicit.cpp
    cryptominisat/src/datasync.cpp
    cryptominisat/src/reducedb.cpp
    cryptominisat/src/intree.cpp
    cryptominisat/src/searchstats.cpp
    cryptominisat/src/xorfinder.cpp
    cryptominisat/src/cardfinder.cpp
    cryptominisat/src/cryptominisat_c.cpp
    cryptominisat/src/sls.cpp
    cryptominisat/src/sqlstats.cpp
    cryptominisat/src/vardistgen.cpp
    cryptominisat/src/ccnr.cpp
    cryptominisat/src/ccnr_cms.cpp
    cryptominisat/src/lucky.cpp
    cryptominisat/src/get_clause_query.cpp
    cryptominisat/src/gaussian.cpp
    cryptominisat/src/packedrow.cpp
    cryptominisat/src/matrixfinder.cpp
    cryptominisat/src/mpicosat/mpicosat.c
    cryptominisat/src/mpicosat/version.c
    cryptominisat/src/oracle/oracle.cpp
    ${CMAKE_CURRENT_BINARY_DIR}/cryptominisat/GitSHA1.cpp
    cryptominisat/src/cryptominisat.cpp
)
target_link_libraries(cms PUBLIC ${GMP_LIBRARIES})
target_compile_options(cms PUBLIC "-Wno-all" )


#setup library for lazy version of lineral
add_library(
    lineral_lazy
    STATIC
    #lineral
    lineral_watch.hpp
    lineral_watch.cpp
    cls_watch.hpp
    cls_watch_resolver.hpp
    #linsys_watched
    lin_sys_lazy.hpp
    lin_sys_lazy.cpp
    cryptominisat/src/cryptominisat.h
    cryptominisat/src/solver.h
    cryptominisat/src/gaussian.h
)
add_dependencies(lineral_lazy cms)
target_link_libraries(lineral_lazy PUBLIC cms ${EXTRA_LIBS} lineral)



# add impl_graph library
# options
option(USE_TRIE "Use trie for graph labels" OFF) #SEGVs when turned on! ...something with ctor and dtor of vl_trie seems wrong...
if(USE_TRIE)
    message("using trie data structure for graph labels!")
    add_definitions(-DUSE_TRIE)
endif()


#add graph library
add_library(
    impl_graph
    STATIC
    #misc
    xornado/misc.hpp
    #graph
    xornado/graph/graph.hpp
    xornado/graph/graph_al.hpp
    xornado/graph/graph_al.cpp
    #impl_graph
    xornado/impl_graph.hpp
    xornado/impl_graph.cpp
    #vert_label
    xornado/vl/vl.hpp
    xornado/vl/vl_trie.hpp
    xornado/vl/vl_trie.cpp
    xornado/vl/vl_hmap.hpp
    xornado/vl/vl_hmap.cpp
    #hashmaps
    xornado/parallel-hashmap/phmap.h
    xornado/robin_hood-3.11.5/robin_hood.h
)

target_link_libraries(impl_graph PUBLIC ${EXTRA_LIBS} PRIVATE lineral ${M4RI_LIBRARY})
target_include_directories(impl_graph PUBLIC ${CMAKE_CURRENT_BINARY_DIR}/m4ri-src)

#setup library for solver
add_library(
    solver
    STATIC
    #solve
    io.hpp
    io.cpp
    misc.cpp
    solver.hpp
    solver.cpp
    #heap
    order_heap/heap.h
    order_heap/vec.h
)

#generate 
target_link_libraries(solver PUBLIC ${EXTRA_LIBS} lineral_lazy impl_graph PRIVATE ${M4RI_LIBRARY})
target_include_directories(solver PUBLIC ${CMAKE_CURRENT_BINARY_DIR}/m4ri-src)

