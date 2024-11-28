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

target_include_directories(lineral PUBLIC ${Boost_INCLUDE_DIRS})
target_link_libraries(lineral PUBLIC ${EXTRA_LIBS})

#setup library for lazy version of lineral
add_library(
    lineral_lazy
    STATIC
    #lineral
    lineral_watch.hpp
    lineral_watch.cpp
    cls_watch.hpp
    cls_watch_resolver.hpp
    cls_watch_resolver.cpp
)
target_link_libraries(lineral_lazy PUBLIC ${EXTRA_LIBS} PRIVATE lineral)


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

# get m4ri library 
configure_file(CMakeLists.txt.m4ri m4ri-download/CMakeLists.txt)
execute_process(COMMAND "${CMAKE_COMMAND}" -G "${CMAKE_GENERATOR}" .
    WORKING_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/m4ri-download"
)
execute_process(COMMAND "${CMAKE_COMMAND}" --build .
    WORKING_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/m4ri-download"
)
find_library(M4RI_LIBRARY NAMES m4ri PATHS "${CMAKE_CURRENT_BINARY_DIR}/m4ri-src/.libs" NO_DEFAULT_PATH)
if(NOT M4RI_LIBRARY)
    message(FATAL_ERROR "m4ri library not found!")
endif()

# add impl_graph library
# options
option(USE_TRIE "Use trie for graph labels" ON)
if(USE_TRIE)
    message("using trie data structure for graph labels!")
    add_definitions(-DUSE_TRIE)
endif()

option(FULL_REDUCTION "always fully reduce vertex labels" ON) #DO NOT DEACTIVATE!
if(FULL_REDUCTION)
    message("use full-reduction for updating vertices")
    add_definitions(-DFULL_REDUCTION)
else()
    message( FATAL_ERROR "THERE ARE KNOWN BUGS when FULL_REDUCTION is OFF! -- DO NOT DEACTIVATE!")
endif()

#add graph library
add_library(
    impl_graph
    STATIC
    #misc
    xornado/misc.hpp
    #xlit
    xornado/LA/lineral.hpp
    xornado/LA/lineral.cpp
    #xsys
    xornado/LA/lineqs.hpp
    xornado/LA/lineqs.cpp 
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

target_link_libraries(impl_graph PUBLIC ${EXTRA_LIBS} ${M4RI_LIBRARY})
target_include_directories(impl_graph PUBLIC "${CMAKE_CURRENT_BINARY_DIR}/m4ri-src")


#generate 
target_link_libraries(solver PUBLIC ${EXTRA_LIBS} ${M4RI_LIBRARY} PRIVATE lineral_lazy)
target_include_directories(solver PUBLIC "${CMAKE_CURRENT_BINARY_DIR}/m4ri-src")

