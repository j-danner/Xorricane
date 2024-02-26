add_library(
    xlit
    #misc
    misc.hpp
    #xlit
    xlit/xlit.hpp
    xlit/xlit.cpp
    xlit/xcls.hpp
    xlit/xcls.cpp
    #xsys
    xlit/xsys.hpp
    xlit/xsys.cpp 
)

add_library(
    xlit_lazy
    #xlit
    xlit/xlit_watch.hpp
    xlit/xcls_watch.hpp
    xlit/xcls_watch_resolver.hpp
    xlit/xcls_watch_resolver.cpp
    solver.hpp
)

add_library(
    solver
    #solve
    solve.hpp
    solve.cpp
    solver.hpp
    solver.cpp
    #heap
    order_heap/heap.h
    order_heap/vec.h
)

#find openmp package
find_package(OpenMP REQUIRED)

#find and set up boost
set(Boost_USE_STATIC_LIBS ON)
set(Boost_USE_MULTITHREADED ON)
set(Boost_USE_STATIC_RUNTIME OFF)
find_package(Boost 1.67 COMPONENTS container REQUIRED)
message(STATUS "Boost version: ${Boost_VERSION}")

target_link_libraries(xlit PUBLIC ${EXTRA_LIBS} PRIVATE OpenMP::OpenMP_CXX Boost::container)

target_link_libraries(xlit_lazy PUBLIC ${EXTRA_LIBS} PRIVATE m4ri xlit)

target_link_libraries(solver PUBLIC ${EXTRA_LIBS} PRIVATE xlit_lazy)

