add_library(
    xlit
    #misc
    misc.hpp
    #xlit
    xlit/xlit.hpp
    xlit/xlit.cpp
    xlit/xlit_watch.hpp
    xlit/xlit_watch.cpp
    xlit/xcls.hpp
    xlit/xcls.cpp
    xlit/xcls_watch.hpp
    xlit/xcls_watch.cpp
    #xsys
    xlit/xsys.hpp
    xlit/xsys.cpp 
    #hmaps
    robin_hood-3.11.5/robin_hood.h
)

add_library(
    solver
    #solve
    solve.hpp
    solve.cpp
    solver.hpp
    solver.cpp
    #misc
    misc.hpp
    #hmaps
    robin_hood-3.11.5/robin_hood.h
)

#find openmp package
find_package(OpenMP REQUIRED)

#find and set up boost
set(Boost_USE_STATIC_LIBS ON)
set(Boost_USE_MULTITHREADED ON)
set(Boost_USE_STATIC_RUNTIME OFF)
find_package(Boost 1.67 COMPONENTS container REQUIRED)
message(STATUS "Boost version: ${Boost_VERSION}")

target_link_libraries(xlit PUBLIC ${EXTRA_LIBS} PRIVATE OpenMP::OpenMP_CXX Boost::container m4ri)

target_link_libraries(solver PUBLIC ${EXTRA_LIBS} PRIVATE OpenMP::OpenMP_CXX Boost::container m4ri xlit)

