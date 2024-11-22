#setup libraries for xlit, xlit_lazy and solver
add_library(
    xlit
    #misc
    misc.hpp
    #xlit
    xlit/xlit.hpp
    xlit/xlit.cpp
    xlit/xcls.hpp
    #xsys
    xlit/xsys.hpp
    xlit/xsys.cpp 
    #rang - library for colours in terminal
    rang/rang.hpp
)

add_library(
    xlit_lazy
    #xlit
    xlit/xlit_watch.hpp
    xlit/xlit_watch.cpp
    xlit/xcls_watch.hpp
    xlit/xcls_watch_resolver.hpp
    xlit/xcls_watch_resolver.cpp
)

add_library(
    solver
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

#find and set up boost
set(Boost_USE_STATIC_LIBS ON)
set(Boost_USE_MULTITHREADED OFF)
set(Boost_USE_STATIC_RUNTIME OFF)
find_package(Boost 1.67 COMPONENTS container REQUIRED)
message(STATUS "Boost version: ${Boost_VERSION}")

target_include_directories(xlit PUBLIC ${Boost_INCLUDE_DIRS})
target_link_libraries(xlit PUBLIC ${EXTRA_LIBS})

target_link_libraries(xlit_lazy PUBLIC ${EXTRA_LIBS} PRIVATE xlit)

target_link_libraries(solver PUBLIC ${EXTRA_LIBS} PRIVATE xlit_lazy ${m4ri_library})
target_include_directories(solver PRIVATE "${CMAKE_CURRENT_BINARY_DIR}/m4ri-src")

