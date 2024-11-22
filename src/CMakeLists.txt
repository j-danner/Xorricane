#setup library for xlits
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

#find and set up boost
set(Boost_USE_STATIC_LIBS ON)
set(Boost_USE_MULTITHREADED OFF)
set(Boost_USE_STATIC_RUNTIME OFF)
find_package(Boost 1.67 COMPONENTS container REQUIRED)
message(STATUS "Boost version: ${Boost_VERSION}")

target_include_directories(xlit PUBLIC ${Boost_INCLUDE_DIRS})
target_link_libraries(xlit PUBLIC ${EXTRA_LIBS})

#setup library for lazy version of xlit
add_library(
    xlit_lazy
    #xlit
    xlit/xlit_watch.hpp
    xlit/xlit_watch.cpp
    xlit/xcls_watch.hpp
    xlit/xcls_watch_resolver.hpp
    xlit/xcls_watch_resolver.cpp
)
target_link_libraries(xlit_lazy PUBLIC ${EXTRA_LIBS} PRIVATE xlit)


#setup library for solver
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

#generate 
target_link_libraries(solver PUBLIC ${EXTRA_LIBS} ${m4ri_library} PRIVATE xlit_lazy)
target_include_directories(solver PUBLIC "${CMAKE_CURRENT_BINARY_DIR}/m4ri-src")

