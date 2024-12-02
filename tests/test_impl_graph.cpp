//file to test implementation of impl_graph
#include "../src/xornado/impl_graph.hpp"
#include "../src/io.hpp"

#include <catch2/catch_all.hpp>

TEST_CASE( "construct xornado::options" , "[impl_graph]" ) {
    xornado::options opt = xornado::options(10,12);
    CHECK( opt.dh == xornado::dec_heu::mp );
}

TEST_CASE( "construct xornado::stats" , "[impl_graph]" ) {
    xornado::stats s;
    CHECK( s.finished == false );
}

TEST_CASE( "construct impl_graph" , "[impl_graph]" ) {
    auto clss = parse_file("../../benchmarks/instances/2xnfs/test5.xnf");
    CHECK( clss.cls.size()>0 );
    xornado::options opt = xornado::options(clss.num_vars, clss.num_cls);
    auto slvr = xornado::impl_graph(clss.cls, opt);
    //xornado::impl_graph slvr(clss.cls, opt);
    
    //slvr.preprocess();

    CHECK( slvr.get_no_v()>0 );
    CHECK( slvr.to_str() != "0" );
}
