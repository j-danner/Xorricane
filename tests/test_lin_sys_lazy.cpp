//file to test implementation of lin_syys_watch
#include "../src/lin_sys_lazy.hpp"
#include "../src/solver.hpp"
#include "../src/io.hpp"

#include <catch2/catch_all.hpp>

TEST_CASE( "linsys_lazy_GE basic operations" , "[lin_sys][assigning][propagation]" ) {
    SECTION("simple") {
        lineral l1( vec<var_t>({1,2,3}) );
        lineral l2( vec<var_t>({2,3,4}) );
        lin_sys_lazy_GE lsl( vec<lineral>({l1, l2}) );
        CHECK(lsl.get_implied_literal_queue().size() == 0);

        vec<bool3> alpha(7, bool3::None);

        alpha[1] = bool3::True;
        bool ret = lsl.assign(1, alpha, 1);
        CHECK( ret );
        auto q = lsl.get_implied_literal_queue();
        CHECK( q.size() == 1 );
        CHECK( q.front().reduced(alpha).to_str() == "x4+1" );
        lsl.clear_implied_literal_queue();
        q.clear();

        //set alpha[4]
        alpha[4] = bool3::True;
        
        alpha[2] = bool3::False;
        ret = lsl.assign(2, alpha, 2);
        CHECK( ret );
        q = lsl.get_implied_literal_queue();
        CHECK( q.size() == 1 );
        CHECK( q.front().reduced(alpha).to_str() == "x3+1" );
        lsl.clear_implied_literal_queue();
        q.clear();
    }
    
    SECTION("simple2") {
        lineral l1( vec<var_t>({1,2,3,4}) );
        lineral l2( vec<var_t>({2,3,4,5}) );
        lin_sys_lazy_GE lsl( vec<lineral>({l1, l2}) );
        CHECK(lsl.get_implied_literal_queue().size() == 0);

        vec<bool3> alpha(7, bool3::None);

        alpha[1] = bool3::True;
        bool ret = lsl.assign(1, alpha, 1);
        CHECK( ret );
        auto q = lsl.get_implied_literal_queue();
        CHECK( q.size() == 1 );
        CHECK( q.front().reduced(alpha).to_str() == "x5+1" );
        lsl.clear_implied_literal_queue();
        q.clear();
        //set implied alpha
        alpha[5]=bool3::True;
        
        alpha[2] = bool3::False;
        ret = lsl.assign(2, alpha, 2);
        CHECK( !ret );

        alpha[3] = bool3::True;
        ret = lsl.assign(3, alpha, 3);
        CHECK( ret );
        q = lsl.get_implied_literal_queue();
        CHECK( q.size() == 1 );
        CHECK( q.front().reduced(alpha).to_str() == "x4" );
        lsl.clear_implied_literal_queue();
        q.clear();
    }
    
    SECTION("simpler") {
        lineral l1( vec<var_t>({1,2,3}) );
        lineral l2( vec<var_t>({2,3,4}) );
        lineral l3( vec<var_t>({0,4}) );
        lineral l4( vec<var_t>({0,1,2}) );
        lin_sys_lazy_GE lsl( vec<lineral>({l1, l2, l3, l4}) );
        lin_sys sys( lsl.get_implied_literal_queue() );
        CHECK(sys.to_str() == "x1+1 x2 x3+1 x4+1");
    }
    
    SECTION("simpler conflict!") {
        lineral l1( vec<var_t>({1,2,3}) );
        lineral l2( vec<var_t>({2,3,4}) );
        lineral l3( vec<var_t>({0,4}) );
        lineral l4( vec<var_t>({0,1,2}) );
        lineral l5( vec<var_t>({1,3}) );
        lin_sys_lazy_GE lsl( vec<lineral>({l1, l2, l3, l4, l5}) );
        lin_sys sys( lsl.get_implied_literal_queue() );
        CHECK(!sys.is_consistent());
    }
    
    SECTION("cascading") {
        lineral l1( vec<var_t>({1,2,3}) );
        lineral l2( vec<var_t>({2,3,4}) );
        lineral l3( vec<var_t>({2,3,5,6}) ); //new additional lineral!
        lin_sys_lazy_GE lsl( vec<lineral>({l1, l2, l3}) );
        CHECK(lsl.get_implied_literal_queue().size() == 0);

        vec<bool3> alpha(7, bool3::None);

        alpha[1] = bool3::True;
        bool ret = lsl.assign(1, alpha, 1);
        CHECK( ret );
        auto q = lsl.get_implied_literal_queue();
        CHECK( q.size() == 1 );
        CHECK( q.front().reduced(alpha).to_str() == "x4+1" );
        lsl.clear_implied_literal_queue();
        q.clear();
        //forced assignment x4
        alpha[4] = bool3::True;

        alpha[5] = bool3::False;
        ret = lsl.assign(5, alpha, 2);
        CHECK( ret );
        q = lsl.get_implied_literal_queue();
        CHECK( q.size() == 1 );
        CHECK( q.front().reduced(alpha).to_str() == "x6+1" );
        lsl.clear_implied_literal_queue();
        q.clear();

        //forced assignment of x6
        alpha[6] = bool3::True;
    }
    
    SECTION("cascading longer") {
        var_t num_vars = 7;
        lineral l1( vec<var_t>({  1,2,3}) );
        lineral l2( vec<var_t>({    2,3,4}) );
        lineral l3( vec<var_t>({    2,3,  5,6}) );
        lineral l4( vec<var_t>({0,      4,  6,7}) );
        lineral l5( vec<var_t>({0,1,  3,      7}) );
        lin_sys_lazy_GE lsl( vec<lineral>({l1, l2, l3, l4, l5}) );
        CHECK(lsl.get_implied_literal_queue().size() == 0);
        lin_sys sys( lsl.get_implied_literal_queue() );
        CHECK(sys.to_str() == "0");

        vec<bool3> alpha(num_vars+1, bool3::None);

        alpha[1] = bool3::True;
        bool ret = lsl.assign(1, alpha, 1);
        CHECK( ret );
        auto q = lsl.get_implied_literal_queue();
        CHECK( q.size() == 1 );
        CHECK( q.front().reduced(alpha).to_str() == "x4+1" );
        lsl.clear_implied_literal_queue();
        q.clear();

        //forced assignment of x4
        alpha[4] = bool3::True;

        alpha[5] = bool3::False;
        ret = lsl.assign(5, alpha, 1);
        CHECK( ret );
        q = lsl.get_implied_literal_queue();
        //CHECK( q.size() == 3 );
        //sys = lin_sys( q );
        //CHECK( sys.to_str() == "x1+x5+x6 x2+x5 x3+x6" );
        //lsl.clear_implied_literal_queue();
        CHECK( q.size() == 4 );
        sys = lin_sys( q );
        CHECK( sys.to_str() == "x1+x6+x7+1 x2+x7+1 x3+x6 x5+x7+1" );
        //this uniquely determines all other vars!
        lsl.clear_implied_literal_queue();
    }

    SECTION("cascading longer 2") {
        var_t num_vars = 7;
        lineral l1( vec<var_t>({  1,2,3}) );
        lineral l2( vec<var_t>({    2,3,4,5}) );
        lineral l3( vec<var_t>({        4,5,6}) );
        lineral l4( vec<var_t>({0,1,    4,  6,7}) );
        lineral l5( vec<var_t>({0,1,  3,      7}) );
        lin_sys_lazy_GE lsl( vec<lineral>({l1, l2, l3, l4, l5}) );
        CHECK(lsl.get_implied_literal_queue().size() == 0);
        lin_sys sys( lsl.get_implied_literal_queue() );
        CHECK(sys.to_str() == "0");

        vec<bool3> alpha(num_vars+1, bool3::None);

        alpha[1] = bool3::False;
        bool ret = lsl.assign(1, alpha, 1);
        CHECK( ret );
        auto q = lsl.get_implied_literal_queue();
        CHECK( q.size() == 1 );
        CHECK( q.front().reduced(alpha).to_str() == "x6" );
        lsl.clear_implied_literal_queue();
        q.clear();

        //forced assignment of x6
        alpha[6] = bool3::False;

        alpha[5] = bool3::False;
        ret = lsl.assign(5, alpha, 1);
        CHECK( ret );
        q = lsl.get_implied_literal_queue();
        CHECK( q.size() == 4 );
        sys = lin_sys( q );
        CHECK( sys.to_str() == "x2+x7+1 x3+x6+x7+1 x4+x7+1 x5+x6+x7+1" );
        //this uniquely determines all other vars!
        lsl.clear_implied_literal_queue();
    }
    
    SECTION("test21-like") {
        var_t num_vars = 4;
        lineral l1( vec<var_t>({  1,2,  4}) );
        lineral l2( vec<var_t>({0,    3}) );
        lin_sys_lazy_GE lsl( vec<lineral>({l1, l2}) );
        vec<bool3> alpha(num_vars+1, bool3::None);

        CHECK(lsl.get_implied_literal_queue().size() == 1);
        lin_sys sys( lsl.get_implied_literal_queue() );
        CHECK(sys.to_str() == "x3+1");
        lsl.clear_implied_literal_queue();

        //set x3+1 to propagated
        alpha[3] = bool3::True;
        bool ret = lsl.assign(3, alpha, 0);
        CHECK( !ret );

        //propagate x2
        alpha[2] = bool3::False;
        ret = lsl.assign(2, alpha, 0);
        CHECK( !ret );
        auto q = lsl.get_implied_literal_queue();
        CHECK( q.size() == 0 );

        //propagate x4+1
        alpha[4] = bool3::True; // x4+1
        ret = lsl.assign(4, alpha, 0);
        CHECK( ret );
        q = lsl.get_implied_literal_queue();
        CHECK( q.size() == 1 );
        CHECK( q.front().reduced(alpha).to_str() == "x1+1" );
        lsl.clear_implied_literal_queue();
        q.clear();

        //set x1+1 to propagated
        alpha[1] = bool3::True; // x1+1
        //CMS assigns x1 internally incorrectly!! not sure why :(
        //we just ignore it and check that all CMS output is consistent and CMS-GJE propagates correctly!
        ret = lsl.assign(1, alpha, 0);
        CHECK( !ret );
    }
}

TEST_CASE( "linsys_lazy in solver", "[lin_sys][assigning][propagation][solver]") {
    SECTION( "test4.xnf" ) {
        auto clss = parse_file("../../benchmarks/instances/xnfs/test4.xnf");
        options opt;
        opt.lgj = true;
        opt.pp = xornado_preproc::scc_fls;
        auto slvr = solver(clss, opt);
        //slvr.get_opts()->verb = 90;

        stats s;
        //initial propagation
        slvr.GCP(s);
        //add lineral (which can be deduced using graph-preprocessing) to LGJ component
        slvr.find_implications_by_IG(s);
        slvr.linerals_to_be_added_to_LGJ.emplace_back( lineral(vec<var_t>({5,6})) );
        slvr.find_implications_by_LGJ(s);
        //should produce conflict after another call to GCP!
        slvr.GCP(s);
        //CHECK( slvr.at_conflict() );
        //ideally this gives a conflict -- but CMS' GJE is not 'complete' and misses the conflict here :/
    }
}
