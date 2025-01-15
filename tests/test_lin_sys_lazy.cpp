//file to test implementation of lin_syys_watch
#include "../src/lin_sys_lazy.hpp"
#include "../src/solver.hpp"

#include <catch2/catch_all.hpp>

TEST_CASE( "lin_sys_lazy_GE basic operations" , "[lin_sys][assigning][propagation]" ) {
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
        CHECK(lsl.get_implied_literal_queue().size() == 4);
    }
    
    SECTION("simpler conflict!") {
        lineral l1( vec<var_t>({1,2,3}) );
        lineral l2( vec<var_t>({2,3,4}) );
        lineral l3( vec<var_t>({0,4}) );
        lineral l4( vec<var_t>({0,1,2}) );
        lineral l5( vec<var_t>({1,3}) );
        lin_sys_lazy_GE lsl( vec<lineral>({l1, l2, l3, l4, l5}) );
        CHECK(lsl.get_implied_literal_queue().size() == 5);
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
}
