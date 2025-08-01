//file to test implementation of cls_watch
#include "../src/cls_watch.hpp"

#include <catch2/catch_all.hpp>


TEST_CASE( "cls_watch", "[cls_watch]" ) {
    //create non-trivial lineral and checks its string repr
    vec<var_t> idxs1 = {0,3,4,5,6};
    lineral l1 = lineral(idxs1);

    vec<var_t> idxs2 = {0,1,2};
    lineral l2 = lineral(idxs2);

    vec<bool3> alpha = { bool3::None, bool3::True,bool3::True,bool3::None,bool3::None,bool3::None,bool3::None };
    CHECK( !l2.eval(alpha) );



    //auto c1 = cls_watch(l1, l2);
    //CHECK(!c1.is_sat());
    //CHECK(!c1.is_unsat());
    //CHECK(!c1.is_unit());

    //CHECK( (c1.to_str() == "x1+x2+1 x3+x4+x5+x6+1") | (c1.to_str() == "x3+x4+x5+x6+1 x1+x2+1") );

    //CHECK( c1.get_LTs().at(0) == 1 );
    //CHECK( c1.get_LTs().at(1) == 3 );
    
    ////reduce with l1+1
    //lineral reducer = l1.plus_one();
    //c1.reduce( lin_sys(reducer) );
    //CHECK(!c1.is_sat());
    //CHECK(!c1.is_unsat());
    //CHECK(c1.is_unit());
    //CHECK(c1.get_unit() == l2);
    
    //c1.backtrack( st );
    
    ////reduce with l2+1
    //reducer = l2.plus_one();
    //c1.reduce( lin_sys(reducer) );
    //CHECK(!c1.is_sat());
    //CHECK(!c1.is_unsat());
    //CHECK(c1.is_unit());
    //CHECK(c1.get_unit() == l1);
}