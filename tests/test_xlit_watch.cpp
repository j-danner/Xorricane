//file to test implementation of xlit_watch
#include "../src/xlit/xlit_watch.hpp"

#include <catch2/catch_all.hpp>


TEST_CASE( "xlit_watch", "[xlit_watch]" ) {
    vec<bool3> alpha = { bool3::None, bool3::True, bool3::True, bool3::True, bool3::False, bool3::None, bool3::None };
    vec<var_t> alpha_dl = { 0, 1, 1, 3, 2, 2, 1 };
    vec<dl_c_t> dl_count = {1,2,1};

    vec<var_t> idxs1 = {0,3,4,5,6};
    xlit l1 = xlit(idxs1);
    xlit_watch wl1(l1, alpha, alpha_dl, 0, dl_count, -1);
    REQUIRE( wl1.to_xlit().to_str() == "x3+x4+x5+x6+1");
    CHECK( !wl1.is_assigning(alpha) );

    alpha[5] = bool3::False;
    wl1.update(5, alpha);
    REQUIRE( wl1.to_xlit().to_str() == "x3+x4+x5+x6+1");
    CHECK( wl1.is_assigning(alpha) );

    //check assigning lvl if xlit can be evaluated
    vec<var_t> idxs2 = {2,3,4};
    xlit l2 = xlit(idxs2);
    xlit_watch wl2(l2, alpha, alpha_dl, 0, dl_count, -1);
    CHECK( wl2.is_assigning(alpha) );
    CHECK( wl2.get_assigning_lvl(alpha_dl) == 3 );
    
    //check assigning lvl if xlit cannot be evaluated, but is assigning
    vec<var_t> idxs3 = {0,1,2,6};
    xlit l3 = xlit(idxs3);
    xlit_watch wl3(l3, alpha, alpha_dl, 0, dl_count, -1);
    CHECK( wl3.is_assigning(alpha) );
    CHECK( wl3.get_assigning_lvl(alpha_dl) == 1 );
};

