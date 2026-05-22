//file to test implementation of lineral_watch
#include "../src/lineral_watch.hpp"

#include <catch2/catch_all.hpp>


TEST_CASE( "lineral_watch", "[lineral_watch]" ) {
    vec<bool3> alpha = { bool3::None, bool3::True, bool3::True, bool3::True, bool3::False, bool3::None, bool3::None };
    vec<var_t> alpha_dl = { (var_t) -1, 1, 1, 3, 2, (var_t) -1, (var_t) -1 };
    vec<dl_c_t> dl_count = {1,2,1,1};

    vec<var_t> idxs1 = {0,3,4,5,6};
    lineral l1 = lineral(idxs1);
    lineral_watch wl1(l1, alpha, alpha_dl, dl_count, -1);
    REQUIRE( wl1.to_lineral().to_str() == "x3+x4+x5+x6+1");
    CHECK( !wl1.is_assigning(alpha) );

    alpha[5] = bool3::False;
    wl1.update(5, alpha, 0, dl_count);
    REQUIRE( wl1.to_lineral().to_str() == "x3+x4+x5+x6+1");
    CHECK( wl1.is_assigning(alpha) );

    //check assigning lvl if lineral can be evaluated
    vec<var_t> idxs2 = {2,3,4};
    lineral l2 = lineral(idxs2);
    lineral_watch wl2(l2, alpha, alpha_dl, dl_count, -1);
    CHECK( wl2.is_assigning(alpha) );
    CHECK( wl2.get_assigning_lvl(alpha_dl) == 3 );
    
    //check assigning lvl if lineral cannot be evaluated, but is assigning
    vec<var_t> idxs3 = {0,1,2,6};
    lineral l3 = lineral(idxs3);
    lineral_watch wl3(l3, alpha, alpha_dl, dl_count, -1);
    CHECK( wl3.is_assigning(alpha) );
    CHECK( wl3.get_assigning_lvl(alpha_dl) == 1 );

    //reduction with equiv_lits
    alpha = { bool3::None, bool3::None, bool3::None, bool3::None, bool3::None, bool3::None, bool3::None, bool3::None };
    lineral_watch lin = lineral_watch(l3, alpha, alpha_dl, dl_count, 0);
    alpha_dl = { (var_t) -1, (var_t) -1, (var_t) -1, (var_t) -1, (var_t) -1, (var_t) -1, (var_t) -1, (var_t) -1 };
    vec< equivalence > equiv_lits(8);

    SECTION( "reduction with equiv_lits 1" ) {
        equiv_lits[1].ind = 2;
        lin.reduce(alpha, alpha_dl, dl_count, equiv_lits);
        CHECK( lin.to_str()=="x6+1" );
    }
    
    SECTION( "reduction with equiv_lits 2" ) {
        equiv_lits[1].ind = 2; equiv_lits[1].polarity = true;
        lin.reduce(alpha, alpha_dl, dl_count, equiv_lits);
        CHECK( lin.to_str()=="x6" );
    }
    
    SECTION( "reduction with equiv_lits 3" ) {
        equiv_lits[1].ind = 3;
        lin.reduce(alpha, alpha_dl, dl_count, equiv_lits);
        CHECK( lin.to_str()=="x2+x3+x6+1" );
    }
    
    SECTION( "reduction with equiv_lits 4" ) {
        equiv_lits[1].ind = 6;
        lin.reduce(alpha, alpha_dl, dl_count, equiv_lits);
        CHECK( lin.to_str()=="x2+1" );
    }
    
    SECTION( "reduction with equiv_lits 5" ) {
        equiv_lits[1].ind = 2; equiv_lits[1].polarity = true;
        equiv_lits[6].ind = 7; equiv_lits[6].polarity = true;
        lin.reduce(alpha, alpha_dl, dl_count, equiv_lits);
        CHECK( lin.to_str()=="x7+1" );
    }
    
    SECTION( "reduction with equiv_lits 6" ) {
        equiv_lits[1].ind = 7; equiv_lits[1].polarity = true;
        lin.reduce(alpha, alpha_dl, dl_count, equiv_lits);
        CHECK( lin.to_str()=="x2+x6+x7" );
    }
    
    SECTION( "reduction with equiv_lits 7" ) {
        equiv_lits[1].ind = 6;
        equiv_lits[2].ind = 3;
        lin.reduce(alpha, alpha_dl, dl_count, equiv_lits);
        CHECK( lin.to_str()=="x3+1" );
    }
    
    SECTION( "reduction with equiv_lits 8" ) {
        equiv_lits[2].ind = 7;
        lin.reduce(alpha, alpha_dl, dl_count, equiv_lits);
        CHECK( lin.to_str()=="x1+x6+x7+1" );
    }
    
    SECTION( "reduction with equiv_lits 9" ) {
        equiv_lits[1].ind = 7;
        equiv_lits[2].ind = 7;
        lin.reduce(alpha, alpha_dl, dl_count, equiv_lits);
        CHECK( lin.to_str()=="x6+1" );
    }
    
    SECTION( "reduction with equiv_lits 9.1" ) {
        equiv_lits[1].ind = 3;
        equiv_lits[3].ind = 4;
        alpha[3] = bool3::False;
        alpha_dl[3] = 1;
        lin.reduce(alpha, alpha_dl, dl_count, equiv_lits);
        CHECK( lin.to_str()=="x2+x6+1" );
        alpha[3] = bool3::None;
        alpha_dl[3] = (var_t) -1;
    }
    
    SECTION( "reduction with equiv_lits 9.2" ) {
        equiv_lits[1].ind = 3;
        equiv_lits[3].ind = 4;
        alpha[4] = bool3::True;
        alpha_dl[4] = 1;
        lin.reduce(alpha, alpha_dl, dl_count, equiv_lits);
        CHECK( lin.to_str()=="x2+x6" );
        alpha[4] = bool3::None;
        alpha_dl[4] = (var_t) -1;
    }
   
   
   
    //SECTION( "reduction with equiv_lits 8" ) {
    //    equiv_lits[1].ind = 1;
    //    equiv_lits[2].ind = 2;
    //    equiv_lits[3].ind = 3;
    //    equiv_lits[4].ind = 4;
    //    equiv_lits[5].ind = 5;
    //    equiv_lits[6].ind = 6;
    //    lin.reduce(alpha, alpha_dl, dl_count, equiv_lits);
    //    CHECK( lin.to_str()=="x1+x2+x6+1" );
    //}

    lin = lineral_watch(l1, alpha, alpha_dl, dl_count, 0);
    
    SECTION( "reduction with equiv_lits 10" ) {
        equiv_lits[3].ind = 6;
        equiv_lits[4].ind = 5;
        lin.reduce(alpha, alpha_dl, dl_count, equiv_lits);
        CHECK( lin.to_str()=="1" );
    }
    
    SECTION( "reduction with equiv_lits 11" ) {
        equiv_lits[3].ind = 6; equiv_lits[3].polarity = true;
        equiv_lits[4].ind = 5;
        lin.reduce(alpha, alpha_dl, dl_count, equiv_lits);
        CHECK( lin.to_str()=="0" );
    }
    
    SECTION( "reduction with equiv_lits 12" ) {
        equiv_lits[3].ind = 4; equiv_lits[3].polarity = true;
        equiv_lits[4].ind = 5;
        lin.reduce(alpha, alpha_dl, dl_count, equiv_lits);
        CHECK( lin.to_str()=="x5+x6" );
    }

};


TEST_CASE("lineral_watch update propagation chain", "[lineral_watch]") {
    // Lineral: x3+x4+x5+x6+1; assign x3=True@dl1, x4=False@dl2, leaving x5 and x6 as watches;
    // then assign x5=True@dl2, at which point the lineral becomes assigning (x6 is forced).
    vec<bool3> alpha(8, bool3::None);
    vec<var_t>  alpha_dl(8, static_cast<var_t>(-1));
    vec<dl_c_t> dl_count = {1, 1, 1};

    // l = x3+x4+x5+x6+1
    lineral l(vec<var_t>({0, 3, 4, 5, 6}));
    lineral_watch lw(l, alpha, alpha_dl, dl_count, static_cast<var_t>(-1));
    CHECK(!lw.is_assigning(alpha));

    // Assign x3=True@dl1: update the watch for x3; lineral still has 3 free vars -> not assigning
    alpha[3] = bool3::True; alpha_dl[3] = 1;
    auto [nw1, ret1] = lw.update(3, alpha, 1, dl_count);
    CHECK(ret1 == lineral_upd_ret::UNIT);
    CHECK(!lw.is_assigning(alpha));

    // Assign x4=False@dl2: update the watch for x4; lineral still has 2 free vars -> not assigning
    alpha[4] = bool3::False; alpha_dl[4] = 2;
    auto [nw2, ret2] = lw.update(4, alpha, 2, dl_count);
    CHECK(ret2 == lineral_upd_ret::UNIT);
    CHECK(!lw.is_assigning(alpha));

    // Assign x5=True@dl2: update the watch for x5; now only x6 is free -> assigning
    alpha[5] = bool3::True; alpha_dl[5] = 2;
    auto [new_watch, upd_ret] = lw.update(5, alpha, 2, dl_count);
    CHECK(upd_ret == lineral_upd_ret::ASSIGNING);
    CHECK(lw.is_assigning(alpha));
}


TEST_CASE("lineral_watch get_assigning_lvl", "[lineral_watch]") {
    // l = x2+x3+x4; assign x2=False@dl1 and x3=True@dl3; x4 is free -> assigning
    // ws[0] holds the highest-dl assigned variable (x3@dl3), get_assigning_lvl returns dl3=3
    vec<bool3> alpha(8, bool3::None);
    vec<var_t>  alpha_dl(8, static_cast<var_t>(-1));
    vec<dl_c_t> dl_count = {1, 2, 1, 1};

    alpha[2] = bool3::False; alpha_dl[2] = 1;
    alpha[3] = bool3::True;  alpha_dl[3] = 3;
    lineral l(vec<var_t>({2, 3, 4}));
    lineral_watch lw(l, alpha, alpha_dl, dl_count, static_cast<var_t>(-1));
    REQUIRE(lw.is_assigning(alpha));
    // ws[0] is the highest-dl assigned var (x3@dl3); get_assigning_lvl returns alpha_dl[ws[0]] = 3
    CHECK(lw.get_assigning_lvl(alpha_dl) == 3);
}


TEST_CASE("lineral_watch to_lineral round-trip", "[lineral_watch]") {
    vec<bool3> alpha(5, bool3::None);
    vec<var_t>  alpha_dl(5, static_cast<var_t>(-1));
    vec<dl_c_t> dl_count = {1, 1};

    lineral original(vec<var_t>({0, 1, 3}));  // x1+x3+1
    lineral_watch lw(original, alpha, alpha_dl, dl_count, static_cast<var_t>(-1));
    // to_lineral() must return a lineral equal to the original even after assignments
    CHECK(lw.to_lineral() == original);

    // Assign x1=True@dl1: lw becomes assigning (only x3 left free)
    alpha[1] = bool3::True; alpha_dl[1] = 1;
    lw.update(1, alpha, 1, dl_count);
    CHECK(lw.is_assigning(alpha));
    // to_lineral() must still return the *original* unmodified lineral, not a reduced form
    CHECK(lw.to_lineral() == original);
}

