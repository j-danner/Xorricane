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

