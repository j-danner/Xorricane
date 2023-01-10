//file to test implementation of xlit
#include "../src/xlit/xlit.hpp"

#include <catch2/catch_all.hpp>


TEST_CASE( "xlits creation, comparison, addition, zero/one-checks", "[xlit]" ) {
    //create xlit 0 and xlit 1 of various lengths
    xlit zero = xlit(vec<var_t>({}));
    xlit zero_ = xlit(vec<var_t>({}));
    xlit zero__ = xlit(vec<var_t>({}));
    xlit one = xlit(vec<var_t>({0}));
    xlit one_ = xlit(vec<var_t>({0}));
    xlit one__ = xlit(vec<var_t>({0}));
    
    CHECK(zero.to_str() == "0");
    CHECK(zero_.to_str() == "0");
    CHECK(zero__.to_str() == "0");
    CHECK(one.to_str() == "1");
    CHECK(one_.to_str() == "1");
    CHECK(one__.to_str() == "1");
    CHECK(zero.plus_one().to_str() == "1");
    CHECK(one.plus_one().to_str() == "0");
    zero.add_one();
    one.add_one();
    CHECK(zero.to_str() == "1");
    CHECK(one.to_str() == "0");
    zero.add_one();
    one.add_one();
    CHECK(zero.to_str() == "0");
    CHECK(one.to_str() == "1");
    CHECK(!zero.has_constant());
    CHECK(one.has_constant());

    //create non-trivial xlit and checks its string repr
    vec<var_t> idxs1 = {0,3,40,23,17,39,234,59,203};
    xlit l1 = xlit(idxs1);
    xlit l1_ = xlit(idxs1);

    vec<var_t> idxs2 = {0,3,12,23,123,234,59,203};
    xlit l2 = xlit(idxs2);

    CHECK(l1.to_str() == "x3+x17+x23+x39+x40+x59+x203+x234+1");
    CHECK(l1_.to_str() == "x3+x17+x23+x39+x40+x59+x203+x234+1");
    CHECK(l2.to_str() == "x3+x12+x23+x59+x123+x203+x234+1");

    CHECK(l1.LT() == 3);
    CHECK(l1_.LT() == 3);
    CHECK(l2.LT() == 3);

    CHECK(l1.has_constant());
    CHECK(!l1.plus_one().has_constant());

    for (size_t i = 0; i < 235; i++)
    {
        if(std::find(idxs2.begin(), idxs2.end(), i) != idxs2.end()) {
            CHECK( l2[i] );
        } else {
            CHECK( !l2[i] );
        }
    }

    //SECTION( "check is_zero and is_one" ) {
        CHECK(!one.is_zero());
        CHECK(one.is_one());
        CHECK(!one_.is_zero());
        CHECK(one_.is_one());
        CHECK(!one__.is_zero());
        CHECK(one__.is_one());
        CHECK(zero.is_zero());
        CHECK(!zero.is_one());
        CHECK(zero_.is_zero());
        CHECK(!zero_.is_one());
        CHECK(zero__.is_zero());
        CHECK(!zero__.is_one());


        CHECK(one.LT() == (var_t) 0);
        CHECK(zero.LT() == (var_t) 0);
    //}

    //SECTION( "check comparison of xlits" ) {
        CHECK(l1 == l1_);
        CHECK(!(one == zero));
        CHECK(!(one_ == zero_));
        CHECK(!(one__ == zero__));
    //}

    //SECTION( "check that get_idxs() is sorted" ) {
        std::sort(idxs1.begin(), idxs1.end());
        CHECK(l1.get_idxs() == idxs1 );
        CHECK(l1_.get_idxs() == idxs1 );
        
        std::sort(idxs2.begin(), idxs2.end());
        CHECK(l2.get_idxs() == idxs2);
    //}

    xlit f = xlit(idxs1);
    xlit g = xlit(idxs2);
    
    //change l1 and l1_ !
    l1 = xlit(vec<var_t>({0,1,2,3}));
    l1_ = xlit(vec<var_t>({3,1,2,0}));
    
    CHECK(l1 == l1_);

    //SECTION( "check string representations (2)" ) {
        CHECK(l1.to_str() == "x1+x2+x3+1");
        CHECK(l1_.to_str() == "x1+x2+x3+1");

        CHECK(l1.LT() == (var_t) 1);
    //}

    //redefine f and g
    f = xlit(vec<var_t>({0,1,2,3    }));
    g = xlit(vec<var_t>({  1,  3,4,5}));
    
    //SECTION( "test addition" ) {
        CHECK( (l1+l1).is_zero() );
        
        CHECK( (one+one).is_zero() );
        CHECK( (zero+zero).is_zero() );
        
        xlit fpg = f+g;
        xlit fpg_ = xlit(vec<var_t>({0,2,4,5}));
        CHECK(fpg == fpg_);
    //}

    f = xlit(vec<var_t>({2,3,5,10,13,16,32}));

    CHECK(f.to_str() == "x2+x3+x5+x10+x13+x16+x32");

    //SECTION( "test plus_one" ) {
        xlit fp1 = f.plus_one();
        CHECK(fp1.to_str() == "x2+x3+x5+x10+x13+x16+x32+1");

        CHECK( (f+fp1).is_one() );
    
        f = f.plus_one();
        CHECK( (f+fp1).is_zero() );
    //}
    
    //SECTION( "check assignment operator" ) {
        xlit h;
        h = f;
        CHECK(h == f);
    //}

    //SECTION( "check add_one" ) {
        xlit k(vec<var_t>({123,2315,132,42,3,5,12343,21,3,465,312}));
        xlit k_p1 = k.plus_one();
        k.add_one();
    
        CHECK(k_p1 == k);
        CHECK(k.LT() == 3);
    //}

    //comparison
    l1 =      xlit(vec<var_t>({0,1,2,3}));
    l2 =      xlit(vec<var_t>({1,2,3}));
    xlit l3 = xlit(vec<var_t>({1,6}));
    xlit l4 = xlit(vec<var_t>({1,5}));

    CHECK(l1 < l2);
    CHECK(l1 < l3);
    CHECK(l1 < l4);
    CHECK(l2 < l3);
    CHECK(l2 < l4);
    CHECK(l4 < l3);
    CHECK(one < zero);
}


TEST_CASE("eval xlit", "[xlit][xsys]"){
    xlit zero = xlit(vec<var_t>({}));
    xlit one = xlit(vec<var_t>({0}));

    vec<bool> sol = {true, false, true, true, false, true}; //note: true == 1, false == 0; ind i gets value sol[i-1]
    vec<bool3> sol3 = {bool3::None, bool3::True, bool3::False, bool3::True, bool3::True, bool3::False, bool3::True}; //note: ind i gets value sol3[i]
    CHECK(zero.eval(sol) == true);
    CHECK(one.eval(sol) == false);
    CHECK(zero.eval(sol3) == true);
    CHECK(one.eval(sol3) == false);

    xlit l = xlit(vec<var_t>({0,1,2,3}));
    CHECK(l.to_str() == "x1+x2+x3+1");
    CHECK(l.eval(sol) == false);
    CHECK(l.plus_one().eval(sol) == true);
    CHECK(l.eval(sol3) == false);
    CHECK(l.plus_one().eval(sol3) == true);
    
    l = xlit(vec<var_t>({1,3}));
    CHECK(l.to_str() == "x1+x3");
    CHECK(l.eval(sol) == false);
    CHECK(l.plus_one().eval(sol) == true);
    CHECK(l.eval(sol3) == false);
    CHECK(l.plus_one().eval(sol3) == true);
    
    
    l = xlit(vec<var_t>({1,6}));
    CHECK(l.to_str() == "x1+x6");
    CHECK(l.eval(sol) == true);
    CHECK(l.plus_one().eval(sol) == false);
    CHECK(l.eval(sol3) == true);
    CHECK(l.plus_one().eval(sol3) == false);
}