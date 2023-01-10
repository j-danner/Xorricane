//file to test implementation of xsys
#include "../src/xlit/xsys.hpp"

#include <catch2/catch_all.hpp>


TEST_CASE( "xsys creation/reduction/addition", "[xsys]" ) {
    auto xlits = vec<xlit>({xlit(vec<var_t>({0,1})), xlit(vec<var_t>({1,2})), xlit(vec<var_t>({0,2}))});
    xsys ls = xsys( xlits );
    CHECK( ls.to_str() == "x1+1 x2+1" );
    
    xlits = vec<xlit>({xlit(vec<var_t>({0,1})), xlit(vec<var_t>({0,1})), xlit(vec<var_t>({0,1}))});
    ls = xsys( xlits );
    CHECK( ls.to_str() == "x1+1" );
    
    xlits = vec<xlit>({xlit(vec<var_t>({0,1})), xlit(vec<var_t>({1,2})), xlit(vec<var_t>({0,2}))});
    ls = xsys( xlits );
    CHECK( ls.to_str() == "x1+1 x2+1" );
    
    
    xlits = vec<xlit>({xlit(vec<var_t>({0,1})), xlit(vec<var_t>({0,1})), xlit(vec<var_t>({0,1}))});
    ls = xsys( xlits );
    CHECK( ls.to_str() == "x1+1" );
    
    xlits = vec<xlit>({xlit(vec<var_t>({0,1})), xlit(vec<var_t>({1,2})), xlit(vec<var_t>({2,3})), xlit(vec<var_t>({3,4})), xlit(vec<var_t>({4,5}))});
    ls = xsys( xlits );
    CHECK( ls.to_str() == "x1+1 x2+1 x3+1 x4+1 x5+1" );
    CHECK( ls.reduce( xlit(vec<var_t>({0})) ).to_str() == "1" );
    CHECK( ls.reduce( xlit(vec<var_t>({1})) ).to_str() == "1" );
    CHECK( ls.reduce( xlit(vec<var_t>({0,1})) ).to_str() == "0" );
    CHECK( ls.reduce( xlit(vec<var_t>({6})) ).to_str() == "x6" );
    
    xlits = vec<xlit>({xlit(vec<var_t>({0,1,2,3})), xlit(vec<var_t>({1,2,3,5})), xlit(vec<var_t>({3,4})), xlit(vec<var_t>({0,4})), xlit(vec<var_t>({0,5,6})) });
    ls = xsys( xlits );
    CHECK( xlits[0].to_str() == "x1+x2+x3+1" );
    CHECK( xlits[1].to_str() == "x1+x2+x3+x5" );
    CHECK( xlits[2].to_str() == "x3+x4" );
    CHECK( xlits[3].to_str() == "x4+1" );
    CHECK( xlits[4].to_str() == "x5+x6+1" );

    CHECK( ls.to_str() == "x1+x2 x3+1 x4+1 x5+1 x6" );
    CHECK( ls.reduce( xlit(vec<var_t>({2})) ).to_str() == "x2" );
    CHECK( ls.reduce( xlit(vec<var_t>({2,3,0})) ).to_str() == "x2" );
    CHECK( ls.reduce( xlit(vec<var_t>({2,3,4,6,0})) ).to_str() == "x2+1" );
    vec<bool> sol(6, false);
    ls.solve( sol );
    CHECK( sol == vec<bool>({0,0,1,1,1,0}) );
    vec<bool> sol_(6, true);
    ls.solve( sol_ );
    CHECK( sol_ == vec<bool>({1,1,1,1,1,0}) );

    CHECK( xlits[0].to_str() == "x1+x2+x3+1" );
    CHECK( xlits[1].to_str() == "x1+x2+x3+x5" );
    CHECK( xlits[2].to_str() == "x3+x4" );
    CHECK( xlits[3].to_str() == "x4+1" );
    CHECK( xlits[4].to_str() == "x5+x6+1" );
    
    std::reverse(xlits.begin(), xlits.end());
    REQUIRE( xlits[4].to_str() == "x1+x2+x3+1" );
    REQUIRE( xlits[3].to_str() == "x1+x2+x3+x5" );
    REQUIRE( xlits[2].to_str() == "x3+x4" );
    REQUIRE( xlits[1].to_str() == "x4+1" );
    REQUIRE( xlits[0].to_str() == "x5+x6+1" );

    ls = xsys( xlits );

    REQUIRE( xlits[4].to_str() == "x1+x2+x3+1" );
    REQUIRE( xlits[3].to_str() == "x1+x2+x3+x5" );
    REQUIRE( xlits[2].to_str() == "x3+x4" );
    REQUIRE( xlits[1].to_str() == "x4+1" );
    REQUIRE( xlits[0].to_str() == "x5+x6+1" );

    CHECK( ls.to_str() == "x1+x2 x3+1 x4+1 x5+1 x6" );
    CHECK( ls.reduce( xlit(vec<var_t>({2})) ).to_str() == "x2" );
    CHECK( ls.reduce( xlit(vec<var_t>({2,3,0})) ).to_str() == "x2" );
    CHECK( ls.reduce( xlit(vec<var_t>({2,3,4,6,0})) ).to_str() == "x2+1" );


    //test operator +=
    xlits = vec<xlit>({xlit(vec<var_t>({0,1,2,3})), xlit(vec<var_t>({1,2,3,5}))});
    auto xlits2 = vec<xlit>({xlit(vec<var_t>({3,4})), xlit(vec<var_t>({0,4})), xlit(vec<var_t>({0,5,6})) });

    auto sys1 = xsys(xlits);
    auto sys2 = xsys(xlits2);

    REQUIRE( sys1.to_str() == "x1+x2+x3+1 x5+1");
    REQUIRE( sys2.to_str() == "x3+1 x4+1 x5+x6+1");

    sys1 += sys2;
    CHECK( sys1.to_str() == "x1+x2 x3+1 x4+1 x5+1 x6" );

    //operator +
    sys1 = xsys(xlits);
    sys2 = xsys(xlits2);

    REQUIRE( sys1.to_str() == "x1+x2+x3+1 x5+1");
    REQUIRE( sys2.to_str() == "x3+1 x4+1 x5+x6+1");

    auto sys3 = sys1+sys2;
    CHECK( sys3.to_str() == "x1+x2 x3+1 x4+1 x5+1 x6" );
}