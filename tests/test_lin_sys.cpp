//file to test implementation of lin_sys
#include "../src/lin_sys.hpp"

#include <catch2/catch_all.hpp>


TEST_CASE( "lin_sys creation/reduction/addition", "[lin_sys]" ) {
    auto linerals = vec<lineral>({lineral(vec<var_t>({0,1})), lineral(vec<var_t>({1,2})), lineral(vec<var_t>({0,2}))});
    lin_sys ls = lin_sys( linerals );
    CHECK( ls.to_str() == "x1+1 x2+1" );
    
    linerals = vec<lineral>({lineral(vec<var_t>({0,1})), lineral(vec<var_t>({0,1})), lineral(vec<var_t>({0,1}))});
    ls = lin_sys( linerals );
    CHECK( ls.to_str() == "x1+1" );
    
    linerals = vec<lineral>({lineral(vec<var_t>({0,1})), lineral(vec<var_t>({1,2})), lineral(vec<var_t>({0,2}))});
    ls = lin_sys( linerals );
    CHECK( ls.to_str() == "x1+1 x2+1" );
    
    
    linerals = vec<lineral>({lineral(vec<var_t>({0,1})), lineral(vec<var_t>({0,1})), lineral(vec<var_t>({0,1}))});
    ls = lin_sys( linerals );
    CHECK( ls.to_str() == "x1+1" );
    
    linerals = vec<lineral>({lineral(vec<var_t>({0,1})), lineral(vec<var_t>({1,2})), lineral(vec<var_t>({2,3})), lineral(vec<var_t>({3,4})), lineral(vec<var_t>({4,5}))});
    ls = lin_sys( linerals );
    CHECK( ls.to_str() == "x1+1 x2+1 x3+1 x4+1 x5+1" );
    CHECK( ls.reduce( lineral(vec<var_t>({0})) ).to_str() == "1" );
    CHECK( ls.reduce( lineral(vec<var_t>({1})) ).to_str() == "1" );
    CHECK( ls.reduce( lineral(vec<var_t>({0,1})) ).to_str() == "0" );
    CHECK( ls.reduce( lineral(vec<var_t>({6})) ).to_str() == "x6" );
    
    linerals = vec<lineral>({lineral(vec<var_t>({0,1,2,3})), lineral(vec<var_t>({1,2,3,5})), lineral(vec<var_t>({3,4})), lineral(vec<var_t>({0,4})), lineral(vec<var_t>({0,5,6})) });
    ls = lin_sys( linerals );
    CHECK( linerals[0].to_str() == "x1+x2+x3+1" );
    CHECK( linerals[1].to_str() == "x1+x2+x3+x5" );
    CHECK( linerals[2].to_str() == "x3+x4" );
    CHECK( linerals[3].to_str() == "x4+1" );
    CHECK( linerals[4].to_str() == "x5+x6+1" );

    CHECK( ls.to_str() == "x1+x2 x3+1 x4+1 x5+1 x6" );
    CHECK( ls.reduce( lineral(vec<var_t>({2})) ).to_str() == "x2" );
    CHECK( ls.reduce( lineral(vec<var_t>({2,3,0})) ).to_str() == "x2" );
    CHECK( ls.reduce( lineral(vec<var_t>({2,3,4,6,0})) ).to_str() == "x2+1" );
    vec<bool> sol(6, false);
    ls.solve( sol );
    CHECK( sol == vec<bool>({0,0,1,1,1,0}) );
    vec<bool> sol_(6, true);
    ls.solve( sol_ );
    CHECK( sol_ == vec<bool>({1,1,1,1,1,0}) );

    CHECK( linerals[0].to_str() == "x1+x2+x3+1" );
    CHECK( linerals[1].to_str() == "x1+x2+x3+x5" );
    CHECK( linerals[2].to_str() == "x3+x4" );
    CHECK( linerals[3].to_str() == "x4+1" );
    CHECK( linerals[4].to_str() == "x5+x6+1" );
    
    std::reverse(linerals.begin(), linerals.end());
    REQUIRE( linerals[4].to_str() == "x1+x2+x3+1" );
    REQUIRE( linerals[3].to_str() == "x1+x2+x3+x5" );
    REQUIRE( linerals[2].to_str() == "x3+x4" );
    REQUIRE( linerals[1].to_str() == "x4+1" );
    REQUIRE( linerals[0].to_str() == "x5+x6+1" );

    ls = lin_sys( linerals );

    REQUIRE( linerals[4].to_str() == "x1+x2+x3+1" );
    REQUIRE( linerals[3].to_str() == "x1+x2+x3+x5" );
    REQUIRE( linerals[2].to_str() == "x3+x4" );
    REQUIRE( linerals[1].to_str() == "x4+1" );
    REQUIRE( linerals[0].to_str() == "x5+x6+1" );

    CHECK( ls.to_str() == "x1+x2 x3+1 x4+1 x5+1 x6" );
    CHECK( ls.reduce( lineral(vec<var_t>({2})) ).to_str() == "x2" );
    CHECK( ls.reduce( lineral(vec<var_t>({2,3,0})) ).to_str() == "x2" );
    CHECK( ls.reduce( lineral(vec<var_t>({2,3,4,6,0})) ).to_str() == "x2+1" );


    //test operator +=
    linerals = vec<lineral>({lineral(vec<var_t>({0,1,2,3})), lineral(vec<var_t>({1,2,3,5}))});
    auto linerals2 = vec<lineral>({lineral(vec<var_t>({3,4})), lineral(vec<var_t>({0,4})), lineral(vec<var_t>({0,5,6})) });

    auto sys1 = lin_sys(linerals);
    auto sys2 = lin_sys(linerals2);

    REQUIRE( sys1.to_str() == "x1+x2+x3+1 x5+1");
    REQUIRE( sys2.to_str() == "x3+1 x4+1 x5+x6+1");

    sys1 += sys2;
    CHECK( sys1.to_str() == "x1+x2 x3+1 x4+1 x5+1 x6" );

    //operator +
    sys1 = lin_sys(linerals);
    sys2 = lin_sys(linerals2);

    REQUIRE( sys1.to_str() == "x1+x2+x3+1 x5+1");
    REQUIRE( sys2.to_str() == "x3+1 x4+1 x5+x6+1");

    auto sys3 = sys1+sys2;
    CHECK( sys3.to_str() == "x1+x2 x3+1 x4+1 x5+1 x6" );


    sys3 += lin_sys(lineral(vec<var_t>({0,1,2})));
    CHECK( sys3.to_str() == "x1+x2 x3 x4 x5 x6 1" );
    CHECK( sys3.get_pivot_poly_idx().contains(0) );
    CHECK( sys3.get_pivot_poly_idx().contains(1) );
    CHECK( sys3.get_pivot_poly_idx().contains(3) );
    CHECK( sys3.get_pivot_poly_idx().contains(4) );
    CHECK( sys3.get_pivot_poly_idx().contains(5) );
    CHECK( sys3.get_pivot_poly_idx().contains(6) );
}


//TEST_CASE( "lin_sys creation addition", "[lin_sys]" ) {
//    //bug when using hashmaps as pivot_map (!)
//    lin_sys L;
//    lineral lin( "x8+x12+x13+x14+x16+x17+x18+x19+x20+x21+x23+x24+x27+x29+x30+x31+x33+x34+x35+x36+x37+x38+x40+x42+x45+x47+x48+x50+x51+x55+x56+x57+x59+x62+x63+x64+x69+x71+x73+x76+x77+x78+x82+x84+x85+x86+x87+x89+x90+x92+x95+x96+x97+x98+x100+x102+x103+x105+x106+x107+x108+x109+x111+x112+x113+x114+x117+x119+1" );
//    
//    L.add_lineral(L);
//    x6+x7+x8+x9+x10+x11+x12+x13+x14+x15+x16+x17+x18+x19+x20+x21+x25+x26+x27+x28+x32+x35+x36+x38+x40+x42+x43+x46+x47+x50+x58+x60+x61+x64+x66+x67+x70+x71+x72+x75+x76+x77+x80+x81+x82+x83+x84+x87+x89+x91+x92+x93+x94+x98+x99+x102+x103+x104+x105+x106+x110+x111+x112+x118+x120+1
//
//    x13+x16+x17+x18+x21+x22+x25+x26+x28+x29+x34+x38+x41+x43+x44+x46+x49+x50+x51+x53+x54+x59+x63+x64+x66+x69+x70+x72+x73+x75+x76+x77+x79+x83+x84+x85+x86+x88+x91+x92+x93+x94+x100+x103+x105+x106+x107+x110+x111+x114+x115
//
//    x11+x12+x14+x17+x20+x21+x24+x25+x26+x27+x30+x31+x32+x33+x36+x38+x39+x43+x47+x48+x49+x50+x51+x57+x60+x63+x65+x66+x67+x69+x71+x72+x76+x77+x79+x81+x82+x84+x85+x86+x90+x91+x92+x100+x101+x102+x104+x105+x107+x108+x109+x114+x115+x116+x120+1
//
//    x9+x10+x13+x14+x15+x16+x17+x18+x19+x20+x24+x26+x28+x30+x31+x35+x36+x37+x38+x39+x40+x41+x42+x44+x45+x49+x52+x53+x54+x56+x57+x58+x60+x61+x62+x63+x64+x65+x66+x67+x68+x69+x73+x76+x78+x83+x84+x88+x93+x94+x95+x96+x98+x101+x102+x104+x105+x109+x110+x111+x115+x117+1
//
//    x14+x76+x118
//
//    x6+x10+x11+x12+x15+x17+x20+x22+x25+x26+x28+x30+x36+x39+x40+x41+x44+x45+x48+x49+x52+x55+x58+x61+x63+x64+x65+x66+x67+x70+x71+x72+x74+x75+x76+x77+x78+x79+x80+x82+x84+x85+x86+x87+x91+x93+x95+x102+x105+x107+x108+x112+x113+x118+x119
//
//    x9+x10+x11+x12+x15+x16+x17+x18+x23+x24+x27+x29+x31+x32+x34+x35+x36+x38+x39+x41+x43+x45+x46+x47+x49+x51+x55+x56+x59+x60+x61+x63+x66+x67+x68+x71+x72+x73+x74+x75+x76+x77+x78+x79+x81+x83+x86+x93+x95+x104+x107+x108+x112+x113+x119+x120+1
//
//    x1+x3+x10+x37+x64+x66+x89+x105+x108+1
//
//    x12+x18+1
//
//    x6+x7+x8+x9+x10+x12+x13+x14+x15+x16+x17+x18+x19+x20+x21+x25+x27+x35+x36+x38+x42+x43+x44+x46+x47+x48+x51+x52+x53+x58+x62+x64+x67+x70+x71+x72+x74+x75+x76+x77+x78+x80+x81+x82+x83+x85+x87+x89+x91+x92+x93+x94+x95+x99+x100+x102+x103+x105+x106+x110+x111+x112+x114+x115+x116+x117+x118+x119
//}