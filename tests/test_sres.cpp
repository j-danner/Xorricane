//file to test implementation of sres
#include "../src/xlit/xcls.hpp"
#include "../src/xlit/xcls.cpp"

#include <catch2/catch_all.hpp>

TEST_CASE( "simple sres", "[sres]") {
    SECTION ("trivial sres") {
        xlit f1 = xlit(vec<var_t>({0,1,2,3    }));
        xlit f2 = xlit(vec<var_t>({  1,  3,4,5}));
        
        xcls F = xcls(vec<xlit>({f1, f2}));
        xcls G = xcls();

        xcls r = sres_opt(F,G);

        CHECK( r.to_str() == F.to_str());
    }

    SECTION( "intersection of VS" ) {
        xlit f1 = xlit(vec<var_t>({0,1,2,3    }));
        xlit f2 = xlit(vec<var_t>({  1,  3,4,5}));

        xlit g1 = xlit(vec<var_t>({0,1,2,3    }));
        xlit g2 = xlit(vec<var_t>({    2,3  ,5}));

        xcls F = xcls(vec<xlit>({f1, f2}));
        xcls G = xcls(vec<xlit>({g1, g2}));

        CHECK( F.to_str() == "x1+x3+x4+x5 x2+x4+x5" );
        CHECK( G.to_str() == "x1+x5 x2+x3+x5" );

        xsys V_F = F.get_ass_VS();
        xsys V_G = G.get_ass_VS();

        CHECK( V_F.to_str() == "x1+x3+x4+x5+1 x2+x4+x5+1" );
        CHECK( V_G.to_str() == "x1+x5+1 x2+x3+x5+1" );

        xsys V_F_cap_V_G = intersectVS( V_F, V_G );

        CHECK( V_F_cap_V_G.to_str() == "x1+x2+x3" );

        xsys V_G_cap_V_F = intersectVS( V_G, V_F );
        CHECK( V_G_cap_V_F.to_str() == V_F_cap_V_G.to_str() );

        //intersectaffineVS
        const auto& [b,a] = intersectaffineVS( V_G, V_F );
        CHECK( !b );
        CHECK( a.to_str() == "0" );

        const auto& [b_,a_] = intersectaffineVS( V_F, V_G );
        CHECK( !b_ );
        CHECK( a_.to_str() == "0" );

        //sres:
        xcls r = sres_opt(F, G);
        CHECK( r.to_str() == "x1+x5 x2+x4+x5 x3+x4+1" );

        xcls r2 = sres_opt(G, F);
        CHECK( r.to_str() == r2.to_str() );
    }

    SECTION( "intersection of VS - edge case" ) {
        xlit f1 = xlit(vec<var_t>({0,1,2,3    }));
        xlit f2 = xlit(vec<var_t>({  1,  3  ,5}));

        xlit g1 = xlit(vec<var_t>({0,1,2,3    }));
        xlit g2 = xlit(vec<var_t>({0  ,2    ,5}));

        xcls F = xcls(vec<xlit>({f1, f2}));
        xcls G = xcls(vec<xlit>({g1, g2}));

        CHECK( F.to_str() == "x1+x3+x5 x2+x5" );
        CHECK( G.to_str() == "x1+x3+x5+1 x2+x5+1" );

        xsys V_F = F.get_ass_VS();
        xsys V_G = G.get_ass_VS();

        CHECK( V_F.to_str() == "x1+x3+x5+1 x2+x5+1" );
        CHECK( V_G.to_str() == "x1+x3+x5 x2+x5" );

        xsys V_F_cap_V_G = intersectVS( V_F, V_G );

        CHECK( V_F_cap_V_G.to_str() == "x1+x2+x3" );

        CHECK( V_F.to_str() == "x1+x3+x5+1 x2+x5+1" );
        CHECK( V_G.to_str() == "x1+x3+x5 x2+x5" );

        xsys V_G_cap_V_F = intersectVS( V_G, V_F );
        CHECK( V_G_cap_V_F.to_str() == V_F_cap_V_G.to_str() );

        //intersectaffineVS
        const auto& [b,a] = intersectaffineVS( V_G, V_F );
        CHECK( b );
        CHECK( a.to_str() == "x1+x3+x5" );

        const auto& [b_,a_] = intersectaffineVS( V_F, V_G );
        CHECK( b_ );
        CHECK( a_.to_str() == "x1+x3+x5+1" );

        //sres:
        xcls r = sres_opt(F, G);
        CHECK( r.to_str() == "x1+x2+x3+1" );

        xcls r2 = sres_opt(G, F);
        CHECK( r.to_str() == r2.to_str() );
    }

    SECTION( "intersection of VS - empty" ) {
        xlit f1 = xlit(vec<var_t>({0,1,2,3,4  }));
        xlit f2 = xlit(vec<var_t>({  1,  3  ,5}));

        xlit g1 = xlit(vec<var_t>({0,1,2,3    }));
        xlit g2 = xlit(vec<var_t>({0  ,2    ,5}));

        xcls F = xcls(vec<xlit>({f1, f2}));
        xcls G = xcls(vec<xlit>({g1, g2}));

        CHECK( F.to_str() == "x1+x3+x5 x2+x4+x5" );
        CHECK( G.to_str() == "x1+x3+x5+1 x2+x5+1" );

        xsys V_F = F.get_ass_VS();
        xsys V_G = G.get_ass_VS();

        CHECK( V_F.to_str() == "x1+x3+x5+1 x2+x4+x5+1" );
        CHECK( V_G.to_str() == "x1+x3+x5 x2+x5" );

        xsys V_F_cap_V_G = intersectVS( V_F, V_G );

        CHECK( V_F_cap_V_G.to_str() == "0" );

        xsys V_G_cap_V_F = intersectVS( V_G, V_F );
        CHECK( V_G_cap_V_F.to_str() == V_F_cap_V_G.to_str() );

        //intersectaffineVS
        const auto& [b,a] = intersectaffineVS( V_G, V_F );
        CHECK( b );
        CHECK( a.to_str() == "x1+x3+x5" );

        const auto& [b_,a_] = intersectaffineVS( V_F, V_G );
        CHECK( b_ );
        CHECK( a_.to_str() == "x1+x3+x5+1" );

        //sres:
        xcls r = sres_opt(F, G);
        CHECK( r.to_str() == "x2+x5+1 x4" );

        xcls r2 = sres_opt(G, F);
        CHECK( r.to_str() == r2.to_str() );
    }

    SECTION("non-trivial sres") {
        xlit f1 = xlit(vec<var_t>({1,5}));
        xlit f2 = xlit(vec<var_t>({2}));
        xlit f3 = xlit(vec<var_t>({3}));
        xlit f4 = xlit(vec<var_t>({4}));

        xlit g1 = xlit(vec<var_t>({2,4}));
        xlit g2 = xlit(vec<var_t>({0,3,4}));

        xcls F = xcls(vec<xlit>({f1, f2, f3, f4}));
        xcls G = xcls(vec<xlit>({g1, g2}));

        CHECK( F.to_str() == "x1+x5 x2 x3 x4");
        CHECK( G.to_str() == "x2+x4 x3+x4+1");

        CHECK( F.get_ass_VS().to_str() == "x1+x5+1 x2+1 x3+1 x4+1");
        CHECK( G.get_ass_VS().to_str() == "x2+x4+1 x3+x4");

        xcls r = sres_opt(F,G);
        // pB = x2+x4 x2+x3
        // F.assVS ~ x2+x4 x2+x3 x1+x5+1 x2+1
        // G.assVS ~ x2+x4+1 x2+x3+1
        // r.assVS = x3+x4 x1+x5+1 x2+1  => cls x1+x5 x2 x3+x4+1
        // OR:
        // pB = x2+x4 x2+x3
        // F.assVS ~ x2+x4 x2+x3 x1+x5+1 x4+1
        // G.assVS ~ x2+x4+1 x2+x3+1
        // r.assVS = x3+1 x1+x5+1 x4+1  => cls x1+x5 x4 x3
        
        CHECK( (r.to_str() == "x1+x5 x2 x3+x4+1") | (r.to_str() == "x1+x5 x4 x3") );
    }
    
    SECTION("trivial sres") {
        xlit f1 = xlit(vec<var_t>({1,5}));
        xlit f2 = xlit(vec<var_t>({2}));
        xlit f3 = xlit(vec<var_t>());

        xlit g1 = xlit(vec<var_t>({2,4}));
        xlit g2 = xlit(vec<var_t>({0,3,4}));

        xcls F = xcls(vec<xlit>({f1, f2, f3}));
        xcls G = xcls(vec<xlit>({g1, g2}));

        CHECK( F.to_str() == "x1+x5 x2 0");
        CHECK( G.to_str() == "x2+x4 x3+x4+1");

        CHECK( F.get_ass_VS().to_str() == "x1+x5+1 x2+1 1");
        CHECK( G.get_ass_VS().to_str() == "x2+x4+1 x3+x4");

        xcls r = sres_opt(F,G);
        // pB = x2+x4 x2+x3
        // F.assVS ~ x2+x4 x2+x3 x1+x5+1 x2+1
        // G.assVS ~ x2+x4+1 x2+x3+1
        // r.assVS = x3+x4 x1+x5+1 x2+1  => cls x1+x5 x2 x3+x4+1

        CHECK( r.to_str() == "x2+x4 x3+x4+1" );
    }
}