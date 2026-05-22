#include "../src/gauss_elim/gauss_engine.hpp"
#include "../src/lineral.hpp"
#include <catch2/catch_all.hpp>
#include <list>

TEST_CASE("GaussElimEngine init basic", "[gauss_engine]") {
    GaussElimEngine ge;
    std::list<lineral> lins;
    lins.push_back(lineral(vec<var_t>({1}), false, presorted::yes));   // x1=0
    lins.push_back(lineral(vec<var_t>({1,2}), false, presorted::yes)); // x1+x2=0
    vec<bool3> alpha;
    std::list<lineral> implied;
    ge.init(lins, 2, alpha, implied);
    // x1=0 implies x2=0 via GJ
    CHECK(ge.is_ok());
    CHECK(implied.size() >= 1);
}

TEST_CASE("GaussElimEngine GJ produces RREF", "[gauss_engine]") {
    // x1+x2+x3=0, x1+x2=0 → after GJ: row0: x1+x2=0, row1: x3=0
    GaussElimEngine ge;
    std::list<lineral> lins;
    lins.push_back(lineral(vec<var_t>({1,2,3}), false, presorted::yes));
    lins.push_back(lineral(vec<var_t>({1,2}),   false, presorted::yes));
    vec<bool3> alpha;
    std::list<lineral> implied;
    ge.init(lins, 3, alpha, implied);
    // x3=0 must be immediately implied
    CHECK(ge.is_ok());
    bool found = false;
    for(const auto& l : implied) if(l.is_assigning() && l.LT()==3) found = true;
    CHECK(found);
}
