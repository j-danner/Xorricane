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

TEST_CASE("GaussElimEngine init detects unit and sets up watches", "[gauss_engine]") {
    GaussElimEngine ge;
    vec<bool3> alpha;
    std::list<lineral> implied;

    SECTION("unit x1=1 detected at init") {
        std::list<lineral> lins;
        lins.push_back(lineral(vec<var_t>({1}), true, presorted::yes));  // x1=1
        ge.init(lins, 2, alpha, implied);
        CHECK(ge.is_ok());
        CHECK(implied.size() == 1);
        CHECK(implied.front().is_assigning());
        CHECK(implied.front().LT() == 1);
        CHECK(implied.front().has_constant() == true);  // x1=1
    }

    SECTION("x1+x2=0 gets watches (no immediate implication)") {
        std::list<lineral> lins;
        lins.push_back(lineral(vec<var_t>({1,2}), false, presorted::yes));
        ge.init(lins, 2, alpha, implied);
        CHECK(ge.is_ok());
        CHECK(implied.empty());
        // After assigning x1=true, x2 is implied
        ge.enqueue(1, true, 1);
        ge.propagate();
        const auto& props = ge.get_new_props();
        REQUIRE(props.size() == 1);
        CHECK(props[0].first == 2);
        CHECK(props[0].second == true);  // x2=1
    }

    SECTION("conflict: x1=0 and x1=1") {
        std::list<lineral> lins;
        lins.push_back(lineral(vec<var_t>({1}), false, presorted::yes)); // x1=0
        lins.push_back(lineral(vec<var_t>({1}), true,  presorted::yes)); // x1=1
        ge.init(lins, 1, alpha, implied);
        CHECK(!ge.is_ok());
    }
}
