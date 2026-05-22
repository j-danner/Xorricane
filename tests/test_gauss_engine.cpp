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
