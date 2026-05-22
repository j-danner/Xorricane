#include "../src/gauss_elim/gauss_engine.hpp"
#include "../src/lin_sys_lazy.hpp"
#include "../src/lineral.hpp"
#include <catch2/catch_all.hpp>
#include <list>

TEST_CASE("GaussElimEngine init basic", "[gauss_engine]") {
    GaussElimEngine ge;
    list<lineral> lins;
    lins.push_back(lineral(vec<var_t>({1}), false, presorted::yes));   // x1=0
    lins.push_back(lineral(vec<var_t>({1,2}), false, presorted::yes)); // x1+x2=0
    vec<bool3> alpha;
    list<lineral> implied;
    ge.init(lins, 2, alpha, implied);
    // x1=0 implies x2=0 via GJ
    CHECK(ge.is_ok());
    CHECK(implied.size() >= 1);
}

TEST_CASE("GaussElimEngine GJ produces RREF", "[gauss_engine]") {
    // x1+x2+x3=0, x1+x2=0 → after GJ: row0: x1+x2=0, row1: x3=0
    GaussElimEngine ge;
    list<lineral> lins;
    lins.push_back(lineral(vec<var_t>({1,2,3}), false, presorted::yes));
    lins.push_back(lineral(vec<var_t>({1,2}),   false, presorted::yes));
    vec<bool3> alpha;
    list<lineral> implied;
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
    list<lineral> implied;

    SECTION("unit x1=1 detected at init") {
        list<lineral> lins;
        lins.push_back(lineral(vec<var_t>({1}), true, presorted::yes));  // x1=1
        ge.init(lins, 2, alpha, implied);
        CHECK(ge.is_ok());
        CHECK(implied.size() == 1);
        CHECK(implied.front().is_assigning());
        CHECK(implied.front().LT() == 1);
        CHECK(implied.front().has_constant() == true);  // x1=1
    }

    SECTION("x1+x2=0 gets watches (no immediate implication)") {
        list<lineral> lins;
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
        list<lineral> lins;
        lins.push_back(lineral(vec<var_t>({1}), false, presorted::yes)); // x1=0
        lins.push_back(lineral(vec<var_t>({1}), true,  presorted::yes)); // x1=1
        ge.init(lins, 1, alpha, implied);
        CHECK(!ge.is_ok());
    }
}

TEST_CASE("GaussElimEngine propagation chain", "[gauss_engine]") {
    // x1+x2=0, x2+x3=0 → assign x1=TRUE → propagates x2=TRUE, x3=TRUE
    GaussElimEngine ge;
    list<lineral> lins;
    lins.push_back(lineral(vec<var_t>({1,2}), false, presorted::yes));
    lins.push_back(lineral(vec<var_t>({2,3}), false, presorted::yes));
    vec<bool3> alpha;
    list<lineral> implied;
    ge.init(lins, 3, alpha, implied);
    CHECK(implied.empty());  // no units at init

    ge.enqueue(1, true, 1);   // x1=TRUE at dl=1
    ge.propagate();

    auto& props = ge.get_new_props();
    REQUIRE(props.size() == 2);
    // Both x2 and x3 should be propagated
    bool found_x2 = false, found_x3 = false;
    for(auto& [v, val] : props) {
        if(v == 2) found_x2 = true;
        if(v == 3) found_x3 = true;
    }
    CHECK(found_x2);
    CHECK(found_x3);
}

TEST_CASE("GaussElimEngine backtrack restores state", "[gauss_engine]") {
    // x1+x2+x3=0. Assign x1=TRUE dl=1, x2=TRUE dl=2 → x3 propagates TRUE.
    // Backtrack to dl=1. x2,x3 should be unassigned. Re-assign x2=FALSE → x3=FALSE.
    GaussElimEngine ge;
    list<lineral> lins;
    lins.push_back(lineral(vec<var_t>({1,2,3}), false, presorted::yes));
    vec<bool3> alpha;
    list<lineral> implied;
    ge.init(lins, 3, alpha, implied);

    ge.push_decision_level();
    ge.enqueue(1, true, 1);
    ge.propagate();
    ge.clear_new_props();

    ge.push_decision_level();
    ge.enqueue(2, true, 2);
    ge.propagate();
    auto& props = ge.get_new_props();
    REQUIRE(props.size() == 1);
    CHECK(props[0].first == 3);  // x3 propagated
    ge.clear_new_props();

    // Backtrack to dl=1
    ge.backtrack(1);
    CHECK(ge.decision_level() == 1);
    CHECK(ge.is_ok());

    // Re-assign x2=FALSE at dl=2
    ge.push_decision_level();
    ge.enqueue(2, false, 2);
    ge.propagate();
    auto& props2 = ge.get_new_props();
    REQUIRE(props2.size() == 1);
    CHECK(props2[0].first == 3);
    ge.clear_new_props();
}

TEST_CASE("GaussElimEngine get_reason returns correct lineral", "[gauss_engine]") {
    // x1+x2+x3=0, assign x1=TRUE, x2=TRUE → propagates x3.
    // Reason for x3: the row x1+x2+x3=0
    GaussElimEngine ge;
    list<lineral> lins;
    lins.push_back(lineral(vec<var_t>({1,2,3}), false, presorted::yes));
    vec<bool3> alpha;
    list<lineral> implied;
    ge.init(lins, 3, alpha, implied);

    ge.push_decision_level();
    ge.enqueue(1, true, 1);
    ge.push_decision_level();
    ge.enqueue(2, true, 2);
    ge.propagate();

    auto& props = ge.get_new_props();
    REQUIRE(props.size() == 1);
    var_t propagated_var = props[0].first;
    CHECK(propagated_var == 3);

    lineral reason = ge.get_reason(propagated_var);
    // Reason should be x1+x2+x3=0 (or some equivalent row)
    CHECK(reason.size() == 3);
    CHECK(!reason.has_constant());  // rhs=0
    // Variables in reason are 1,2,3
    vec<var_t> vars;
    for(var_t v : reason) vars.push_back(v);
    CHECK(std::find(vars.begin(),vars.end(),1u) != vars.end());
    CHECK(std::find(vars.begin(),vars.end(),2u) != vars.end());
    CHECK(std::find(vars.begin(),vars.end(),3u) != vars.end());
}

TEST_CASE("lin_sys_lazy_GE uses GaussElimEngine", "[gauss_engine][integration]") {
    SECTION("3-variable chain: x1+x2=0, x2+x3=0") {
        lineral l1(vec<var_t>({1,2}));
        lineral l2(vec<var_t>({2,3}));
        lin_sys_lazy_GE lsl(vec<lineral>({l1, l2}), 3);
        lsl.clear_implied_literal_queue();

        vec<bool3> alpha(4, bool3::None);
        alpha[1] = bool3::True;
        bool ret = lsl.assign(1, alpha, 1);
        CHECK(ret);
        CHECK(lsl.get_implied_literal_queue().size() >= 1);
    }

    SECTION("unit lineral x3=0 at construction") {
        lineral l1(vec<var_t>({1,2,3}));
        lineral l2(vec<var_t>({1,2}));
        lin_sys_lazy_GE lsl(vec<lineral>({l1, l2}), 3);
        auto& q = lsl.get_implied_literal_queue();
        bool found = false;
        for(const auto& l : q) if(l.is_assigning() && l.LT()==3) found = true;
        CHECK(found);
    }
}
