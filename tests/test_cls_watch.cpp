#include "../src/cls_watch.hpp"
#include <catch2/catch_all.hpp>


TEST_CASE("cls_watch is_disjoint", "[cls_watch]") {
    // Disjoint: {x1,x2} and {x3,x4} share no variables
    cls_watch c1(lineral(vec<var_t>({1, 2})), lineral(vec<var_t>({3, 4})));
    CHECK(c1.is_disjoint());

    // Non-disjoint: {x1,x2} and {x2,x3} share x2
    cls_watch c2(lineral(vec<var_t>({1, 2})), lineral(vec<var_t>({2, 3})));
    CHECK(!c2.is_disjoint());

    // Disjoint with constants: constant bit (0) is not a variable
    cls_watch c3(lineral(vec<var_t>({0, 1})), lineral(vec<var_t>({0, 2})));
    CHECK(c3.is_disjoint());
}


TEST_CASE("cls_watch basic construction", "[cls_watch]") {
    cls_watch cw(lineral(vec<var_t>({1, 2})), lineral(vec<var_t>({3, 4})));
    // Under no assignment: clause is neither satisfied (at dl0) nor a unit
    CHECK(!cw.is_sat0());
    CHECK(!cw.is_unit());
}
