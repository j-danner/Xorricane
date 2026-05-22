//file to test implementation of lineral
#include "../src/lineral.hpp"

#include <catch2/catch_all.hpp>
#include <algorithm>
#include <numeric>
#include <unordered_set>


TEST_CASE( "linerals creation, comparison, addition, zero/one-checks", "[lineral]" ) {
    //create lineral 0 and lineral 1 of various lengths
    lineral zero = lineral(vec<var_t>({}));
    lineral zero_ = lineral(vec<var_t>({}));
    lineral zero__ = lineral(vec<var_t>({}));
    lineral one = lineral(vec<var_t>({0}));
    lineral one_ = lineral(vec<var_t>({0}));
    lineral one__ = lineral(vec<var_t>({0}));
    
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

    //create non-trivial lineral and checks its string repr
    vec<var_t> idxs1 = {0,3,40,23,17,39,234,59,203};
    lineral l1 = lineral(idxs1);
    lineral l1_ = lineral(idxs1);

    vec<var_t> idxs2 = {0,3,12,23,123,234,59,203};
    lineral l2 = lineral(idxs2);

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

    //SECTION( "check comparison of linerals" ) {
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

    lineral f = lineral(idxs1);
    lineral g = lineral(idxs2);
    
    //change l1 and l1_ !
    l1 = lineral(vec<var_t>({0,1,2,3}));
    l1_ = lineral(vec<var_t>({3,1,2,0}));
    
    CHECK(l1 == l1_);

    //SECTION( "check string representations (2)" ) {
        CHECK(l1.to_str() == "x1+x2+x3+1");
        CHECK(l1_.to_str() == "x1+x2+x3+1");

        CHECK(l1.LT() == (var_t) 1);
    //}

    //redefine f and g
    f = lineral(vec<var_t>({0,1,2,3    }));
    g = lineral(vec<var_t>({  1,  3,4,5}));
    
    //SECTION( "test addition" ) {
        CHECK( (l1+l1).is_zero() );
        
        CHECK( (one+one).is_zero() );
        CHECK( (zero+zero).is_zero() );
        
        lineral fpg = f+g;
        lineral fpg_ = lineral(vec<var_t>({0,2,4,5}));
        CHECK(fpg == fpg_);
    //}

    f = lineral(vec<var_t>({2,3,5,10,13,16,32}));

    CHECK(f.to_str() == "x2+x3+x5+x10+x13+x16+x32");

    //SECTION( "test plus_one" ) {
        lineral fp1 = f.plus_one();
        CHECK(fp1.to_str() == "x2+x3+x5+x10+x13+x16+x32+1");

        CHECK( (f+fp1).is_one() );
    
        f = f.plus_one();
        CHECK( (f+fp1).is_zero() );
    //}
    
    //SECTION( "check assignment operator" ) {
        lineral h;
        h = f;
        CHECK(h == f);
    //}

    //SECTION( "check add_one" ) {
        lineral k(vec<var_t>({123,2315,132,42,3,5,12343,21,3,465,312}));
        lineral k_p1 = k.plus_one();
        k.add_one();
    
        CHECK(k_p1 == k);
        CHECK(k.LT() == 3);
    //}

    //comparison
    l1 =      lineral(vec<var_t>({0,1,2,3}));
    l2 =      lineral(vec<var_t>({1,2,3}));
    lineral l3 = lineral(vec<var_t>({1,6}));
    lineral l4 = lineral(vec<var_t>({1,5}));

    CHECK(l1 < l2);
    CHECK(l1 < l3);
    CHECK(l1 < l4);
    CHECK(l2 < l3);
    CHECK(l2 < l4);
    CHECK(l4 < l3);
    CHECK(one < zero);
}


TEST_CASE("eval lineral", "[lineral][lin_sys]"){
    lineral zero = lineral(vec<var_t>({}));
    lineral one = lineral(vec<var_t>({0}));

    vec<bool> sol = {true, false, true, true, false, true}; //note: true == 1, false == 0; ind i gets value sol[i-1]
    vec<bool3> sol3 = {bool3::None, bool3::True, bool3::False, bool3::True, bool3::True, bool3::False, bool3::True}; //note: ind i gets value sol3[i]
    CHECK(zero.eval(sol) == true);
    CHECK(one.eval(sol) == false);
    CHECK(zero.eval(sol3) == true);
    CHECK(one.eval(sol3) == false);

    lineral l = lineral(vec<var_t>({0,1,2,3}));
    CHECK(l.to_str() == "x1+x2+x3+1");
    CHECK(l.eval(sol) == false);
    CHECK(l.plus_one().eval(sol) == true);
    CHECK(l.eval(sol3) == false);
    CHECK(l.plus_one().eval(sol3) == true);
    
    l = lineral(vec<var_t>({1,3}));
    CHECK(l.to_str() == "x1+x3");
    CHECK(l.eval(sol) == true);
    CHECK(l.plus_one().eval(sol) == false);
    CHECK(l.eval(sol3) == true);
    CHECK(l.plus_one().eval(sol3) == false);
    
    l = lineral(vec<var_t>({1,6}));
    CHECK(l.to_str() == "x1+x6");
    CHECK(l.eval(sol) == true);
    CHECK(l.plus_one().eval(sol) == false);
    CHECK(l.eval(sol3) == true);
    CHECK(l.plus_one().eval(sol3) == false);
}


TEST_CASE("lineral size, get_max_var, is_constant, is_equiv, is_assigning, as_bool3", "[lineral]") {
    lineral zero;
    lineral one(cnst::one);
    lineral unit1(vec<var_t>({1}));
    lineral unit2(vec<var_t>({2}));
    lineral unit1c(vec<var_t>({0, 1}));  // x1+1
    lineral equiv(vec<var_t>({3, 7}));   // x3+x7
    lineral big(vec<var_t>({1,2,3,4,5}));

    // size() counts variables, not the constant bit
    CHECK(zero.size() == 0);
    CHECK(one.size() == 0);
    CHECK(unit1.size() == 1);
    CHECK(unit1c.size() == 1);
    CHECK(equiv.size() == 2);
    CHECK(big.size() == 5);

    // get_max_var
    CHECK(zero.get_max_var() == 0);
    CHECK(one.get_max_var() == 0);
    CHECK(unit1.get_max_var() == 1);
    CHECK(equiv.get_max_var() == 7);
    CHECK(big.get_max_var() == 5);

    // is_constant: no variables present
    CHECK(zero.is_constant());
    CHECK(one.is_constant());
    CHECK(!unit1.is_constant());
    CHECK(!equiv.is_constant());

    // is_equiv: exactly 2 variables
    CHECK(!zero.is_equiv());
    CHECK(!unit1.is_equiv());
    CHECK(equiv.is_equiv());
    CHECK(!big.is_equiv());

    // is_assigning: 0 or 1 variable
    CHECK(zero.is_assigning());
    CHECK(one.is_assigning());
    CHECK(unit1.is_assigning());
    CHECK(unit1c.is_assigning());
    CHECK(!equiv.is_assigning());
    CHECK(!big.is_assigning());

    // as_bool3: True if size==1 with constant (x1+1 evaluated as assigning True), False if size==1 no constant
    // Logic: (size()!=1 && !is_one()) ? None : (has_constant() ? True : False)
    CHECK(unit1.as_bool3() == bool3::False);
    CHECK(unit1c.as_bool3() == bool3::True);
    CHECK(zero.as_bool3() == bool3::None);  // size==0 and !is_one -> None
    CHECK(one.as_bool3() == bool3::True);   // is_one() -> condition false -> has_constant() -> True
    CHECK(equiv.as_bool3() == bool3::None);
}


TEST_CASE("lineral cnst constructor and (var_t, bool) constructor", "[lineral]") {
    lineral cz(cnst::zero);
    lineral co(cnst::one);
    CHECK(cz.is_zero());
    CHECK(co.is_one());
    CHECK(!cz.has_constant());
    CHECK(co.has_constant());

    // lineral(0, false) -> constant 1 (bit 0 set, no variables)
    lineral l0f(static_cast<var_t>(0), false);
    CHECK(l0f.is_one());
    CHECK(l0f.size() == 0);

    // lineral(0, true) -> zero (no bits set)
    lineral l0t(static_cast<var_t>(0), true);
    CHECK(l0t.is_zero());

    // lineral(v, false) -> variable v, no constant
    lineral lv(static_cast<var_t>(5), false);
    CHECK(lv.size() == 1);
    CHECK(lv.LT() == 5);
    CHECK(!lv.has_constant());

    // lineral(v, true) -> variable v + constant
    lineral lvc(static_cast<var_t>(5), true);
    CHECK(lvc.size() == 1);
    CHECK(lvc.LT() == 5);
    CHECK(lvc.has_constant());
}


TEST_CASE("lineral get_idxs_ and VarIter", "[lineral]") {
    lineral l(vec<var_t>({0, 1, 3, 5, 7}));  // constant + x1+x3+x5+x7

    // get_idxs_() excludes the constant (index 0)
    vec<var_t> vars = l.get_idxs_();
    CHECK(vars == vec<var_t>({1, 3, 5, 7}));

    // get_idxs() includes index 0 when constant is set
    vec<var_t> all = l.get_idxs();
    CHECK(all == vec<var_t>({0, 1, 3, 5, 7}));

    // range-for via VarIter yields same sequence as get_idxs_()
    vec<var_t> iter_result;
    for(var_t v : l) iter_result.push_back(v);
    CHECK(iter_result == vars);

    // zero lineral: no iterations
    lineral zero;
    int count = 0;
    for([[maybe_unused]] var_t v : zero) ++count;
    CHECK(count == 0);

    // constant-only lineral: no variable iterations
    lineral one(cnst::one);
    count = 0;
    for([[maybe_unused]] var_t v : one) ++count;
    CHECK(count == 0);

    // std::find works on the iterator (requires iterator_traits)
    CHECK(std::find(l.begin(), l.end(), static_cast<var_t>(3)) != l.end());
    CHECK(std::find(l.begin(), l.end(), static_cast<var_t>(4)) == l.end());
    CHECK(std::find(l.begin(), l.end(), static_cast<var_t>(0)) == l.end());  // constant not in var iter

    // first_var / next_var_after
    CHECK(l.first_var() == 1);
    CHECK(l.next_var_after(1) == 3);
    CHECK(l.next_var_after(3) == 5);
    CHECK(l.next_var_after(5) == 7);
    CHECK(l.next_var_after(7) == static_cast<var_t>(-1));
}


TEST_CASE("lineral operator+=, mixed sizes, multi-block", "[lineral]") {
    // Basic += agrees with +
    lineral a(vec<var_t>({1, 2, 3}));
    lineral b(vec<var_t>({2, 3, 4}));
    lineral sum = a + b;
    lineral a2(vec<var_t>({1, 2, 3}));
    a2 += b;
    CHECK(a2 == sum);
    CHECK(sum == lineral(vec<var_t>({1, 4})));

    // += is self-inverse
    lineral c(vec<var_t>({0, 5, 10}));
    lineral c_copy(c);
    c += c_copy;
    CHECK(c.is_zero());

    // mixed sizes: small += large
    lineral small(vec<var_t>({1, 2}));
    lineral large(vec<var_t>({2, 100}));
    small += large;
    CHECK(small == lineral(vec<var_t>({1, 100})));
    CHECK(small.get_max_var() == 100);

    // mixed sizes: large += small (no resize needed)
    lineral big(vec<var_t>({1, 100}));
    lineral tiny(vec<var_t>({1}));
    big += tiny;
    CHECK(big == lineral(vec<var_t>({100})));

    // multi-block: variables beyond 64 (second block)
    lineral mb1(vec<var_t>({1, 65, 127}));
    lineral mb2(vec<var_t>({65, 128}));
    lineral mb_sum = mb1 + mb2;
    CHECK(mb_sum == lineral(vec<var_t>({1, 127, 128})));

    // multi-block: XOR of identical linerals is zero
    lineral mb3(vec<var_t>({0, 10, 64, 65, 130}));
    lineral mb3_copy(mb3);
    mb3 += mb3_copy;
    CHECK(mb3.is_zero());

    // constant propagation through multi-block add
    lineral p(vec<var_t>({0, 70}));   // x70+1
    lineral q(vec<var_t>({0, 70}));   // x70+1
    CHECK((p + q).is_zero());

    lineral r(vec<var_t>({0, 70}));   // x70+1
    lineral s(vec<var_t>({70}));      // x70
    lineral rs = r + s;
    CHECK(rs.is_one());
}


TEST_CASE("lineral shared_part", "[lineral]") {
    lineral a(vec<var_t>({1, 2, 3, 5}));
    lineral b(vec<var_t>({2, 3, 4, 5}));
    lineral sp = a.shared_part(b);
    // intersection = {2,3,5}, no constant
    CHECK(sp == lineral(vec<var_t>({2, 3, 5})));
    CHECK(!sp.has_constant());

    // constant is NOT included in shared part even if both have it
    lineral ac(vec<var_t>({0, 1, 2}));  // x1+x2+1
    lineral bc(vec<var_t>({0, 2, 3}));  // x2+x3+1
    lineral spc = ac.shared_part(bc);
    CHECK(spc == lineral(vec<var_t>({2})));
    CHECK(!spc.has_constant());

    // no common variables
    lineral x(vec<var_t>({1, 3}));
    lineral y(vec<var_t>({2, 4}));
    CHECK(x.shared_part(y).is_zero());

    // shared_part with self = self (without constant)
    lineral z(vec<var_t>({0, 1, 2, 3}));
    lineral zz = z.shared_part(z);
    CHECK(zz == lineral(vec<var_t>({1, 2, 3})));
}


TEST_CASE("lineral rm", "[lineral]") {
    lineral l(vec<var_t>({1, 2, 3}));  // x1+x2+x3

    // rm variable assigned False: just removes it, no constant change
    bool changed = l.rm(2, bool3::False);
    CHECK(changed);
    CHECK(l == lineral(vec<var_t>({1, 3})));
    CHECK(!l.has_constant());

    // rm variable assigned True: removes it AND toggles constant
    changed = l.rm(1, bool3::True);
    CHECK(changed);
    CHECK(l == lineral(vec<var_t>({0, 3})));  // x3+1
    CHECK(l.has_constant());

    // rm variable assigned True again: toggles constant back
    changed = l.rm(3, bool3::True);
    CHECK(changed);
    CHECK(l.is_zero());

    // rm variable not present: returns false, no change
    lineral m(vec<var_t>({5}));
    CHECK(!m.rm(3, bool3::False));
    CHECK(m == lineral(vec<var_t>({5})));
}


TEST_CASE("lineral clear and swap", "[lineral]") {
    lineral a(vec<var_t>({0, 1, 2, 3}));
    lineral b(vec<var_t>({4, 5}));
    lineral a_orig(a);
    lineral b_orig(b);

    a.swap(b);
    CHECK(a == b_orig);
    CHECK(b == a_orig);

    a.clear();
    CHECK(a.is_zero());
    CHECK(b == a_orig);  // b unaffected
}


TEST_CASE("lineral reduce(vec<bool3>)", "[lineral]") {
    // x1+x2+x3+x4 with x2=True, x4=False
    lineral l(vec<var_t>({1, 2, 3, 4}));
    vec<bool3> alpha(10, bool3::None);
    alpha[2] = bool3::True;
    alpha[4] = bool3::False;

    bool changed = l.reduce(alpha);
    CHECK(changed);
    // x2=True contributes 1 to constant; x4=False removed without toggle
    // result: x1+x3+1
    CHECK(l.to_str() == "x1+x3+1");
    CHECK(l.has_constant());
    CHECK(l.get_idxs_() == vec<var_t>({1, 3}));

    // No assigned variables: no change
    lineral m(vec<var_t>({5, 6}));
    CHECK(!m.reduce(alpha));
    CHECK(m.to_str() == "x5+x6");

    // All variables assigned: becomes constant
    lineral n(vec<var_t>({0, 2, 4}));  // x2+x4+1
    // x2=True: removes x2, flips bit0 (constant was 1, now 0). x4=False: removes x4.
    // Result: zero lineral
    changed = n.reduce(alpha);
    CHECK(changed);
    CHECK(n.is_zero());
}


TEST_CASE("lineral reduce(vec<bool3>, alpha_dl, lvl)", "[lineral]") {
    lineral l(vec<var_t>({1, 2, 3, 4}));
    vec<bool3> alpha(10, bool3::None);
    vec<var_t> alpha_dl(10, 0);
    alpha[1] = bool3::True;  alpha_dl[1] = 1;
    alpha[2] = bool3::False; alpha_dl[2] = 3;
    alpha[3] = bool3::True;  alpha_dl[3] = 2;

    // reduce at lvl=2: only assignments at dl <= 2 apply (x1 at dl1, x3 at dl2)
    bool changed = l.reduce(alpha, alpha_dl, 2);
    CHECK(changed);
    // x1=True: flip constant (was 0, now 1); remove x1
    // x3=True: flip constant (was 1, now 0); remove x3
    // x2 at dl3 > 2: skipped. x4: unassigned.
    CHECK(l.to_str() == "x2+x4");
    CHECK(l.get_idxs_() == vec<var_t>({2, 4}));

    // reduce at lvl=3: now x2=False also applies
    changed = l.reduce(alpha, alpha_dl, 3);
    CHECK(changed);
    CHECK(l.to_str() == "x4");
    CHECK(l.get_idxs_() == vec<var_t>({4}));
}


TEST_CASE("lineral reduce(vec<lineral>)", "[lineral]") {
    // assignments: x1 -> x3+x5, x3 -> x7
    vec<lineral> assignments(10);
    assignments[1] = lineral(vec<var_t>({1, 3, 5}));  // x1 ~ x3+x5 (LT=1)
    assignments[3] = lineral(vec<var_t>({3, 7}));      // x3 ~ x7   (LT=3)

    // reduce x1+x2: x1 -> x3+x5, then x3 -> x7 -> x2+x5+x7
    lineral l(vec<var_t>({1, 2}));
    bool changed = l.reduce(assignments);
    CHECK(changed);
    // x1 += {1,3,5} => x2+x3+x5; then x3 += {3,7} => x2+x5+x7
    CHECK(l.to_str() == "x2+x5+x7");
    CHECK(l.get_idxs_() == vec<var_t>({2, 5, 7}));

    // No reducible variables: no change
    lineral m(vec<var_t>({2, 4}));
    CHECK(!m.reduce(assignments));
    CHECK(m.to_str() == "x2+x4");
}


TEST_CASE("lineral reduce(vec<equivalence>)", "[lineral]") {
    // equiv: x2 ~ x5 (polarity=false means x2+x5=0)
    vec<equivalence> equivs(10);
    equivs[2] = equivalence(5, false, 0);  // x2 <-> x5, no constant

    lineral l(vec<var_t>({1, 2, 3}));  // x1+x2+x3
    bool changed = l.reduce(equivs);
    CHECK(changed);
    // x2 replaced by x5: x1+x2+x3 += x2+x5 => x1+x3+x5
    CHECK(l.to_str() == "x1+x3+x5");
    CHECK(l.get_idxs_() == vec<var_t>({1, 3, 5}));

    // equiv with polarity: x2 ~ x5+1
    vec<equivalence> equivs2(10);
    equivs2[2] = equivalence(5, true, 0);  // x2+x5+1=0, i.e. x2=x5+1

    lineral l2(vec<var_t>({1, 2, 3}));
    changed = l2.reduce(equivs2);
    CHECK(changed);
    // x2 replaced by x5+1: x1+x2+x3 += x2+x5+1 => x1+x3+x5+1
    CHECK(l2.to_str() == "x1+x3+x5+1");
    CHECK(l2.has_constant());
    CHECK(l2.get_idxs_() == vec<var_t>({1, 3, 5}));
}


TEST_CASE("lineral hash", "[lineral]") {
    lineral a(vec<var_t>({1, 2, 3}));
    lineral b(vec<var_t>({1, 2, 3}));
    lineral c(vec<var_t>({1, 2, 4}));

    // equal linerals have equal hashes
    CHECK(a.hash() == b.hash());
    // different linerals should have different hashes (not guaranteed but expected)
    CHECK(a.hash() != c.hash());

    // std::hash specialisation works
    std::unordered_set<lineral> s;
    s.insert(a);
    CHECK(s.count(b) == 1);
    CHECK(s.count(c) == 0);

    // zero and one have distinct hashes
    lineral zero;
    lineral one(cnst::one);
    CHECK(zero.hash() != one.hash());
}


TEST_CASE("lineral to_xnf_str", "[lineral]") {
    // No constant: starts with '-'
    lineral l(vec<var_t>({1, 3, 5}));
    CHECK(l.to_xnf_str() == "-1+3+5");

    // With constant: no leading '-'
    lineral lc(vec<var_t>({0, 1, 3}));
    CHECK(lc.to_xnf_str() == "1+3");

    // Zero lineral: empty string
    lineral zero;
    CHECK(zero.to_xnf_str() == "");

    // Constant-one lineral: no variables, has constant -> no '-', no vars -> ""?
    // to_xnf_str: if size()==0 && !has_constant() return ""; else: if !constant append '-', then vars
    // one has constant, size==0 -> str is "" (no vars appended)
    lineral one(cnst::one);
    CHECK(one.to_xnf_str() == "");
}


TEST_CASE("lineral move semantics", "[lineral]") {
    lineral a(vec<var_t>({0, 1, 2, 3}));
    lineral a_copy(a);

    lineral b(std::move(a));
    CHECK(b == a_copy);
    // a is now in a valid but unspecified state (bitvec_ moved-from)

    lineral c;
    c = std::move(b);
    CHECK(c == a_copy);
}


TEST_CASE("lineral large (multi-block) correctness", "[lineral]") {
    // Build a lineral spanning 3 uint64 blocks (vars 1..130)
    vec<var_t> vars1, vars2;
    for(var_t i = 1; i <= 64; i += 2) vars1.push_back(i);   // odd vars 1..63
    for(var_t i = 2; i <= 130; i += 2) vars2.push_back(i);  // even vars 2..130

    lineral l1(vars1);
    lineral l2(vars2);

    // sum: all vars 1..130 appear exactly once (no overlap), so size = 64+65 - 0 overlap...
    // Actually odds 1,3,...,63 = 32 vars; evens 2,4,...,130 = 65 vars. No overlap.
    lineral lsum = l1 + l2;
    CHECK(lsum.size() == vars1.size() + vars2.size());
    CHECK(lsum.get_max_var() == 130);

    // XOR with self is zero
    lineral l1_copy(l1);
    l1 += l1_copy;
    CHECK(l1.is_zero());

    // iterator yields all expected variables in order
    vec<var_t> iter_vars;
    for(var_t v : l2) iter_vars.push_back(v);
    CHECK(iter_vars == vars2);
    CHECK(std::is_sorted(iter_vars.begin(), iter_vars.end()));
}

TEST_CASE("lineral last_var and prev_var_before", "[lineral]") {
    lineral l(vec<var_t>({1, 3, 5, 7}));
    CHECK(l.last_var() == 7);
    CHECK(l.prev_var_before(7) == 5);
    CHECK(l.prev_var_before(5) == 3);
    CHECK(l.prev_var_before(3) == 1);
    CHECK(l.prev_var_before(1) == static_cast<var_t>(-1));

    // constant bit (0) must be skipped
    lineral lc(vec<var_t>({0, 1, 5}));  // x1+x5+1
    CHECK(lc.last_var() == 5);
    CHECK(lc.prev_var_before(5) == 1);
    CHECK(lc.prev_var_before(1) == static_cast<var_t>(-1));

    // zero lineral: no variables
    lineral zero;
    CHECK(zero.last_var() == static_cast<var_t>(-1));

    // constant-only lineral
    lineral one(cnst::one);
    CHECK(one.last_var() == static_cast<var_t>(-1));

    // single variable
    lineral single(vec<var_t>({42}));
    CHECK(single.last_var() == 42);
    CHECK(single.prev_var_before(42) == static_cast<var_t>(-1));

    // multi-block (vars > 64)
    lineral mb(vec<var_t>({1, 65, 130}));
    CHECK(mb.last_var() == 130);
    CHECK(mb.prev_var_before(130) == 65);
    CHECK(mb.prev_var_before(65) == 1);
    CHECK(mb.prev_var_before(1) == static_cast<var_t>(-1));

    // reverse iteration matches get_idxs_() in reverse
    lineral rtest(vec<var_t>({2, 7, 11, 20}));
    vec<var_t> reversed;
    for(var_t v = rtest.last_var(); v != static_cast<var_t>(-1); v = rtest.prev_var_before(v))
        reversed.push_back(v);
    CHECK(reversed == vec<var_t>({20, 11, 7, 2}));
}