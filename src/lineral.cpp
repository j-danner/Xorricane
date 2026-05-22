// Copyright (c) 2022-2025 Julian Danner <julian@danner-web.de>
//
// Permission is hereby granted, free of charge, to any person obtaining a copy of
// this software and associated documentation files (the "Software"), to deal in
// the Software without restriction, including without limitation the rights to
// use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
// the Software, and to permit persons to whom the Software is furnished to do so,
// subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
// FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
// COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
// IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
// CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

#include <iostream>
#include <algorithm>
#include <iterator>
#include <functional>
#include <list>

#include "misc.hpp"
#include "lineral.hpp"
#include "lin_sys.hpp"


size_t lineral::hash() const {
    size_t h = 0;
    const auto last = bitvec_.final_set();
    if(last == bit::vector<>::npos) return h;
    const std::size_t nb = bit::vector<>::block_index_for(last) + 1;
    for(std::size_t i = 0; i < nb; ++i)
        h ^= std::hash<bit::vector<>::block_type>()(bitvec_.block(i)) + 0x9e3779b9 + (h << 6) + (h >> 2);
    return h;
}

#define LOG2(X) ((int) (8*sizeof (unsigned long long) - __builtin_clzll((X)) - 1))

bool lineral::reduce(const lin_sys& sys) {
    bool changed = false;
    if( size() > LOG2(size())*sys.size() ) {
        for (const auto &[lt,row] : sys.get_pivot_poly_idx()) {
            if( (*this)[lt] ) { *this += *row; changed = true; }
        }
    } else {
        auto upd_idxs = list<list<lineral>::iterator>();
        const auto& pivot_poly_its = sys.get_pivot_poly_idx();
        for(auto v = first_var(); v != static_cast<var_t>(-1); v = next_var_after(v)) {
            auto search = pivot_poly_its.find(v);
            if( search != pivot_poly_its.end() ) upd_idxs.push_back( search->second );
        }
        for(const auto& row: upd_idxs) *this += *row;
        changed = !upd_idxs.empty();
        if(has_constant() && sys.contains_lt(0)) {
            if(bitvec_.size() > 0) bitvec_.reset(0);
        }
    }
    return changed;
}

lineral tmp;

bool lineral::reduce_short(const lin_sys& sys) {
    bool changed = false;
    auto prev_sz = size();
    for (const auto &[lt,row] : sys.get_pivot_poly_idx()) {
        if(prev_sz <= 3) break;
        if( (*this)[lt] ) {
            tmp = *this + *row;
            if(tmp.size() < 1.50 * prev_sz) {
                swap(tmp);
                prev_sz = size();
                changed = true;
            }
        }
    }
    return changed;
}

bool lineral::reduce(const vec<bool3>& alpha) {
    bool changed = false;
    for(auto v = first_var(); v != static_cast<var_t>(-1); ) {
        const auto next = next_var_after(v);
        if(alpha[v] != bool3::None) {
            changed = true;
            if(b3_to_bool(alpha[v])) {
                if(bitvec_.size() == 0) bitvec_.resize(1);
                bitvec_.flip(0);
            }
            bitvec_.reset(v);
        }
        v = next;
    }
    return changed;
}

bool lineral::reduce(const vec<bool3>& alpha, const vec<var_t>& alpha_dl, const var_t& lvl) {
    bool changed = false;
    for(auto v = first_var(); v != static_cast<var_t>(-1); ) {
        const auto next = next_var_after(v);
        if(alpha[v] != bool3::None && alpha_dl[v] <= lvl) {
            changed = true;
            if(b3_to_bool(alpha[v])) {
                if(bitvec_.size() == 0) bitvec_.resize(1);
                bitvec_.flip(0);
            }
            bitvec_.reset(v);
        }
        v = next;
    }
    return changed;
}

bool lineral::reduce(const vec<lineral>& assignments) {
    bool ret = false;
    for(auto v = first_var(); v != static_cast<var_t>(-1); ) {
        if( assignments[v].LT() > 0 ) {
            ret = true;
            *this += assignments[v];
            v = first_var(); // restart after bitvec_ changed
        } else {
            v = next_var_after(v);
        }
    }
    return ret;
}

bool lineral::reduce(const vec<lineral>& assignments, const vec<var_t>& assignments_dl, const var_t& lvl) {
    bool ret = false;
    for(auto v = first_var(); v != static_cast<var_t>(-1); ) {
        if( assignments[v].LT() > 0 && assignments_dl[v] <= lvl ) {
            ret = true;
            *this += assignments[v];
            v = first_var();
        } else {
            v = next_var_after(v);
        }
    }
    return ret;
}

bool lineral::reduce(const vec<bool3>& alpha, const vec<equivalence>& equiv_lits) {
    bool ret = false;
    for(auto v = first_var(); v != static_cast<var_t>(-1); ) {
        if(alpha[v] != bool3::None) {
            ret = true;
            if(b3_to_bool(alpha[v])) {
                if(bitvec_.size() == 0) bitvec_.resize(1);
                bitvec_.flip(0);
            }
            bitvec_.reset(v);
            v = next_var_after(v);
        } else if( equiv_lits[v].ind > 0 ) {
            ret = true;
            assert(v < equiv_lits[v].ind);
            *this += lineral({v, equiv_lits[v].ind}, equiv_lits[v].polarity, presorted::yes);
            v = first_var(); // restart
        } else {
            v = next_var_after(v);
        }
    }
    return ret;
}

bool lineral::reduce(const vec<equivalence>& equiv_lits) {
    bool ret = false;
    for(auto v = first_var(); v != static_cast<var_t>(-1); ) {
        if( equiv_lits[v].ind > 0 ) {
            ret = true;
            assert(v < equiv_lits[v].ind);
            *this += lineral({v, equiv_lits[v].ind}, equiv_lits[v].polarity, presorted::yes);
            v = first_var();
        } else {
            v = next_var_after(v);
        }
    }
    return ret;
}

bool lineral::reduce(const vec<equivalence>& equiv_lits, const var_t& lvl) {
    bool ret = false;
    for(auto v = first_var(); v != static_cast<var_t>(-1); ) {
        if( equiv_lits[v].is_active(lvl) ) {
            ret = true;
            assert(v < equiv_lits[v].ind);
            *this += lineral({v, equiv_lits[v].ind}, equiv_lits[v].polarity, presorted::yes);
            v = first_var();
        } else {
            v = next_var_after(v);
        }
    }
    return ret;
}

vec<var_t> lineral::support() const {
    return get_idxs_();
}

vec<var_t> lineral::reducers(const vec<lineral>& assignments) const {
    vec<var_t> ret;
    lineral l(*this);
    for(auto v = l.first_var(); v != static_cast<var_t>(-1); ) {
        if( assignments[v].LT() > 0 ) {
            ret.emplace_back(v);
            l += assignments[v];
            v = l.first_var();
        } else {
            v = l.next_var_after(v);
        }
    }
    return ret;
}

std::string lineral::to_str() const {
    if(size() == 0 && !has_constant()) return "0";
    std::string str;
    for(auto v = first_var(); v != static_cast<var_t>(-1); v = next_var_after(v))
        str.append("x"+std::to_string(v)+"+");
    if(has_constant()) {
        str.append("1");
    } else {
        if(str.length()>0) str.pop_back();
        else str = "0";
    }
    return str;
}

std::string lineral::to_xnf_str() const {
    if(size() == 0 && !has_constant()) return "";
    std::string str;
    if(!has_constant()) str.append("-");
    bool first_seen = true;
    for(auto v = first_var(); v != static_cast<var_t>(-1); v = next_var_after(v)) {
        if(!first_seen) str.append("+");
        str.append(std::to_string(v));
        first_seen = false;
    }
    return str;
}

std::string lineral::to_full_str(var_t num_vars) const {
    std::string str(num_vars, '0');
    for(auto v = first_var(); v != static_cast<var_t>(-1); v = next_var_after(v))
        if(v < num_vars) str[v] = '1';
    if(has_constant()) str[0] = '1';
    std::rotate(str.begin(), str.begin()+1, str.end());
    return str;
}

lineral lineral::shared_part(const lineral& other) const {
    // intersection via bitwise AND; result does NOT include constant bit
    lineral result;
    const std::size_t n = std::min(bitvec_.size(), other.bitvec_.size());
    if(n == 0) return result;
    result.bitvec_.resize(n);
    result.bitvec_.reset();
    const std::size_t nb = result.bitvec_.block_count();
    for(std::size_t i = 0; i < nb; ++i)
        result.bitvec_.block(i) = bitvec_.block(i) & other.bitvec_.block(i);
    if(result.bitvec_.size() > 0) result.bitvec_.reset(0); // no constant in shared part
    return result;
}

lineral lineral::operator+(const lineral& other) const {
    lineral result(*this);
    result += other;
    return result;
}

// O(n/64) block-parallel XOR
lineral& lineral::operator+=(const lineral& other) {
    if(bitvec_.size() < other.bitvec_.size())
        bitvec_.resize(other.bitvec_.size());
    const std::size_t nb = other.bitvec_.block_count();
    for(std::size_t i = 0; i < nb; ++i)
        bitvec_.block(i) ^= other.bitvec_.block(i);
    return *this;
}

bool lineral::operator<(const lineral& other) const {
    auto it1 = begin(), it2 = other.begin();
    while(it1 != end() && it2 != other.end()) {
        if(*it1 > *it2) return false;
        ++it1; ++it2;
    }
    return true;
}

std::ostream& lineral::operator<<(std::ostream& os) const {
    os << to_str();
    return os;
}
