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

#include "lineral_watch.hpp"
#include "cls_watch.hpp"

#ifndef TREE_LIKE_REASON_CLS_COMP
void lineral_watch::merge_reason_idx(const vec<var_t>& idxs) {
    if(idxs.empty()) return;
    vec<var_t> diff_tmp;
    std::set_symmetric_difference(reason_cls_idxs.begin(), reason_cls_idxs.end(), idxs.begin(), idxs.end(), std::back_inserter(diff_tmp));
    std::swap(reason_cls_idxs, diff_tmp);
}
#endif

bool lineral_watch::reduce(const vec<bool3>& alpha, const vec<var_t>& alpha_dl, const vec<dl_c_t>& dl_count, const vec<equivalence>& equiv_lits) {
    assert(reducible);

    // Iterate over variables in bitvec_.
    // Note: equiv_lits[v].ind > v is always guaranteed, so forward iteration is safe:
    // equivalence substitution only introduces larger variables which we encounter later.
    bool changed = false;
    for(auto v = first_var(); v != static_cast<var_t>(-1); ) {
        if(alpha[v] != bool3::None) {
            changed = true;
            if(b3_to_bool(alpha[v])) {
                if(bitvec_.size() == 0) bitvec_.resize(1);
                bitvec_.flip(0);
            }
            bitvec_.reset(v);
            v = next_var_after(v);
        } else if(equiv_lits[v].is_active()) {
            changed = true;
            const auto other_lit = equiv_lits[v].ind;
            assert(v < other_lit);
            reason_lins.emplace_back(equiv_lits[v].reason_lin);
            if(equiv_lits[v].polarity) {
                if(bitvec_.size() == 0) bitvec_.resize(1);
                bitvec_.flip(0);
            }
            bitvec_.reset(v);
            // Toggle other_lit (XOR)
            if(other_lit >= bitvec_.size()) bitvec_.resize(other_lit + 1);
            bitvec_.flip(other_lit);
            // other_lit > v so continue from next_var_after(v) which is >= v+1
            v = next_var_after(v);
        } else {
            v = next_var_after(v);
        }
    }

    if(changed) init(alpha, alpha_dl, dl_count);
    assert(assert_data_struct(alpha));

#ifndef NDEBUG
    for(auto v = first_var(); v != static_cast<var_t>(-1); v = next_var_after(v))
        assert(alpha[v] == bool3::None && !equiv_lits[v].is_active());
    assert(assert_data_struct(alpha, dl_count));
#endif

    return changed;
}

bool lineral_watch::reduce(const vec<bool3>& alpha, const vec<var_t>& alpha_dl, const vec<dl_c_t>& dl_count, const vec<equivalence>& equiv_lits, const var_t lvl) {
    assert(reducible);
    if(size() <= 1) return false;

    bool changed = false;
    for(auto v = first_var(); v != static_cast<var_t>(-1); ) {
        if(alpha[v] != bool3::None && alpha_dl[v] <= lvl) {
            changed = true;
            if(b3_to_bool(alpha[v])) {
                if(bitvec_.size() == 0) bitvec_.resize(1);
                bitvec_.flip(0);
            }
            bitvec_.reset(v);
            v = next_var_after(v);
        } else if(equiv_lits[v].is_active(lvl)) {
            changed = true;
            const auto other_lit = equiv_lits[v].ind;
            assert(v < other_lit);
            reason_lins.emplace_back(equiv_lits[v].reason_lin);
            if(equiv_lits[v].polarity) {
                if(bitvec_.size() == 0) bitvec_.resize(1);
                bitvec_.flip(0);
            }
            bitvec_.reset(v);
            if(other_lit >= bitvec_.size()) bitvec_.resize(other_lit + 1);
            bitvec_.flip(other_lit);
            v = next_var_after(v);
        } else {
            v = next_var_after(v);
        }
    }

    if(changed) init(alpha, alpha_dl, dl_count);
    assert(assert_data_struct(alpha));

#ifdef DEBUG_SLOW
    for(auto v = first_var(); v != static_cast<var_t>(-1); v = next_var_after(v))
        assert((alpha[v] == bool3::None || alpha_dl[v] > lvl) && !equiv_lits[v].is_active(lvl));
    assert(assert_data_struct(alpha, dl_count));
#endif

    return changed;
}
