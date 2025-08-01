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

// this suppresses creating the new objects again and again
vec<var_t> diff_tmp;

#ifndef TREE_LIKE_REASON_CLS_COMP
void lineral_watch::merge_reason_idx(const vec<var_t>& idxs) {
    if(idxs.empty()) return;
    diff_tmp.clear(); // diff_tmp is declared global and static, this saves creating new diff_s for each calling
    std::set_symmetric_difference(reason_cls_idxs.begin(), reason_cls_idxs.end(), idxs.begin(), idxs.end(), std::back_inserter(diff_tmp));
    std::swap(reason_cls_idxs, diff_tmp);
}
#endif

bool lineral_watch::reduce(const vec<bool3>& alpha, const vec<var_t>& alpha_dl, const vec<dl_c_t>& dl_count, const vec<equivalence>& equiv_lits) {
    assert(reducible);
    diff_tmp.clear(); diff_tmp.reserve(idxs.size());

    //@todo replace erase with copying? (similar to lineral::operator+ ?)
    std::set<var_t> rm_idxs;
  
    const auto wl0 = size()>0 ? get_wl0() : 0;
    const auto wl1 = size()>1 ? get_wl1() : 0;
    ws[0] = (var_t) -1;
    ws[1] = (var_t) -1;

    var_t idx = 0;
    auto it = idxs.begin();
    while(it != idxs.end()) {
        while(!rm_idxs.empty() && *rm_idxs.begin() < *it) {
            //add el from rm_idxs -- if it is neither assigned nor equiv
            if(alpha[*rm_idxs.begin()] != bool3::None) {
                //*it is assigned -- skip *it
                p1 ^= b3_to_bool(alpha[*rm_idxs.begin()]);
            } else if(equiv_lits[*rm_idxs.begin()].is_active()) {
                //equivalent substitution possible -- skip *rm_idxs.begin()
                const auto other_lit = equiv_lits[*rm_idxs.begin()].ind;
                assert(*rm_idxs.begin() < other_lit);
                //add reduction reasons
                reason_lins.emplace_back( equiv_lits[*rm_idxs.begin()].reason_lin );
                //update rm_idxs
                p1 ^= equiv_lits[*rm_idxs.begin()].polarity;
                const auto search = rm_idxs.find(other_lit);
                if( search!=rm_idxs.end() && *search==other_lit ) rm_idxs.erase(search);
                else rm_idxs.emplace_hint( search, other_lit );
            } else {
                diff_tmp.emplace_back( *rm_idxs.begin() );
            }
            rm_idxs.erase( rm_idxs.begin() );
        }
        if(!rm_idxs.empty() && *rm_idxs.begin() == *it) {
            //skip *it
            rm_idxs.erase( rm_idxs.begin() );
        } else if( alpha[*it] != bool3::None ) {
            //*it is assigned -- skip *it
            p1 ^= b3_to_bool(alpha[*it]);
        } else if(equiv_lits[*it].is_active()) {
            //equivalent substitution possible -- skip *it
            const auto other_lit = equiv_lits[*it].ind;
            assert(*it < other_lit);
            //add reduction reasons
            reason_lins.emplace_back( equiv_lits[*it].reason_lin );
            //update rm_idxs
            p1 ^= equiv_lits[*it].polarity;
            const auto search = rm_idxs.find(other_lit);
            if( search!=rm_idxs.end() && *search==other_lit ) rm_idxs.erase(search);
            else rm_idxs.emplace_hint( search, other_lit );
        } else {
            //add *it
            if(*it==wl0) ws[0] = diff_tmp.size();
            if(*it==wl1) ws[1] = diff_tmp.size();
            diff_tmp.emplace_back( *it );
            ++idx;
        }
        ++it;
    }
    //add remaining inds
    while(!rm_idxs.empty()) {
        if(alpha[*rm_idxs.begin()] != bool3::None) {
            //*it is assigned -- skip *it
            p1 ^= b3_to_bool(alpha[*rm_idxs.begin()]);
        } else if(equiv_lits[*rm_idxs.begin()].is_active()) {
            //equivalent substitution possible -- skip *rm_idxs.begin()
            const auto other_lit = equiv_lits[*rm_idxs.begin()].ind;
            assert(*rm_idxs.begin() < other_lit);
            //add reduction reasons
            reason_lins.emplace_back( equiv_lits[*rm_idxs.begin()].reason_lin );
            //update rm_idxs
            p1 ^= equiv_lits[*rm_idxs.begin()].polarity;
            const auto search = rm_idxs.find(other_lit);
            if( search!=rm_idxs.end() && *search==other_lit ) rm_idxs.erase(search);
            else rm_idxs.emplace_hint( search, other_lit );
        } else {
            diff_tmp.emplace_back( *rm_idxs.begin() );
        }
        rm_idxs.erase( rm_idxs.begin() );
    }
    //swap diff_tmp.and idxs
    std::swap(diff_tmp, idxs);

    const bool ret = (ws[0]==(var_t)-1) || (ws[1]==(var_t)-1);
    //re-init watches if watched literals were replaced!
    if( ret ) init(alpha, alpha_dl, dl_count);
    assert(assert_data_struct(alpha));

    //ensure that no un-reduced inds is left
  #ifndef NDEBUG
    for(auto& v : idxs) assert( alpha[v]==bool3::None && !equiv_lits[v].is_active() );
    assert( assert_data_struct(alpha, dl_count) );
  #endif

    return ret;
}

bool lineral_watch::reduce(const vec<bool3>& alpha, const vec<var_t>& alpha_dl, const vec<dl_c_t>& dl_count, const vec<equivalence>& equiv_lits, const var_t lvl) {
    assert(reducible);
    if(size()<=1) return false;
    diff_tmp.clear(); diff_tmp.reserve(idxs.size());

    std::set<var_t> rm_idxs;
  
    const auto wl0 = size()>0 ? get_wl0() : 0;
    const auto wl1 = size()>1 ? get_wl1() : 0;
    ws[0] = (var_t) -1;
    ws[1] = (var_t) -1;

    var_t idx = 0;
    auto it = idxs.begin();
    while(it != idxs.end()) {
        while(!rm_idxs.empty() && *rm_idxs.begin() < *it) {
            //add el from rm_idxs -- if it is neither assigned nor equiv
            if(alpha[*rm_idxs.begin()] != bool3::None && alpha_dl[*rm_idxs.begin()]<=lvl) {
                //*it is assigned -- skip *it
                p1 ^= b3_to_bool(alpha[*rm_idxs.begin()]);
            } else if(equiv_lits[*rm_idxs.begin()].is_active(lvl)) {
                //equivalent substitution possible -- skip *rm_idxs.begin()
                const auto other_lit = equiv_lits[*rm_idxs.begin()].ind;
                assert(*rm_idxs.begin() < other_lit);
                //add reduction reasons
                reason_lins.emplace_back( equiv_lits[*rm_idxs.begin()].reason_lin );
                //update rm_idxs
                p1 ^= equiv_lits[*rm_idxs.begin()].polarity;
                const auto search = rm_idxs.find(other_lit);
                if( search!=rm_idxs.end() && *search==other_lit ) rm_idxs.erase(search);
                else rm_idxs.emplace_hint( search, other_lit );
            } else {
                diff_tmp.emplace_back( *rm_idxs.begin() );
            }
            rm_idxs.erase( rm_idxs.begin() );
        }
        if(!rm_idxs.empty() && *rm_idxs.begin() == *it) {
            //skip *it
            rm_idxs.erase( rm_idxs.begin() );
        } else if( alpha[*it] != bool3::None && alpha_dl[*it] <= lvl ) {
            //*it is assigned -- skip *it
            p1 ^= b3_to_bool(alpha[*it]);
        } else if(equiv_lits[*it].is_active(lvl)) {
            //equivalent substitution possible -- skip *it
            const auto other_lit = equiv_lits[*it].ind;
            assert(*it < other_lit);
            //add reduction reasons
            reason_lins.emplace_back( equiv_lits[*it].reason_lin );
            //update rm_idxs
            p1 ^= equiv_lits[*it].polarity;
            const auto search = rm_idxs.find(other_lit);
            if( search!=rm_idxs.end() && *search==other_lit ) rm_idxs.erase(search);
            else rm_idxs.emplace_hint( search, other_lit );
        } else {
            //add *it
            if(*it==wl0) ws[0] = diff_tmp.size();
            if(*it==wl1) ws[1] = diff_tmp.size();
            diff_tmp.emplace_back( *it );
            ++idx;
        }
        ++it;
    }
    //add remaining inds
    while(!rm_idxs.empty()) {
        if(alpha[*rm_idxs.begin()] != bool3::None && alpha_dl[*rm_idxs.begin()] <= lvl) {
            //*it is assigned -- skip *it
            p1 ^= b3_to_bool(alpha[*rm_idxs.begin()]);
        } else if(equiv_lits[*rm_idxs.begin()].is_active(lvl)) {
            //equivalent substitution possible -- skip *rm_idxs.begin()
            const auto other_lit = equiv_lits[*rm_idxs.begin()].ind;
            assert(*rm_idxs.begin() < other_lit);
            //add reduction reasons
            reason_lins.emplace_back( equiv_lits[*rm_idxs.begin()].reason_lin );
            //update rm_idxs
            p1 ^= equiv_lits[*rm_idxs.begin()].polarity;
            const auto search = rm_idxs.find(other_lit);
            if( search!=rm_idxs.end() && *search==other_lit ) rm_idxs.erase(search);
            else rm_idxs.emplace_hint( search, other_lit );
        } else {
            diff_tmp.emplace_back( *rm_idxs.begin() );
        }
        rm_idxs.erase( rm_idxs.begin() );
    }
    //swap diff_tmp.and idxs
    std::swap(diff_tmp, idxs);

    const bool ret = (ws[0]==(var_t)-1) || (ws[1]==(var_t)-1);
    //re-init watches if watched literals were replaced!
    if( ret ) init(alpha, alpha_dl, dl_count);
    assert(assert_data_struct(alpha));

  #ifdef DEBUG_SLOW
    //ensure that no un-reduced inds are left
    for(auto& v : idxs) assert( (alpha[v]==bool3::None || alpha_dl[v]>lvl) && !equiv_lits[v].is_active(lvl) );
    assert( assert_data_struct(alpha, dl_count) );
  #endif

    return ret;
}