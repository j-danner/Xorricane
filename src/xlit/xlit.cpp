#include <iostream>
#include <algorithm>
#include <iterator>
#include <parallel/algorithm>
#include <functional>

#include <list>

#include "../misc.hpp"

#include "xlit.hpp"
#include "xsys.hpp"
#include "omp.h"

//implementation inspired by the one of 3BA by Jan Horacek
#define DIFF diff_[omp_get_thread_num()]

// this suppresses creating the new objects again and again (each thread has their own diff-vec)
vec< vec<var_t> > diff_( omp_get_max_threads() );


size_t xlit::hash() const {
    size_t h = idxs.size() + (p1 ? 1 : 0);
    h = p1 ? h : h^~0;
    for (auto &&i : idxs) {  
        h = (h << i) ^ ~i;
    }
    return h;
};

//gcc-dependent integer log2 func
#define LOG2(X) ((int) (8*sizeof (unsigned long long) - __builtin_clzll((X)) - 1))

bool xlit::reduce(const xsys& sys) {
    bool changed = false;
    if( size() > LOG2(size())*sys.size() ) {
        //complexity to find correct update xlits: O( log( this.size() ) * sys.size() )
        for (const auto &[lt,row] : sys.get_pivot_poly_idx()) {
            if( (*this)[lt] ) {
                *this += *row;
                changed = true;
            }
        }
    } else {
        //complexity to find correct update xlits: amortized O( this.size() )
        auto upd_idxs = list<list<xlit>::iterator>();
        const auto& pivot_poly_its = sys.get_pivot_poly_idx();
        for(const auto& l : idxs) {
            auto search = pivot_poly_its.find(l);
            if( search != pivot_poly_its.end() ) upd_idxs.push_back( search->second );
        }
        for(const auto& row: upd_idxs) *this += *row;
        changed = !upd_idxs.empty();
    }
    return changed;
};

xlit tmp;

bool xlit::reduce_short(const xsys& sys) {
    bool changed = false;
    auto prev_sz = size();
    //complexity to find correct update xlits: O( log( this.size() ) * sys.size() )
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
};


bool xlit::reduce(const vec<bool3>& alpha) {
    //IMPLEMENATION 1 (swapping)
    //const auto sz = idxs.size();
    //DIFF.clear();
    //std::copy_if(idxs.begin(), idxs.end(), std::back_inserter(DIFF), [&](var_t i){ return alpha[i] == bool3::None; } );
    //std::for_each(idxs.begin(), idxs.end(), [&](var_t i){ if(alpha[i] != bool3::None) p1 ^= b3_to_bool(alpha[i]); } );
    //std::swap(idxs, DIFF);
    //return sz != idxs.size();

    //IMPLEMENATION 2 (in-place)
    const auto sz = idxs.size();
    std::for_each(idxs.begin(), idxs.end(), [&](const var_t& i){ if(alpha[i] != bool3::None) p1 ^= b3_to_bool(alpha[i]); } );
    const auto new_end = std::remove_if(idxs.begin(), idxs.end(), [&](const var_t& i){ return alpha[i] != bool3::None; } );
    idxs.erase(new_end, idxs.end());
    return sz != idxs.size();

    //IMPLEMENATION 3 (inefficient)
    //bool ret = false;
    //auto it = idxs.begin();
    //while(it != idxs.end()) {
    //    if( alpha[*it] != bool3::None ) {
    //        ret = true;
    //        p1 ^= b3_to_bool(alpha[*it]);
    //        it = idxs.erase(it);
    //    } else {
    //        ++it;
    //    }
    //}
    //return ret;
};

bool xlit::reduce(const vec<bool3>& alpha, const vec<var_t>& alpha_dl, const var_t& lvl) {
    const auto sz = idxs.size();
    std::for_each(idxs.begin(), idxs.end(), [&](const var_t& i){ if(alpha[i] != bool3::None && alpha_dl[i]<=lvl) p1 ^= b3_to_bool(alpha[i]); } );
    const auto new_end = std::remove_if(idxs.begin(), idxs.end(), [&](const var_t& i){ return alpha[i] != bool3::None && alpha_dl[i]<=lvl; } );
    idxs.erase(new_end, idxs.end());
    return sz != idxs.size();
};


bool xlit::reduce(const vec<xlit>& assignments) {
    bool ret = false;
    var_t offset = 0;
    while(offset<idxs.size()) {
        if( assignments[ idxs[offset] ].LT()>0 ) {
            ret = true;
            *this += assignments[ idxs[offset] ];
        } else {
            ++offset;
        }
    }
    return ret;
};

bool xlit::reduce(const vec<xlit>& assignments, const vec<var_t>& assignments_dl, const var_t& lvl) {
    bool ret = false;
    var_t offset = 0;
    while(offset<idxs.size()) {
        if( assignments[ idxs[offset] ].LT()>0 && assignments_dl[ idxs[offset] ] <= lvl ) {
            ret = true;
            *this += assignments[ idxs[offset] ];
        } else {
            ++offset;
        }
    }
    return ret;
};

bool xlit::reduce(const vec<equivalence>& equiv_lits) {
    bool ret = false;
    var_t offset = 0;
    while(offset<idxs.size()) {
        if( equiv_lits[ idxs[offset] ].ind>0 ) {
            ret = true;
            assert(idxs[offset] < equiv_lits[ idxs[offset] ].ind);
            *this += xlit({idxs[offset], equiv_lits[ idxs[offset] ].ind}, equiv_lits[ idxs[offset] ].polarity, presorted::yes);
        } else {
            ++offset;
        }
    }
    return ret;
};

bool xlit::reduce(const vec<equivalence>& equiv_lits, const vec<var_t>& equiv_lits_dl, const var_t& lvl) {
    bool ret = false;
    var_t offset = 0;
    while(offset<idxs.size()) {
        if( equiv_lits[ idxs[offset] ].ind>0 && equiv_lits_dl[ idxs[offset] ] <= lvl ) {
            ret = true;
            assert(idxs[offset] < equiv_lits[ idxs[offset] ].ind);
            *this += xlit({idxs[offset], equiv_lits[ idxs[offset] ].ind}, equiv_lits[ idxs[offset] ].polarity, presorted::yes);
        } else {
            ++offset;
        }
    }
    return ret;
};

vec<var_t> xlit::support() const {
    vec<var_t> ret;
    for (auto &&i : idxs) ret.emplace_back(i);
    return ret;
};

vec<var_t> xlit::reducers(const vec<xlit>& assignments) const {
    vec<var_t> ret;
    xlit l(*this);
    for(var_t offset = 0; offset<l.idxs.size(); offset++) {
        if( assignments[ l.idxs[offset] ].LT()>0 ) {
            ret.emplace_back( l.idxs[offset] );
            l += assignments[ l.idxs[offset] ];
            offset--;
        }
    }
    return ret;
};

std::string xlit::to_str() const {
    //if empty
    if(idxs.size() == 0 && !has_constant()) return "0";
    //else construct string
    std::string str;
    for (var_t i = 0; i < idxs.size(); i++)
    {
        str.append("x"+std::to_string( idxs[i] )+"+");
    }
    if(has_constant()) {
        str.append("1");
    } else {
        if (str.length()>0) str.pop_back();
        else str = "0";
    }
    return str;
};

std::string xlit::to_xnf_str() const {
    //if empty
    if(idxs.size() == 0 && !has_constant()) return "";
    //else construct string
    std::string str;
    if(!has_constant()) {
        str.append("-");
    }
    for (var_t i = 0; i < idxs.size(); i++) {
        str.append( std::to_string( idxs[i] )+"+" );
    }
    if(idxs.size()>0) str.pop_back();
    return str;
};

std::string xlit::to_full_str(var_t num_vars) const{ 
    std::string str(num_vars, '0');
    for (auto &&i : idxs) {
        str[i] = '1';
    }
    if(has_constant()) str[0]='1';
    std::rotate(str.begin(), str.begin()+1, str.end());

    return str;
};


xlit xlit::shared_part(const xlit& other) const {
  DIFF.clear(); // DIFF is declared global and static, this saves creating new DIFFs for each calling
  std::set_intersection(idxs.begin(), idxs.end(), other.idxs.begin(), other.idxs.end(), std::back_inserter(DIFF));
  return xlit(DIFF, false, presorted::yes); //call ctor that does NOT sort DIFF
};

//overloaded operators
xlit xlit::operator+(const xlit &other) const {
    /* \warning we assume that both xlits have same num_vars (!) */
    DIFF.clear(); // DIFF is declared global and static, this saves creating new DIFFs for each calling
    std::set_symmetric_difference(idxs.begin(), idxs.end(), other.idxs.begin(), other.idxs.end(), std::back_inserter(DIFF));
    //NOTE back_insterter might lead to repeated reallocations!
    //idxs = DIFF;

    return xlit(DIFF, p1^other.p1, presorted::yes); //call ctor that does NOT sort DIFF
};

//in-place operation (!)
xlit& xlit::operator +=(const xlit& other) {
    if(other.size()==0) { p1^=other.p1; return *this; }

    DIFF.clear(); // DIFF is declared global and static, this saves creating new DIFFs for each calling
    std::set_symmetric_difference(idxs.begin(), idxs.end(), other.idxs.begin(), other.idxs.end(), std::back_inserter(DIFF));
    std::swap(idxs, DIFF);

    p1 ^= other.p1;

    return *this;
};


bool xlit::operator <(const xlit& other) const {
    //get min of sizes
    var_t m = idxs.size() > other.idxs.size() ? other.idxs.size() : idxs.size();
    for (var_t idx = 0; idx < m; ++idx) {
        if(idxs[idx] > other.idxs[idx]) return false;
    }
    return true;
};

std::ostream& xlit::operator<<(std::ostream& os) const {
    os << to_str();
    return os;
};
