#include <iostream>
#include <algorithm>
#include <iterator>
#include <parallel/algorithm>
#include <functional>

#include <list>

#include "misc.hpp"

#include "lineral.hpp"
#include "lin_sys.hpp"

// this suppresses creating the new objects again and again
vec<var_t> diff_;


size_t lineral::hash() const {
    size_t h = std::hash<bool>()(p1); // Hash the boolean value p1
    // Combine the hash of each element in idxs with the current hash
    for (const auto& i : idxs) {
        h ^= std::hash<var_t>()(i) + 0x9e3779b9 + (h << 6) + (h >> 2); // Use a mixing function
    }
    return h;
}

//gcc-dependent integer log2 func
#define LOG2(X) ((int) (8*sizeof (unsigned long long) - __builtin_clzll((X)) - 1))

bool lineral::reduce(const lin_sys& sys) {
    bool changed = false;
    if( size() > LOG2(size())*sys.size() ) {
        //complexity to find correct update linerals: O( log( this.size() ) * sys.size() )
        for (const auto &[lt,row] : sys.get_pivot_poly_idx()) {
            if( (*this)[lt] ) {
                *this += *row;
                changed = true;
            }
        }
    } else {
        //complexity to find correct update linerals: amortized O( this.size() )
        auto upd_idxs = list<list<lineral>::iterator>();
        const auto& pivot_poly_its = sys.get_pivot_poly_idx();
        for(const auto& l : idxs) {
            auto search = pivot_poly_its.find(l);
            if( search != pivot_poly_its.end() ) upd_idxs.push_back( search->second );
        }
        for(const auto& row: upd_idxs) *this += *row;
        changed = !upd_idxs.empty();
        //reduce constant
        if(p1 && sys.contains_lt(0)) { p1 = false; }
    }
    return changed;
};

lineral tmp;

bool lineral::reduce_short(const lin_sys& sys) {
    bool changed = false;
    auto prev_sz = size();
    //complexity to find correct update linerals: O( log( this.size() ) * sys.size() )
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


bool lineral::reduce(const vec<bool3>& alpha) {
    //IMPLEMENATION 1 (swapping)
    //const auto sz = idxs.size();
    //diff_.clear();
    //std::copy_if(idxs.begin(), idxs.end(), std::back_inserter(diff_), [&](var_t i){ return alpha[i] == bool3::None; } );
    //std::for_each(idxs.begin(), idxs.end(), [&](var_t i){ if(alpha[i] != bool3::None) p1 ^= b3_to_bool(alpha[i]); } );
    //std::swap(idxs, diff_);
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

bool lineral::reduce(const vec<bool3>& alpha, const vec<var_t>& alpha_dl, const var_t& lvl) {
    const auto sz = idxs.size();
    std::for_each(idxs.begin(), idxs.end(), [&](const var_t& i){ if(alpha[i] != bool3::None && alpha_dl[i]<=lvl) p1 ^= b3_to_bool(alpha[i]); } );
    const auto new_end = std::remove_if(idxs.begin(), idxs.end(), [&](const var_t& i){ return alpha[i] != bool3::None && alpha_dl[i]<=lvl; } );
    idxs.erase(new_end, idxs.end());
    return sz != idxs.size();
};


bool lineral::reduce(const vec<lineral>& assignments) {
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

bool lineral::reduce(const vec<lineral>& assignments, const vec<var_t>& assignments_dl, const var_t& lvl) {
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

bool lineral::reduce(const vec<bool3>& alpha, const vec<equivalence>& equiv_lits) {
    bool ret = false;
    var_t offset = 0;
    while(offset<idxs.size()) {
        if(alpha[idxs[offset]] != bool3::None) {
            ret = true;
            p1 ^= b3_to_bool(alpha[idxs[offset]]);
            idxs.erase( idxs.begin()+offset );
        } else if( equiv_lits[ idxs[offset] ].ind>0 ) {
            ret = true;
            assert(idxs[offset] < equiv_lits[ idxs[offset] ].ind);
            //@todo optimize impl: next step iterates once over full length, but it suffices to start at idxs[offset]!
            *this += lineral({idxs[offset], equiv_lits[ idxs[offset] ].ind}, equiv_lits[ idxs[offset] ].polarity, presorted::yes);
        } else {
            ++offset;
        }
    }
    return ret;
};


bool lineral::reduce(const vec<equivalence>& equiv_lits) {
    bool ret = false;
    var_t offset = 0;
    while(offset<idxs.size()) {
        if( equiv_lits[ idxs[offset] ].ind>0 ) {
            ret = true;
            assert(idxs[offset] < equiv_lits[ idxs[offset] ].ind);
            //@todo optimize impl: next step iterates once over full length, but it suffices to start at idxs[offset]!
            *this += lineral({idxs[offset], equiv_lits[ idxs[offset] ].ind}, equiv_lits[ idxs[offset] ].polarity, presorted::yes);
        } else {
            ++offset;
        }
    }
    return ret;
};

bool lineral::reduce(const vec<equivalence>& equiv_lits, const var_t& lvl) {
    bool ret = false;
    var_t offset = 0;
    while(offset<idxs.size()) {
        if( equiv_lits[ idxs[offset] ].is_active(lvl) ) {
            ret = true;
            assert(idxs[offset] < equiv_lits[ idxs[offset] ].ind);
            *this += lineral({idxs[offset], equiv_lits[ idxs[offset] ].ind}, equiv_lits[ idxs[offset] ].polarity, presorted::yes);
        } else {
            ++offset;
        }
    }
    return ret;
};

vec<var_t> lineral::support() const {
    vec<var_t> ret;
    for (auto &&i : idxs) ret.emplace_back(i);
    return ret;
};

vec<var_t> lineral::reducers(const vec<lineral>& assignments) const {
    vec<var_t> ret;
    lineral l(*this);
    for(var_t offset = 0; offset<l.idxs.size(); offset++) {
        if( assignments[ l.idxs[offset] ].LT()>0 ) {
            ret.emplace_back( l.idxs[offset] );
            l += assignments[ l.idxs[offset] ];
            offset--;
        }
    }
    return ret;
};

std::string lineral::to_str() const {
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

std::string lineral::to_xnf_str() const {
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

std::string lineral::to_full_str(var_t num_vars) const{ 
    std::string str(num_vars, '0');
    for (auto &&i : idxs) {
        str[i] = '1';
    }
    if(has_constant()) str[0]='1';
    std::rotate(str.begin(), str.begin()+1, str.end());

    return str;
};


lineral lineral::shared_part(const lineral& other) const {
  diff_.clear(); // diff_ is declared global and static, this saves creating new diff_s for each calling
  std::set_intersection(idxs.begin(), idxs.end(), other.idxs.begin(), other.idxs.end(), std::back_inserter(diff_));
  return lineral(diff_, presorted::yes); //call ctor that does NOT sort diff_
};

//overloaded operators
lineral lineral::operator+(const lineral &other) const {
    diff_.clear(); // diff_ is declared global and static, this saves creating new diff_s for each calling
    std::set_symmetric_difference(idxs.begin(), idxs.end(), other.idxs.begin(), other.idxs.end(), std::back_inserter(diff_));
    //NOTE back_insterter might lead to repeated reallocations!
    //idxs = diff_;

    return lineral(diff_, p1^other.p1, presorted::yes);
};

//in-place operation (!)
lineral& lineral::operator +=(const lineral& other) {
    if(other.size()==0) { p1^=other.p1; return *this; }

    diff_.clear(); // diff_ is declared global and static, this saves creating new diff_s for each calling
    std::set_symmetric_difference(idxs.begin(), idxs.end(), other.idxs.begin(), other.idxs.end(), std::back_inserter(diff_));
    std::swap(idxs, diff_);

    p1 ^= other.p1;

    return *this;
};


bool lineral::operator <(const lineral& other) const {
    //get min of sizes
    var_t m = idxs.size() > other.idxs.size() ? other.idxs.size() : idxs.size();
    for (var_t idx = 0; idx < m; ++idx) {
        if(idxs[idx] > other.idxs[idx]) return false;
    }
    return true;
};

std::ostream& lineral::operator<<(std::ostream& os) const {
    os << to_str();
    return os;
};
