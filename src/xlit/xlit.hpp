//from std
#pragma once

#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <execution>
#include <memory>

#include "../misc.hpp"
//#include "xsys.hpp"
//forward declaration of class xsys
class xsys;


//sparse implementation of a xor-literal
class xlit
{
    private:
        bool p1;
        //sparse repr of literal
        vec< var_t > idxs; /**<  List of sorted indices of the terms. */

    public:
        xlit() noexcept : p1(false), idxs(vec<var_t>({})) {};
        xlit(xlit&& l) noexcept : p1(std::move(l.p1)), idxs(std::move(l.idxs)) {};
        xlit(const xlit& l) noexcept : p1(l.p1), idxs(l.idxs) {}; // no init required, as l.idxs is already sorted (i.e. initialized!)
        //b can be set to true if idxs_ is already sorted...
        xlit(const vec< var_t >& idxs_, const bool b = false) noexcept : p1(false), idxs(std::move(idxs_)) {
          if(!b){ init(); }
          else if( idxs.size()>0 && idxs[0]==0 ) { idxs.erase(idxs.begin()); p1^=true; }
        };
        xlit(vec< var_t >&& idxs_, const bool b = false) noexcept : p1(false), idxs(std::move(idxs_)) {
          if(!b){ init(); }
          else if( idxs.size()>0 && idxs[0]==0 ) { idxs.erase(idxs.begin()); p1^=true; }
        };
        xlit(const vec< var_t >& idxs_, const bool p1_, const bool b) noexcept : p1(p1_), idxs(idxs_) { if(!b){ init(); } };
        xlit(vec< var_t >&& idxs_, const bool p1_, const bool b) noexcept : p1(p1_), idxs(std::move(idxs_)) { if(!b){ init(); } };
        xlit(var_t& idx, const bool p1_) noexcept : p1(p1_), idxs({idx}) {};

        ~xlit() = default;

        inline void init() noexcept { 
            //sort
            std::sort(std::execution::par, idxs.begin(), idxs.end()); 
            //remove duplicates -- should never be necessary!
            //idxs.erase( std::unique( idxs.begin(), idxs.end() ), idxs.end() );
            if( idxs.size()>0 && idxs[0]==0 ) { idxs.erase(idxs.begin()); p1^=true; }
            assert( idxs.empty() || idxs[0]!=0);
        }

        inline bool is_one() const { return p1 && (idxs.empty()); };
        inline bool is_zero() const { return !p1 && idxs.empty(); };

        inline bool3 as_bool3() const { return (size()!=1 && !is_one()) ? bool3::None : (has_constant() ? bool3::True : bool3::False); };

        inline bool has_constant() const { return p1; };

        inline var_t LT() const { return idxs.empty() ? 0 : idxs[0]; };

        size_t hash() const;

        inline xlit plus_one() const { return xlit( idxs, !p1, true ); };

        inline xlit add_one() { p1 ^= true; return *this; };

        bool reduce(const xsys& sys);
        bool reduce(const vec<xlit>& assignments, const vec<var_t>& assignments_dl, const var_t lvl);
        
        bool reduce(const vec<xlit>& assignments);
        vec<var_t> reducers(const vec<xlit>& assignments) const;

        inline vec<var_t> get_idxs() const { vec<var_t> r = idxs; if(p1){ r.insert(r.begin(), 0); } return r; };
        inline const vec<var_t>& get_idxs_() const { return idxs; };

        typedef vec<var_t>::const_iterator iterator;
        iterator begin() const { return idxs.begin(); };
        iterator end() const { return idxs.end(); };

        inline int size() const { return idxs.size(); };

        std::string to_str() const;
        std::string to_full_str(var_t num_vars) const;

        //overloaded operators
	      xlit operator+(const xlit &other) const;
        //in-place operation (!)
        xlit& operator +=(const xlit& other);	
        inline xlit& operator =(const xlit& other) noexcept { idxs = other.idxs; p1 = other.p1; return *this; };
        inline xlit& operator =(const xlit&& other) noexcept { idxs = std::move(other.idxs); p1 = std::move(other.p1); return *this; };
        //xlit& operator =(xlit&& other) : idxs(std::move(other.idxs)) { return *this; }; //NOTE fails to compile...

        void swap(xlit& other) noexcept { std::swap(idxs, other.idxs); std::swap(p1, other.p1); };

        inline bool operator ==(const xlit& other) const { return (p1==other.p1) && (idxs==other.idxs); };
        bool operator <(const xlit& other) const;
        inline bool operator[](const var_t idx) const { return idx==0 ? p1 : std::binary_search(idxs.begin(), idxs.end(), idx); };
        std::ostream& operator<<(std::ostream& os) const;

        bool eval(const vec<bool> &sol) const { bool out = !p1; for(const auto &i : idxs) out ^= sol[i-1]; return out; };
        bool eval(const vec<bool3> &sol) const { bool out = !p1; for(const auto &i : idxs) { assert(sol[i]!=bool3::None); out ^= (sol[i] == bool3::True); } return out; };
        void solve(vec<bool>& sol_) const { if(LT()>0) { sol_[LT()-1] = eval(sol_) ? sol_[LT()-1] : !sol_[LT()-1]; } };
};

namespace std {
  //template<> // specialization
  //void swap<xlit>(xlit& lhs, xlit& rhs) noexcept {
  //  lhs.swap(rhs);
  //};

  template <>
  struct hash<xlit> {
    std::size_t operator()(const xlit& k) const {
      return k.hash();
    }
  };
}

