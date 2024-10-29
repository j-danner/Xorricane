#pragma once

#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <execution>
#include <memory>

#include "../misc.hpp"
//forward declaration of class xsys
class xsys;

enum class presorted { yes, no };

//sparse implementation of a xor-literal
class xlit
{
    friend class xlit_watch;

    private:
        bool p1;
        //sparse repr of literal
        vec< var_t > idxs; /**<  List of sorted indices of the terms. */
        
        //constructor for internal use only -- skips a check for flag 'presorted'
        xlit(const vec< var_t >& idxs_, const bool p1_) noexcept : p1(p1_), idxs(idxs_) {
          assert( std::is_sorted(idxs.begin(), idxs.end()) );
        };

    public:
        xlit() noexcept : p1(false), idxs(vec<var_t>({})) {};
        xlit(xlit&& l) noexcept : p1(std::move(l.p1)), idxs(std::move(l.idxs)) {};
        xlit(const xlit& l) noexcept : p1(l.p1), idxs(l.idxs) {}; // no init required, as l.idxs is already sorted (i.e. initialized!)
        //b can be set to true if idxs_ is already sorted...
        xlit(const vec< var_t >& idxs_, const presorted b = presorted::no) noexcept : p1(false), idxs(std::move(idxs_)) {
          if(b==presorted::no){ init(); }
          else if( idxs.size()>0 && idxs[0]==0 ) { idxs.erase(idxs.begin()); p1^=true; }
        };
        xlit(vec< var_t >&& idxs_, const presorted b = presorted::no) noexcept : p1(false), idxs(std::move(idxs_)) {
          if(b==presorted::no){ init(); }
          else if( idxs.size()>0 && idxs[0]==0 ) { idxs.erase(idxs.begin()); p1^=true; }
        };
        xlit(const vec< var_t >& idxs_, const bool p1_, const presorted b) noexcept : p1(p1_), idxs(idxs_) { if(b==presorted::no){ init(); } };
        xlit(vec< var_t >&& idxs_, const bool p1_, const presorted b = presorted::no) noexcept : p1(p1_), idxs(std::move(idxs_)) {
          if(b==presorted::no){ init(); }
          else if( idxs.size()>0 && idxs[0]==0 ) { idxs.erase(idxs.begin()); p1^=true; }
        };
        xlit(const var_t& idx, const bool p1_) noexcept : p1(p1_), idxs({idx}) { 
          if( idxs.size()>0 && idxs[0]==0 ) { idxs.clear(); p1^=true; }
        }

        ~xlit() = default;

        inline void init() noexcept { 
            //sort
            std::sort(idxs.begin(), idxs.end()); 
            //remove duplicates -- should never be necessary!
            //idxs.erase( std::unique( idxs.begin(), idxs.end() ), idxs.end() );
            if( idxs.size()>0 && idxs[0]==0 ) { idxs.erase(idxs.begin()); p1^=true; }
            assert( idxs.empty() || idxs[0]!=0 );
        }

        inline void clear() noexcept { p1 = false; idxs.clear(); };

        inline bool is_one() const { return p1 && idxs.empty(); };
        inline bool is_zero() const { return !p1 && idxs.empty(); };
        inline bool is_constant() const { return idxs.empty(); };

        inline bool3 as_bool3() const { return (size()!=1 && !is_one()) ? bool3::None : (has_constant() ? bool3::True : bool3::False); };
        inline bool is_equiv() const { return size()==2; };
        inline bool is_assigning() const { return size()<=1; };

        inline bool has_constant() const { return p1; };

        inline var_t LT() const { return idxs.empty() ? 0 : idxs[0]; };

        size_t hash() const;

        inline xlit plus_one() const { return xlit( idxs, !p1, presorted::yes ); };

        inline xlit add_one() { p1 ^= true; return *this; };
    
        vec<var_t> support() const;

        bool reduce(const xsys& sys);

        /**
         * @brief Reduces the lineral by the given system s.t. the lineral increases in size no more than (1.50)^(sys.size()); also does nothing when size()<=3.
         * 
         * @param sys input xsys
         * @return true iff lineral was updated
         */
        bool reduce_short(const xsys& sys);
        bool reduce(const vec<xlit>& assignments, const vec<var_t>& assignments_dl, const var_t& lvl);
        bool reduce(const vec<equivalence>& equiv_lits);
        bool reduce(const vec<equivalence>& equiv_lits, const var_t& lvl);
        bool reduce(const vec<bool3>& alpha);
        bool reduce(const vec<bool3>& alpha, const vec<equivalence>& equiv_lits);
        bool reduce(const vec<bool3>& alpha, const vec<var_t>& alpha_dl, const var_t& lvl);
        bool reduce(const vec<xlit>& assignments);
        xlit reduced(const vec<xlit>& assignments) const { xlit ret(*this); ret.reduce(assignments); return ret; };
        xlit reduced(const vec<bool3>& alpha) const { xlit ret(*this); ret.reduce(alpha); return ret; };
        xlit reduced(const vec<bool3>& alpha, const vec<var_t>& alpha_dl, const var_t& lvl) const { xlit ret(*this); ret.reduce(alpha, alpha_dl, lvl); return ret; };
        xlit reduced(const vec<equivalence>& equiv_lits) { xlit ret(*this); ret.reduce(equiv_lits); return ret;};
        xlit reduced(const vec<bool3>& alpha, const vec<equivalence>& equiv_lits) const { xlit ret(*this); ret.reduce(alpha, equiv_lits); return ret; };
        vec<var_t> reducers(const vec<xlit>& assignments) const;

        inline vec<var_t> get_idxs() const { vec<var_t> r = idxs; if(p1){ r.insert(r.begin(), 0); } return r; };
        inline const vec<var_t>& get_idxs_() const { return idxs; };

        typedef vec<var_t>::const_iterator iterator;
        iterator begin() const { return idxs.begin(); };
        iterator end() const { return idxs.end(); };

        inline std::size_t size() const { return idxs.size(); };

        std::string to_str() const;
        std::string to_xnf_str() const;
        std::string to_full_str(var_t num_vars) const;

        //overloaded operators
	      xlit operator+(const xlit &other) const;
        //in-place operation (!)
        xlit& operator +=(const xlit& other);	
        inline xlit& operator =(const xlit& other) noexcept { idxs = other.idxs; p1 = other.p1; return *this; };
        inline xlit& operator =(xlit&& other) noexcept { idxs = std::move(other.idxs); p1 = std::move(other.p1); return *this; };

        void swap(xlit& other) noexcept { std::swap(idxs, other.idxs); std::swap(p1, other.p1); };

        xlit shared_part(const xlit& other) const;

        inline bool operator ==(const xlit& other) const { return (p1==other.p1) && (idxs==other.idxs); };
        bool operator <(const xlit& other) const;
        inline bool operator[](const var_t idx) const { return idx==0 ? p1 : std::binary_search(idxs.begin(), idxs.end(), idx); };
        std::ostream& operator<<(std::ostream& os) const;

        /**
         * @brief computes the LBD (literal-block-distance) of the xlit; i.e., the number of different dl's occuring in idxs
         * 
         * @param alpha_dl current alpha dl
         * @return var_t LBD value
         */
        var_t LBD(const vec<var_t>& alpha_dl) const {
          std::set<var_t> l;
          std::for_each(idxs.begin(), idxs.end(), [&](const auto i){ l.insert(alpha_dl[i]); });
          return l.size();
        };

        /**
         * @brief Get the second highest lineral, i.e., the lvl at which this lineral is assigned
         * 
         * @param alpha_dl current alpha dl
         * @return var_t dl at which the lineral is assigned
         */
        inline var_t get_assigning_lvl(const vec<var_t>& alpha_dl) const {
          var_t max_dl = 0;
          var_t max_dl2 = 0;
          for(auto v : idxs) { 
            if(alpha_dl[v] > max_dl) {
              max_dl2 = max_dl;
              max_dl = alpha_dl[v];
            } else if(alpha_dl[v] > max_dl2) {
              max_dl2 = alpha_dl[v];
            }
          }
          return max_dl2;
        };
        
        /**
         * @brief compute the var, dl, alpha trail pos and idx pos of the lineral on highest dl with maximal trail pos
         * 
         * @param alpha_dl dl of current alpha assignments
         * @param alpha_trail_pos positions in trail of alpha ssignments
         * @return std::tuple<var_t,var_t,var_t,var_t> tuple of var, var dl, trail pos and idx pos
         */
        inline std::tuple<var_t,var_t,var_t,var_t> get_watch_tuple(const vec<var_t>& alpha_dl, const vec<var_t>& alpha_trail_pos) const {
          if(idxs.empty()) return {-1, 0, 0, -1};
          assert(!is_constant());
          var_t max_idx = 0;
          var_t max_v = idxs[0];
          var_t max_trail_pos = alpha_trail_pos[max_v];
          for(var_t i=0; i<idxs.size(); ++i) {
            const var_t& v = idxs[i];
            if(alpha_trail_pos[v]==(var_t)-1) return {v,-1,-1,i};
            if(alpha_trail_pos[v]>max_trail_pos) { 
              max_trail_pos = alpha_trail_pos[v]; max_idx = i; max_v = v;
            }
          }
          return {max_v, alpha_dl[max_v], max_trail_pos, max_idx};
        }
        
        /**
         * @brief compute the dl, alpha trail pos and idx pos of the lineral on highest dl with maximal trail pos
         * 
         * @param alpha_trail_pos positions in trail of alpha ssignments
         * @return std::pair<var_t,var_t> tuple of trail pos and idx pos
         */
        inline std::pair<var_t,var_t> get_watch_var(const vec<var_t>& alpha_trail_pos) const {
          if(idxs.empty()) return {0,-1};
          var_t max_idx = 0;
          var_t max_trail_pos = alpha_trail_pos[idxs[0]];
          for(var_t i=0; i<idxs.size(); ++i) {
            const var_t& v = idxs[i];
            if(alpha_trail_pos[v]==(var_t)-1) return {-1,i};
            if(alpha_trail_pos[v]>max_trail_pos) { 
              max_trail_pos = alpha_trail_pos[v]; max_idx = i;
            }
          }
          return {max_trail_pos, max_idx};
        }

        inline var_t get_watch_idx(const vec<var_t>& alpha_trail_pos) const {
          return get_watch_var(alpha_trail_pos).second;
        }

        inline bool rm(const var_t lt, const bool3 val) {
          const auto pos = std::lower_bound(idxs.begin(), idxs.end(), lt);
          if(pos==idxs.end() || *pos != lt) return false;
          idxs.erase(pos);
          if(val==bool3::True) p1^=true;
          return true;
        }

        inline bool eval(const vec<bool> &sol) const { bool out = !p1; for(const auto &i : idxs) out ^= sol[i-1]; return out; };
        inline bool eval(const vec<bool3> &sol) const { bool out = !p1; for(const auto &i : idxs) { assert(sol[i]!=bool3::None); out ^= (sol[i] == bool3::True); } return out; };
        inline bool partial_eval(const vec<bool3> &sol) const { bool out = !p1; for(const auto &i : idxs) { out ^= (sol[i] == bool3::True); } return out; };
        void solve(vec<bool>& sol_) const { if(LT()>0) { sol_[LT()-1] = eval(sol_) ? sol_[LT()-1] : !sol_[LT()-1]; } };
};

namespace std {
  template <>
  struct hash<xlit> {
    std::size_t operator()(const xlit& k) const {
      return k.hash();
    }
  };
}

