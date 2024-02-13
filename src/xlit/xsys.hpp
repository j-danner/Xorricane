#pragma once

#include <string>
#include <map>
#include <list>

#include "xlit.hpp"

//#include "../robin_hood-3.11.5/robin_hood.h"

#ifdef NDEBUG
  //template<class K, class V>
  //using pivot_map = robin_hood::unordered_flat_map<K,V>;
  template<class K, class V>
  using pivot_map = std::unordered_map<K,V>;
#else

  template<class K, class V>
  using pivot_map = std::map<K,V>;
#endif

typedef std::list<xlit>::iterator xlits_it;

class xsys
{
  private:
    std::list< xlit > xlits;

    pivot_map<var_t, xlits_it > pivot_poly_its;

    void rref();
  public:
    xsys() noexcept { xlits = std::list<xlit>(); };
    xsys(const xlit& lit) noexcept : xlits(std::list<xlit>({lit})) { rref(); };
    xsys(xlit&& lit) noexcept : xlits(std::list<xlit>({std::move(lit)})) { rref(); };
    xsys(const vec<xlit>& xlits_) noexcept : xlits(xlits_.begin(),xlits_.end()) { rref(); };
    xsys(const std::list<xlit>& xlits_) noexcept : xlits(xlits_) { rref(); };
    xsys(std::list<xlit>&& xlits_) noexcept : xlits(std::move(xlits_)) { rref(); };
    xsys(const xsys& o) noexcept : xlits(o.xlits) { fix_pivot_poly_idx(); };
    xsys(xsys&& o) noexcept : xlits(std::move(o.xlits)) { fix_pivot_poly_idx(); };
    ~xsys() = default;

    /**
     * @brief inits pivot_poly_its given that xlits are already in row-reduced form
     * @note necessary to have the iterators point to the correct list as required in, e.g., cpy- and mv-ctor
     */
    inline void fix_pivot_poly_idx() {
      assert_slow( to_str() == xsys(xlits).to_str() );
      pivot_poly_its.clear();
      for(auto it = xlits.begin(); it!=xlits.end(); ++it) {
        pivot_poly_its[ it->LT() ] = it;
      }
    };

    /**
     * @brief reduces a given xlit by the linsys
     * 
     * @param l given xlit
     * @return xlit reduced with the xlits in the linsys
     */
    xlit reduce(const xlit& l) const;

    /**
     * @brief updates xsyses LTs modulo l
     * 
     * @param l lit to reduce with
     * @return true iff clause was changed
     */
    bool lt_update(const xlit& l);
    
    /**
     * @brief updates xsyses LTs modulo l -- if every single reduction does not increase the size by more than 50% -- and the lineral has already a length > 3
     * 
     * @param l lit to reduce with
     * @return true iff clause was changed
     */
    bool lt_update_short(const xlit& l);
    
    inline xlit get_non_zero_el() const { return *(pivot_poly_its.begin()->second); };

    bool is_consistent() const { return pivot_poly_its.find(0) == pivot_poly_its.end(); };

    /**
     * @brief evaluates xsys with tuple sol
     * 
     * @param sol 
     * @return true if sol is a solution of the linsys
     * @return false if sol is not a solution of the linsys
     */
    bool eval(const vec<bool>& sol) const;

    /**
     * @brief returns a solution of the linsys, 'extends' sol_ it to a solution of this linsys, i.e., the LTs of this xsys are determined based on the values of sol_
     * 
     * @param sol_  (partial) solution to be extended
     * @return vec<bool> solution of linsys, if there exists one
     * @note throws an assertion-failure if linsys is inconsistent
     */
    void solve(vec<bool>& sol_) const;

    std::string to_str() const;

    inline int dim() const { return pivot_poly_its.size(); };
    
    inline std::size_t size() const { return xlits.size(); };
    
    //deprecated!
    inline const vec<xlit> get_xlits_vec() const { return vec<xlit>(xlits.begin(),xlits.end()); };
    inline const std::list<xlit>& get_xlits() const { return xlits; };
    inline const xlit& get_xlits(var_t i) const { return *(std::next(xlits.begin(),i)); };
    inline const xlit& get_xlits(xlits_it it) const { return *it; };
    inline const pivot_map<var_t,xlits_it>& get_pivot_poly_idx() const { return pivot_poly_its; };

    inline bool operator ==(const xsys& other) const { return to_str()==other.to_str(); };
    //inline bool operator ==(const xsys& other) const { return std::all_of(xlits.begin(), xlits.end(), [&](const xlit& lit){ return other.reduce(lit).is_zero(); } ) && std::all_of(other.xlits.begin(), other.xlits.end(), [&](const xlit& lit){ return reduce(lit).is_zero(); } ); };

    xsys& operator =(const xsys& other) { xlits = other.xlits; pivot_poly_its = other.pivot_poly_its; return *this; };
    //TODO: do we need to run fix_pivot_poly_idx() after move???
    xsys& operator =(xsys&& other) { xlits = std::move(other.xlits); pivot_poly_its = std::move(other.pivot_poly_its); return *this; };

    bool contains_lt(const var_t lt) const { return pivot_poly_its.contains(lt); };
    
	  xsys operator+(const xsys &other) const;
    //in-place operation (!)
    xsys& operator +=(const xsys& other);	

    /**
     * @brief add a reduced literal to this xsys
     * 
     * @param l literal to be added
     */
    void add_reduced_lit(const xlit& l);
};
