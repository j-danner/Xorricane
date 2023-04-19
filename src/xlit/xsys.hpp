#pragma once

#include <string>
#include <map>

#include "xlit.hpp"

#include "../robin_hood-3.11.5/robin_hood.h"

#ifdef NDEBUG
  template<class K, class V>
  using pivot_map = robin_hood::unordered_flat_map<K,V>;
#else

  template<class K, class V>
  //using pivot_map = std::unordered_map<K,V>;
  using pivot_map = std::map<K,V>;
#endif

class xsys
{
  private:
    vec< xlit > xlits;

    pivot_map<var_t, var_t> pivot_poly_idx;

    void rref();
  public:
    xsys() noexcept { xlits = vec<xlit>(0); };
    xsys(const xlit& lit) noexcept : xlits(vec<xlit>({lit})) { rref(); };
    xsys(xlit&& lit) noexcept : xlits(vec<xlit>({std::move(lit)})) { rref(); };
    xsys(const vec<xlit>& xlits_) noexcept : xlits(xlits_) { rref(); };
    xsys(vec<xlit>&& xlits_) noexcept : xlits(std::move(xlits_)) { rref(); };
    xsys(const xsys& o) noexcept : xlits(o.xlits), pivot_poly_idx(o.pivot_poly_idx) {};
    xsys(xsys&& o) noexcept : xlits(std::move(o.xlits)), pivot_poly_idx(std::move(o.pivot_poly_idx)) {};
    ~xsys() = default;

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
     */
    void lt_update(const xlit& l);
    
    /**
     * @brief updates xsyses LTs modulo l
     * 
     * @param assignments to reduce with
     */
    void lt_update(const vec<xlit>& assignments);
    
    /**
     * @brief updates xsyses LTs modulo l
     * 
     * @param assignments to reduce with
     * @param assignments_dl dl of each assignment
     * @param dl dl up to which assignments are considered
     */
    void lt_update(const vec<xlit>& assignments, const vec<var_t>& assignments_dl, const var_t dl);
    
    void update(const vec<xlit>& assignments, const vec<var_t>& assignments_dl, const var_t dl);

    inline xlit get_non_zero_el() const { return xlits[pivot_poly_idx.begin()->second]; };

    bool is_consistent() const { return pivot_poly_idx.find(0) == pivot_poly_idx.end(); };

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

    inline int dim() const { return pivot_poly_idx.size(); };
    
    inline int size() const { return xlits.size(); };
    
    inline const vec<xlit>& get_xlits() const { return xlits; };
    inline const xlit& get_xlits(var_t i) const { return xlits[i]; };
    inline const pivot_map<var_t,var_t>& get_pivot_poly_idx() const { return pivot_poly_idx; };

    inline bool operator ==(const xsys& other) const { return to_str()==other.to_str(); };
    xsys& operator =(const xsys& other) { xlits = other.xlits; pivot_poly_idx = other.pivot_poly_idx; return *this; };
    xsys& operator =(xsys&& other) { xlits = std::move(other.xlits); pivot_poly_idx = std::move(other.pivot_poly_idx); return *this; };

    bool contains_lt(const var_t lt) const { return pivot_poly_idx.contains(lt); };
    
	  xsys operator+(const xsys &other) const;
    //in-place operation (!)
    xsys& operator +=(const xsys& other);	
};
