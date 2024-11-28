#pragma once

#include <string>
#include <map>
#include <list>

#include "lineral.hpp"


#ifdef NDEBUG
  template<class K, class V>
  using pivot_map = std::map<K,V>;
  //using pivot_map = std::unordered_map<K,V>; //this is sometimes different thatn std::map (see test59.xnf); generally negative effect :/
#else
  template<class K, class V>
  using pivot_map = std::map<K,V>;
  //using pivot_map = std::unordered_map<K,V>;
#endif

typedef list<lineral>::iterator linerals_it;

class lin_sys
{
  private:
    list< lineral > linerals;

    pivot_map<var_t, linerals_it > pivot_poly_its;

    void rref();
  public:
    lin_sys() noexcept { linerals = list<lineral>(); };
    lin_sys(const lineral& lit) noexcept : linerals(list<lineral>({lit})) { rref(); };
    lin_sys(lineral&& lit) noexcept : linerals(list<lineral>({std::move(lit)})) { rref(); };
    lin_sys(const vec<lineral>& linerals_) noexcept : linerals(linerals_.begin(),linerals_.end()) { rref(); };
    lin_sys(const list<lineral>& linerals_) noexcept : linerals(linerals_) { rref(); };
    lin_sys(list<lineral>&& linerals_) noexcept : linerals(std::move(linerals_)) { rref(); };
    lin_sys(const lin_sys& o) noexcept : linerals(o.linerals) { fix_pivot_poly_idx(); };
    lin_sys(lin_sys&& o) noexcept : linerals(std::move(o.linerals)) { fix_pivot_poly_idx(); };
    ~lin_sys() = default;

    /**
     * @brief inits pivot_poly_its given that linerals are already in row-reduced form
     * @note necessary to have the iterators point to the correct list as required in, e.g., cpy- and mv-ctor
     */
    inline void fix_pivot_poly_idx() {
      assert_slow( to_str() == lin_sys(linerals).to_str() );
      pivot_poly_its.clear();
      for(auto it = linerals.begin(); it!=linerals.end(); ++it) {
        pivot_poly_its[ it->LT() ] = it;
      }
    };

    /**
     * @brief reduces a given lineral by the linsys
     * 
     * @param l given lineral
     * @return lineral reduced with the linerals in the linsys
     */
    lineral reduce(const lineral& l) const;

    /**
     * @brief updates lin_syses LTs modulo l
     * 
     * @param l lit to reduce with
     * @return true iff clause was changed
     */
    bool lt_update(const lineral& l);
    
    /**
     * @brief updates lin_syses LTs modulo l -- if every single reduction does not increase the size by more than 50% -- and the lineral has already a length > 3
     * 
     * @param l lit to reduce with
     * @return true iff clause was changed
     */
    bool lt_update_short(const lineral& l);
    
    inline lineral get_non_zero_el() const { return *(pivot_poly_its.begin()->second); };

    bool is_consistent() const { return pivot_poly_its.find(0) == pivot_poly_its.end(); };

    /**
     * @brief evaluates lin_sys with tuple sol
     * 
     * @param sol 
     * @return true if sol is a solution of the linsys
     * @return false if sol is not a solution of the linsys
     */
    bool eval(const vec<bool>& sol) const;

    /**
     * @brief returns a solution of the linsys, 'extends' sol_ it to a solution of this linsys, i.e., the LTs of this lin_sys are determined based on the values of sol_
     * 
     * @param sol_  (partial) solution to be extended
     * @return vec<bool> solution of linsys, if there exists one
     * @note throws an assertion-failure if linsys is inconsistent
     */
    void solve(vec<bool>& sol_) const;

    std::string to_str() const;

    inline int dim() const { return pivot_poly_its.size(); };
    
    inline std::size_t size() const { return linerals.size(); };
    
    //deprecated!
    inline const vec<lineral> get_linerals_vec() const { return vec<lineral>(linerals.begin(),linerals.end()); };
    inline const list<lineral>& get_linerals() const { return linerals; };
    inline const lineral& get_linerals(var_t i) const { return *(std::next(linerals.begin(),i)); };
    inline const lineral& get_linerals(linerals_it it) const { return *it; };
    inline const pivot_map<var_t,linerals_it>& get_pivot_poly_idx() const { return pivot_poly_its; };

    inline bool operator ==(const lin_sys& other) const { return to_str()==other.to_str(); };
    //inline bool operator ==(const lin_sys& other) const { return std::all_of(linerals.begin(), linerals.end(), [&](const lineral& lit){ return other.reduce(lit).is_zero(); } ) && std::all_of(other.linerals.begin(), other.linerals.end(), [&](const lineral& lit){ return reduce(lit).is_zero(); } ); };

    lin_sys& operator =(const lin_sys& other) { linerals = other.linerals; pivot_poly_its = other.pivot_poly_its; return *this; };
    //TODO: do we need to run fix_pivot_poly_idx() after move???
    lin_sys& operator =(lin_sys&& other) { linerals = std::move(other.linerals); pivot_poly_its = std::move(other.pivot_poly_its); return *this; };

    bool contains_lt(const var_t lt) const { return pivot_poly_its.contains(lt); };
    
	  lin_sys operator+(const lin_sys &other) const;
    //in-place operation (!)
    lin_sys& operator +=(const lin_sys& other);	

    /**
     * @brief add a reduced literal to this lin_sys
     * 
     * @param l literal to be added
     */
    void add_reduced_lit(const lineral& l);
    void add_reduced_lit(lineral&& l);

    void add_lineral(lineral&& l) noexcept { l.reduce(*this); add_reduced_lit( std::move(l) ); };
    void add_lineral(const lineral& l) noexcept { lineral l_ = l; l_.reduce(*this); add_reduced_lit( std::move(l_) ); };

    void clear() noexcept { linerals.clear(); pivot_poly_its.clear(); };
};
