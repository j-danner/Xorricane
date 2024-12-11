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


template<class T>
class lin_sys_T
{
  protected:
    list< T > linerals;

    typedef list<T>::iterator linerals_it;
    pivot_map<var_t, linerals_it > pivot_poly_its;

    virtual void rref() {
      pivot_poly_its.clear();
      for(linerals_it it = linerals.begin(); it!=linerals.end();) {
          //reduce new row (with non-zero pivot-rows)
          for (const auto &[lt,row] : pivot_poly_its)
          {
              if((*it)[lt]) {
                  *it += *row;
              }
          }
          if(!(it->is_zero()) ) {
              //if non-zero, add to LT_to_row_idx-map
              const var_t new_lt = it->LT();
              //add new LT to map
              pivot_poly_its[ new_lt ] = it;

              //full-reduction of previous pivot-rows, i.e., reduce all previously found rows:
              for (auto &[lt,row] : pivot_poly_its)
              {
                  if (lt!=new_lt && (*row)[new_lt]) *row += *it;
              }

              ++it;
          } else {
              //if zero, remove row from linerals + adjust running var i
              it = linerals.erase( it );
          }
      }
    };
  public:
    lin_sys_T() noexcept {};
    lin_sys_T(const T& lit) noexcept : linerals(list<lineral>({lit})) { rref(); };
    lin_sys_T(T&& lit) noexcept : linerals(list<lineral>({std::move(lit)})) { rref(); };
    template <typename Iterable>
    lin_sys_T(const Iterable& iterable) : linerals(std::begin(iterable), std::end(iterable)) { rref(); }
    lin_sys_T(list<T>&& linerals_) noexcept : linerals(std::move(linerals_)) { rref(); };
    lin_sys_T(const lin_sys_T& o) noexcept : linerals(o.linerals) { fix_pivot_poly_idx(); };
    lin_sys_T(lin_sys_T&& o) noexcept : linerals(std::move(o.linerals)) { fix_pivot_poly_idx(); };
    ~lin_sys_T() = default;

    /**
     * @brief inits pivot_poly_its given that linerals are already in row-reduced form
     * @note necessary to have the iterators point to the correct list as required in, e.g., cpy- and mv-ctor
     */
    inline void fix_pivot_poly_idx() {
      assert_slower( to_str() == lin_sys_T(linerals).to_str() );
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
    lineral reduce(const T& l) const {
      T l_(l);
      for (const auto &[lt,row] : pivot_poly_its) {
          if(l_[lt]) {
              l_ += *row;
          }
      }
      return l_;
    };

    /**
     * @brief updates lin_syses LTs modulo l
     * 
     * @param l lit to reduce with
     * @return true iff clause was changed
     */
    bool lt_update(const T& l) {
      const auto search = pivot_poly_its.find( l.LT() );
      if(search == pivot_poly_its.end()) return false;
      const auto row = search->second;
      //LT found -- start reduction!
      *row += l;
      //rm from pivot_poly_its, then reduce with other eqs
      pivot_poly_its.erase( search );
      for (const auto &[lt,row_lt] : pivot_poly_its)
      {
          if((*row)[lt]) {
              *row += *row_lt;
          }
      }
      //if non-zero, add back to pivot_poly_its
      if(!(row->is_zero())) {
          pivot_poly_its[row->LT()] = row;
      }
      return true;
    };

    T tmp_lin;    
    /**
     * @brief updates lin_syses LTs modulo l -- if every single reduction does not increase the size by more than 50% -- and the lineral has already a length > 3
     * 
     * @param l lit to reduce with
     * @return true iff clause was changed
     */
    bool lt_update_short(const T& l) {
      //complexity to find correct update linerals: O( log( this.size() ) * sys.size() )
      const auto search = pivot_poly_its.find( l.LT() );
      if(search == pivot_poly_its.end()) return false;
      const auto row = search->second;
      //LT found -- start reduction!
      tmp_lin.clear();
      tmp_lin = *row + l;
      //update row -- if short enough
      if(tmp_lin.size() > 1.50 * row->size()) return false;
      row->swap(tmp_lin);
      //rm from pivot_poly_its, then reduce with other eqs
      pivot_poly_its.erase( search );
      for (const auto &[lt,row_lt] : pivot_poly_its) {
          if((*row)[lt]) {
              *row += *row_lt;
          }
      }
      //if non-zero, add back to pivot_poly_its
      if(!(row->is_zero())) {
          pivot_poly_its[row->LT()] = row;
      }
      return true;
    };
    
    inline T get_non_zero_el() const { return *(pivot_poly_its.begin()->second); };

    bool is_consistent() const { return pivot_poly_its.find(0) == pivot_poly_its.end(); };

    /**
     * @brief evaluates lin_sys_T with tuple sol
     * 
     * @param sol 
     * @return true if sol is a solution of the linsys
     * @return false if sol is not a solution of the linsys
     */
    bool eval(const vec<bool>& sol) const {
      return std::all_of(linerals.begin(), linerals.end(), [&sol](lineral l) { return l.eval(sol); } );
    };

    /**
     * @brief returns a solution of the linsys, 'extends' sol_ it to a solution of this linsys, i.e., the LTs of this lin_sys_T are determined based on the values of sol_
     * 
     * @param sol_  (partial) solution to be extended
     * @return vec<bool> solution of linsys, if there exists one
     * @note throws an assertion-failure if linsys is inconsistent
     */
    void solve(vec<bool>& sol_) const {
      if(linerals.size()==0) return;
      for (const auto &[lt,row] : pivot_poly_its) {
          sol_[lt-1] = row->eval(sol_) ? sol_[lt-1] : !sol_[lt-1];
      }
    };

    std::string to_str() const {
      vec< std::string > str_linerals( linerals.size() );
      auto to_str = [](const lineral l) -> std::string {return l.to_str();};
      std::transform(linerals.begin(), linerals.end(), str_linerals.begin(), to_str);
      std::sort(str_linerals.begin(), str_linerals.end());
      //rotate if 1 is first element
      if(str_linerals.size()>0 && str_linerals[0]=="1") std::rotate(str_linerals.begin(), str_linerals.begin()+1, str_linerals.end());
      std::stringstream ss;
      std::copy(str_linerals.begin(), str_linerals.end(), std::ostream_iterator<std::string>(ss, " "));
      std::string result = ss.str();
      if (!result.empty()) {
          result.resize(result.length() - 1); // trim trailing space
          return result;
      } else {
          return "0";
      }
    };

    inline int dim() const { return pivot_poly_its.size(); };
    
    inline std::size_t size() const { return linerals.size(); };
    
    //deprecated!
    inline const vec<T> get_linerals_vec() const { return vec<T>(linerals.begin(),linerals.end()); };
    inline const list<T>& get_linerals() const { return linerals; };
    inline const T& get_linerals(var_t i) const { return *(std::next(linerals.begin(),i)); };
    inline const T& get_linerals(linerals_it it) const { return *it; };
    inline const pivot_map<var_t,linerals_it>& get_pivot_poly_idx() const { return pivot_poly_its; };

    inline bool operator ==(const lin_sys_T& other) const { return to_str()==other.to_str(); };
    //inline bool operator ==(const lin_sys_T& other) const { return std::all_of(linerals.begin(), linerals.end(), [&](const lineral& lit){ return other.reduce(lit).is_zero(); } ) && std::all_of(other.linerals.begin(), other.linerals.end(), [&](const lineral& lit){ return reduce(lit).is_zero(); } ); };

    lin_sys_T& operator =(const lin_sys_T& other) { linerals = other.linerals; pivot_poly_its = other.pivot_poly_its; return *this; };
    //TODO: do we need to run fix_pivot_poly_idx() after move???
    lin_sys_T& operator =(lin_sys_T&& other) { linerals = std::move(other.linerals); pivot_poly_its = std::move(other.pivot_poly_its); return *this; };

    bool contains_lt(const var_t lt) const { return pivot_poly_its.contains(lt); };
    
	  lin_sys_T operator+(const lin_sys_T &other) const {
      lin_sys_T cpy(*this);
      cpy += other;
      return cpy;
    };

    //in-place operation (!)
    lin_sys_T& operator +=(const lin_sys_T& other) {
      linerals_it it = linerals.end();
      it--;
      auto other_linerals = other.get_linerals();
      linerals.splice(linerals.end(), std::move(other_linerals));
      it++; //now it points to first element in other.linerals
      while(it!=linerals.end()) {
          //reduce new row
          for (const auto &[lt,row] : pivot_poly_its)
          {
              if((*it)[lt]) {
                  *it += *row;
              }
          }
          if(!(it->is_zero()) ) {
              //if non-zero, add to LT_to_row_idx-map
              const var_t new_lt = it->LT();
              //add new LT to map
              pivot_poly_its[ new_lt ] = it;

              //full-reduction of previous pivot-rows, i.e., reduce all previously found rows:
              for (auto &[lt,row] : pivot_poly_its)
              {
                  if (lt!=new_lt && (*row)[new_lt]) *row += *it;
              }

              ++it;
          } else {
              //if zero, remove row from linerals + adjust running var i
              it = linerals.erase( it );
          }
      }
      return *this;
    };	

    /**
     * @brief add a reduced literal to this lin_sys_T
     * 
     * @param l literal to be added
     */
    void add_reduced_lit(const T& l) {
      if(l.is_zero()) return;
      //assert that l is indeed reduced
      assert( reduce(l) == l );
      for(auto& r : linerals) {
          if(r[l.LT()]) r += l;
      }
      //append l to linerals
      linerals.push_back( l );
      //add to pivot_poly_its
      assert(!pivot_poly_its.contains(l.LT()));
      pivot_poly_its[linerals.back().LT()] = std::prev(linerals.end());
    };
    void add_reduced_lit(T&& l) {
      if(l.is_zero()) return;
      //assert that l is indeed reduced
      assert( reduce(l) == l );
      for(auto& r : linerals) {
          if(r[l.LT()]) r += l;
      }
      //append l to linerals
      linerals.emplace_back( std::move(l) );
      //add to pivot_poly_its
      assert(!pivot_poly_its.contains(linerals.back().LT()));
      pivot_poly_its[linerals.back().LT()] = std::prev(linerals.end());
    };

    void add_lineral(T&& l) noexcept { l.reduce(*this); add_reduced_lit( std::move(l) ); };
    void add_lineral(const T& l) noexcept { T l_ = l; l_.reduce(*this); add_reduced_lit( std::move(l_) ); };

    void clear() noexcept { linerals.clear(); pivot_poly_its.clear(); };
};

using lin_sys = lin_sys_T<lineral>;