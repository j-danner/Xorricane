#pragma once

#include <set>
#include <sstream>

#include "misc.hpp"

#include "lineral.hpp"
#include "lin_sys.hpp"

class lin_sys_lazy_GE
{
  private:
    /**
     * @brief linerals in lin_sys
     */
    vec<lineral> linerals;

    /**
     * @brief map from var to idx, where lineral[idx] is pivot for var; these simultaneously also are the first watches of each lineral!
     */
    pivot_map<var_t, var_t> pivot_poly;
    
    /**
     * @brief firsst_watch[i] gives the 1st watch of lineral[i]; this coincides with pivot_poly's keys
     */
    vec<var_t> first_watch;
    
    /**
     * @brief second_watch[i] gives the 2nd watch of lineral[i]
     */
    vec<var_t> second_watch;

    /**
     * @brief watch_list[var] contains all idxs, where lineral[idx] watches var
     */
    pivot_map< var_t, list<var_t> > watch_list;

    /**
     * @brief assigning linerals (literals), not yet fetched
     */
    list<lineral> implied_literal_queue;

    /**
     * @brief initialises lin_sys_watch, fixes second watches
     * @note after init use get_implied_literal_queue to check if any literals could be deduced directly!
     */
    void init() {
        //initialize first-watches
        first_watch = vec<var_t>(linerals.size());
        for(auto& [lt,row_idx] : pivot_poly) {
            first_watch[row_idx] = lt;
        }

        //initialize second-watches
        second_watch = vec<var_t>(linerals.size());
        for(var_t idx=0; idx<linerals.size(); ++idx) {
            if(linerals[idx].is_assigning()) {
                second_watch[idx] = first_watch[idx];
                implied_literal_queue.emplace_back( linerals[idx] );
                continue;
            }
            //there must be another variable to watch!
            for(const auto& v : linerals[idx].get_idxs_()) {
                if( v!=first_watch[idx] ) {
                    assert(!pivot_poly.contains(v));
                    second_watch[idx] = v;
                    watch_list[v].push_back(idx);
                    break;
                }
            }
        }
    }

    void rref() {
        pivot_poly.clear();
        for(var_t idx = 0; idx<linerals.size(); ++idx) {
            //reduce new row (with non-zero pivot-rows)
            for (const auto &[lt,row] : pivot_poly) {
                if(linerals[idx][lt]) {
                    linerals[idx] += linerals[row];
                }
            }
            if(!(linerals[idx].is_zero()) ) {
                //if non-zero, add to LT_to_row_idx-map
                const var_t new_lt = linerals[idx].LT();
                //add new LT to map
                pivot_poly[ new_lt ] = idx;

                //full-reduction of previous pivot-rows, i.e., reduce all previously found rows:
                for (auto &[lt,row] : pivot_poly) {
                    if (lt!=new_lt && linerals[row][new_lt]) linerals[row] += linerals[idx];
                }
            }
        }
    }

    void init_and_rref() {
        rref();
        init();
        assert( assert_data_struct() );
    }

  public:
    lin_sys_lazy_GE() noexcept { init_and_rref(); };
    
    lin_sys_lazy_GE(lin_sys&& sys) noexcept {
        linerals.reserve( sys.linerals.size() );
        for(auto&& l : sys.linerals) linerals.emplace_back( std::move(l) );
        //only init pivot_polys and init!
        //init_and_rref(); -- not necessary!
        for(var_t idx = 0; idx<linerals.size(); ++idx) {
            pivot_poly[ linerals[idx].LT() ] = idx;
        }

        init();
    };
    lin_sys_lazy_GE(const vec<lineral>& linerals_) noexcept : linerals(linerals_.begin(),linerals_.end()) { init_and_rref(); };
    ~lin_sys_lazy_GE() = default;

    list<lineral>& get_implied_literal_queue() { return implied_literal_queue; }
    void clear_implied_literal_queue() { implied_literal_queue.clear(); }

    const vec<lineral>& get_linerals() const { return linerals; }

    /**
     * @brief checks if linerals[idx] is inactive
     * 
     * @param idx index in linerals
     * @param alpha current alpha-assignments
     * @return true if and only if the clause has been set inactive
     */
    bool is_active(const var_t& idx, const vec<bool3>& alpha) {
        return alpha[first_watch[idx]]==bool3::None;
    }
    bool is_active(const var_t& idx, const vec<var_t>& alpha_trail_pos) {
        return alpha_trail_pos[first_watch[idx]]==(var_t) -1;
    }
    
    /**
     * @brief fix second watch of linerals[idx] after another linerals[jdx] was added to it; note: the first_watch cannot change by that, only the second one does!
     * 
     * @param idx index of lineral
     * @param alpha current alpha assignment
     * @return bool true iff clause linerals[idx] is inactive OR a second watch could be found, i.e., a lineral[idx] is not assigning under alpha
     */
    bool fix_second_watch_after_addition(const var_t& idx, const vec<var_t>& alpha_trail_pos) {
        //abort if currently inactive
        //if( !is_active(idx, alpha_trail_pos) ) return true;
        //early abort if second watch needs no update, i.e., it is not assigned!
        //if( second_watch[idx]!=(var_t)-1 && alpha_trail_pos[second_watch[idx]]==(var_t) -1 ) return true;
        
        //rm pointer in watch_list (!)
        watch_list[second_watch[idx]].remove(idx);

        if(linerals[idx].is_assigning()) {
            second_watch[idx] = first_watch[idx];
            return false;
        }
        const auto& idxs = linerals[idx].get_idxs_();
        var_t max_v = idxs[0];
        var_t max_trail_pos = alpha_trail_pos[max_v];
        for(const var_t& v : idxs) {
          if(v==first_watch[idx]) continue;
          if(alpha_trail_pos[v]==(var_t)-1) { 
            //watch found!
            assert(!pivot_poly.contains(v));
            //update watch_list
            second_watch[idx] = v;
            watch_list[second_watch[idx]].push_back(idx);
            return true;
          }
          if(alpha_trail_pos[v]>max_trail_pos) { 
            max_v = v;
            max_trail_pos = alpha_trail_pos[v];
          }
        }
        //since linerals is not assigning, there is at least ONE other variable -- except first_watch[idx]!
        assert(max_trail_pos<=(var_t)-1);
        second_watch[idx] = max_v;
        watch_list[second_watch[idx]].push_back(idx);
        return false;
    }
    
    /**
     * @brief fix second watch of lineral[idx]
     * @note does not update watch_lists!
     * 
     * @param idx index of lineral
     * @param alpha current alpha assignment
     * @return bool true iff clause linerals[idx] is inactive OR a second watch could be found, i.e., a lineral[idx] is not assigning under alpha
     */
    bool fix_second_watch(const var_t& idx, const vec<var_t>& alpha_trail_pos) {
        //abort if currently inactive
        if( !is_active(idx, alpha_trail_pos) ) return true;
        //early abort if second watch needs no update, i.e., it is not assigned!
        if( second_watch[idx]!=(var_t)-1 && alpha_trail_pos[second_watch[idx]]==(var_t) -1 ) return true;

        //since there was no addition, the second watch EXISTS inside linerals[idx], i.e., if no new var to watch is found, we may keep it where it is!
        assert( linerals[idx][second_watch[idx]] );

        for(const auto& v : linerals[idx].get_idxs_()) {
            if(v==first_watch[idx]) continue;
            if(alpha_trail_pos[v]==(var_t)-1) { 
                //watch found!
                assert(!pivot_poly.contains(v));
                //watch_list[second_watch[idx]].remove(idx);
                second_watch[idx] = v;
                //watch_list[second_watch[idx]].push_back(idx);
                return true;
            }
        }
        return false;
    }

    var_t find_third_watch(const var_t& idx, const vec<var_t>& alpha_trail_pos) {
        for(const auto& v : linerals[idx].get_idxs_()) {
            if(v==first_watch[idx] || v==second_watch[idx]) continue;
            if(alpha_trail_pos[v]==(var_t)-1) { 
                //watch found!
                assert(!pivot_poly.contains(v));
                return v;
            }
        }
        return (var_t) -1;
    }



    /**
     * @brief assigns var, i.e., ensures it is not watched, and fixes row-echelon under alpha
     * 
     * @param var newly assigned variable
     * @param alpha current alpha-assignment
     * @return bool true iff new alpha-assignments were deduced!
     */
    bool assign(const var_t var, const vec<var_t>& alpha_trail_pos) {
        //#ifndef NDEBUG
        //  std::cout << "assigning x" << std::to_string(var) << " in " << to_str() << std::endl;
        //  //add variables for all assigned vals
        //  vec<lineral> tmp;
        //  for(var_t idx=0; idx<alpha_trail_pos.size(); ++idx) {
        //      if(alpha_trail_pos[idx]!=(var_t)-1) tmp.push_back( lineral(idx, false) );
        //  }
        //  std::copy(linerals.begin(), linerals.end(), std::back_inserter(tmp));
        //  lin_sys sys(tmp);
        //  std::cout << "we should find new assignments: " << std::endl;
        //  for(const auto& lin : sys.get_linerals()) {
        //      if(lin.is_assigning() && alpha_trail_pos[lin.LT()]==(var_t)-1) std::cout << lin.to_str() << std::endl;
        //  }
        //#endif

        std::set<var_t> new_lit_idxs;
        //if var is watched by pivot, then update pivots!
        if( pivot_poly.contains(var) ) {
            //update pivot_poly_its
            var_t idx = pivot_poly[var];

            //early abort if linerals[idx] was already assigned previously!
            assert(first_watch[idx]==var);
            if(alpha_trail_pos[ second_watch[idx] ]!=(var_t)-1 && alpha_trail_pos[second_watch[idx]]<alpha_trail_pos[first_watch[idx]]) return false;
            
            // try to find a third watch in linerals[idx]
            var_t third_watch = find_third_watch(idx, alpha_trail_pos);

            if(third_watch==(var_t)-1 && alpha_trail_pos[first_watch[idx]]==(var_t)-1) {
                //no third watch found => linerals[idx] is assigning under alpha & pivot-poly and watch_lists need no update!
                new_lit_idxs.insert(idx);
            } else {
                //new wathchable var found => update pivot variable to third_watch! (this requires no update to watch_lists!)
                pivot_poly.erase(var);
                // pivot-var of linerals[idx] is 
                pivot_poly[third_watch] = idx;
                first_watch[idx] = third_watch;
            }

            //full-reduction with new pivot-row
            //BEWARE this messes up our watch_list! (as of now!)
            for(var_t jdx=0; jdx<linerals.size(); ++jdx) {
                if(idx==jdx) continue;
                if(third_watch!=(var_t) -1 && linerals[jdx][third_watch]) {
                    linerals[jdx] += linerals[idx];
                    //fix second watch -- note LTs cannot cancel -- only second watches need to be updated!
                    if( !fix_second_watch_after_addition(jdx, alpha_trail_pos) ) new_lit_idxs.insert(jdx);
                    //TODO remove old second watch!
                } else if(second_watch[jdx]==var) {
                    //fix second_watch
                    if( fix_second_watch(jdx, alpha_trail_pos) ) {
                        //second watch is found!
                        watch_list[second_watch[jdx]].emplace_front(jdx);
                        //TODO remove from old watch list!
                    } else if (alpha_trail_pos[second_watch[jdx]]!=(var_t)-1) {
                        new_lit_idxs.insert(jdx);
                    }
                }
            }
        } else {
            //update all remaining second watches
            for(auto it = watch_list[var].begin(); it!=watch_list[var].end();) {
                if( var!=second_watch[*it] ) {
                    //outdated watch, remove it!
                    it = watch_list[var].erase(it);
                    //assert(false); // can/should this even happen?!
                } else if( fix_second_watch(*it, alpha_trail_pos) ) {
                    //second watch is found
                    watch_list[second_watch[*it]].emplace_front(*it);
                    it = watch_list[var].erase(it);
                } else {
                    new_lit_idxs.insert(*it);
                    ++it;
                }
            }
        }

        //add propagated literals to queue
        for(const auto& idx : new_lit_idxs) implied_literal_queue.emplace_back( linerals[idx] );

        assert( assert_data_struct() );

      //#ifndef NDEBUG
      //  sys = lin_sys( get_implied_literal_queue() );
      //  std::cout << "found " << sys.to_str() << std::endl;
      //#endif
        
        return !new_lit_idxs.empty();
    }

    bool add_lineral(const lineral& l) {
        assert(false);
        //lin_sys::add_lineral(l);
        //FIX data structs!
        return true;
    }

    bool assert_data_struct() const {
        //check that watches are present in linerals
        for(var_t idx=0; idx<linerals.size(); ++idx) {
            if(linerals[idx].is_constant()) continue;
            assert( first_watch[idx]==(var_t)-1 || linerals[idx][first_watch[idx]] );
            assert( second_watch[idx]==(var_t)-1 || linerals[idx][second_watch[idx]] );
        }

        //check that second_watches are present in watch-list; it must be at least the the number of linerals
        std::unordered_map< var_t, std::set<var_t> > idx_to_wlist_entries;
        for(const auto& [v,s] : watch_list) {
            for(const auto& idx : s) {
                //assert( second_watch[idx]==v ); //must not hold, BUT every second_watch[idx] must be watched!
                idx_to_wlist_entries[idx].insert( v );
            }
        }
        for([[maybe_unused]] const auto& [idx, s] : idx_to_wlist_entries) {
            assert( std::any_of(s.begin(), s.end(), [&](const auto& v){ return second_watch[idx]==v; }) );
        }

        //check that first_watch coincides with pivot_polys
        for([[maybe_unused]] const auto& [v,idx] : pivot_poly) {
            assert( v==first_watch[idx] );
        }

        return true;
    }

    var_t size() const { return linerals.size(); };

    std::string to_str() const;
};


using sub_sys_it = list<lin_sys_lazy_GE>::iterator;

/**
 * @brief lazy GJE for lin_sys under variable assignments; needs no updates on backtracking
 */
class lin_sys_watch
{
    private:
    /**
     * @brief vector of linerals corresponding to each subsystem
     * @note the total linsys is segmented into subsystems of linerals sharing variables
     */
    list< lin_sys_lazy_GE > lin_sub_systems;
    // to separate us CMS5 code; pseudo-code available at 'https://www.msoos.org/largefiles/matesoos-satsmt-winterschool-2019.pdf' pg. 55

    /**
     * @brief get iterator to the subsystem a variable occurs in; whenever a lineral is added that corresponds to multiple subsystems, those have to be merged!
     */
    pivot_map< var_t, sub_sys_it > var_to_subsys;

    /**
     * @brief watch_list[i] contains all linerals that watch variable i
     */
    pivot_map< var_t, list<var_t> > watch_list;


    public:
    lin_sys_watch() {};

    bool assert_data_struct() const {
      for(const auto& l : lin_sub_systems) {
        assert(l.assert_data_struct());
      }
      return true;
    };
};
