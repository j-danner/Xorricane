#pragma once

#include "cls_watch.hpp"

#include <queue>

//forward declaration
class solver;


class cls_watch_resolver : public cls_watch {
private:
  /**
   * @brief maps t_pos to idxs of linerals, i.e., linerals[ t_pos_to_idxs[t_pos] ] = t_pos
   */
  //@todo replace with 'https://www.codeproject.com/script/Articles/ViewDownloads.aspx?aid=27799' ?
  std::map<var_t, list<var_t> > t_pos_to_idxs;

  /**
   * @brief number of non-zero linerals in linerals
   */
  var_t num_nz_lins = 1;

  inline void init() {
    //distribute shared_part
    if(idx[0]<linerals.size()) WLIN0 += shared_part;
    if(idx[1]<linerals.size()) WLIN1 += shared_part;
    shared_part.clear();

    //init num_nz_lins
    num_nz_lins = 0;
    for(var_t i = 0; i<linerals.size(); ++i) {
      if(linerals[i].is_zero()) remove_zero_lineral(i);
      else ++num_nz_lins;
    }

    //init t_pos_to_idxs
    t_pos_to_idxs.clear();
    //init filtration list
    for(var_t i = 0; i<linerals.size(); ++i) {
      filtration_add(i);
    }
    
    //recalculate ws[0] and ws[1] if necessary! - can be skipped in theory, as ws[0] and ws[1] are not used + updated correctly either during 'resolve', but definitely during 'finalize' (!)
    //                                          - in practice, however, it is necessary when running in debug mode due to sanity checks on ptr_cache and ws !
  #ifndef NDEBUG
    if(ptr_cache[0]!=WLIN0.get_idxs_()[ws[0]]) ws[0] = std::distance(WLIN0.get_idxs_().begin(), std::lower_bound(WLIN0.get_idxs_().begin(), WLIN0.get_idxs_().end(), ptr_cache[0]));
    if(size()>1 && ptr_cache[1]!=WLIN1.get_idxs_()[ws[1]]) ws[1] = std::distance(WLIN1.get_idxs_().begin(), std::lower_bound(WLIN1.get_idxs_().begin(), WLIN1.get_idxs_().end(), ptr_cache[1]));
  #endif

    assert( assert_data_struct() );
  }

  /**
   * @brief adds linerals[i] to t_pos_to_idxs; ensuring that first el is smallest
   * 
   * @param i idx of lineral to add
   * @return true iff no other lineral with same lineral_trail_pos has been found in t_pos_to_idxs
   */
  inline bool filtration_add(const var_t& i) {
    auto lb = t_pos_to_idxs.lower_bound(lineral_t_pos[i]);
    if(lb!=t_pos_to_idxs.end() && lb->first == lineral_t_pos[i]) {
      if( linerals[lb->second.front()].size() > linerals[i].size() ) lb->second.push_front(i);
      else lb->second.push_back(i);
      return false;
    } else {
      t_pos_to_idxs.emplace_hint(lb, lineral_t_pos[i], list<var_t>({i}));
      return true;
    }
  }

public:
  cls_watch_resolver() = default;
  cls_watch_resolver(const cls_watch_resolver& o) = default;
  cls_watch_resolver(cls_watch_resolver&& o) = default;
  cls_watch_resolver(const cls_watch &rs_cls) : cls_watch(rs_cls) { init(); };
  cls_watch_resolver(cls_watch &&rs_cls) : cls_watch(std::move(rs_cls)) { init(); };

  /**
   * @brief reduces each linerals s.t. for each t_pos there are at most max_size many linerals
   */
  inline void reduction(const var_t max_size, const vec<var_t> &alpha_dl, const vec<var_t> &alpha_trail_pos, const vec<dl_c_t> &dl_count) {
    if(t_pos_to_idxs.empty()) return;
    const bool ret = (t_pos_to_idxs.rbegin()->second.size()>1) || (t_pos_to_idxs.size()>1 && std::next(t_pos_to_idxs.rbegin())->second.size()>1);
    for(auto it=t_pos_to_idxs.rbegin(); it!=t_pos_to_idxs.rend(); ++it) {
      auto& [k,l] = *it;
      if(l.size()<=max_size && (l.size()==0 || linerals[l.front()].size()>=2)) continue;
      const var_t i0 = l.front(); //note first el is shortest lineral with that t_pos - by construction
      l.pop_front();
      //add first el in l to all others, re-evaluate lineral_t_pos, adapt lineral_dl_count0, AND add them back to t_pos_to_idxs
      for(const var_t& i : l) {
        assert(i!=i0);
        linerals[i] += linerals[i0];
        if(linerals[i].is_zero()) {
          --num_nz_lins;
          continue;
        }
        const auto& [v, dl, t_pos, _idx] = linerals[i].get_watch_tuple(alpha_dl, alpha_trail_pos);
        assert(v==(var_t)-1 || t_pos < t_pos_to_idxs.rbegin()->first);
        lineral_t_pos[i] = t_pos;
        lineral_dl_count0[i] = {dl, dl_count[dl]};
        filtration_add(i);
        assert(t_pos < k);
      }
      l.clear();
      l.emplace_front( i0 );
      assert(t_pos_to_idxs[k].size()<=max_size);
    }
    assert( std::all_of(t_pos_to_idxs.begin(), t_pos_to_idxs.end(), [max_size](const auto& k_l){ return k_l.second.size()<=max_size; }) );
    if(ret) fix_watched_idx(alpha_dl, alpha_trail_pos, dl_count);
  }

  /**
   * @brief call once when no more resolvents are computed.
   * @note recompute shared_parts to 'repair' cls_watch data_struct
   */
  inline cls_watch finalize(const vec<var_t> &alpha_dl, const vec<var_t> &alpha_trail_pos, const vec<dl_c_t> &dl_count, const var_t max_size_=(var_t)-1) {
    //@heuristic choose good value!
    const var_t max_size = max_size_==(var_t)-1 ? std::min(4, (int) (num_nz_lins / std::max(1, (int) t_pos_to_idxs.size())) + 2 ) : max_size_;
    reduction(max_size, alpha_dl, alpha_trail_pos, dl_count);

    assert( is_zero() || num_nz_lins <= max_size*t_pos_to_idxs.size() );
    assert( size()<1 || linerals[idx[0]][ptr_cache[0]] );
    assert( size()<2 || linerals[idx[1]][ptr_cache[1]] );

    //@heuristic: decide whether to remove duplicates up to a given size!
    ////rm zero linerals AND duplicates of 'small' size -- this step breaks t_pos_to_idxs !
    //std::unordered_set<lineral> hashes;
    ////iterate over t_pos_to_idxs and set all linerals to be removed to zero!
    //for(auto& [_, l] : t_pos_to_idxs) {
    //  for(var_t i : l) {
    //    if(linerals[i].size()>3) continue;
    //    if(hashes.contains(linerals[i])) {
    //      linerals[i].clear();
    //      --num_nz_lins;
    //    } else {
    //      hashes.insert(linerals[i]);
    //    }
    //  }
    //  hashes.clear();
    //}
    //iterate through other lins and remove duplicates and zero-linerals
    for(var_t j=0; j<linerals.size(); ++j) {
      const var_t k = linerals.size() - j - 1;
      if(linerals[k].is_zero()) { cls_watch::remove_zero_lineral(k); --j; }
    }
    assert(num_nz_lins == linerals.size());
    assert( size()<1 || linerals[idx[0]][ptr_cache[0]] );
    assert( size()<2 || linerals[idx[1]][ptr_cache[1]] );
    assert( size()<2 || ptr_cache[0]!=ptr_cache[1] );

    //recompute shared_part
    assert(shared_part.is_zero());
    if(linerals.size()<=1) return *this;
    //from now on linerals.size()>1
    
    shared_part = WLIN0.shared_part(WLIN1);
    WLIN0 += shared_part;
    WLIN1 += shared_part;
    if(!WLIN1[ptr_cache[1]]) WLIN1.swap(shared_part);
    
    ws[0] = std::distance(WLIN0.get_idxs_().begin(), std::lower_bound(WLIN0.get_idxs_().begin(), WLIN0.get_idxs_().end(), ptr_cache[0]));
    ws[1] = std::distance(WLIN1.get_idxs_().begin(), std::lower_bound(WLIN1.get_idxs_().begin(), WLIN1.get_idxs_().end(), ptr_cache[1]));

    assert( cls_watch::assert_data_struct() );

    return *this;
  }


  /**
   * @brief rm linerals that are implied by others; roughly follows ideas of 'vivification'
   * 
   * @return true iff clause could be shortened
   */
  bool minimize(const solver &s, const vec<bool3> &alpha, const vec<var_t> &alpha_dl, const vec<var_t> &alpha_trail_pos, const vec<lin_w_it>& alpha_lin, const vec<dl_c_t> &dl_count) noexcept;
  
  /**
   * @brief differs from resolve in that we do not update the watched linerals (idx[0] and idx[1]), i.e. t_pos_to_idxs.rbegin() may contain multiple elements AND does not reduce those at all -- this might miss simplifications every now and then BUT ensures that we can change the order when computing reason clauses
   * @note subsequent calls to assert_data_struct() will fail!
   * @note use fix_data_struct() to ensure correctness after all resolvents have been computed!
   */
  void resolve_unsafe(const cls_watch &rs_cls, [[maybe_unused]] const vec<bool3> &alpha, [[maybe_unused]] const vec<var_t> &alpha_dl, [[maybe_unused]] const vec<var_t> &alpha_trail_pos, [[maybe_unused]] const vec<dl_c_t> &dl_count) {
      //resolve(rs_cls, alpha, alpha_dl, alpha_trail_pos, dl_count);
      //return;

      if(size()==0 || is_zero()) {
        this->operator=(std::move(rs_cls));
        //prepare unsafe resolving -- assign WLIN0 to t_pos -1
        //rm unit from t_pos_to_idxs
        assert(idx[0]==t_pos_to_idxs.rbegin()->second.front());
        assert(t_pos_to_idxs.rbegin()->second.size()==1);
        t_pos_to_idxs.erase( std::prev( t_pos_to_idxs.end() ) );
        lineral_t_pos[idx[0]] = (var_t) -1;
        filtration_add(idx[0]);
        return;
      }

      // fix unit part ('resolving' part)
      WLIN0 += rs_cls.get_unit();

      //add remaining linerals
      //copy the remaining linerals
      linerals.reserve(linerals.size()+rs_cls.linerals.size());
      lineral_dl_count0.reserve(linerals.size()+rs_cls.linerals.size());
      lineral_t_pos.reserve(linerals.size()+rs_cls.linerals.size());
      for(var_t i=0; i<rs_cls.size(); ++i) {
        assert(!rs_cls.linerals[i].is_constant());
        if(i==rs_cls.idx[0]) continue;
        ++num_nz_lins;
        linerals.emplace_back( rs_cls.linerals[i] );
        //if 2nd watched lineral, fix with shared part
        if(i==rs_cls.idx[1]) linerals.back() += rs_cls.shared_part;
        lineral_dl_count0.emplace_back( rs_cls.lineral_dl_count0[i] );
        lineral_t_pos.emplace_back(rs_cls.lineral_t_pos[i]);
        filtration_add(linerals.size()-1);
      }
  };

  /**
   * @brief to be used after 'resolve_unsafe'
   */
  void fix_data_struct([[maybe_unused]] const vec<bool3> &alpha, const vec<var_t> &alpha_dl, const vec<var_t> &alpha_trail_pos, const vec<dl_c_t> &dl_count) {
      //rm unit from t_pos_to_idxs
      if(!t_pos_to_idxs.empty()) {
        assert(idx[0]==t_pos_to_idxs.rbegin()->second.front());
        assert(t_pos_to_idxs.rbegin()->first == (var_t) -1);
        //if(t_pos_to_idxs.rbegin()->second.size()>1) t_pos_to_idxs.rbegin()->second.erase( t_pos_to_idxs.rbegin()->second.begin() );
        t_pos_to_idxs.erase( std::prev( t_pos_to_idxs.end() ) );
      }
      //and add it back...
      if(!WLIN0.is_zero()) {
        //if unit-part is non-zero
        const auto& [v, dl, t_pos, _idx] = WLIN0.get_watch_tuple(alpha_dl, alpha_trail_pos);
        lineral_t_pos[idx[0]] = t_pos;
        //add new 'unit' to t_pos_to_idxs
        filtration_add(idx[0]);
      } else {
        //if unit-part is zero -- do not add it back to lineral_t_pos, i.e., 'remove' it
        lineral_dl_count0[idx[0]] = {0,1};
        //remove_zero_lineral(idx[0]);
        --num_nz_lins;
        idx[0] = (idx[1]==(var_t)-1) ? 0 : idx[1];
        ptr_cache[0] = ptr_cache[1];
        idx[1] = -1;
        ptr_cache[1] = -1;
      }

      //finally 'fix' watched idxs
      fix_watched_idx(alpha_dl, alpha_trail_pos, dl_count);
  }
  
  void resolve(const cls_watch &rs_cls, [[maybe_unused]] const vec<bool3> &alpha, const vec<var_t> &alpha_dl, const vec<var_t> &alpha_trail_pos, const vec<dl_c_t> &dl_count) {
      assert( assert_data_struct() );
      assert( assert_data_struct(alpha, alpha_trail_pos, dl_count) );

      if(size()==0) {
        this->operator=(std::move(rs_cls));
        return;
      }
      assert(size()>0);
      assert(size()<2 || idx[0]!=idx[1]);

      // fix unit part ('resolving' part)
      WLIN0 += rs_cls.get_unit();
      assert(!WLIN0.is_one());
      //rm unit from t_pos_to_idxs
      if(!t_pos_to_idxs.empty()) t_pos_to_idxs.erase( std::prev(t_pos_to_idxs.end()) );

      if(!WLIN0.is_zero()) {
        //if unit-part is non-zero
        const auto& [v, dl, t_pos, _idx] = WLIN0.get_watch_tuple(alpha_dl, alpha_trail_pos);
        lineral_t_pos[idx[0]] = t_pos;
        //add new 'unit' to t_pos_to_idxs
        filtration_add(idx[0]);
      } else {
        //if unit-part is zero -- do not add it back to lineral_t_pos, i.e., 'remove' it
        lineral_dl_count0[idx[0]] = {0,1};
        //remove_zero_lineral(idx[0]);
        --num_nz_lins;
        idx[0] = (idx[1]==(var_t)-1) ? 0 : idx[1];
        ptr_cache[0] = ptr_cache[1];
        idx[1] = -1;
        ptr_cache[1] = -1;
      }

      //add remaining linerals
      //copy the remaining linerals
      linerals.reserve(linerals.size()+rs_cls.linerals.size());
      lineral_dl_count0.reserve(linerals.size()+rs_cls.linerals.size());
      lineral_t_pos.reserve(linerals.size()+rs_cls.linerals.size());
      for(var_t i=0; i<rs_cls.size(); ++i) {
        assert(!rs_cls.linerals[i].is_constant());
        if(i==rs_cls.idx[0]) continue;
        ++num_nz_lins;
        linerals.emplace_back( rs_cls.linerals[i] );
        //if 2nd watched lineral, fix with shared part
        if(i==rs_cls.idx[1]) linerals.back() += rs_cls.shared_part;
        lineral_dl_count0.emplace_back( rs_cls.lineral_dl_count0[i] );
        lineral_t_pos.emplace_back(rs_cls.lineral_t_pos[i]);
        filtration_add(linerals.size()-1);
      }

      fix_watched_idx(alpha_dl, alpha_trail_pos, dl_count);
      
      if(size()>256) {
        //@heuristic choose good value!
        const var_t max_size = std::min(4, (int) (num_nz_lins / t_pos_to_idxs.size()) + 2 );
        reduction(max_size, alpha_dl, alpha_trail_pos, dl_count);
      }

      assert( assert_data_struct(alpha, alpha_trail_pos, dl_count) );
      assert( assert_data_struct() );
      assert( is_unit(dl_count) );

      assert( !to_cls().is_zero() );
  };
  
  inline void resolve(cls_watch&& rs_cls, [[maybe_unused]] const vec<bool3> &alpha, const vec<var_t> &alpha_dl, const vec<var_t> &alpha_trail_pos, const vec<dl_c_t> &dl_count) noexcept {
      assert( assert_data_struct() );
      assert( assert_data_struct(alpha, alpha_trail_pos, dl_count) );

      if(size()==0) {
        this->operator=(std::move(rs_cls));
        return;
      }
      assert(size()>0);
      assert(size()<2 || idx[0]!=idx[1]);

      //'normalize' rs_cls
      if(rs_cls.size()>1) {
        rs_cls.linerals[rs_cls.idx[0]] += rs_cls.shared_part;
        rs_cls.linerals[rs_cls.idx[1]] += rs_cls.shared_part;
        rs_cls.shared_part.clear();
      }

      // fix unit part ('resolving' part)
      WLIN0 += rs_cls.linerals[rs_cls.idx[0]]; WLIN0.add_one();
      //rm unit from t_pos_to_idxs
      if(!t_pos_to_idxs.empty()) t_pos_to_idxs.erase( std::prev(t_pos_to_idxs.end()) );

      if(!WLIN0.is_zero()) {
        //if unit-part is non-zero
        const auto& [v, dl, t_pos, _idx] = WLIN0.get_watch_tuple(alpha_dl, alpha_trail_pos);
        lineral_t_pos[idx[0]] = t_pos;
        //add new 'unit' to t_pos_to_idxs
        filtration_add(idx[0]);
      } else {
        //if unit-part is zero -- do not add it back to lineral_t_pos, i.e., 'remove' it
        lineral_dl_count0[idx[0]] = {0,1};
        //remove_zero_lineral(idx[0]);
        --num_nz_lins;
        idx[0] = (idx[1]<(var_t) -1) ? idx[1] : 0;
        ptr_cache[0] = ptr_cache[1];
        idx[1] = -1;
        ptr_cache[1] = -1;
      }

      //add remaining linerals
      //copy the remaining linerals
      linerals.reserve(linerals.size()+rs_cls.linerals.size());
      lineral_dl_count0.reserve(linerals.size()+rs_cls.linerals.size());
      lineral_t_pos.reserve(linerals.size()+rs_cls.linerals.size());
      for(var_t i=0; i<rs_cls.size(); ++i) {
        assert(!rs_cls.linerals[i].is_zero());
        if(i==rs_cls.idx[0]) continue;
        ++num_nz_lins;
        linerals.emplace_back( std::move(rs_cls.linerals[i]) );
        lineral_dl_count0.emplace_back( std::move(rs_cls.lineral_dl_count0[i]) );
        lineral_t_pos.emplace_back( std::move(rs_cls.lineral_t_pos[i]) );
        filtration_add(linerals.size()-1);
      }

      fix_watched_idx(alpha_dl, alpha_trail_pos, dl_count);
  
      if(size()>256) {
        //@heuristic choose good value!
        const var_t max_size = std::min(4, (int) (num_nz_lins / t_pos_to_idxs.size()) + 2 );
        reduction(max_size, alpha_dl, alpha_trail_pos, dl_count);
      }

      assert( assert_data_struct(alpha, alpha_trail_pos, dl_count) );
      assert( assert_data_struct() );
      assert( is_unit(dl_count) );
  };

  /**
   * @brief essentially an implementation of 'WatchableReFiltr'
   */
  inline void fix_watched_idx(const vec<var_t> &alpha_dl, const vec<var_t> &alpha_trail_pos, const vec<dl_c_t> &dl_count) noexcept {
    //find highest two t_pos linerals to watch; and reduce those as long as they are not unique!
    if(t_pos_to_idxs.size()>0) {
      const auto it = t_pos_to_idxs.rbegin();
      const var_t i0 = it->second.front();
      //set idx, ws, and ptr_cache
      const auto& [v, dl, t_pos, _idx] = linerals[i0].get_watch_tuple(alpha_dl, alpha_trail_pos);
      idx[0] = i0; 
      ws[0] = _idx;
      ptr_cache[0] = v;
      lineral_t_pos[i0] = t_pos;
      //find unique lineral of highest t_pos to watch
      if(it->second.size()>1) {
        auto& l = it->second;
        l.pop_front();
        //add first el in l to all others, re-evaluate lineral_t_pos, adapt lineral_dl_count0, AND add them back to t_pos_to_idxs
        for(const var_t i : l) {
          assert(i!=i0);
          linerals[i] += WLIN0;
          if(linerals[i].is_zero()) {
            --num_nz_lins;
            continue;
          }
          const auto& [v, dl, t_pos, _idx] = linerals[i].get_watch_tuple(alpha_dl, alpha_trail_pos);
          assert(v==(var_t)-1 || t_pos < t_pos_to_idxs.rbegin()->first); //this assertion might fail on large examples!
          lineral_t_pos[i] = t_pos;
          lineral_dl_count0[i] = {dl, dl_count[dl]};
          filtration_add(i);
        }
        l.clear();
        l.emplace_front( i0 );
      }
      assert(it->second.size()==1);
    }

    if(t_pos_to_idxs.size()>1) {
      const auto it = std::next(t_pos_to_idxs.rbegin());
      //set idx, ws, and ptr_cache
      const var_t i1 = it->second.front();
      const auto& [v, dl, t_pos, _idx] = linerals[i1].get_watch_tuple(alpha_dl, alpha_trail_pos);
      idx[1] = i1;
      ws[1] = _idx;
      ptr_cache[1] = v;
      if(dl==(var_t)-1) lineral_dl_count0[i1] = {0, 0};
      else              lineral_dl_count0[i1] = {dl, dl_count[dl]};
      assert(lineral_t_pos[idx[1]] == t_pos);
      //@todo re-add as heuristic reduction?!
      //if(it->second.size() > 1 ) {
      //  //find unique lineral of 2nd-highest t_pos to watch
      //  auto& l = it->second; 
      //  l.pop_front();
      //  //add first el in l to all others, re-evaluate lineral_t_pos, adapt lineral_dl_count0, AND add them back to t_pos_to_idxs
      //  for(const var_t i : l) {
      //    assert(i!=i1);
      //    linerals[i] += WLIN1;
      //    if(linerals[i].is_zero()) {
      //      --num_nz_lins;
      //      continue;
      //    }
      //    const auto& [v, dl, t_pos, _idx] = linerals[i].get_watch_tuple(alpha_dl, alpha_trail_pos);
      //    assert(v==(var_t)-1 || t_pos < it->first);
      //    lineral_t_pos[i] = t_pos;
      //    lineral_dl_count0[i] = {dl, dl_count[dl]};
      //    filtration_add(i);
      //  }
      //  l.clear();
      //  l.emplace_front( i1 );
      //}
      //assert(it->second.size()==1);
    }
    assert( size()<1 || (linerals[idx[0]][ptr_cache[0]] && linerals[idx[0]].get_idxs_()[ws[0]]==ptr_cache[0] ));
    assert( size()<2 || (linerals[idx[1]][ptr_cache[1]] && linerals[idx[1]].get_idxs_()[ws[1]]==ptr_cache[1] ));
  };


  /**
   * @brief returns number of stored linerals
   * @note beware: if clause is zero we have size()==1 and size()==0 means claus is one (!)
   * 
   * @return var_t number of linerals
   */
  inline var_t size() const override { return num_nz_lins; };

  bool assert_data_struct() const {
    if(size()==1 && linerals[0].is_one()) return true;
    assert( size()<1 || (linerals[idx[0]][ptr_cache[0]] && linerals[idx[0]].get_idxs_()[ws[0]]==ptr_cache[0] ));
    assert( size()<2 || (linerals[idx[1]][ptr_cache[1]] && linerals[idx[1]].get_idxs_()[ws[1]]==ptr_cache[1] ));

    //check num_nz_lins
    assert( num_nz_lins == (var_t) std::count_if(linerals.begin(), linerals.end(), [](const auto& l){ return !l.is_zero(); }) );

    //check t_pos_to_idxs
    //every value must appear at most once!
    std::set<var_t> tmp;
    for(const auto& [k,l] : t_pos_to_idxs) {
      for(const auto& i : l) {
        assert(!tmp.contains(i));
        tmp.insert(i);
      }
    }
    
    //every idx of a non-zero lineral must be contained in t_pos_to_idxs
    tmp.clear();
    for(var_t j=0; j<linerals.size(); ++j) {
      if(!linerals[j].is_zero()) tmp.insert(j);
    }
    for(const auto& [k,l] : t_pos_to_idxs) {
      for(const auto& i : l) {
        tmp.erase( i );
      }
    }
    assert(tmp.empty());

    //there are as many different keys in t_pos_to_idxs as there are different values in lineral_t_pos
    tmp.clear();
    for(var_t j=0; j<linerals.size(); ++j) {
      if(!linerals[j].is_zero()) tmp.insert( lineral_t_pos[j] );
    }
    assert( t_pos_to_idxs.size() == tmp.size() );
    
    return true;
  }

#ifdef NDEBUG
  bool assert_data_struct([[maybe_unused]] const vec<bool3> &alpha, [[maybe_unused]] const vec<var_t> &alpha_trail_pos, [[maybe_unused]] const vec<dl_c_t> &dl_count) const { return true; }
#else
  bool assert_data_struct(const vec<bool3> &alpha, const vec<var_t> &alpha_trail_pos, const vec<dl_c_t> &dl_count) const {
    assert(is_unit(dl_count) || is_sat(dl_count) || alpha[ptr_ws(0)] == bool3::None);
    if (!is_unit(dl_count) && alpha[ptr_ws(0)] != bool3::None) {
      assert(is_sat(dl_count) || eval0(alpha) || (!eval0(alpha) && !eval1(alpha)));
    }
    if(is_sat(dl_count)) {
      assert(dl_count[SAT_dl_count.first] == SAT_dl_count.second);
      assert_slow(to_cls().reduced(alpha).is_zero());
    }
    if( size()>0 && dl_count[lineral_dl_count0[idx[0]].first] == lineral_dl_count0[idx[0]].second ) assert( !eval0(alpha) );
    if( size()>1 && dl_count[lineral_dl_count0[idx[1]].first] == lineral_dl_count0[idx[1]].second ) assert( !eval1(alpha) || is_unit(dl_count) );
    for(var_t i = 0; i<linerals.size(); ++i) {
      if(i==idx[0] || i==idx[1]) continue;
      if( dl_count[lineral_dl_count0[i].first] == lineral_dl_count0[i].second ) assert( linerals[i].eval(alpha) );
    }

    //check lineral_t_pos
    for(var_t i = 0; i<linerals.size(); ++i) {
      if(i==idx[0] || i==idx[1]) continue;
      if(dl_count[lineral_dl_count0[i].first] == lineral_dl_count0[i].second && !linerals[i].is_zero()) assert( linerals[i].get_watch_var(alpha_trail_pos).first == lineral_t_pos[i] );
    }
    if(idx[0]<linerals.size() && dl_count[lineral_dl_count0[idx[0]].first] == lineral_dl_count0[idx[0]].second && !linerals[idx[0]].is_zero())
      assert( (linerals[idx[0]]+shared_part).get_watch_var(alpha_trail_pos).first  == lineral_t_pos[idx[0]] );
    if(idx[1]<linerals.size() && dl_count[lineral_dl_count0[idx[1]].first] == lineral_dl_count0[idx[1]].second && !linerals[idx[1]].is_zero())
      assert( (linerals[idx[1]]+shared_part).get_watch_var(alpha_trail_pos).first  == lineral_t_pos[idx[1]] );

    assert( size()<2 || alpha_trail_pos[ptr_cache[0]] > alpha_trail_pos[ptr_cache[1]] );

    return assert_data_struct();
  };
#endif

  inline cls_watch& operator=(const cls_watch &o) {
    cls_watch::operator=(o);
    init();
    return *this;
  };

  inline cls_watch& operator=(cls_watch &&o) {
    cls_watch::operator=(std::move(o));
    init();
    return *this;
  };
};