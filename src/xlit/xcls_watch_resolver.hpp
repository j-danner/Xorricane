#pragma once

#include "xcls_watch.hpp"

#include <queue>

//forward declaration
class solver;


class xcls_watch_resolver : public xcls_watch {
private:
  /**
   * @brief maps t_pos to idxs of xlits, i.e., xlits[ t_pos_to_idxs[t_pos] ] = t_pos
   */
  //@todo replace with 'https://www.codeproject.com/script/Articles/ViewDownloads.aspx?aid=27799' ?
  std::map<var_t, list<var_t> > t_pos_to_idxs;

  /**
   * @brief number of non-zero linerals in xlits
   */
  var_t num_nz_lins = 1;

  inline void init() {
    //distribute shared_part
    if(idx[0]<xlits.size()) WLIN0 += shared_part;
    if(idx[1]<xlits.size()) WLIN1 += shared_part;
    shared_part.clear();

    //init num_nz_lins
    num_nz_lins = 0;
    for(var_t i = 0; i<xlits.size(); ++i) {
      if(xlits[i].is_zero()) remove_zero_lineral(i);
      else ++num_nz_lins;
    }

    //init t_pos_to_idxs
    t_pos_to_idxs.clear();
    //init filtration list
    for(var_t i = 0; i<xlits.size(); ++i) {
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
   * @brief adds xlits[i] to t_pos_to_idxs; ensuring that first el is smallest
   * 
   * @param i idx of lineral to add
   * @return true iff no other lineral with same xlit_trail_pos has been found in t_pos_to_idxs
   */
  inline bool filtration_add(const var_t& i) {
    auto lb = t_pos_to_idxs.lower_bound(xlit_t_pos[i]);
    if(lb!=t_pos_to_idxs.end() && lb->first == xlit_t_pos[i]) {
      if( xlits[lb->second.front()].size() > xlits[i].size() ) lb->second.push_front(i);
      else lb->second.push_back(i);
      return false;
    } else {
      t_pos_to_idxs.emplace_hint(lb, xlit_t_pos[i], list<var_t>({i}));
      return true;
    }
  }

public:
  xcls_watch_resolver() = default;
  xcls_watch_resolver(const xcls_watch_resolver& o) = default;
  xcls_watch_resolver(xcls_watch_resolver&& o) = default;
  xcls_watch_resolver(const xcls_watch &rs_cls) : xcls_watch(rs_cls) { init(); };
  xcls_watch_resolver(xcls_watch &&rs_cls) : xcls_watch(std::move(rs_cls)) { init(); };

  /**
   * @brief reduces each xlits s.t. for each t_pos there are at most max_size many linerals
   */
  inline void reduction(const var_t max_size, const vec<var_t> &alpha_dl, const vec<var_t> &alpha_trail_pos, const vec<dl_c_t> &dl_count) {
    if(t_pos_to_idxs.empty()) return;
    const bool ret = (t_pos_to_idxs.rbegin()->second.size()>1) || (t_pos_to_idxs.size()>1 && std::next(t_pos_to_idxs.rbegin())->second.size()>1);
    for(auto it=t_pos_to_idxs.rbegin(); it!=t_pos_to_idxs.rend(); ++it) {
      auto& [k,l] = *it;
      if(l.size()<=max_size) continue;
      const var_t i0 = l.front(); //note first el is shortest xlit with that t_pos - by construction
      l.pop_front();
      //add first el in l to all others, re-evaluate xlit_t_pos, adapt xlit_dl_count0, AND add them back to t_pos_to_idxs
      for(const var_t i : l) {
        assert(i!=i0);
        xlits[i] += xlits[i0];
        if(xlits[i].is_zero()) {
          --num_nz_lins;
          continue;
        }
        const auto& [v, dl, t_pos, _idx] = xlits[i].get_watch_tuple(alpha_dl, alpha_trail_pos);
        assert(v==(var_t)-1 || t_pos < t_pos_to_idxs.rbegin()->first);
        xlit_t_pos[i] = t_pos;
        xlit_dl_count0[i] = {dl, dl_count[dl]};
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
   * @note recompute shared_parts to 'repair' xcls_watch data_struct
   */
  inline xcls_watch finalize(const vec<var_t> &alpha_dl, const vec<var_t> &alpha_trail_pos, const vec<dl_c_t> &dl_count, const var_t max_size_=(var_t)-1) {
    //@heuristic choose good value!
    const var_t max_size = max_size_==(var_t)-1 ? std::min(4, (int) (num_nz_lins / std::max(1, (int) t_pos_to_idxs.size())) + 2 ) : max_size_;
    reduction(max_size, alpha_dl, alpha_trail_pos, dl_count);

    assert( is_zero() || num_nz_lins <= max_size*t_pos_to_idxs.size() );
    assert( size()<1 || xlits[idx[0]][ptr_cache[0]] );
    assert( size()<2 || xlits[idx[1]][ptr_cache[1]] );

    //rm zero linerals -- this step breaks t_pos_to_idxs!
    for(var_t j=0; j<xlits.size(); ++j) {
      const var_t k = xlits.size() - j - 1;
      if(xlits[k].is_zero()) { xcls_watch::remove_zero_lineral(k); --j; }
    }
    assert(num_nz_lins == xlits.size());
    assert( size()<1 || xlits[idx[0]][ptr_cache[0]] );
    assert( size()<2 || xlits[idx[1]][ptr_cache[1]] );
    assert( size()<2 || ptr_cache[0]!=ptr_cache[1] );

    //recompute shared_part
    assert(shared_part.is_zero());
    if(xlits.size()<=1) return *this;
    //from now on xlits.size()>1
    
    shared_part = WLIN0.shared_part(WLIN1);
    WLIN0 += shared_part;
    WLIN1 += shared_part;
    if(!WLIN1[ptr_cache[1]]) WLIN1.swap(shared_part);
    
    ws[0] = std::distance(WLIN0.get_idxs_().begin(), std::lower_bound(WLIN0.get_idxs_().begin(), WLIN0.get_idxs_().end(), ptr_cache[0]));
    ws[1] = std::distance(WLIN1.get_idxs_().begin(), std::lower_bound(WLIN1.get_idxs_().begin(), WLIN1.get_idxs_().end(), ptr_cache[1]));

    assert( xcls_watch::assert_data_struct() );

    return *this;
  }


  /**
   * @brief rm linerals that are implied by others; roughly follows ideas of 'vivification'
   * 
   * @return true iff clause could be shortened
   */
  bool minimize(solver& s, const vec<bool3> &alpha, const vec<var_t> &alpha_dl, const vec<var_t> &alpha_trail_pos, const vec<dl_c_t> &dl_count) noexcept;
  
  xcls_upd_ret resolve(const xcls_watch &rs_cls, [[maybe_unused]] const vec<bool3> &alpha, const vec<var_t> &alpha_dl, const vec<var_t> &alpha_trail_pos, const vec<dl_c_t> &dl_count) {
      assert( assert_data_struct() );
      assert( assert_data_struct(alpha, alpha_trail_pos, dl_count) );

      if(size()==0) {
         xlits.emplace_back( xlit(0, true) );
         xlit_dl_count0.emplace_back( 0, dl_count[0] );
         xlit_t_pos.emplace_back((var_t) -1);
         ws[0] = 0;
         idx[0] = 0;
         t_pos_to_idxs[0] = {0};
      }
      assert(size()>0);
      assert(size()<2 || idx[0]!=idx[1]);

      // fix unit part ('resolving' part)
      WLIN0 += rs_cls.get_unit();
      //rm unit from t_pos_to_idxs
      t_pos_to_idxs.erase( std::prev(t_pos_to_idxs.end()) );

      if(!WLIN0.is_zero()) {
        //if unit-part is non-zero
        const auto& [v, dl, t_pos, _idx] = WLIN0.get_watch_tuple(alpha_dl, alpha_trail_pos);
        xlit_t_pos[idx[0]] = t_pos;
        //add new 'unit' to t_pos_to_idxs
        filtration_add(idx[0]);
      } else {
        //if unit-part is zero -- do not add it back to xlit_t_pos, i.e., 'remove' it
        xlit_dl_count0[idx[0]] = {0,1};
        //remove_zero_lineral(idx[0]);
        --num_nz_lins;
        idx[0] = (idx[1]==(var_t)-1) ? 0 : idx[1];
        ptr_cache[0] = ptr_cache[1];
        idx[1] = -1;
        ptr_cache[1] = -1;
      }

      //add remaining xlits
      //copy the remaining linerals
      xlits.reserve(xlits.size()+rs_cls.xlits.size());
      xlit_dl_count0.reserve(xlits.size()+rs_cls.xlits.size());
      xlit_t_pos.reserve(xlits.size()+rs_cls.xlits.size());
      for(var_t i=0; i<rs_cls.size(); ++i) {
        assert(!rs_cls.xlits[i].is_zero());
        if(i==rs_cls.idx[0]) continue;
        ++num_nz_lins;
        xlits.emplace_back( rs_cls.xlits[i] );
        //if 2nd watched lineral, fix with shared part
        if(i==rs_cls.idx[1]) xlits.back() += rs_cls.shared_part;
        xlit_dl_count0.emplace_back( rs_cls.xlit_dl_count0[i] );
        xlit_t_pos.emplace_back(rs_cls.xlit_t_pos[i]);
        filtration_add(xlits.size()-1);
      }

      fix_watched_idx(alpha_dl, alpha_trail_pos, dl_count);

      assert( assert_data_struct(alpha, alpha_trail_pos, dl_count) );
      assert( assert_data_struct() );
      assert( is_unit(dl_count) );

      assert( !to_xcls().is_zero() );

      return xcls_upd_ret::UNIT;
  };
  
  inline xcls_upd_ret resolve(xcls_watch&& rs_cls, [[maybe_unused]] const vec<bool3> &alpha, const vec<var_t> &alpha_dl, const vec<var_t> &alpha_trail_pos, const vec<dl_c_t> &dl_count) noexcept {
      assert( assert_data_struct() );
      assert( assert_data_struct(alpha, alpha_trail_pos, dl_count) );

      if(size()==0) {
         xlits.emplace_back( xlit(0, true) );
         xlit_dl_count0.emplace_back( 0, dl_count[0] );
         xlit_t_pos.emplace_back((var_t) -1);
         ws[0] = 0;
         idx[0] = 0;
         t_pos_to_idxs[0] = {0};
      }
      assert(size()>0);
      assert(size()<2 || idx[0]!=idx[1]);

      //'normalize' rs_cls
      if(rs_cls.size()>1) {
        rs_cls.xlits[rs_cls.idx[0]] += rs_cls.shared_part;
        rs_cls.xlits[rs_cls.idx[1]] += rs_cls.shared_part;
        rs_cls.shared_part.clear();
      }

      // fix unit part ('resolving' part)
      WLIN0 += rs_cls.xlits[rs_cls.idx[0]]; WLIN0.add_one();
      //rm unit from t_pos_to_idxs
      t_pos_to_idxs.erase( std::prev(t_pos_to_idxs.end()) );

      if(!WLIN0.is_zero()) {
        //if unit-part is non-zero
        const auto& [v, dl, t_pos, _idx] = WLIN0.get_watch_tuple(alpha_dl, alpha_trail_pos);
        xlit_t_pos[idx[0]] = t_pos;
        //add new 'unit' to t_pos_to_idxs
        filtration_add(idx[0]);
      } else {
        //if unit-part is zero -- do not add it back to xlit_t_pos, i.e., 'remove' it
        xlit_dl_count0[idx[0]] = {0,1};
        //remove_zero_lineral(idx[0]);
        --num_nz_lins;
        idx[0] = (idx[1]<(var_t) -1) ? idx[1] : 0;
        ptr_cache[0] = ptr_cache[1];
        idx[1] = -1;
        ptr_cache[1] = -1;
      }

      //add remaining xlits
      //copy the remaining linerals
      xlits.reserve(xlits.size()+rs_cls.xlits.size());
      xlit_dl_count0.reserve(xlits.size()+rs_cls.xlits.size());
      xlit_t_pos.reserve(xlits.size()+rs_cls.xlits.size());
      for(var_t i=0; i<rs_cls.size(); ++i) {
        assert(!rs_cls.xlits[i].is_zero());
        if(i==rs_cls.idx[0]) continue;
        ++num_nz_lins;
        xlits.emplace_back( std::move(rs_cls.xlits[i]) );
        xlit_dl_count0.emplace_back( std::move(rs_cls.xlit_dl_count0[i]) );
        xlit_t_pos.emplace_back( std::move(rs_cls.xlit_t_pos[i]) );
        filtration_add(xlits.size()-1);
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

      return xcls_upd_ret::UNIT;
  };

  inline void fix_watched_idx(const vec<var_t> &alpha_dl, const vec<var_t> &alpha_trail_pos, const vec<dl_c_t> &dl_count) noexcept {
    //find highest two t_pos linerals to watch; and reduce those as long as they are not unique!
    if(t_pos_to_idxs.size()>0) {
      const auto it = t_pos_to_idxs.rbegin();
      const var_t i0 = it->second.front();
      //set idx, ws, and ptr_cache
      const auto& [v, dl, t_pos, _idx] = xlits[i0].get_watch_tuple(alpha_dl, alpha_trail_pos);
      idx[0] = i0; 
      ws[0] = _idx;
      ptr_cache[0] = v;
      xlit_t_pos[i0] = t_pos;
      //find unique lineral of highest t_pos to watch
      if(it->second.size()>1) {
        auto& l = it->second;
        l.pop_front();
        //add first el in l to all others, re-evaluate xlit_t_pos, adapt xlit_dl_count0, AND add them back to t_pos_to_idxs
        for(const var_t i : l) {
          assert(i!=i0);
          xlits[i] += WLIN0;
          if(xlits[i].is_zero()) {
            --num_nz_lins;
            continue;
          }
          const auto& [v, dl, t_pos, _idx] = xlits[i].get_watch_tuple(alpha_dl, alpha_trail_pos);
          assert(v==(var_t)-1 || t_pos < t_pos_to_idxs.rbegin()->first); //this assertion might fail on large examples!
          xlit_t_pos[i] = t_pos;
          xlit_dl_count0[i] = {dl, dl_count[dl]};
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
      const auto& [v, dl, t_pos, _idx] = xlits[i1].get_watch_tuple(alpha_dl, alpha_trail_pos);
      idx[1] = i1;
      ws[1] = _idx;
      ptr_cache[1] = v;
      xlit_dl_count0[i1] = {dl, dl_count[dl]};
      assert(xlit_t_pos[idx[1]] == t_pos);
      //@todo re-add as heuristic reduction?!
      //if(it->second.size() > 1 ) {
      //  //find unique lineral of 2nd-highest t_pos to watch
      //  auto& l = it->second; 
      //  l.pop_front();
      //  //add first el in l to all others, re-evaluate xlit_t_pos, adapt xlit_dl_count0, AND add them back to t_pos_to_idxs
      //  for(const var_t i : l) {
      //    assert(i!=i1);
      //    xlits[i] += WLIN1;
      //    if(xlits[i].is_zero()) {
      //      --num_nz_lins;
      //      continue;
      //    }
      //    const auto& [v, dl, t_pos, _idx] = xlits[i].get_watch_tuple(alpha_dl, alpha_trail_pos);
      //    assert(v==(var_t)-1 || t_pos < it->first);
      //    xlit_t_pos[i] = t_pos;
      //    xlit_dl_count0[i] = {dl, dl_count[dl]};
      //    filtration_add(i);
      //  }
      //  l.clear();
      //  l.emplace_front( i1 );
      //}
      //assert(it->second.size()==1);
    }
    assert( size()<1 || (xlits[idx[0]][ptr_cache[0]] && xlits[idx[0]].get_idxs_()[ws[0]]==ptr_cache[0] ));
    assert( size()<2 || (xlits[idx[1]][ptr_cache[1]] && xlits[idx[1]].get_idxs_()[ws[1]]==ptr_cache[1] ));
  };


  /**
   * @brief returns number of stored linerals
   * @note beware: if clause is zero we have size()==1 and size()==0 means claus is one (!)
   * 
   * @return var_t number of linerals
   */
  inline var_t size() const override { return num_nz_lins; };

  bool assert_data_struct() const {
    assert( size()<1 || (xlits[idx[0]][ptr_cache[0]] && xlits[idx[0]].get_idxs_()[ws[0]]==ptr_cache[0] ));
    assert( size()<2 || (xlits[idx[1]][ptr_cache[1]] && xlits[idx[1]].get_idxs_()[ws[1]]==ptr_cache[1] ));

    //check num_nz_lins
    assert( num_nz_lins == (var_t) std::count_if(xlits.begin(), xlits.end(), [](const auto& l){ return !l.is_zero(); }) );

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
    for(var_t j=0; j<xlits.size(); ++j) {
      if(!xlits[j].is_zero()) tmp.insert(j);
    }
    for(const auto& [k,l] : t_pos_to_idxs) {
      for(const auto& i : l) {
        tmp.erase( i );
      }
    }
    assert(tmp.empty());

    //there are as many different keys in t_pos_to_idxs as there are different values in xlit_t_pos
    tmp.clear();
    for(var_t j=0; j<xlits.size(); ++j) {
      if(!xlits[j].is_zero()) tmp.insert( xlit_t_pos[j] );
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
      assert_slow(to_xcls().reduced(alpha).is_zero());
    }
    if( size()>0 && dl_count[xlit_dl_count0[idx[0]].first] == xlit_dl_count0[idx[0]].second ) assert( !eval0(alpha) );
    if( size()>1 && dl_count[xlit_dl_count0[idx[1]].first] == xlit_dl_count0[idx[1]].second ) assert( !eval1(alpha) || is_unit(dl_count) );
    for(var_t i = 0; i<xlits.size(); ++i) {
      if(i==idx[0] || i==idx[1]) continue;
      if( dl_count[xlit_dl_count0[i].first] == xlit_dl_count0[i].second ) assert( xlits[i].eval(alpha) );
    }

    //check xlit_t_pos
    for(var_t i = 0; i<xlits.size(); ++i) {
      if(i==idx[0] || i==idx[1]) continue;
      if(dl_count[xlit_dl_count0[i].first] == xlit_dl_count0[i].second && !xlits[i].is_zero()) assert( xlits[i].get_watch_var(alpha_trail_pos).first == xlit_t_pos[i] );
    }
    if(idx[0]<xlits.size() && dl_count[xlit_dl_count0[idx[0]].first] == xlit_dl_count0[idx[0]].second && !xlits[idx[0]].is_zero())
      assert( (xlits[idx[0]]+shared_part).get_watch_var(alpha_trail_pos).first  == xlit_t_pos[idx[0]] );
    if(idx[1]<xlits.size() && dl_count[xlit_dl_count0[idx[1]].first] == xlit_dl_count0[idx[1]].second && !xlits[idx[1]].is_zero())
      assert( (xlits[idx[1]]+shared_part).get_watch_var(alpha_trail_pos).first  == xlit_t_pos[idx[1]] );

    assert( size()<2 || alpha_trail_pos[ptr_cache[0]] > alpha_trail_pos[ptr_cache[1]] );

    return assert_data_struct();
  };
#endif

  inline xcls_watch& operator=(const xcls_watch &o) {
    xcls_watch::operator=(o);
    init();
    return *this;
  };

  inline xcls_watch& operator=(xcls_watch &&o) {
    xcls_watch::operator=(std::move(o));
    init();
    return *this;
  };
};