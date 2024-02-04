#pragma once

#include "xcls_watch.hpp"

#include <queue>



class xcls_watch_resolver : public xcls_watch {
private:
  /**
   * @brief maps t_pos to idxs of xlits, i.e., xlits[ t_pos_to_idxs[t_pos] ] = t_pos
   */
  std::map<var_t, std::list<var_t> > t_pos_to_idxs;

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
    num_nz_lins = xlits.size();

    //init t_pos_to_idxs
    t_pos_to_idxs.clear();
    //init filtration list
    for(var_t i = 0; i<xlits.size(); ++i) {
      filtration_add(i);
    }
    assert( assert_data_struct() );
  }

  inline bool filtration_add(const var_t& i) {
    //@todo rewrite with 'lower_bound'
    if(t_pos_to_idxs.contains(xlit_t_pos[i])) {
      t_pos_to_idxs[xlit_t_pos[i]].push_back(i);
      return false;
    } else {
      t_pos_to_idxs[xlit_t_pos[i]] = {i};
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
   * @brief call once when no more resolvents are computed.
   * @note recompute shared_parts to 'repair' xcls_watch data_struct
   */
  xcls_watch& finalize() {
    //rm zero linerals
    for(var_t j=0; j<xlits.size(); ++j) {
      if(xlits[j].is_zero()) { xcls_watch::remove_zero_lineral(j); --j; }
    }

    //recompute shared_part
    assert(shared_part.is_zero());
    if(xlits.size()<=1) return *this;

    shared_part = xlits.size() > 1 ? WLIN0.shared_part(WLIN1) : xlit();
    WLIN0 += shared_part;
    ws[0] = std::distance(WLIN0.get_idxs_().begin(), std::lower_bound(WLIN0.get_idxs_().begin(), WLIN0.get_idxs_().end(), ptr_cache[0]));
    if(ws[0] >= WLIN0.size() || ptr_(idx[0],ws[0])!=ptr_cache[0] ) {
      WLIN0.swap(shared_part);
      assert( WLIN1[ptr_cache[0]] );
      ws[0] = std::distance(WLIN0.get_idxs_().begin(), std::lower_bound(WLIN0.get_idxs_().begin(), WLIN0.get_idxs_().end(), ptr_cache[0]));
    }

    if (xlits.size() > 1) {
      WLIN1 += shared_part;
      ws[1] = std::distance(WLIN1.get_idxs_().begin(), std::lower_bound(WLIN1.get_idxs_().begin(), WLIN1.get_idxs_().end(), ptr_cache[1]));
      if(ws[1] >= WLIN1.size() || ptr_(idx[1],ws[1])!=ptr_cache[1] ) {
        WLIN1.swap(shared_part);
        assert( WLIN1[ptr_cache[1]] );
        ws[1] = std::distance(WLIN1.get_idxs_().begin(), std::lower_bound(WLIN1.get_idxs_().begin(), WLIN1.get_idxs_().end(), ptr_cache[1]));
      }
    }

    assert( xcls_watch::assert_data_struct() );
    assert( xcls_watch::assert_data_struct() );

    return *this;
  }

  xcls_upd_ret resolve(const xcls_watch &rs_cls, const vec<bool3> &alpha, const vec<var_t> &alpha_dl, const vec<var_t> &alpha_trail_pos, const vec<dl_c_t> &dl_count, const bool opt = false) {
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
        idx[0] = idx[1];
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
      //@todo shortcut if size()==1!

      //find highest two t_pos linerals to watch; and reduce those as long as they are not unique!
      if(t_pos_to_idxs.size()>0) {
        //find unique lineral of highest t_pos to watch
        auto l = std::move(t_pos_to_idxs.rbegin()->second);
        //add first el in l to all others, re-evaluate xlit_t_pos, adapt xlit_dl_count0, AND add them back to t_pos_to_idxs
        const var_t i0 = l.front(); l.pop_front();
        //set idx, ws, and ptr_cache
        const auto& [v, dl, t_pos, _idx] = xlits[i0].get_watch_tuple(alpha_dl, alpha_trail_pos);
        idx[0] = i0; 
        ws[0] = _idx;
        ptr_cache[0] = v;
        assert(xlit_t_pos[i0] == t_pos);
        //reduce other lins
        for(const var_t i : l) {
          assert(i!=i0);
          xlits[i] += WLIN0;
          if(xlits[i].is_zero()) {
            //remove_zero_lineral(i_);
            --num_nz_lins;
            xlit_dl_count0[i] = {0,1}; //@todo do we need this?
            continue;
          }
          const auto& [v, dl, t_pos, _idx] = xlits[i].get_watch_tuple(alpha_dl, alpha_trail_pos);
          assert(v==(var_t)-1 || t_pos < t_pos_to_idxs.rbegin()->first);
          xlit_t_pos[i] = t_pos;
          xlit_dl_count0[i] = {dl, dl_count[dl]};
          if(!xlits[i].is_zero())
            filtration_add(i);
        }
        l.clear();
        l.emplace_front( i0 );
        t_pos_to_idxs.rbegin()->second = std::move(l);
        assert(t_pos_to_idxs.rbegin()->second.size()==1);
      }

      if(t_pos_to_idxs.size()>1) {
        //find unique lineral of 2nd-highest t_pos to watch
        auto l = std::move( std::next(t_pos_to_idxs.rbegin())->second );
        //add first el in l to all others, re-evaluate xlit_t_pos, adapt xlit_dl_count0, AND add them back to t_pos_to_idxs
        const var_t i1 = l.front(); l.pop_front();
        //set idx, ws, and ptr_cache
        const auto& [v, dl, t_pos, _idx] = xlits[i1].get_watch_tuple(alpha_dl, alpha_trail_pos);
        idx[1] = i1; 
        ws[1] = _idx;
        ptr_cache[1] = v;
        xlit_dl_count0[i1] = {dl, dl_count[dl]};
        assert(xlit_t_pos[idx[1]] == t_pos);
        for(const var_t i : l) {
          assert(i!=i1);
          xlits[i] += WLIN1;
          if(xlits[i].is_zero()) {
            //remove_zero_lineral(i_);
            --num_nz_lins;
            xlit_dl_count0[i] = {0,1}; //@todo do we need this?
            continue;
          }
          const auto& [v, dl, t_pos, _idx] = xlits[i].get_watch_tuple(alpha_dl, alpha_trail_pos);
          assert(v==(var_t)-1 || t_pos < std::next(t_pos_to_idxs.rbegin())->first);
          xlit_t_pos[i] = t_pos;
          xlit_dl_count0[i] = {dl, dl_count[dl]};
          if(!xlits[i].is_zero()) 
            filtration_add(i);
        }
        l.clear();
        l.emplace_front( i1 );
        std::next(t_pos_to_idxs.rbegin())->second = std::move(l);
      }

      assert( assert_data_struct(alpha, alpha_trail_pos, dl_count) );
      assert( assert_data_struct() );
      assert( is_unit(dl_count) );

      return xcls_upd_ret::UNIT;

      // add xlits from rs_cls to this
      if(rs_cls.size() == 1) {
        //no more lins to add!
        //const auto ret = init_unit(alpha, alpha_dl, alpha_trail_pos, dl_count);
        //assert(ret == xcls_upd_ret::UNIT);
        //assert(is_unit(dl_count));

        assert( assert_data_struct() );
        assert( assert_data_struct(alpha, alpha_trail_pos, dl_count) );
        return xcls_upd_ret::UNIT;
      }
      if(size()==1) {
        //now xlits will get at least one additional lineral! ...so we need to init idx[1]! -- the precise value does in fact not matter it is just used once within init_unit() to distribute the shared part
        assert(shared_part.is_zero());
        assert(idx[0]==0);
        idx[1] = 1;
      }
      //const auto ret = init_unit_opt(alpha, alpha_dl, alpha_trail_pos, dl_count, rs_cls.xlits.size());
      //const auto ret = init_unit(alpha, alpha_dl, alpha_trail_pos, dl_count);
      const auto ret = opt ? init_unit_opt(alpha, alpha_dl, alpha_trail_pos, dl_count, rs_cls.xlits.size()) : init_unit(alpha, alpha_dl, alpha_trail_pos, dl_count);
      assert(ret == xcls_upd_ret::UNIT);
      assert(is_unit(dl_count));
      assert( assert_data_struct(alpha, alpha_trail_pos, dl_count) );
      return ret;
  };


  /**
   * @brief returns number of stored linerals
   * @note beware: if clause is zero we have size()==1 and size()==0 means claus is one (!)
   * 
   * @return var_t number of linerals
   */
  inline var_t size() const override { return num_nz_lins; };

  bool assert_data_struct() const {
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

  void operator=(const xcls_watch &o) {
    xcls_watch::operator=(o);
    init();
  };

  void operator=(xcls_watch &&o) {
    xcls_watch::operator=(std::move(o));
    init();
  };
};