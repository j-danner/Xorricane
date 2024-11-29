#pragma once

#include "misc.hpp"
#include "lineral.hpp"
#include "cls.hpp"
#include "lin_sys.hpp"
#include <list>
#include <set>
#include <unordered_set>
#include "lineral_watch.hpp"

using lit_watch = var_t;

/**
 * @brief return type for update of cls_watch
 */
enum class cls_upd_ret {
  SAT,
  UNIT,
  NONE
};

#define WLIN0 linerals[idx[0]]
#define WLIN1 linerals[idx[1]]

// watch cls
class cls_watch
{
  friend class cls_watch_resolver;
  friend class solver;
private:
  /**
   * @brief lits in the linerals that form a generating set for the associated vector space
   */
  vec<lineral> linerals;
  // TODO would it be better to store linerals NOT as objects of class lineral, but as UNSORTED vecs of var_t's ??

  /**
   * @brief shared part of WLIN0 and WLIN1
   */
  lineral shared_part;

  /**
   * @brief lineral_dl_counts_1[i] tells in which dl and at what count lineral[i] was last evaluated to be 0 ({0,0} default)
   */
  vec<std::pair<var_t, dl_c_t>> lineral_dl_count0;

  /**
   * @brief lineral_dl_counts_0 tells in which dl the cls is 0, i.e., SAT
   */
  std::pair<var_t, dl_c_t> SAT_dl_count = {0,0};
  
  /**
   * @brief trail pos where linerals evaluated last to 0
   */
  vec<var_t> lineral_t_pos;

  /**
   * @brief lineral watches; offset into linerals
   */
  lit_watch idx[2];

  /**
   * @brief literal watches; offset into idxs-sets of WLIN0 and WLIN1
   */
  lit_watch ws[2];

  /**
   * @brief cache watched vars
   */
  var_t ptr_cache[2];

  // flags
  /**
   * @brief indicates whether clause is irredundant; be default all clauses are irredundant (and cannot be removed!)
   */
  bool irredundant = true;

  /**
   * @brief indicates whether clause should be removed on next cleanup
   */
  bool delete_on_cleanup = false;

  /**
   * @brief initializes shared_part, ws[0], ws[1] and ptr_cache
   * @note assumes that linerals are already set; wl_it must still be initiated!
   */
  void init() {
    // init lineral_dl_counts
    lineral_dl_count0.resize(size(), {0, 0});
    lineral_t_pos.resize(size(), (var_t) -1);

    if (size() == 0) {
      shared_part.clear();
      return;
    } else if (size() == 1) {
      idx[0] = 0;
      ws[0] = 0;
      ptr_cache[0] = ptr_(idx[0], ws[0]);
      shared_part.clear();
      return;
    }
    assert(size() > 1);
    idx[0] = 0;
    idx[1] = 1;
    
    // init shared
    shared_part = WLIN0.shared_part(WLIN1);
    // rm shared part from WLIN0 and WLIN1
    WLIN0 += shared_part;
    WLIN1 += shared_part;

    if(WLIN0.size()==0) WLIN0.swap(shared_part);
    if(WLIN1.size()==0) WLIN1.swap(shared_part);
    // ensure that WLIN0 and WLIN1 are non-empty
    assert(WLIN0.size() > 0 && WLIN1.size() > 0);

    // init ws/idx
    ws[0] = 0;
    ws[1] = 0;
    ptr_cache[0] = ptr_(idx[0], ws[0]);
    ptr_cache[1] = ptr_(idx[1], ws[1]);
    assert(get_wl0() != get_wl1());

    assert_slow(assert_data_struct());
  }

  inline var_t ptr_(const cls_size_t &i, const var_t val) const {
    if(val == 0 && linerals[i].size()==0) return 0;
    assert(val < linerals[i].size());
    // return linerals[i].get_idxs_().at(val);
    return linerals[i].get_idxs_()[val];
  }

  inline const var_t &ptr_ws(const cls_size_t &i) const {
    assert(i==0 || i==1);
    assert(ptr_(idx[i], ws[i]) == ptr_cache[i]);
    return ptr_cache[i];
  }

  /**
   * @brief check if clause in current repr is disjoint
   */
  bool is_disjoint() const {
    if(!shared_part.is_constant()) return false;
    std::unordered_set<var_t> idxs;
    for(const auto& l : linerals) {
      for(const auto& v : l.get_idxs_()) {
        if(idxs.contains(v)) return false;
        idxs.insert(v);
      }
    }
    return true;
  };
  
  /**
   * @brief advances ws[0] such that ws[0] and ws[1] satisfy all invariants; 'repairs' inactive watches
   * @note assumes that clause is UNIT under alpha
   *
   * @param alpha current bool3-alpha
   * @param alpha_dl dl of alpha-assignments
   * @param alpha_trail_pos t_pos of alpha-assignments
   * @return pair<var_t,cls_upd_ret> upd_ret is SAT if cls became satisfied, UNIT if cls became unit (includes UNSAT case, i.e., unit 1), NONE otherwise; var_t indicates changed watched literal (if non-zero)
   */
  inline void fix_ws0([[maybe_unused]] const vec<bool3> &alpha, const vec<var_t> &alpha_dl, const vec<var_t> &alpha_trail_pos) noexcept {
    const auto& [v, _, t_pos, pos] = WLIN0.get_watch_tuple(alpha_dl, alpha_trail_pos);
    ws[0] = pos;
    ptr_cache[0] = v;
    lineral_t_pos[idx[0]] = t_pos;
    assert(assert_data_struct());
  }

  /**
   * @brief advances ws[0]
   *
   * @param alpha current bool3-alpha
   * @param alpha_dl dl of alpha-assignments
   * @param alpha_trail_pos t_pos of alpha-assignments
   * @param dl_count current dl_count
   * @return pair<var_t,cls_upd_ret> upd_ret is SAT if cls became satisfied, UNIT if cls became unit (includes UNSAT case, i.e., unit 1), NONE otherwise; var_t watched variable (if non-zero)
   */
  inline std::pair<var_t, cls_upd_ret> advance(const vec<bool3> &alpha, const vec<var_t> &alpha_dl, const vec<var_t> &alpha_trail_pos, const vec<dl_c_t> &dl_count) noexcept {
    if(alpha[ptr_ws(0)] == bool3::None) return {ptr_ws(0), cls_upd_ret::NONE};
    assert(alpha[ptr_ws(0)] != bool3::None);

    // TODO shorter & cleaner impl with c++20 ranges?
    // vec<std::ranges::subrange<lit_watch, lineral::iterator, std::ranges::subrange_kind::sized>> tmp{ std::ranges::subrange(ws[i], linerals[i].end()), std::ranges::subrange(linerals[i].begin(), ws[i]) };
    // auto r = tmp | std::ranges::views::join;

    // advance iterator as long as there is another unassigned idx to point to
    auto new_w = ws[0];
    while ((new_w < (var_t)WLIN0.size()) && (alpha[ptr_(idx[0], new_w)] != bool3::None)) { ++new_w; }
    if (new_w == (var_t)WLIN0.size()) {
      /*wrap around end if necessary */ new_w = 0;
      while ((alpha[ptr_(idx[0], new_w)] != bool3::None) && (new_w != ws[0])) { ++new_w; }
    }
    // advancing done; now new_w points to ws[0] or at an unassigned idx -- or again to ws[0] (!)

    if (new_w != ws[0]) {
      assert(alpha[ptr_(idx[0], new_w)] == bool3::None);
      ws[0] = new_w;
      ptr_cache[0] = ptr_(idx[0], ws[0]);
      assert(assert_data_struct());
      return {ptr_ws(0), cls_upd_ret::NONE};
    }
    // now WLIN0 is constant under alpha! ...i.e. check shared part
    new_w = 0;
    while ((new_w < (var_t)shared_part.size()) && (alpha[shared_part.get_idxs_()[new_w]] != bool3::None)) ++new_w;
    if (new_w != (var_t)shared_part.size()) {
      // lit in shared_part can be watched!
      // rewrite WLIN1:
      WLIN0.swap(shared_part);
      ws[0] = new_w;
      ptr_cache[0] = ptr_(idx[0], ws[0]);
      assert(assert_data_struct());
      return {ptr_ws(0), cls_upd_ret::NONE};
    }

    // now shared_part can also be evaluated --> WLIN0+shared_part can be evaluated!
    if (WLIN0.eval(alpha) ^ shared_part.eval(alpha)) {
      // WLIN0+shared_part evaluates to 1
      // corresponding lineral is 1 --> clause does not need to be watched any longer!
      // do not change watches!
      SAT_dl_count = {alpha_dl[ptr_ws(0)], dl_count[alpha_dl[ptr_ws(0)]]};
      assert(!is_active(dl_count)); // clause is no longer active!
      assert(assert_data_struct());
      return {ptr_ws(0), cls_upd_ret::SAT};
    }
    // now WLIN0+shared_part evaluates to 0 under alpha, i.e., we check whether a different lineral can be watched.
    lineral_dl_count0[idx[0]] = {alpha_dl[ptr_ws(0)], dl_count[alpha_dl[ptr_ws(0)]]};
    //@todo how to obtain lineral_t_pos information without another iteration?
    lineral_t_pos[idx[0]] = std::max( linerals[idx[0]].get_watch_var(alpha_trail_pos).first, shared_part.get_watch_var(alpha_trail_pos).first );

    // note that WLIN0 and WLIN1 are always the linerals that are watched, i.e., start search from linerals[2] (!)
    cls_size_t new_i = 0;
    for (; new_i < size(); ++new_i) {
      if(new_i==idx[0] || new_i==idx[1]) continue;
      // skip linerals which evaluate to 0 in current search tree
      if (dl_count[lineral_dl_count0[new_i].first] == lineral_dl_count0[new_i].second)
        continue;
      
      if(linerals[new_i][ptr_ws(1)]) {
        //add WLIN1 to linerals[new_i] to eliminate shared part in linerals[new_i]
        linerals[new_i] += WLIN1;
        linerals[new_i] += shared_part;
      }

      const auto& [v, dl_assigned, t_pos, _] = linerals[new_i].get_watch_tuple(alpha_dl, alpha_trail_pos);
      new_w = _;

      //rm linerals[new_i] if it is just zero!
      if(linerals[new_i].is_zero()) {
        remove_zero_lineral(new_i);
        //repeat with same new_i
        --new_i;
        continue;
      } else if(linerals[new_i].is_one()) {
        //leave watches untouched; but set SAT_dl_count s.t. clause is satisfied already at dl 0!
        SAT_dl_count = {0, 1};
        return {ptr_ws(0), cls_upd_ret::SAT};
      }
      assert(!linerals[new_i].is_one());

      assert(!(v == ptr_ws(1) || ( linerals[new_i][ptr_ws(1)] && (WLIN1[v] || shared_part[v]) ) ));
      if (alpha[v] == bool3::None ) {
        //if ptr_(new_i,new_w) AND ptr_(idx[1],ws[1]) both are in shared part of WLIN1 AND linerals[new_i]; rewrite linerals[new_i] and start over
        // new lineral to be watched found --> change watched lineral and return SAT
        const auto wl0 = v;
        const auto wl1 = ptr_ws(1);
        WLIN0 += shared_part;
        WLIN1 += shared_part;
        idx[0] = new_i;
        // fix shared_parts && update ws[0] and ws[1] accordingly!
        shared_part = WLIN0.shared_part(WLIN1);
        WLIN0 += shared_part;
        WLIN1 += shared_part;
        // fix ws[0] AND ws[1]!
        ws[0] = std::distance(WLIN0.get_idxs_().begin(), std::lower_bound(WLIN0.get_idxs_().begin(), WLIN0.get_idxs_().end(), wl0));
        //if ptr_(idx[0],ws[0]) is NOT wl0, then we need to rewrite WLIN0
        if(ws[0] >= WLIN0.size() || ptr_(idx[0],ws[0])!=wl0 ) {
          WLIN0.swap(shared_part);
          assert( WLIN1[wl1] );
          ws[0] = std::distance(WLIN0.get_idxs_().begin(), std::lower_bound(WLIN0.get_idxs_().begin(), WLIN0.get_idxs_().end(), wl0));
        }
        ws[1] = std::distance(WLIN1.get_idxs_().begin(), std::lower_bound(WLIN1.get_idxs_().begin(), WLIN1.get_idxs_().end(), wl1));
        if(ws[1] >= WLIN1.size() || ptr_(idx[1],ws[1])!=wl1 ) {
          WLIN1.swap(shared_part);
          assert( WLIN1[wl1] );
          ws[1] = std::distance(WLIN1.get_idxs_().begin(), std::lower_bound(WLIN1.get_idxs_().begin(), WLIN1.get_idxs_().end(), wl1));
        }
        ptr_cache[0] = ptr_(idx[0], ws[0]);
        ptr_cache[1] = ptr_(idx[1], ws[1]);
        assert(ptr_cache[0] == wl0 && ptr_cache[1] == wl1);
        assert(is_active(dl_count));
        return {ptr_ws(0), cls_upd_ret::NONE};
      } else {
        // linerals[new_i] evaluates to a constant; this is only useful if linerals[new_i].eval(alpha) is 1, i.e., the clause is SAT
        if(!linerals[new_i].eval(alpha)) {
          //note: we can leave all watches as they were!
          SAT_dl_count = {dl_assigned, dl_count[dl_assigned]};
          
          assert(!is_active(dl_count));
          assert(is_sat(dl_count));
          assert(assert_data_struct());
          assert(assert_data_struct(alpha, alpha_trail_pos, dl_count));
          return {ptr_ws(0), cls_upd_ret::SAT};
        }
        // now linerals[new_i] evaluates to 0 --> choose different new_i
        lineral_dl_count0[new_i] = {dl_assigned, dl_count[dl_assigned]};
        //update t_pos information
        lineral_t_pos[new_i] = t_pos;
        assert_slow(lineral_t_pos[new_i] == linerals[new_i].get_watch_var(alpha_trail_pos).first);
        
        assert( dl_assigned <= alpha_dl[ptr_ws(0)] );
      }
    }
    // if the above did not yet return, then all linerals (except WLIN1) evaluate to 0 under alpha, i.e., we learn a unit clause!
    // moreover, no watch literals need to be updated! (ws[0] is already at highest dl and WLIN0 evaluates to 0!)
    
    //set lineral_t_pos of unit to -1
    //@todo can we also just set it to -1 ??
    lineral_t_pos[idx[1]] = std::max( linerals[idx[1]].get_watch_var(alpha_trail_pos).first, shared_part.get_watch_var(alpha_trail_pos).first );

    //ensure that WLIN0 is the unit:
    swap_wl();
    assert(!is_active(dl_count));
    assert(is_unit(dl_count));
    assert( !(size()>1) || (lineral_t_pos[idx[0]] > lineral_t_pos[idx[1]]) );
    assert(assert_data_struct());
    return {ptr_ws(1), cls_upd_ret::UNIT};
  };

  /**
   * @brief swap watched literals
   */
  void swap_wl() {
    std::swap(idx[0], idx[1]);
    std::swap(ws[0], ws[1]);
    std::swap(ptr_cache[0], ptr_cache[1]);
  }

public:
  cls_watch() noexcept {
    idx[0] = 0; idx[1] = 0;
    ws[0] = 0; ws[1] = 0;
    ptr_cache[0] = 0; ptr_cache[1] = 0;
    linerals.emplace_back( lineral().add_one() );
    lineral_dl_count0.resize(1, {0,0});
    lineral_t_pos.resize(1, 0);
    assert(assert_data_struct());
  };

  cls_watch(const lineral &l1, const lineral &l2) noexcept : linerals(vec<lineral>({l1, l2})), lineral_dl_count0({{0,0},{0,0}}) {
    WLIN0.add_one(); WLIN1.add_one();
    assert(!l1.is_one() && !l1.is_zero());
    assert(!l2.is_one() && !l2.is_zero());
    init();
  };
  
  cls_watch(const lineral& lit, const vec<bool3> &alpha, const vec<var_t> &alpha_dl, const vec<var_t> &alpha_trail_pos, const vec<dl_c_t> &dl_count) noexcept : linerals(vec<lineral>{lit}), lineral_dl_count0({{0,0}}), lineral_t_pos({(var_t)-1}) {
    linerals = vec<lineral>({lit.plus_one()});
    idx[0] = 0; idx[1] = 0;
    shared_part.clear();

    const auto& [v, v_dl, t_pos, offset] = linerals[0].get_watch_tuple(alpha_dl, alpha_trail_pos);
    ws[1] = 0; ptr_cache[1] = 0;
    ws[0] = offset; ptr_cache[0] = v;

    lineral_t_pos[0] = t_pos;

    //if lit is reduced to 0 by alpha, set lineral_dl_count0
    if(t_pos < (var_t) -1 && !eval0(alpha)) {
      lineral_dl_count0[0] = {v_dl, dl_count[v_dl]};
      //@todo do we even need to set lineral_dl_count0 ?!
    }

    assert(assert_data_struct());
  };

  cls_watch(const cls &cl) noexcept : linerals(vec<lineral>(cl.get_ass_VS().get_linerals().begin(), cl.get_ass_VS().get_linerals().end())), lineral_dl_count0(cl.deg(),{0,0}) {
    init();
  };

  cls_watch(cls &&cl) noexcept {
    linerals = vec<lineral>();
    linerals.reserve(cl.deg());
    for (auto lit : cl.get_ass_VS().get_linerals()) {
      if(!lit.is_zero()) linerals.emplace_back(std::move(lit));
    }
    init();
  };

  cls_watch(const cls_watch &o) noexcept = default;
  cls_watch(cls_watch &&o) noexcept = default;

  cls_watch(const lin_sys &lits) noexcept : linerals(lits.get_linerals().begin(), lits.get_linerals().end()) {
    assert(lits.dim() >= 1);
    init();
  };

  void set_redundancy(const bool red) { irredundant = !red; };

  /**
   * @brief mark clause for removal, i.e., remove clause on cleanup
   * @note clause is not marked if it is irredundant -- except if it is satisfied on dl 0
   */
  void mark_for_removal() { if(!irredundant || is_sat0()) { delete_on_cleanup = true; } };

  bool is_marked_for_removal() const { return delete_on_cleanup; };
  bool is_irredundant() const { return irredundant; };

  /**
   * @brief evals the 0-th watched literal at alpha
   *
   * @param alpha current bool3-assignments
   *
   * @return true iff alpha( WLIN0+shared_part ) = 0
   */
  bool eval0(const vec<bool3> &alpha) const {
    return WLIN0.eval(alpha) ^ shared_part.eval(alpha);
  }

  /**
   * @brief evals the 1-th watched literal at alpha
   *
   * @param alpha current bool3-assignments
   *
   * @return true iff alpha( WLIN1+shared_part ) = 0
   */
  bool eval1(const vec<bool3> &alpha) const {
    return WLIN1.eval(alpha) ^ shared_part.eval(alpha);
  }
  
  /**
   * @brief removes literal upd_lt from lineral, if is present
   * 
   * @param upd_lt literal to be removed
   * @param val value that is assigned to literal
   * @return true iff clause became inactive, i.e., SAT
   */
  bool rm(const var_t upd_lt, const bool3 val, const vec<var_t>& alpha_trail_pos) {
    assert( !watches(upd_lt) );
    bool ret = false;
    //rm from unwatched linerals
    shared_part.rm(upd_lt, val);
    for(var_t j=0; j<size(); ++j) {
      if(j==idx[0] || j==idx[1]) continue;
      if( !linerals[j].rm(upd_lt, val) ) continue;
      if(linerals[j].is_one()) {
        //now clause becomes SAT!
        SAT_dl_count = {0,1};
        ret = true;
      } else if (linerals[j].is_zero()) {
        //linerals[j] can now be ignored, remove!
        remove_zero_lineral(j);
        //repeat removal with j-th lineral!
        --j;
      } else {
        //now linerals[j] is non-constant
        //(potentially) fix lineral_t_pos[j]
        if(lineral_t_pos[j]==alpha_trail_pos[upd_lt]) {
          lineral_t_pos[j] = linerals[j].get_watch_var(alpha_trail_pos).first;
        }
      }
    }
    //rm from WLIN0
    if( WLIN0.rm(upd_lt, val) ) {
      //adapt ws[0]
      if(ptr_cache[0] > upd_lt) ws[0]--;
      assert(ptr_(idx[0],ws[0]) == ptr_cache[0]);
      assert(!WLIN0.is_zero());
      if(lineral_t_pos[idx[0]]==alpha_trail_pos[upd_lt]) {
        lineral_t_pos[idx[0]] = linerals[idx[0]].get_watch_var(alpha_trail_pos).first;
      }
    }

    if( size()>0 && WLIN1.rm(upd_lt, val) ) {
      //adapt ws[0]
      if(ptr_cache[1] > upd_lt) ws[1]--;
      assert(ptr_(idx[1],ws[1]) == ptr_cache[1]);
      assert(!WLIN1.is_zero());
      if(lineral_t_pos[idx[1]]==alpha_trail_pos[upd_lt]) {
        lineral_t_pos[idx[1]] = linerals[idx[1]].get_watch_var(alpha_trail_pos).first;
      }
    }

    assert(assert_data_struct());

    return ret;
  }

  /**
   * @brief removes linerals[i] (assumed to be zero), by swapping out to last position and truncating
   * @note beware of removing watched linerals! (first distribute shared_part!)
   *
   * @param i index of lineral to be removed
   */
  inline void remove_zero_lineral(const var_t& i) {
    assert(linerals[i].is_zero());
    linerals[i].swap(linerals.back());
    linerals.pop_back();
    std::swap( lineral_dl_count0[i], lineral_dl_count0.back() );
    lineral_dl_count0.pop_back();
    std::swap( lineral_t_pos[i], lineral_t_pos.back() );
    lineral_t_pos.pop_back();
    //adapt idx-pos -- if it was swapped!
    if(idx[0] == linerals.size()) {
      idx[0] = i;
      assert(size()<=1 || i < linerals.size() || is_zero());
    } else if(idx[1] == linerals.size()) {
      idx[1] = i;
      if(linerals.size()==i) {
        idx[1] = 0;
        ws[1] = 0;
        ptr_cache[1] = 0;
      }
      assert(size()<=1 || i <= linerals.size() || is_zero());
    }
  }

  /**
   * @brief updates cls_watch and watch_list according to the new assigned literal lit, dl_count, dl and alpha.
   *
   * @param new_lit literal that was newly assigned
   * @param alpha current bool3-assignment
   * @param alpha_dl dl of alpha-assignments
   * @param alpha_trail_pos t_pos of alpha-assignments
   * @param dl_count current dl_count
   * @return var_t,cls_upd_ret upd_ret is SAT if cls does not need any further updates (i.e. it is a unit or satisfied), UNIT if cls became unit just now (includes UNSAT case, i.e., unit 1), NONE otherwise; var_t is the new-watched literal (or the same if unchanged!)
   */
  std::pair<var_t, cls_upd_ret> update(const var_t &new_lit, const vec<bool3> &alpha, const vec<var_t> &alpha_dl, const vec<var_t> &alpha_trail_pos, const vec<dl_c_t> &dl_count) {
    // check if clause needs any processing
    assert(is_active(dl_count));
    if (!is_active(dl_count)) {
      assert(is_sat(dl_count) || is_unit(dl_count));
      return {new_lit, cls_upd_ret::SAT}; // NOTE here it might also be a UNIT, but it did not become one by this update!
    }
    // exactly one of { ptr_ws(0), ptr_ws(1) } must be new_lit
    assert((ptr_ws(0) == new_lit) ^ (ptr_ws(1) == new_lit));
    // swap s.t. ptr_ws(0) == new_lit
    if (ptr_ws(0) != new_lit)
      swap_wl();
    assert(ptr_ws(0) == new_lit);

    // advance ws[0]
    const auto [new_w, upd] = advance(alpha, alpha_dl, alpha_trail_pos, dl_count);
    assert(is_sat(dl_count) || is_unit(dl_count) || ptr_ws(0) != new_lit);
    assert(watches(new_w));
    assert(assert_data_struct());

    // assert correct return value!
    if (upd == cls_upd_ret::NONE) {
      // assert( is_none(alpha) ); //leads to error: it might be SAT but ONLY after all updates have been performed! (i.e. if WLIN0 AND WLIN1 needs an update!)
      assert(is_none(dl_count));
      return {new_w, upd};
    } else if (upd == cls_upd_ret::SAT) {
      assert(is_sat(dl_count));
      return {new_w, upd};
    } else {
      assert(upd == cls_upd_ret::UNIT);
      assert(is_unit(dl_count));
      assert( !(is_unit(dl_count) && size()>1) || (lineral_t_pos[idx[0]] > lineral_t_pos[idx[1]]) );
      return {new_w, upd};
    }
  };
  
  /**
   * @brief reduces cls_watch with all equivalences -- and rewrites the clause if necessary!
   *
   * @param alpha current bool3-assignment
   * @param alpha_dl dl of alpha-assignments
   * @param alpha_trail_pos t_pos of alpha-assignments
   * @param equiv_lits vec of equivalences
   * @param dl_count current dl_count
   * @return cls_upd_ret SAT if cls does not need any further updates (i.e. it is a unit or satisfied), UNIT if cls became unit just now (includes UNSAT case, i.e., unit 1), NONE otherwise
   */
  cls_upd_ret reduce_equiv(const vec<bool3>& alpha, const vec<equivalence> &equiv_lits, const vec<dl_c_t> &dl_count) {
    // check if clause needs any processing
    assert(is_active(dl_count));
    if (!is_active(dl_count)) {
      assert(is_sat(dl_count) || is_unit(dl_count));
      return cls_upd_ret::SAT; // NOTE here it might also be a UNIT, but it did not become one by this update!
    }
    //reduce all unwatched linerals
    for(var_t i=0; i<linerals.size(); ++i) {
      if(i==idx[0] || i==idx[1]) continue;
      if(linerals[i].reduce(alpha, equiv_lits)) {
       #ifdef DEBUG_SLOW
        for(const auto& v: linerals[i].get_idxs()) assert( alpha[v]==bool3::None && !equiv_lits[v].is_active() );
       #endif
        //reset t_pos and dl_count -- do we really need this?!
        //@todo do we really need to do this? note: the new equiv could only be discoverd as the corr alpha are NOT assigned, i.e., reduction is possible!
        lineral_t_pos[i] = (var_t) -1;
        lineral_dl_count0[i] = {0, 0};
        //treat special cases -- reduction to constant
        if(linerals[i].is_zero()) {
          remove_zero_lineral(i);
          --i; //repeat for same idx i
        } else if(linerals[i].is_one()) {
          //leave watches untouched; but set SAT_dl_count s.t. clause is satisfied already at dl 0!
          SAT_dl_count = {0, 1};
          //swap into first position -- remove all other linerals!
          shared_part.clear();
          linerals[0].clear(); linerals[0].add_one();
          idx[0] = 0;
          linerals.resize(1);
          lineral_dl_count0.resize(1, {0,0});
          lineral_t_pos.resize(1, (var_t)-1);
          return cls_upd_ret::SAT;
        }
      }
    }
    //reduce watched linerals
    while(true) {
      if(size()==0) {
        return cls_upd_ret::SAT;
      } else if(size()==1) {
        assert(idx[0] == 0);
        ws[0] = 0;
        ptr_cache[0] = ptr_(idx[0],ws[0]);
        return cls_upd_ret::UNIT;
      }

      //distribute shared part
      WLIN0 += shared_part;
      WLIN1 += shared_part;
      shared_part.clear();
      //reduce watched linerals
      WLIN0.reduce(alpha, equiv_lits);
      WLIN1.reduce(alpha, equiv_lits);

      //recompute shared_part
      shared_part = WLIN0.shared_part(WLIN1);
      WLIN0 += shared_part;
      WLIN1 += shared_part;
    
      if(WLIN0.size()==0) WLIN0.swap(shared_part);
      if(WLIN1.size()==0) WLIN1.swap(shared_part);

      //if((WLIN0+WLIN1).is_one() || WLIN0.is_one() || WLIN1.is_one()){
      if((WLIN0+shared_part).is_one() || (WLIN1+shared_part).is_one()) {
        //clause is SAT!
        SAT_dl_count = {0, 1};
        //swap into first position -- remove all other linerals!
        shared_part.clear();
        linerals[0].clear(); linerals[0].add_one();
        idx[0] = 0;
        linerals.resize(1);
        lineral_dl_count0.resize(1, {0,0});
        lineral_t_pos.resize(1, (var_t)-1);
        return cls_upd_ret::SAT;
      } else if((WLIN0+shared_part).is_zero() || (WLIN1+shared_part).is_zero()) {
      //if((WLIN0+WLIN1).is_zero() || WLIN0.is_zero() || WLIN1.is_zero()) {
        if(WLIN0.is_zero()) swap_wl(); //ensure that WLIN0 is non-zero (if possible)
        //one of the watched linerals should be removed!
        WLIN1.clear();
        WLIN0 += shared_part;
        shared_part.clear();
        remove_zero_lineral(idx[1]);
        if(linerals.size()>1) {
          idx[1] = (idx[0]==1) ? 0 : 1;
          continue;
        }
        assert(size()==1);
        ws[0] = 0;
        ptr_cache[0] = WLIN0.size()>0 ? ptr_(idx[0], ws[0]) : 0;
        return cls_upd_ret::UNIT;
      } else {
        //clause is neither SAT nor UNIT --> NONE
        ws[0] = 0;
        ws[1] = 0;
        ptr_cache[0] = ptr_(idx[0],ws[0]);
        ptr_cache[1] = ptr_(idx[1],ws[1]);
        return cls_upd_ret::NONE;
      }
    }
    
    if(WLIN0.is_zero()) {
      remove_zero_lineral(idx[0]);
      WLIN1 += shared_part;
      shared_part.clear();
    }
    if(WLIN1.is_zero()) {
      remove_zero_lineral(idx[1]);
      WLIN0 += shared_part;
      shared_part.clear();
    }
    assert(size()>=2);

    if(WLIN0.is_one()) swap_wl();
    if(WLIN1.is_one()) {
      //set SAT_dl_count s.t. clause is satisfied already at dl 0
      SAT_dl_count = {0, 1};
      return cls_upd_ret::SAT;
    }
   
    assert( assert_data_struct() );
    
    return cls_upd_ret::NONE;
  };

  /**
   * @brief updates cls_watch and watch_list according to current alpha (and requires dl_count and dl)
   * @note should only be used when new clauses are added!
   *
   * @param alpha current bool3-assignment
   * @param alpha_dl dl of alpha-assignments
   * @param dl_count current dl_count
   * @return cls_upd_ret SAT if cls does not need any further updates (i.e. it is a unit or satisfied), UNIT if cls became unit just now (includes UNSAT case, i.e., unit 1), NONE otherwise
   */
  cls_upd_ret init(const vec<bool3> &alpha, const vec<var_t> &alpha_dl, const vec<var_t> &alpha_trail_pos, const vec<dl_c_t> &dl_count) {
    // check if clause needs any processing
    if (!is_active(dl_count)) {
      assert(is_sat(dl_count) || is_unit(dl_count));
      return is_sat(dl_count) ? cls_upd_ret::SAT : cls_upd_ret::UNIT; // NOTE here it might also be a UNIT, but it did not become one by this update!
    }

    // check if -- and which ws need to be updated
    if (alpha[ptr_ws(0)] == bool3::None && alpha[ptr_ws(1)] == bool3::None) {
      // nothing needs to be updated!
      if (is_none(dl_count))
        return cls_upd_ret::NONE; // TODO these next two cases should never occur, or??
      else if (is_sat(dl_count))
        return cls_upd_ret::SAT;
      else if (is_unit(dl_count))
        return cls_upd_ret::UNIT;
    }

    if(alpha[ptr_ws(1)] == bool3::None) {
      [[maybe_unused]] const auto [new_w, _] = advance(alpha, alpha_dl, alpha_trail_pos, dl_count);
      assert(is_sat(dl_count) || is_unit(dl_count) || ptr_ws(0) == new_w);
      assert(watches(new_w));
      assert(assert_data_struct());
    }
    if(alpha[get_wl0()] == bool3::None) {
      swap_wl(); // if one of the watched literals is unassigned, ensure it is wl1

      [[maybe_unused]] const auto [new_w, _] = advance(alpha, alpha_dl, alpha_trail_pos, dl_count);
      assert(is_sat(dl_count) || is_unit(dl_count) || ptr_ws(0) == new_w);
      assert(watches(new_w));
      assert(assert_data_struct());

      assert(!is_sat(dl_count));

      if (is_unit(dl_count)) {
        // ensure we watch the lineral with highest dl!
        const var_t new_i = std::distance(lineral_dl_count0.begin(), std::max_element(lineral_dl_count0.begin(), lineral_dl_count0.end(),
                                                                              [](const auto &a, const auto &b) { return a.first < b.first; }));
        idx[0] = new_i;
        // esnure we watch the variable with hightest dl!
        const var_t new_w = std::distance(WLIN0.begin(), std::max_element(WLIN0.begin(), WLIN0.end(), 
                                                                              [&](const auto &a, const auto &b) { return alpha_trail_pos[a] < alpha_trail_pos[b]; }));
        ws[0] = new_w;
        ptr_cache[0] = ptr_(idx[0], ws[0]);
        std::swap(lineral_dl_count0[idx[0]], lineral_dl_count0[new_i]);
      }
    }

    if (is_active(dl_count))
      return cls_upd_ret::NONE;
    else if (is_sat(dl_count))
      return cls_upd_ret::SAT;
    else
      assert(is_unit(dl_count));
    return cls_upd_ret::UNIT;
  };

  
  //use only if all linerals are literals and pairwise distinct, and order w.r.t alpha_trail_pos!
  void init_dpll([[maybe_unused]] const vec<bool3> &alpha, const vec<var_t> &alpha_dl, const vec<var_t> &alpha_trail_pos, const vec<dl_c_t> &dl_count) {
    shared_part.clear();
    for(var_t i=0; i<size(); ++i) {
      const var_t& lt = linerals[i].LT();
      lineral_t_pos[i] = alpha_trail_pos[ lt ];
      lineral_dl_count0[i] = {alpha_dl[lt], dl_count[ alpha_dl[lt] ]};
    }
    if(size()>=1) { idx[0]=(size()-1); ptr_cache[0]=linerals[(size()-1)].LT(); };
    if(size()>=2) { idx[1]=(size()-2); ptr_cache[1]=linerals[(size()-2)].LT(); };

    assert( assert_data_struct(alpha, alpha_trail_pos, dl_count) );
  }

  std::string to_str() const {
    if (size() == 0)
      return "1";
    if (size() == 1) {
      assert(shared_part.is_zero());
      return WLIN0.plus_one().to_str();
    }
    std::string out;
    for (var_t i = 0; i < linerals.size(); ++i) {
      if(i==idx[0] || i==idx[1]) out += (shared_part+linerals[i]).plus_one().to_str() + " ";
      else out += linerals[i].plus_one().to_str() + " ";
    }
    out.erase(out.end() - 1);
    return out;
  };

  std::string to_xnf_str() const {
    if (linerals.empty())
      return "";
    if (linerals.size() == 1)
      return WLIN0.plus_one().to_xnf_str();
    std::string out;
    for (var_t i = 0; i < linerals.size(); ++i) {
      if(i==idx[0] || i==idx[1]) out += (shared_part+linerals[i]).plus_one().to_xnf_str() + " ";
      if(i==idx[0] || i==idx[1]) continue;
      out += linerals[i].plus_one().to_xnf_str() + " ";
    }
    out.erase(out.end() - 1);
    return out;
  };

  cls to_cls() const {
    vec<lineral> linerals_cpy(linerals);
    if(size()>0) linerals_cpy[idx[0]] += shared_part;
    if(size()>1) linerals_cpy[idx[1]] += shared_part;
    return cls( std::move( lin_sys( std::move(linerals_cpy) ) ) );
  };

  const lit_watch &get_wl0() const { return ptr_ws(0); };
  const lit_watch &get_wl1() const { return ptr_ws(1); };

  /**
   * @brief determines if cls is currently satsified
   *
   * @param dl_count current dl_count of solver
   * @return true iff cls is satisfied under current alpha
   */
  inline bool is_sat(const vec<dl_c_t> &dl_count) const {
    return (dl_count[SAT_dl_count.first] == SAT_dl_count.second);
  }
  
  /**
   * @brief returns if it is known that cls is satsified on dl0
   *
   * @return true iff it is known that cls is satisfied on dl0
   */
  inline bool is_sat0() const {
    return SAT_dl_count.first == 0 && SAT_dl_count.second == 1;
  }

  /**
   * @brief determines if cls is unit at current dl_count
   *
   * @param dl_count current dl_count of solver
   * @return true iff cls is evaluates to unit (including 1, i.e., unsat!)
   */
  inline bool is_unit(const vec<dl_c_t> &dl_count) const {
    return !is_sat(dl_count) && (size()<=1 || dl_count[lineral_dl_count0[idx[1]].first] == lineral_dl_count0[idx[1]].second);
  }
  
  /**
   * @brief determines if cls is a unit cls
   *
   * @return true iff cls is a unit
   */
  inline bool is_unit() const {
    assert( size()<=1 || WLIN0!=WLIN1 ); //either size is small OR we have two distinct linerals
    return size()<=1;
  }

  /**
   * @brief returns the lvl at which the clss is unit
   * @note assumes that cls is unit at current dl!
   *
   * @return var_t lvl at which cls is unit
   */
  inline var_t get_unit_at_lvl() const {
    return size() <= 1 ? 0 : lineral_dl_count0[idx[1]].first;
  }

  /**
   * @brief computes the LBD (literal-block-distance) of the lineral; i.e., the number of different dl's occuring in idxs
   * 
   * @param alpha_dl current alpha dl
   * @return var_t LBD value
   */
  var_t LBD(const vec<var_t>& alpha_dl) const {
    std::set<var_t> l;
    //for(const auto& [lvl,lvl_c] : lineral_dl_count0) {
    //  l.insert(lvl);
    //}
    for(const auto& lin : linerals) {
      for(const auto& i : lin.get_idxs_()) {
        l.insert(alpha_dl[i]);
      }
      for(const auto& i : shared_part) {
        l.insert(alpha_dl[i]);
      }
    }
    return l.size();
  };

#ifndef NDEBUG
  var_t compute_unit_assigning_lvl(const vec<var_t>& alpha_dl) const {
    return size()==0 ? 0 : ( size() == 1 ? WLIN0.get_assigning_lvl(alpha_dl) : std::max( shared_part.get_assigning_lvl(alpha_dl), WLIN1.get_assigning_lvl(alpha_dl) ) );
  }
#endif

  /**
   * @brief returns the lvl at which the clss is unit AND the unit is assigning
   * @note requires that both is indeed the case!
   *
   * @param alpha_dl dl of alpha-assignments
   *
   * @return var_t lvl at which cls is unit and the unit is assigning
   */
  inline var_t get_assigning_lvl(const vec<var_t>& alpha_dl) const {
    return (size()==0) ? 0 : std::max(get_unit_at_lvl(), WLIN0.get_assigning_lvl(alpha_dl));
  }

  inline bool is_inactive(const vec<dl_c_t> &dl_count) const {
    return is_sat(dl_count) || is_unit(dl_count);
  }

  /**
   * @brief determines whether cls is active
   *
   * @param dl_count current dl_count of solver
   * @return true iff both literal_watches point to unassigned variables
   */
  inline bool is_active(const vec<dl_c_t> &dl_count) const {
    // if it is satisfied, then ws[0] points to assigned variable!
    return !is_inactive(dl_count);
  }

  /**
   * @brief determines if cls is neither sat nor unit
   *
   * @param dl_count current dl_count of solver
   * @return true iff cls is satisfied under current alpha
   */
  inline bool is_none(const vec<bool3> &alpha) const {
    return alpha[ptr_ws(0)] == bool3::None && alpha[ptr_ws(1)] == bool3::None;
  }

  inline bool is_none(const vec<dl_c_t> &dl_count) const {
    return !is_unit(dl_count) && !is_sat(dl_count);
  }

  /**
   * @brief check wether given ind is watched by cls
   *
   * @param ind indet to check
   * @return true if and only if ind is watched by cls
   */
  inline bool watches(const var_t &ind) const {
    return (ptr_ws(0) == ind) || (ptr_ws(1) == ind);
  }

  /**
   * @brief returns the unit if is_unit is true (i.e. returns the second lineral)
   *
   * @return lineral unit that this clause was reduced to
   */
  inline lineral get_unit() const { 
    return size()==0 ? lineral(0,false) : (WLIN0 + shared_part).add_one();
  };

  inline bool unit_contains(const var_t &ind) const {
    return shared_part[ind] || WLIN0[ind];
  }


  /**
   * @brief Get the dl at which the clause got inactive (i.e. unit or sat)
   *
   * @param dl_count current dl_count of solver
   * @return var_t lvl at which clause got inactive
   */
  inline var_t get_inactive_lvl(const vec<dl_c_t> &dl_count) const {
    assert(is_inactive(dl_count)); // implies is_unit(dl_count) OR is_sat(dl_count)
    return size()<=1 ? 0 : (is_sat(dl_count) ? SAT_dl_count.first : lineral_dl_count0[idx[1]].first);
  }

  /**
   * @brief returns number of stored linerals
   * @note beware: if clause is zero we have size()==1 and size()==0 means claus is one (!)
   * 
   * @return var_t number of linerals
   */
  virtual inline var_t size() const { return linerals.size(); };


  bool is_zero() const { return (size()==1 && WLIN0.is_one()); };

  var_t LT(const cls_size_t i) const { return linerals[i].LT(); };

  const vec<lineral> &get_linerals() const { return linerals; };
  
  vec<lineral> &get_linerals_() { return linerals; };

  bool assert_data_struct() const {
    assert(lineral_dl_count0.size() == size());
    assert(size() == lineral_t_pos.size());
    // sanity check to see whether ws[i] is actually contained in linerals[i]
    assert(size()==0 || WLIN0.is_constant() || std::find(WLIN0.begin(), WLIN0.end(), ptr_ws(0)) != WLIN0.end());
    assert(size()<2 || std::find(WLIN1.begin(), WLIN1.end(), ptr_ws(1)) != WLIN1.end());

    assert(size()<2 || ptr_ws(0) != ptr_ws(1));

    assert(size()==0 || size()==1 || !WLIN0.is_constant() || is_sat0());
    assert(size()<2 || !WLIN0.is_constant());

    // check that WLIN0 and WLIN1 share no inds!
    assert(size()<2 || WLIN0.shared_part(WLIN1).is_zero());

    // check ptr_cache
    assert(size()==0 || (size()==1 && WLIN0.is_constant()) || ptr_cache[0] == ptr_(idx[0], ws[0]));
    assert(size()<2 || ptr_cache[1] == ptr_(idx[1], ws[1]));

    // check size of linerals -- ensure it does not 'explode'
    assert( linerals.size() < ((int) 1) << 16);

    return true;
  };
#ifdef NDEBUG
  bool assert_data_struct([[maybe_unused]] const vec<bool3> &alpha, [[maybe_unused]] const vec<var_t> &alpha_trail_pos, [[maybe_unused]] const vec<dl_c_t> &dl_count) const { return true; }
#else
  bool assert_data_struct(const vec<bool3> &alpha, const vec<var_t> &alpha_trail_pos, const vec<dl_c_t> &dl_count) const {
    assert(is_unit(dl_count) || is_sat(dl_count) || alpha[ptr_ws(0)] == bool3::None);
    if (!is_unit(dl_count) && !WLIN0.is_one() && alpha[ptr_ws(0)] != bool3::None) {
      assert(is_sat(dl_count) || eval0(alpha) || (!eval0(alpha) && !eval1(alpha)));
    }
    if(is_sat(dl_count)) {
      assert(dl_count[SAT_dl_count.first] == SAT_dl_count.second);
      assert_slow(to_cls().reduced(alpha).is_zero());
    }
    if( size()>0 && dl_count[lineral_dl_count0[idx[0]].first] == lineral_dl_count0[idx[0]].second ) assert( !eval0(alpha) );
    if( size()>1 && dl_count[lineral_dl_count0[idx[1]].first] == lineral_dl_count0[idx[1]].second ) assert( !eval1(alpha) || is_unit(dl_count) );
    for(var_t i = 0; i<size(); ++i) {
      if(i==idx[0] || i==idx[1]) continue;
      if( dl_count[lineral_dl_count0[i].first] == lineral_dl_count0[i].second ) assert( linerals[i].eval(alpha) );
    }

    //check lineral_t_pos
    for(var_t i = 0; i<size(); ++i) {
      if(i==idx[0] || i==idx[1]) continue;
      if(dl_count[lineral_dl_count0[i].first] == lineral_dl_count0[i].second && !linerals[i].is_zero()) assert( linerals[i].get_watch_var(alpha_trail_pos).first == lineral_t_pos[i] );
    }
    if(idx[0]<size() && dl_count[lineral_dl_count0[idx[0]].first] == lineral_dl_count0[idx[0]].second && !linerals[idx[0]].is_zero())
      assert( (linerals[idx[0]]+shared_part).get_watch_var(alpha_trail_pos).first  == lineral_t_pos[idx[0]] );
    if(idx[1]<size() && dl_count[lineral_dl_count0[idx[1]].first] == lineral_dl_count0[idx[1]].second && !linerals[idx[1]].is_zero())
      assert( (linerals[idx[1]]+shared_part).get_watch_var(alpha_trail_pos).first  == lineral_t_pos[idx[1]] );

    assert( size()<2 || is_sat(dl_count) || alpha_trail_pos[ptr_cache[0]] >= alpha_trail_pos[ptr_cache[1]] );

    if(is_unit(dl_count) && size()>1) {
      //ensure that idx[1] points to second-highest alpha_trail_pos!
      assert( lineral_t_pos[idx[0]] > lineral_t_pos[idx[1]] );
      for(var_t j=0; j<size(); ++j) {
        if(j==idx[0] || j==idx[1]) continue;
        assert( lineral_t_pos[idx[1]] >= lineral_t_pos[j] );
      }
      //note: 
    }

    return assert_data_struct();
  };
#endif

  cls_watch& operator=(const cls_watch &o) = default;

  cls_watch& operator=(cls_watch &&o) = default;
};
