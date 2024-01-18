#pragma once

#include "../misc.hpp"
#include "xlit.hpp"
#include "xcls.hpp"
#include "xsys.hpp"
#include <list>
#include <set>
#include <m4ri/m4ri.h>
#include "xlit_watch.hpp"

using lit_watch = var_t;
  
/**
 * @brief return type for update of xcls_watch
 */
enum class xcls_upd_ret {
  SAT,
  UNIT,
  NONE
};

// watch xcls
class xcls_watch
{
private:
  /**
   * @brief lits in the xlits that form a generating set for the associated vector space
   */
  vec<xlit> xlits;
  // TODO would it be better to store xlits NOT as objects of class xlit, but as UNSORTED vecs of var_t's ??

  /**
   * @brief shared part of xlits[0] and xlits[1]
   */
  xlit shared_part;

  /**
   * @brief xlit_dl_counts_1[i] tells in which dl and at what count xlit[i] was last evaluated to be 0 ({0,0} default)
   */
  vec<std::pair<var_t, dl_c_t>> xlit_dl_count0;

  /**
   * @brief xlit_dl_counts_0 tells in which dl the cls is 0, i.e., SAT
   */
  std::pair<var_t, dl_c_t> SAT_dl_count = {0,0};

  /**
   * @brief literal watches; offset into idxs-sets of xlits[0] and xlits[1]
   */
  lit_watch ws[2];

  /**
   * @brief cache watched vars
   */
  var_t ptr_cache[2];

  // flags
  /**
   * @brief indicates if clause is irredundant; be default all clauses are irredundant (and cannot be removed!)
   */
  bool irredundant = true;

  /**
   * @brief indicates if clause should be removed on next cleanup
   */
  bool delete_on_cleanup = false;

  /**
   * @brief indicates the dl at which the cls is unit AND the unit is assigning!
   * @note only changed externally AND when 'resolve' is called!
   */
  var_t assigning_lvl = (var_t)-1;

  /**
   * @brief initializes shared_part, ws[0], ws[1] and ptr_cache
   * @note assumes that xlits are already set; wl_it must still be initiated!
   */
  void init() {
    // init xlit_dl_counts
    xlit_dl_count0.resize(xlits.size(), {0, 0});


    if (xlits.size() == 0) {
      shared_part.clear();
      return;
    } else if (xlits.size() == 1) {
      ws[0] = 0;
      ptr_cache[0] = ptr_(0, ws[0]);
      shared_part.clear();
      return;
    }

    assert(xlits.size() > 1);
    // init shared
    shared_part = xlits[0].shared_part(xlits[1]);
    // rm shared part from xlits[0] and xlits[1]
    xlits[0] += shared_part;
    xlits[1] += shared_part;

    // ensure that xlits[0] and xlits[1] are non-empty
    assert(xlits[0].size() > 0 && xlits[1].size() > 0);
    // if xlits[0] is empty: std::swap(xlits[0],shared_part); xlits[1].add_one();
    // if xlits[1] is empty: std::swap(xlits[1],shared_part); xlits[0].add_one();

    // init ws
    ws[0] = 0;
    ws[1] = 0;
    ptr_cache[0] = ptr_(0, ws[0]);
    ptr_cache[1] = ptr_(1, ws[1]);
    assert(get_wl0() != get_wl1());
  }

  var_t ptr_(const cls_size_t &i, const var_t val) const {
    if(val == 0 && xlits[i].size()==0) return 0;
    assert(val < xlits[i].size());
    // return xlits[i].get_idxs_().at(val);
    return xlits[i].get_idxs_()[val];
  }

  const var_t &ptr_ws(const cls_size_t &i) const {
    assert(ptr_(i, ws[i]) == ptr_cache[i]);
    return ptr_cache[i];
  }

  /**
   * @brief advances ws[0], requires that alpha[ ptr_ws(0) ] != bool3::None
   *
   * @param alpha current bool3-alpha
   * @param alpha_dl dl of alpha-assignments
   * @param dl_count current dl_count
   * @return pair<var_t,xcls_upd_ret> upd_ret is SAT if xcls became satisfied, UNIT if xcls became unit (includes UNSAT case, i.e., unit 1), NONE otherwise; var_t indicates changed watched literal (if non-zero)
   */
  std::pair<var_t, xcls_upd_ret> advance(const vec<bool3> &alpha, const vec<var_t> &alpha_dl, const vec<dl_c_t> &dl_count) {
    assert(alpha[ptr_ws(0)] != bool3::None);

    // TODO shorter & cleaner impl with c++20 ranges?
    // vec<std::ranges::subrange<lit_watch, xlit::iterator, std::ranges::subrange_kind::sized>> tmp{ std::ranges::subrange(ws[i], xlits[i].end()), std::ranges::subrange(xlits[i].begin(), ws[i]) };
    // auto r = tmp | std::ranges::views::join;

    // advance iterator as long as there is another unassigned idx to point to
    auto new_w = ws[0];
    while ((new_w < (var_t)xlits[0].size()) && (alpha[ptr_(0, new_w)] != bool3::None)) { ++new_w; }
    if (new_w == (var_t)xlits[0].size()) /*wrap around end if necessary */ new_w = 0;
    while ((alpha[ptr_(0, new_w)] != bool3::None) && (new_w != ws[0])) { ++new_w; }
    // advancing done; now new_w points to ws[0] or at an unassigned idx -- or again to ws[0] (!)

    if (new_w != ws[0]) {
      assert(alpha[ptr_(0, new_w)] == bool3::None);
      ws[0] = new_w;
      ptr_cache[0] = ptr_(0, ws[0]);
      assert(assert_data_struct());
      return {ptr_ws(0), xcls_upd_ret::NONE};
    }
    // now xlits[0] is constant under alpha! ...i.e. check shared part
    new_w = 0;
    while ((new_w < (var_t)shared_part.size()) && (alpha[shared_part.get_idxs_()[new_w]] != bool3::None)) ++new_w;
    if (new_w != (var_t)shared_part.size()) {
      // lit in shared_part can be watched!
      // rewrite xlits[1]:
      xlits[0].swap(shared_part);
      ws[0] = new_w;
      ptr_cache[0] = ptr_(0, ws[0]);
      assert(assert_data_struct());
      return {ptr_ws(0), xcls_upd_ret::NONE};
    }

    // now shared_part can also be evaluated --> xlits[0]+shared_part can be evaluated!
    if (xlits[0].eval(alpha) ^ shared_part.eval(alpha)) {
      // xlits[0]+shared_part evaluates to 1
      // corresponding lineral is 0 --> xclause does not need to be watched any longer!
      // do not change watches!
      SAT_dl_count = {alpha_dl[ptr_ws(0)], dl_count[alpha_dl[ptr_ws(0)]]};
      assert(!is_active(dl_count)); // clause is no longer active!
      assert(assert_data_struct());
      return {ptr_ws(0), xcls_upd_ret::SAT};
    }
    // now xlits[0]+shared_part evaluates to 1 under alpha, i.e., we check whether a different xlit can be watched.
    xlit_dl_count0[0] = {alpha_dl[ptr_ws(0)], dl_count[alpha_dl[ptr_ws(0)]]};

    // note that xlits[0] and xlits[1] are always the xlits that are watched, i.e., start search from xlits[2] (!)
    cls_size_t new_i = 2;
    for (; new_i < xlits.size(); ++new_i) {
      assert(new_i < ( 1 << (CHAR_BIT * sizeof(cls_size_t)) ) );
      // skip xlits which evaluate to 1 in current search tree
      if (dl_count[xlit_dl_count0[new_i].first] == xlit_dl_count0[new_i].second)
        continue;

      //rm xlits[new_i] if it is just zero!
      if(xlits[new_i].is_zero()) {
        xlits[new_i].swap(xlits.back());
        std::swap(xlit_dl_count0[new_i], xlit_dl_count0.back());
        xlits.resize( xlits.size()-1 );
        xlit_dl_count0.resize( xlit_dl_count0.size()-1 );
        //repeat with same new_i
        --new_i;
        continue;
      } else if(xlits[new_i].is_one()) {
        //leave watches untouched; but set SAT_dl_count s.t. clause is satisfied already at dl 0!
        SAT_dl_count = {0, 1};
        return {ptr_ws(0), xcls_upd_ret::SAT};
      }
      assert(!xlits[new_i].is_one());

      // find lit that was assigned at highest dl (req for proper backtracking!) -- or find unassigned lit!
      new_w = 0;
      var_t max_w = 0;
      while (new_w < (var_t)xlits[new_i].size() && alpha[ptr_(new_i, new_w)] != bool3::None) {
        if (alpha_dl[ptr_(new_i, new_w)] > alpha_dl[ptr_(new_i, max_w)]) max_w = new_w;
        ++new_w;
      }
      new_w = ( new_w == (var_t)xlits[new_i].size() ) ? max_w : new_w;
      if (ptr_(new_i, new_w) == ptr_ws(1) || ( xlits[new_i][ptr_ws(1)] && (xlits[1][ptr_(new_i,new_w)] || shared_part[ptr_(new_i,new_w)]) ) ) {
        //add xlits[1] to xlits[new_i] to eliminate shared part in xlits[new_i]
        xlits[new_i] += xlits[1];
        xlits[new_i] += shared_part;
        // repeat with same new_i
        --new_i;
        continue;
      }
      if (alpha[ptr_(new_i,new_w)] == bool3::None ) {
        //if ptr_(new_i,new_w) AND ptr_(1,ws[1]) both are in shared part of xlits[1] AND xlits[new_i]; rewrite xlits[new_i] and start over
        // new xlit to be watched found --> change watched xlit and return SAT
        const auto wl0 = ptr_(new_i, new_w);
        const auto wl1 = ptr_ws(1);
        xlits[0] += shared_part;
        xlits[1] += shared_part;
        xlits[0].swap(xlits[new_i]); // ensures that no iterators are invalidated
        // fix dl_count vals
        std::swap(xlit_dl_count0[0], xlit_dl_count0[new_i]);
        // fix shared_parts && update ws[0] and ws[1] accordingly!
        shared_part = xlits[0].shared_part(xlits[1]);
        xlits[0] += shared_part;
        xlits[1] += shared_part;
        // fix ws[0] AND ws[1]!
        ws[0] = std::distance(xlits[0].get_idxs_().begin(), std::lower_bound(xlits[0].get_idxs_().begin(), xlits[0].get_idxs_().end(), wl0));
        //if ptr_(0,ws[0]) is NOT wl0, then we need to rewrite xlits[0]
        if(ws[0] >= xlits[0].size() || ptr_(0,ws[0])!=wl0 ) {
          xlits[0].swap(shared_part);
          assert( xlits[1][wl1] );
          ws[0] = std::distance(xlits[0].get_idxs_().begin(), std::lower_bound(xlits[0].get_idxs_().begin(), xlits[0].get_idxs_().end(), wl0));
        }
        ws[1] = std::distance(xlits[1].get_idxs_().begin(), std::lower_bound(xlits[1].get_idxs_().begin(), xlits[1].get_idxs_().end(), wl1));
        if(ws[1] >= xlits[1].size() || ptr_(1,ws[1])!=wl1 ) {
          xlits[1].swap(shared_part);
          assert( xlits[0][wl0] );
          ws[1] = std::distance(xlits[1].get_idxs_().begin(), std::lower_bound(xlits[1].get_idxs_().begin(), xlits[1].get_idxs_().end(), wl1));
        }
        ptr_cache[0] = ptr_(0, ws[0]);
        ptr_cache[1] = ptr_(1, ws[1]);
        assert(ptr_cache[0] == wl0 && ptr_cache[1] == wl1);
        assert(is_active(dl_count));
        return {ptr_ws(0), xcls_upd_ret::NONE};
      } else {
        // xlits[new_i] evaluates to a constant; this is only useful if xlits[new_i].eval(alpha) is 1, i.e., the clause is SAT
        const var_t dl_assigned = alpha_dl[ptr_(new_i, new_w)];
        if(!xlits[new_i].eval(alpha)) {
          //note: we can leave all watches as they were!
          SAT_dl_count = {dl_assigned, dl_count[dl_assigned]};
          
          assert(!is_active(dl_count));
          assert(is_sat(dl_count));
          assert(assert_data_struct());
          assert(assert_data_struct(alpha, dl_count));
          return {ptr_ws(0), xcls_upd_ret::SAT};
        }
        // now xlits[new_i] evaluates to 0 --> choose different new_i
        xlit_dl_count0[new_i] = {dl_assigned, dl_count[dl_assigned]};

        assert( dl_assigned <= alpha_dl[ptr_ws(0)] );
      }
    }
    // if the above did not yet return, then all xlits (except xlits[1]) evaluate to 1 under alpha, i.e., we learn a unit clause!
    // moreover, no watch literals need to be updated! (ws[0] is already at highest dl and xlits[0] evaluates to 1!)
    assert(!is_active(dl_count));
    assert(is_unit(dl_count));
    assert(assert_data_struct());
    return {ptr_ws(0), xcls_upd_ret::UNIT};
  };

  /**
   * @brief swap watched literals
   */
  void swap_wl() {
    xlits[0].swap(xlits[1]);
    std::swap(ws[0], ws[1]);
    std::swap(ptr_cache[0], ptr_cache[1]);
    std::swap(xlit_dl_count0[0], xlit_dl_count0[1]);
  }

public:
  xcls_watch() noexcept {
    ws[0] = 0; ws[1] = 0;
    ptr_cache[0] = 0; ptr_cache[1] = 0;
    xlits.emplace_back( xlit().add_one() );
    xlit_dl_count0.resize(1, {0,0});
  };

  xcls_watch(const xlit &l1, const xlit &l2) noexcept : xlits(vec<xlit>({l1, l2})), xlit_dl_count0({{0,0},{0,0}}) {
    xlits[0].add_one(); xlits[1].add_one();
    assert(!l1.is_one() && !l1.is_zero());
    assert(!l2.is_one() && !l2.is_zero());
    init();
  };

  xcls_watch(const xcls &cl) noexcept : xlits(vec<xlit>(cl.get_ass_VS().get_xlits().begin(), cl.get_ass_VS().get_xlits().end())), xlit_dl_count0(cl.deg(),{0,0}) {
    init();
  };

  xcls_watch(xcls &&cl) noexcept {
    xlits = vec<xlit>();
    xlits.reserve(cl.deg());
    for (auto lit : cl.get_ass_VS().get_xlits()) {
      xlits.emplace_back(std::move(lit));
    }
    xlit_dl_count0.resize(xlits.size(), {0,0});
    init();
  };

  xcls_watch(const xcls_watch &o) noexcept : xlits(o.xlits), shared_part(o.shared_part), xlit_dl_count0(o.xlit_dl_count0), SAT_dl_count(o.SAT_dl_count), irredundant(o.irredundant), delete_on_cleanup(o.delete_on_cleanup), assigning_lvl(o.assigning_lvl) {
    ws[0] = o.ws[0];
    ws[1] = o.ws[1];
    ptr_cache[0] = o.ptr_cache[0];
    ptr_cache[1] = o.ptr_cache[1];
  };

  xcls_watch(xcls_watch &&o) noexcept : xlits(std::move(o.xlits)), shared_part(std::move(o.shared_part)), xlit_dl_count0(std::move(o.xlit_dl_count0)), SAT_dl_count(std::move(o.SAT_dl_count)), irredundant(o.irredundant), delete_on_cleanup(o.delete_on_cleanup), assigning_lvl(std::move(o.assigning_lvl)) {
    ws[0] = o.ws[0];
    ws[1] = o.ws[1];
    ptr_cache[0] = o.ptr_cache[0];
    ptr_cache[1] = o.ptr_cache[1];
  };

  xcls_watch(const xlit_watch& lin, const vec<var_t>& alpha_dl) noexcept {
    irredundant = false;
    delete_on_cleanup = false;
    
    xlits.emplace_back( lin );
    xlits[0].add_one();
    // init xlit_dl_count
    xlit_dl_count0.emplace_back(0,0);
    SAT_dl_count = {0,0};
    
    shared_part.clear();

    ws[0] = std::distance(xlits[0].get_idxs_().begin(), std::lower_bound(xlits[0].get_idxs_().begin(), xlits[0].get_idxs_().end(), lin.get_wl0()));
    ptr_cache[0] = lin.get_wl0();
    assigning_lvl = lin.get_assigning_lvl(alpha_dl);
  }

  xcls_watch(const xsys &lits) noexcept {
    assert(lits.dim() >= 1);
    xlits = vec<xlit>(lits.get_xlits().begin(), lits.get_xlits().end());
    xlit_dl_count0.resize(xlits.size(), {0,0});
    init();
  };

  void set_redundancy(const bool red) { irredundant = !red; };
  void mark_for_removal() { if (!irredundant) { delete_on_cleanup = true; } };
  bool is_marked_for_removal() const { return delete_on_cleanup; };
  bool is_irredundant() const { return irredundant; };

  /**
   * @brief evals the 0-th watched literal at alpha
   *
   * @param alpha current bool3-assignments
   *
   * @return true iff alpha( xlits[0]+shared_part ) = 0
   */
  bool eval0(const vec<bool3> &alpha) const {
    return xlits[0].eval(alpha) ^ shared_part.eval(alpha);
  }

  /**
   * @brief evals the 1-th watched literal at alpha
   *
   * @param alpha current bool3-assignments
   *
   * @return true iff alpha( xlits[1]+shared_part ) = 0
   */
  bool eval1(const vec<bool3> &alpha) const {
    return xlits[1].eval(alpha) ^ shared_part.eval(alpha);
  }
  
  /**
   * @brief removes literal upd_lt from lineral, if is present
   * 
   * @param upd_lt literal to be removed
   * @param val value that is assigned to literal
   * @return true iff clause became inactive, i.e., SAT
   */
  bool rm(const var_t upd_lt, const bool3 val) {
    assert( !watches(upd_lt) );
    bool ret = false;
    //rm from unwatched xlits
    shared_part.rm(upd_lt, val);
    for(var_t idx=2; idx<xlits.size(); ++idx) {
      xlits[idx].rm(upd_lt, val);
      if(xlits[idx].is_one()) {
        //now clause becomes SAT!
        SAT_dl_count = {0,1};
        ret = true;
      } else if (xlits[idx].is_zero()) {
        //xlits[idx] can now be ignored, remove!
        //swap xlits[idx] and xlits.back()
        xlits[idx].swap(xlits.back());
        std::swap( xlit_dl_count0.back(), xlit_dl_count0[idx] );
        xlits.pop_back();
        xlit_dl_count0.pop_back();
      }
    }
    //rm from xlits[0]
    if( xlits[0].rm(upd_lt, val) ) {
      //adapt ws[0]
      if(ptr_cache[0] > upd_lt) ws[0]--;
      assert(ptr_(0,ws[0]) == ptr_cache[0]);
    }
    if( xlits.size()>0 && xlits[1].rm(upd_lt, val) ) {
      //adapt ws[0]
      if(ptr_cache[1] > upd_lt) ws[1]--;
      assert(ptr_(1,ws[1]) == ptr_cache[1]);
    }

    assert(assert_data_struct());

    return ret;
  }

  /**
   * @brief updates xcls_watch and watch_list according to the new assigned literal lit, dl_count, dl and alpha.
   *
   * @param new_lit literal that was newly assigned
   * @param alpha current bool3-assignment
   * @param alpha_dl dl of alpha-assignments
   * @param dl_count current dl_count
   * @param dl current dl
   * @return var_t,xcls_upd_ret upd_ret is SAT if xcls does not need any further updates (i.e. it is a unit or satisfied), UNIT if xcls became unit just now (includes UNSAT case, i.e., unit 1), NONE otherwise; var_t is the new-watched literal (or the same if unchanged!)
   */
  std::pair<var_t, xcls_upd_ret> update(const var_t &new_lit, const vec<bool3> &alpha, const vec<var_t> &alpha_dl, const vec<dl_c_t> &dl_count) {
    // check if clause needs any processing
    if (!is_active(dl_count)) {
      assert(is_sat(dl_count) || is_unit(dl_count));
      return {new_lit, xcls_upd_ret::SAT}; // NOTE here it might also be a UNIT, but it did not become one by this update!
    }
    // exactly one of { ptr_ws(0), ptr_ws(1) } must be new_lit
    assert((ptr_ws(0) == new_lit) ^ (ptr_ws(1) == new_lit));
    // swap s.t. ptr_ws(0) == new_lit
    if (ptr_ws(0) != new_lit)
      swap_wl();
    assert(ptr_ws(0) == new_lit);

    // advance ws[0]
    const auto [new_w, upd] = advance(alpha, alpha_dl, dl_count);
    assert(is_sat(dl_count) || is_unit(dl_count) || ptr_ws(0) != new_lit);
    assert(watches(new_w));
    assert(assert_data_struct());

    // assert correct return value!
    if (upd == xcls_upd_ret::NONE) {
      // assert( is_none(alpha) ); //leads to error: it might be SAT but ONLY after all updates have been performed! (i.e. if xlits[0] AND xlits[1] needs an update!)
      assert(is_none(dl_count));
      return {new_w, upd};
    } else if (upd == xcls_upd_ret::SAT) {
      assert(is_sat(dl_count));
      return {new_w, upd};
    } else {
      assert(upd == xcls_upd_ret::UNIT);
      assert(is_unit(dl_count));
      return {new_w, upd};
    }
  };

  /**
   * @brief updates xcls_watch and watch_list according to current alpha (and requires dl_count and dl)
   * @note should only be used when new clauses are added!
   *
   * @param alpha current bool3-assignment
   * @param alpha_dl dl of alpha-assignments
   * @param dl_count current dl_count
   * @return xcls_upd_ret SAT if xcls does not need any further updates (i.e. it is a unit or satisfied), UNIT if xcls became unit just now (includes UNSAT case, i.e., unit 1), NONE otherwise
   */
  xcls_upd_ret init(const vec<bool3> &alpha, const vec<var_t> &alpha_dl, const vec<dl_c_t> &dl_count) {
    // check if clause needs any processing
    if (!is_active(dl_count)) {
      assert(is_sat(dl_count) || is_unit(dl_count));
      return is_sat(dl_count) ? xcls_upd_ret::SAT : xcls_upd_ret::UNIT; // NOTE here it might also be a UNIT, but it did not become one by this update!
    }

    // check if -- and which ws need to be updated
    if (alpha[ptr_ws(0)] == bool3::None && alpha[ptr_ws(1)] == bool3::None) {
      // nothing needs to be updated!
      if (is_none(dl_count))
        return xcls_upd_ret::NONE; // TODO these next two cases should never occur, or??
      else if (is_sat(dl_count))
        return xcls_upd_ret::SAT;
      else if (is_unit(dl_count))
        return xcls_upd_ret::UNIT;
    }

    [[maybe_unused]] const auto [new_w, _] = advance(alpha, alpha_dl, dl_count);
    assert(is_sat(dl_count) || is_unit(dl_count) || ptr_ws(0) == new_w);
    assert(watches(new_w));
    assert(assert_data_struct());

    if (alpha[get_wl0()] == bool3::None) {
      swap_wl(); // if one of the watched literals is unassigned, ensure it is wl1

      advance(alpha, alpha_dl, dl_count);
      assert(is_sat(dl_count) || is_unit(dl_count) || ptr_ws(0) == new_w);
      assert(watches(new_w));
      assert(assert_data_struct());

      assert(!is_sat(dl_count));

      if (is_unit(dl_count)) {
        // ensure we watch the lineral with highest dl!
        const var_t new_i = std::distance(xlit_dl_count0.begin(), std::max_element(xlit_dl_count0.begin(), xlit_dl_count0.end(),
                                                                              [](const auto &a, const auto &b) { return a.first < b.first; }));
        xlits[0].swap(xlits[new_i]); // ensures that no iterators are invalidated
        // esnure we watch the variable with hightest dl!
        const var_t new_w = std::distance(xlits[0].begin(), std::max_element(xlits[0].begin(), xlits[0].end(), 
                                                                              [&](const auto &a, const auto &b) { return alpha_dl[a] < alpha_dl[b]; }));
        ws[0] = new_w;
        ptr_cache[0] = ptr_(0, ws[0]);
        std::swap(xlit_dl_count0[0], xlit_dl_count0[new_i]);
      }
    }

    if (is_active(dl_count))
      return xcls_upd_ret::NONE;
    else if (is_sat(dl_count))
      return xcls_upd_ret::SAT;
    else
      assert(is_unit(dl_count));
    return xcls_upd_ret::UNIT;
  };

  xcls_upd_ret resolve(const xcls_watch &rs_cls, const vec<bool3> &alpha, const vec<var_t> &alpha_dl, const vec<var_t> &alpha_trail_pos, const vec<dl_c_t> &dl_count, const vec<equivalence>& equiv_lits, const vec<var_t>& equiv_lits_dl, const bool opt = false) {
    if(size()==0) {
      xlits.emplace_back( xlit(0, true) );
      xlit_dl_count0.emplace_back( 0, dl_count[0] );
    }
    assert(size()>0);
    // fix unit part ('resolving' part)
    xlits[ (size()==1) ? 0 : 1 ] += rs_cls.get_unit();
    const auto [lvl,_,__] = xlits[ (size()==1) ? 0 : 1 ].get_watch_var(alpha_dl, alpha_trail_pos);
    //TODO do we need to set xlit_dl_count0 here at all?!
    if(lvl < dl_count.size()) {
      xlit_dl_count0[ (size()==1) ? 0 : 1 ] = {lvl, dl_count[lvl]};
    } else {
      xlit_dl_count0[ (size()==1) ? 0 : 1 ] = {0,0};
    }
    // add xlits from rs_cls to this
    if(rs_cls.size() == 1) {
      const auto ret = init_unit(alpha, alpha_dl, alpha_trail_pos, dl_count, equiv_lits, equiv_lits_dl);
      assert(ret == xcls_upd_ret::UNIT);
      assert(is_unit(dl_count));
      return ret;
    }
    //now rs_cls.size()>1
    std::copy(rs_cls.xlits.begin() + 2, rs_cls.xlits.end(), std::back_inserter(xlits));
    std::copy(rs_cls.xlit_dl_count0.begin() + 2, rs_cls.xlit_dl_count0.end(), std::back_inserter(xlit_dl_count0));

    xlits.emplace_back(rs_cls.xlits[0] + rs_cls.shared_part);
    xlit_dl_count0.emplace_back(rs_cls.xlit_dl_count0[0]);
    
    //const auto ret = init_unit_opt(alpha, alpha_dl, alpha_trail_pos, dl_count, equiv_lits, equiv_lits_dl, rs_cls.xlits.size());
    //const auto ret = init_unit(alpha, alpha_dl, alpha_trail_pos, dl_count, equiv_lits, equiv_lits_dl);
    const auto ret = opt ? init_unit_opt(alpha, alpha_dl, alpha_trail_pos, dl_count, equiv_lits, equiv_lits_dl, rs_cls.xlits.size()) : init_unit(alpha, alpha_dl, alpha_trail_pos, dl_count, equiv_lits, equiv_lits_dl);
    assert(ret == xcls_upd_ret::UNIT);
    assert(is_unit(dl_count));
    assert( assert_data_struct(alpha, dl_count) );
    return ret;
  }
  
  
  //tmp vars
  vec<var_t> xlit_idxs;

  /**
   * @brief inits this xcls_watch according to the current alpha, alpha_dl s.t. all invariants hold and it can be used with all other xcls_watches
   * @note should only be used when new clauses are added! && the new clause is UNIT under the current assignments!
   *
   * @param alpha current bool3-assignment
   * @param alpha_dl dl of alpha-assignments
   * @param alpha_trail_pos trail_pos of alpha-assignments
   * @param dl_count current dl_count
   * @param dl currenct dl
   * @return xcls_upd_ret SAT if xcls does not need any further updates (i.e. it is a unit or satisfied), UNIT if xcls became unit just now (includes UNSAT case, i.e., unit 1), NONE otherwise
   */
  xcls_upd_ret init_unit_opt(const vec<bool3> &alpha, const vec<var_t> &alpha_dl, const vec<var_t> &alpha_trail_pos, const vec<dl_c_t> &dl_count, const vec<equivalence>& equiv_lits, const vec<var_t>& equiv_lits_dl, const var_t idx_start_other_cls) {
    if (size() == 1) {
      //reduce xlit[0]
      xlits[0].reduce(alpha, alpha_dl, 0);
      xlits[0].reduce(equiv_lits, equiv_lits_dl, 0, alpha);
      //update watched variable
      ws[0] = std::get<2>( xlits[0].get_watch_var(alpha_dl, alpha_trail_pos) );
      ptr_cache[0] = ptr_(0, ws[0]);
      assigning_lvl = std::max( get_unit_at_lvl(), compute_unit_assigning_lvl(alpha_dl) );
      return xcls_upd_ret::UNIT;
    }
    assert(xlits.size()>1);
    // distribute shared_part
    xlits[0] += shared_part;
    xlits[1] += shared_part;
    shared_part.clear();

    // reduce all xlits at dl 0
    for (auto &l : xlits) {
      l.reduce(alpha, alpha_dl, 0);
      l.reduce(equiv_lits, equiv_lits_dl, 0, alpha);
    }

    if(idx_start_other_cls < xlits.size()) {
      assert(1 < idx_start_other_cls  && idx_start_other_cls < xlits.size());
      //decide which var to watch
      //TODO optimize!
      vec<var_t> tmp; 
      tmp.push_back(0);
      tmp.push_back(1);
      tmp.push_back(idx_start_other_cls);
      std::sort(tmp.begin(), tmp.end(),
                [&alpha_dl, &alpha_trail_pos, this](const var_t a, const var_t b)
                { const auto [a_dl, a_apos, a_] = xlits[a].get_watch_var(alpha_dl, alpha_trail_pos);
                  const auto [b_dl, b_apos, b_] = xlits[b].get_watch_var(alpha_dl, alpha_trail_pos);
                  return a_dl > b_dl || 
                    (a_dl == b_dl && a_apos > b_apos);
                });
      vec<var_t> pos; pos.reserve(xlits.size());
      for(var_t i=0; i<xlits.size(); ++i) pos.push_back(i);
      //swap xlits in correct order
      {
        var_t idx = 0;
        xlits[idx].swap(xlits[pos[tmp[idx]]]);
        std::swap(xlit_dl_count0[idx], xlit_dl_count0[pos[tmp[idx]]]);
        std::swap(pos[0], pos[tmp[idx]]);
      
        idx = 1;
        xlits[idx].swap(xlits[pos[tmp[idx]]]);
        std::swap(xlit_dl_count0[idx], xlit_dl_count0[pos[tmp[idx]]]);
        std::swap(pos[1], pos[tmp[idx]]);

        idx = idx_start_other_cls;
        xlits[idx].swap(xlits[pos[tmp[2]]]);
        std::swap(xlit_dl_count0[idx], xlit_dl_count0[pos[tmp[2]]]);
      }

      if(xlits[idx_start_other_cls].is_zero()) {
        //swap into last position and shorten clauses!
        xlits.back().swap(xlits[idx_start_other_cls]);
        std::swap(xlit_dl_count0[idx_start_other_cls], xlit_dl_count0.back());
        xlits.pop_back();
        xlit_dl_count0.pop_back();
      }
      if(xlits.size()>1 && xlits[1].is_zero()) {
        //swap into last position and shorten clauses!
        xlits.back().swap(xlits[1]);
        std::swap(xlit_dl_count0[1], xlit_dl_count0.back());
        xlits.pop_back();
        xlit_dl_count0.pop_back();
      }
      if(xlits[0].is_zero()) {
        if(size()>1) xlits.back().swap(xlits[1]);
        if(size()>1) std::swap(xlit_dl_count0[1], xlit_dl_count0.back());
        xlits.pop_back();
        xlit_dl_count0.pop_back();
      }
      if(size()==0) {
        assert(is_unit(dl_count));
        assigning_lvl = 0;
        return xcls_upd_ret::UNIT;
      }
      assert(!xlits[0].is_zero());
      const auto [lvl_unit, alpha_t_pos_unit, idx_unit] = xlits[0].get_watch_var(alpha_dl, alpha_trail_pos);
      ptr_cache[0] = xlits[0].get_idxs_()[idx_unit];

      if(size()==1) goto finalize;

      const auto [lvl, alpha_t_pos, idx] = xlits[1].get_watch_var(alpha_dl, alpha_trail_pos);
      ptr_cache[1] = xlits[1].get_idxs_()[idx];

      if(ptr_cache[0]==ptr_cache[1] || lvl_unit==lvl) goto full_reduction;
      if(std::count_if(xlit_dl_count0.begin(), xlit_dl_count0.end(), [&lvl](const std::pair<var_t,dl_c_t> lvl_dlc){ return lvl_dlc.first >= lvl; }) > 1) goto full_reduction;

      assert(std::count_if(xlits.begin(), xlits.end(), [&lvl,&alpha_dl,&alpha_trail_pos](const xlit& l){ return std::get<0>(l.get_watch_var(alpha_dl,alpha_trail_pos)) == lvl; }) == 1);

      goto finalize;
    }

    full_reduction:
    {
    // re-order occuring indets with decreasing dl
    std::set<var_t> tmp;
    for (const auto &l : xlits) {
      tmp.insert(l.get_idxs_().begin(), l.get_idxs_().end());
    }
    vec<var_t> idxs(tmp.begin(), tmp.end());
    std::sort(idxs.begin(), idxs.end(),
              [&alpha_dl, &alpha_trail_pos](const var_t &a, const var_t &b)
              { return alpha_dl[a] > alpha_dl[b] || (alpha_dl[a] == alpha_dl[b] && alpha_trail_pos[a] > alpha_trail_pos[b]); });
    // construct permutation maps
    vec<var_t> perm(alpha.size());
    vec<var_t> perm_inv(alpha.size());
    for (var_t i = 0; i < idxs.size(); ++i) {
      perm[idxs[i]] = i;
      perm_inv[i] = idxs[i];
    }

    const var_t n_vars = idxs.size();
    rci_t nrows = xlits.size();
    rci_t ncols = n_vars+1;

    mzd_t* M = mzd_init(nrows, ncols);
    assert( mzd_is_zero(M) );

    //fill with xlits
    rci_t r = 0;
    for(const auto& l : xlits) {
        if(l.is_zero()) continue;
        if(l.has_constant()) {
            mzd_write_bit(M, r, n_vars, 1);
        }
        for(const auto& i : l.get_idxs_()) {
            assert(i>0);
            assert(perm[i] < (var_t) ncols-1);
            mzd_write_bit(M, r, perm[i], 1);
        }
        ++r;
    }
    assert(r <= nrows); //reducing with alpha at dl 0 might reduce some xlits to 0

    //compute rref
    const rci_t rank = mzd_echelonize_m4ri(M, true, 0); //should we use mzd_echelonize instead?
    //read results
    vec<xlit> xlits_; xlits_.reserve(rank);
    for(rci_t r = 0; r<rank; ++r) {
        vec<var_t> idxs;
        for(rci_t c=0; (unsigned)c<n_vars; ++c) {
            if( mzd_read_bit(M, r, c) ) idxs.push_back(c+1);
        }
        xlits_.emplace_back( std::move(idxs), (bool) mzd_read_bit(M, r, n_vars), presorted::yes );
        if(xlits_.back().is_zero()) xlits_.pop_back();
    }
    mzd_free(M);

    //xlits_ must already be sorted w.r.t. lt!
    assert( std::is_sorted(xlits_.begin(), xlits_.end(), [](const xlit &a, const xlit &b) { return a.LT() < b.LT(); }) );

    // set xlit_dl_count0, since all except the first xlits must be satisfied by assumption
    xlit_dl_count0[0] = {0,0};
    for (var_t i = 1; i < xlits_.size(); ++i) {
      const var_t lvl = alpha_dl[ perm_inv[xlits_[i].LT()-1] ];
      assert( lvl<=alpha.size());
      xlit_dl_count0[i] = {lvl, dl_count[lvl]};
    }

    if(xlits_.size()==0) {
      xlits.clear();
      xlit_dl_count0.resize(xlits.size());
      assert(is_unit(dl_count));
      assigning_lvl = 0;
      return xcls_upd_ret::UNIT;
    }

    // now watch the first two xlits as usual
    const var_t wl0 = perm_inv[xlits_[0].LT()-1];
    const var_t wl1 = xlits_.size() > 1 ? perm_inv[xlits_[1].LT()-1] : -1;

    // translate xlits back AND recompute watched idxs
    for (auto &l : xlits_) {
      xlit_idxs.clear();
      xlit_idxs.reserve(l.size());
      for (const auto &v : l.get_idxs_()) { xlit_idxs.push_back( perm_inv[v-1] ); }
      l = std::move(xlit(std::move(xlit_idxs), l.has_constant(), presorted::no));
    }

    // replace xlits with xlits_
    xlits = std::move(xlits_);

    // resize xlit_dl_count0
    xlit_dl_count0.resize(xlits.size());

    assert(xlits.size()>0);


    //set cache
    ptr_cache[0] = wl0;
    ptr_cache[1] = wl1;
    }

    assert(xlits.size()>0);

    finalize:

    // recompute the indices at which wl0 and wl1 are stored
    shared_part = xlits.size() > 1 ? xlits[0].shared_part(xlits[1]) : xlit();
    xlits[0] += shared_part;
    ws[0] = std::distance(xlits[0].get_idxs_().begin(), std::lower_bound(xlits[0].get_idxs_().begin(), xlits[0].get_idxs_().end(), ptr_cache[0]));
    assert( ptr_cache[0] == ptr_(0, ws[0]) );
    if (xlits.size() == 1) {
      assigning_lvl = xlits[0].get_assigning_lvl(alpha_dl);
      return xcls_upd_ret::UNIT;
    }

    xlits[1] += shared_part;
    ws[1] = std::distance(xlits[1].get_idxs_().begin(), std::lower_bound(xlits[1].get_idxs_().begin(), xlits[1].get_idxs_().end(), ptr_cache[1]));
    if(ws[1] >= xlits[1].size() || xlits[1].get_idxs_()[ws[1]] != ptr_cache[1]) {
      xlits[1].swap(shared_part);
      ws[1] = std::distance(xlits[1].get_idxs_().begin(), std::lower_bound(xlits[1].get_idxs_().begin(), xlits[1].get_idxs_().end(), ptr_cache[1]));
      xlit_dl_count0[1] = { alpha_dl[ptr_cache[1]], dl_count[ alpha_dl[ptr_cache[1]] ] };
    }
    assert( ptr_cache[1] == ptr_(1, ws[1]));

    // ensure that xlits[1] becomes unit
    swap_wl();

    assert(get_wl0() != get_wl1());
    assert(is_unit(dl_count));
    assert(alpha[ptr_ws(0)] != bool3::None);

    // check if clause needs any processing
    assert(!is_active(dl_count));
    assert(!is_sat(dl_count));

    assigning_lvl = std::max( get_unit_at_lvl(), compute_unit_assigning_lvl(alpha_dl) );

    assert( assert_data_struct(alpha, dl_count) );

    return xcls_upd_ret::UNIT;
  };

  xcls_upd_ret init_unit(const vec<bool3> &alpha, const vec<var_t> &alpha_dl, const vec<var_t> &alpha_trail_pos, const vec<dl_c_t> &dl_count, const vec<equivalence>& equiv_lits, const vec<var_t>& equiv_lits_dl) {
    if(size()==0) {
      assigning_lvl = std::max( get_unit_at_lvl(), compute_unit_assigning_lvl(alpha_dl) );
      return xcls_upd_ret::UNIT;
    }
    if (size() == 1) {
      //reduce xlit[0]
      xlits[0].reduce(alpha, alpha_dl, 0);
      xlits[0].reduce(equiv_lits, equiv_lits_dl, 0, alpha);
      //update watched variable
      ws[0] = std::get<2>( xlits[0].get_watch_var(alpha_dl, alpha_trail_pos) );
      ptr_cache[0] = ptr_(0, ws[0]);
      assigning_lvl = std::max( get_unit_at_lvl(), compute_unit_assigning_lvl(alpha_dl) );
      return xcls_upd_ret::UNIT;
    }
    assert(xlits.size()>1);
    // distribute shared_part
    xlits[0] += shared_part;
    xlits[1] += shared_part;
    shared_part.clear();

    // reduce all xlits at dl 0
    for (auto &l : xlits) {
      l.reduce(alpha, alpha_dl, 0);
      l.reduce(equiv_lits, equiv_lits_dl, 0, alpha);
    }

    // re-order occuring indets with decreasing dl
    std::set<var_t> tmp;
    for (const auto &l : xlits) {
      tmp.insert(l.get_idxs_().begin(), l.get_idxs_().end());
    }
    vec<var_t> idxs(tmp.begin(), tmp.end());
    std::sort(idxs.begin(), idxs.end(),
              [&alpha_dl, &alpha_trail_pos](const var_t &a, const var_t &b)
              { return alpha_dl[a] > alpha_dl[b] || (alpha_dl[a] == alpha_dl[b] && alpha_trail_pos[a] > alpha_trail_pos[b]); });
    // construct permutation maps
    vec<var_t> perm(alpha.size());
    vec<var_t> perm_inv(alpha.size());
    for (var_t i = 0; i < idxs.size(); ++i) {
      perm[idxs[i]] = i;
      perm_inv[i] = idxs[i];
    }

    const var_t n_vars = idxs.size();
    rci_t nrows = xlits.size();
    rci_t ncols = n_vars+1;

    mzd_t* M = mzd_init(nrows, ncols);
    assert( mzd_is_zero(M) );

    //fill with xlits
    rci_t r = 0;
    for(const auto& l : xlits) {
        if(l.is_zero()) continue;
        if(l.has_constant()) {
            mzd_write_bit(M, r, n_vars, 1);
        }
        for(const auto& i : l.get_idxs_()) {
            assert(i>0);
            assert(perm[i] < (var_t) ncols-1);
            mzd_write_bit(M, r, perm[i], 1);
        }
        ++r;
    }
    assert(r <= nrows); //reducing with alpha at dl 0 might reduce some xlits to 0

    //compute rref
    const rci_t rank = mzd_echelonize_m4ri(M, true, 0); //should we use mzd_echelonize instead?
    //read results
    vec<xlit> xlits_; xlits_.reserve(rank);
    for(rci_t r = 0; r<rank; ++r) {
        vec<var_t> idxs;
        for(rci_t c=0; (unsigned)c<n_vars; ++c) {
            if( mzd_read_bit(M, r, c) ) idxs.push_back(c+1);
        }
        xlits_.emplace_back( std::move(idxs), (bool) mzd_read_bit(M, r, n_vars), presorted::yes );
        if(xlits_.back().is_zero()) xlits_.pop_back();
    }
    mzd_free(M);

    //xlits_ must already be sorted w.r.t. lt!
    assert( std::is_sorted(xlits_.begin(), xlits_.end(), [](const xlit &a, const xlit &b) { return a.LT() < b.LT(); }) );

    // set xlit_dl_count0, since all except the first xlits must be satisfied by assumption
    xlit_dl_count0[0] = {0,0};
    for (var_t i = 1; i < xlits_.size(); ++i) {
      const var_t lvl = alpha_dl[ perm_inv[xlits_[i].LT()-1] ];
      assert( lvl<=alpha.size());
      xlit_dl_count0[i] = {lvl, dl_count[lvl]};
    }

    if(xlits_.size()==0) {
      xlits.clear();
      xlit_dl_count0.resize(xlits.size());
      assert(is_unit(dl_count));
      assigning_lvl = 0;
      return xcls_upd_ret::UNIT;
    }

    // now watch the first two xlits as usual
    const var_t wl0 = !xlits_[0].is_constant() ? perm_inv[xlits_[0].LT()-1] : -1;
    const var_t wl1 = xlits_.size() > 1 ? perm_inv[xlits_[1].LT()-1] : -1;

    // translate xlits back AND recompute watched idxs
    for (auto &l : xlits_) {
      xlit_idxs.clear();
      xlit_idxs.reserve(l.size());
      for (const auto &v : l.get_idxs_()) { xlit_idxs.push_back( perm_inv[v-1] ); }
      l = std::move(xlit(std::move(xlit_idxs), l.has_constant(), presorted::no));
    }

    // replace xlits with xlits_
    xlits = std::move(xlits_);

    // resize xlit_dl_count0
    xlit_dl_count0.resize(xlits.size());

    assert(xlits.size()>0);

    // recompute the indices at which wl0 and wl1 are stored
    shared_part = xlits.size() > 1 ? xlits[0].shared_part(xlits[1]) : xlit();
    xlits[0] += shared_part;
    ws[0] = std::distance(xlits[0].get_idxs_().begin(), std::lower_bound(xlits[0].get_idxs_().begin(), xlits[0].get_idxs_().end(), wl0));
    ptr_cache[0] = ptr_(0, ws[0]);
    if (xlits.size() == 1) {
      assigning_lvl = xlits[0].get_assigning_lvl(alpha_dl);
      return xcls_upd_ret::UNIT;
    }

    xlits[1] += shared_part;
    ws[1] = std::distance(xlits[1].get_idxs_().begin(), std::lower_bound(xlits[1].get_idxs_().begin(), xlits[1].get_idxs_().end(), wl1));
    ptr_cache[1] = ptr_(1, ws[1]);

    // ensure that xlits[1] becomes unit
    swap_wl();

    assert(get_wl0() != get_wl1());
    assert(is_unit(dl_count));
    assert(alpha[ptr_ws(0)] != bool3::None);

    // check if clause needs any processing
    assert(!is_active(dl_count));
    assert(!is_sat(dl_count));

    assigning_lvl = std::max( get_unit_at_lvl(), compute_unit_assigning_lvl(alpha_dl) );

    return xcls_upd_ret::UNIT;
  };

  std::string to_str() const {
    if (xlits.empty())
      return "1";
    if (xlits.size() == 1) {
      assert(shared_part.is_zero());
      return xlits[0].plus_one().to_str();
    }
    std::string out;
    out += (xlits[0] + shared_part).plus_one().to_str() + " ";
    out += (xlits[1] + shared_part).plus_one().to_str() + " ";
    for (var_t i = 2; i < xlits.size(); ++i) {
      out += xlits[i].plus_one().to_str() + " ";
    }
    out.erase(out.end() - 1);
    return out;
  };

  std::string to_xnf_str() const {
    if (xlits.empty())
      return "";
    if (xlits.size() == 1)
      return xlits[0].plus_one().to_xnf_str();
    std::string out;
    out += (xlits[0] + shared_part).plus_one().to_xnf_str() + " ";
    out += (xlits[1] + shared_part).plus_one().to_xnf_str() + " ";
    for (var_t i = 2; i < xlits.size(); ++i) {
      out += xlits[i].plus_one().to_xnf_str() + " ";
    }
    out.erase(out.end() - 1);
    return out;
  };

  xcls to_xcls() const {
    vec<xlit> xlits_cpy(xlits);
    if(size()>0) xlits_cpy[0] += shared_part;
    if(size()>1) xlits_cpy[1] += shared_part;
    //return xcls( xsys( xlits_cpy ) );
    return xcls( std::move( xsys( std::move(xlits_cpy) ) ) );
  };

  const lit_watch &get_wl0() const { return ptr_ws(0); };
  const lit_watch &get_wl1() const { return ptr_ws(1); };

  // void set_wl_it0(watch_list_it wli) { wl_it[0] = wli; };
  // void set_wl_it1(watch_list_it wli) { wl_it[1] = wli; };

  // const watch_list_it& get_wl_it0() const { return wl_it[0]; };
  // const watch_list_it& get_wl_it1() const { return wl_it[1]; };

  /**
   * @brief determines if xcls is currently satsified
   *
   * @param dl_count current dl_count of solver
   * @return true iff xcls is satisfied under current alpha
   */
  inline bool is_sat(const vec<dl_c_t> &dl_count) const {
    return (dl_count[SAT_dl_count.first] == SAT_dl_count.second);
  }

  /**
   * @brief determines if xcls is unit at current dl_count
   *
   * @param dl_count current dl_count of solver
   * @return true iff xcls is evaluates to unit (including 1, i.e., unsat!)
   */
  inline bool is_unit(const vec<dl_c_t> &dl_count) const {
    return !is_sat(dl_count) && (xlits.size()<=1 || dl_count[xlit_dl_count0[0].first] == xlit_dl_count0[0].second);
  }
  
  /**
   * @brief determines if xcls is a unit cls
   *
   * @return true iff xcls is a unit
   */
  inline bool is_unit() const {
    assert( size()<=1 || xlits[0]!=xlits[1] ); //either size is small OR we have two distinct linerals
    return size()<=1;
  }

  /**
   * @brief returns the lvl at which the xclss is unit
   * @note assumes that xcls is unit at current dl!
   *
   * @return var_t lvl at which xcls is unit
   */
  var_t get_unit_at_lvl() const {
    return xlits.size() <= 1 ? 0 : xlit_dl_count0[0].first;
  }

  var_t compute_unit_assigning_lvl(const vec<var_t>& alpha_dl) const {
    return xlits.size()==0 ? 0 : ( xlits.size() == 1 ? xlits[0].get_assigning_lvl(alpha_dl) : std::max( shared_part.get_assigning_lvl(alpha_dl), xlits[1].get_assigning_lvl(alpha_dl) ) );
  }

  /**
   * @brief returns the lvl at which the xclss is unit AND the unit is assigning
   * @note requires that both is indeed the case!
   *
   * @return var_t lvl at which xcls is unit and the unit is assigning
   */
  inline var_t get_assigning_lvl() const {
    return assigning_lvl;
  }

  inline bool is_inactive(const vec<dl_c_t> &dl_count) const {
    return is_sat(dl_count) || is_unit(dl_count);
  }

  /**
   * @brief determines whether xcls is active
   *
   * @param dl_count current dl_count of solver
   * @return true iff both literal_watches point to unassigned variables
   */
  inline bool is_active(const vec<dl_c_t> &dl_count) const {
    // if it is satisfied, then ws[0] points to assigned variable!
    return !is_inactive(dl_count);
  }

  /**
   * @brief determines if xcls is neither sat nor unit
   *
   * @param dl_count current dl_count of solver
   * @return true iff xcls is satisfied under current alpha
   */
  inline bool is_none(const vec<bool3> &alpha) const {
    return alpha[ptr_ws(0)] == bool3::None && alpha[ptr_ws(1)] == bool3::None;
  }

  inline bool is_none(const vec<dl_c_t> &dl_count) const {
    return !is_unit(dl_count) && !is_sat(dl_count);
  }

  /**
   * @brief check wether given ind is watched by xcls
   *
   * @param ind indet to check
   * @return true if and only if ind is watched by xcls
   */
  inline bool watches(const var_t &ind) const {
    return (ptr_ws(0) == ind) || (ptr_ws(1) == ind);
  }

  /**
   * @brief returns the unit if is_unit is true (i.e. returns the second xlit)
   *
   * @return xlit unit that this clause was reduced to
   */
  inline xlit get_unit() const { return xlits.size() > 1 ? (xlits[1] + shared_part).add_one() : (xlits.size() == 0 ? xlit().add_one() : xlits[0].plus_one()); };

  inline bool unit_contains(const var_t &ind) const {
    return shared_part[ind] || (xlits.size() > 1 ? xlits[1][ind] : xlits[0][ind]);
  }

  /**
   * @brief adds the given literal to the unit of this clause
   * @note assumes that the clause is unit (i.e. is_unit(dl_count) is true)
   * @note xlits[0] and xlits[1] may have shared parts! -- invalid state! (USE ONLY IN CONFLICT ANALYSIS)
   *
   * @param lin lineral to add to unit part
   */
  void add_to_unit(const xlit &lin, const vec<bool3> &alpha, const vec<var_t> &alpha_dl, const vec<var_t> &alpha_trail_pos, const vec<dl_c_t> &dl_count, const vec<equivalence>& equiv_lits, const vec<var_t>& equiv_lits_dl) {
    assert(is_unit(dl_count));
    if(xlits.size()==1) {
      xlits[0] += lin;
    } else {
      xlits[1] += lin;
    }
    // re-init watches!
    init_unit(alpha, alpha_dl, alpha_trail_pos, dl_count, equiv_lits, equiv_lits_dl);
  }

  /**
   * @brief Get the dl at which the clause got inactive (i.e. unit or sat)
   *
   * @param dl_count current dl_count of solver
   * @return var_t lvl at which clause got inactive
   */
  inline var_t get_inactive_lvl(const vec<dl_c_t> &dl_count) const {
    assert(is_inactive(dl_count)); // implies is_unit(dl_count) OR is_sat(dl_count)
    return xlit_dl_count0.empty() ? 0 : (is_unit(dl_count) ?  xlit_dl_count0[0].first : SAT_dl_count.first);
  }

  inline void set_assigning_lvl(const var_t &lvl) {
    assigning_lvl = lvl;
  }

  /**
   * @brief returns number of stored linerals
   * @note beware: if clause is zero we have size()==1 and size()==0 means claus is one (!)
   * 
   * @return var_t number of linerals
   */
  var_t size() const { return xlits.size(); };


  bool is_zero() const { return (xlits.size()==1 && xlits[0].is_one()); };

  var_t LT(const cls_size_t i) const { return xlits[i].LT(); };

  const vec<xlit> &get_xlits() const { return xlits; };

  xlit get_first() const { return (xlits[0] + shared_part).add_one(); };

  bool assert_data_struct() const {
    assert(xlit_dl_count0.size() == xlits.size());
    // sanity check to see whether ws[i] is actually contained in xlits[i]
    assert(size()==0 || xlits[0].is_zero() || std::find(xlits[0].begin(), xlits[0].end(), ptr_ws(0)) != xlits[0].end());
    assert(size()<2 || std::find(xlits[1].begin(), xlits[1].end(), ptr_ws(1)) != xlits[1].end());

    assert(size()<2 || ptr_ws(0) != ptr_ws(1));

    assert(size()==0 || (size()==1 && xlits[0].is_zero()) || !xlits[0].is_constant());
    assert(size()<2 || !xlits[1].is_constant());

    // check that xlits[0] and xlits[1] share no inds!
    assert(size()<2 || xlits[0].shared_part(xlits[1]).is_zero());

    // check ptr_cache
    assert(size()==0 || ptr_cache[0] == ptr_(0, ws[0]));
    assert(size()<2 || ptr_cache[1] == ptr_(1, ws[1]));

    return true;
  };

  bool assert_data_struct(const vec<bool3> &alpha, const vec<dl_c_t> &dl_count) const {
    assert(is_unit(dl_count) || is_sat(dl_count) || alpha[ptr_ws(0)] == bool3::None);
    if (!is_unit(dl_count) && alpha[ptr_ws(0)] != bool3::None) {
      assert(is_sat(dl_count) || eval0(alpha) || (!eval0(alpha) && !eval1(alpha)));
    }
    if(is_sat(dl_count)) {
      assert(dl_count[SAT_dl_count.first] == SAT_dl_count.second);
      assert(to_xcls().reduced(alpha).is_zero());
    }
    // if( alpha[ ptr_ws(1) ] != bool3::None ) assert( !xlits[1].eval(alpha) );
    if( size()>0 && dl_count[xlit_dl_count0[0].first] == xlit_dl_count0[0].second ) assert( !eval0(alpha) );
    if( size()>1  && dl_count[xlit_dl_count0[1].first] == xlit_dl_count0[1].second ) assert( !eval1(alpha) || is_unit(dl_count) );
    for(var_t i = 2; i<xlits.size(); ++i) {
      if( dl_count[xlit_dl_count0[i].first] == xlit_dl_count0[i].second ) assert( xlits[i].eval(alpha) );
    }

    return assert_data_struct();
  };

  bool eval(const vec<bool> &sol) const {
    return std::any_of(xlits.begin()+2, xlits.end(), [&sol](const xlit l) { return !l.eval(sol); })
        || shared_part.eval(sol)^xlits[0].eval(sol)
        || (xlits.size()>1 && shared_part.eval(sol)^xlits[1].eval(sol));
  };
  
  void operator=(const xcls_watch &o) {
    xlits = o.xlits;
    shared_part = o.shared_part;
    xlit_dl_count0 = o.xlit_dl_count0;
    SAT_dl_count = o.SAT_dl_count;
    irredundant = o.irredundant;
    delete_on_cleanup = o.delete_on_cleanup;
    assigning_lvl = o.assigning_lvl;
    ws[0] = o.ws[0];
    ws[1] = o.ws[1];
    ptr_cache[0] = o.ptr_cache[0];
    ptr_cache[1] = o.ptr_cache[1];
  };

  void operator=(xcls_watch &&o) {
    xlits = std::move(o.xlits);
    shared_part = std::move(o.shared_part);
    xlit_dl_count0 = std::move(o.xlit_dl_count0);
    SAT_dl_count = o.SAT_dl_count;
    irredundant = o.irredundant;
    delete_on_cleanup = o.delete_on_cleanup;
    assigning_lvl = o.assigning_lvl;
    ws[0] = o.ws[0];
    ws[1] = o.ws[1];
    ptr_cache[0] = o.ptr_cache[0];
    ptr_cache[1] = o.ptr_cache[1];
  };
};
