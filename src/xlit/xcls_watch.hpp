#pragma once

#include "../misc.hpp"
#include "xlit.hpp"
#include "xcls.hpp"
#include "xsys.hpp"
#include <list>
#include <set>
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
   * @brief lits in the xlits
   */
  vec<xlit> xlits;
  // TODO change from vec< xlit > to std::list< xlit > ?? for faster swapping of elements?
  // TODO would it be better to store xlits NOT as objects of class xlit, but as UNSORTED vecs of var_t's ??

  /**
   * @brief shared part of xlits[0] and xlits[1]
   */
  xlit shared_part;

  /**
   * @brief xlit_dl_counts_1[i] tells in which dl and at what count xlit[i] was last evaluated to be 1 ({0,0} default)
   */
  vec<std::pair<var_t, dl_c_t>> xlit_dl_count1;

  /**
   * @brief xlit_dl_counts_0[i] tells in which dl and at what count xlit[i] was last evaluated to be 0 ({0,0} default)
   */
  vec<std::pair<var_t, dl_c_t>> xlit_dl_count0;

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
   * @brief initializes xlit_dl_count0, xlit_dl_count1, and ws[0], ws[1]
   * @note assumes that xlits are already set; wl_it must still be initiated!
   */
  void init() {
    irredundant = true;
    delete_on_cleanup = false;
    
    // init xlit_dl_counts
    xlit_dl_count1.resize(xlits.size(), {0, 0});
    xlit_dl_count0.resize(xlits.size(), {0, 0});

    if (xlits.size() == 1) {
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

  const var_t &ptr_(const cls_size_t &i, const var_t val) const {
    assert(val < xlits[i].get_idxs_().size());
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
      xlits[1].add_one();
      ws[0] = new_w;
      ptr_cache[0] = ptr_(0, ws[0]);
      assert(assert_data_struct());
      return {ptr_ws(0), xcls_upd_ret::NONE};
    }

    // now shared_part can also be evaluated --> xlits[0]+shared_part can be evaluated!
    if (true ^ xlits[0].eval(alpha) ^ shared_part.eval(alpha)) {
      // xlits[0]+shared_part evaluates to 0
      // xlits[0]+shared_part satisfied! --> xclause does not need to be watched any longer!
      // do not change watches!
      xlit_dl_count0[0] = {alpha_dl[ptr_ws(0)], dl_count[alpha_dl[ptr_ws(0)]]};
      assert(!is_active(dl_count)); // clause is no longer active!
      assert(assert_data_struct());
      return {ptr_ws(0), xcls_upd_ret::SAT};
    }
    // now xlits[0]+shared_part evaluates to 1 under alpha, i.e., we check whether a different xlit can be watched.
    xlit_dl_count1[0] = {alpha_dl[ptr_ws(0)], dl_count[alpha_dl[ptr_ws(0)]]};

    // note that xlits[0] and xlits[1] are always the xlits that are watched, i.e., start search from xlits[2] (!)
    cls_size_t new_i = 2;
    for (; new_i < xlits.size(); ++new_i) {
      assert(new_i < ( 1 << (CHAR_BIT * sizeof(cls_size_t)) ) );
      // skip xlits which evaluate to 1 in current search tree
      if (dl_count[xlit_dl_count1[new_i].first] == xlit_dl_count1[new_i].second)
        continue;

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
        xlits[new_i] += xlits[1]; xlits[new_i] += shared_part;
        xlits[new_i].add_one();
        // repeat with same new_i
        new_i--;
        continue;
      }
      if (alpha[ptr_(new_i,new_w)] == bool3::None ) {
        //if ptr_(new_i,new_w) AND ptr_(1,ws[1]) both are in shared part of xlits[1] AND xlits[new_i]; rewrite xlits[new_i] and start over
        {
          // new xlit to be watched found --> change watched xlit and return SAT
          const auto wl0 = ptr_(new_i, new_w);
          const auto wl1 = ptr_ws(1);
          xlits[0] += shared_part;
          xlits[1] += shared_part;
          xlits[0].swap(xlits[new_i]); // ensures that no iterators are invalidated
          // fix dl_count vals
          std::swap(xlit_dl_count0[0], xlit_dl_count0[new_i]);
          std::swap(xlit_dl_count1[0], xlit_dl_count1[new_i]);
          // fix shared_parts && update ws[0] and ws[1] accordingly!
          shared_part = xlits[0].shared_part(xlits[1]);
          xlits[0] += shared_part;
          xlits[1] += shared_part;
          // fix ws[0] AND ws[1]!
          ws[0] = std::distance(xlits[0].get_idxs_().begin(), std::lower_bound(xlits[0].get_idxs_().begin(), xlits[0].get_idxs_().end(), wl0));
          //if ptr_(0,ws[0]) is NOT wl0, then we need to rewrite xlits[0]
          if(ws[0] >= xlits[0].size() || ptr_(0,ws[0])!=wl0 ) {
            xlits[0].swap(shared_part);
            xlits[1].add_one();
            assert( xlits[1][wl1] );
            ws[0] = std::distance(xlits[0].get_idxs_().begin(), std::lower_bound(xlits[0].get_idxs_().begin(), xlits[0].get_idxs_().end(), wl0));
          }
          ws[1] = std::distance(xlits[1].get_idxs_().begin(), std::lower_bound(xlits[1].get_idxs_().begin(), xlits[1].get_idxs_().end(), wl1));
          if(ws[1] >= xlits[1].size() || ptr_(1,ws[1])!=wl1 ) {
            xlits[1].swap(shared_part);
            xlits[0].add_one();
            assert( xlits[0][wl0] );
            ws[1] = std::distance(xlits[1].get_idxs_().begin(), std::lower_bound(xlits[1].get_idxs_().begin(), xlits[1].get_idxs_().end(), wl1));
          }
          ptr_cache[0] = ptr_(0, ws[0]);
          ptr_cache[1] = ptr_(1, ws[1]);
          assert(ptr_cache[0] == wl0 && ptr_cache[1] == wl1);
          assert(is_active(dl_count)); assert(is_active(alpha));
          return {ptr_ws(0), xcls_upd_ret::NONE};
        }
      } else {
        // xlits[new_i] evaluates to a constant; this is only useful if xlits[new_i].eval(alpha) is SAT
        const var_t dl_assigned = alpha_dl[ptr_(new_i, new_w)];
        // check whether xlit[new_i] it is satisfied
        if (xlits[new_i].eval(alpha)) {
          // new xlit to be watched found (which luckily already renders xcls satisfied!) --> change watched xlit and return SAT
          const auto wl0 = ptr_(new_i, new_w);
          const auto wl1 = ptr_ws(1);
          //add shared part
          xlits[0]+=shared_part;
          xlits[1]+=shared_part;
          //swap xlits
          xlits[0].swap(xlits[new_i]); // ensures that no iterators are invalidated
          std::swap(xlit_dl_count0[0], xlit_dl_count0[new_i]);
          std::swap(xlit_dl_count1[0], xlit_dl_count1[new_i]);
          xlit_dl_count0[0] = {dl_assigned, dl_count[dl_assigned]};
          // fix shared_parts && update ws[0] and ws[1] accordingly!
          shared_part = xlits[0].shared_part(xlits[1]);
          xlits[0] += shared_part;
          xlits[1] += shared_part;
          // fix ws[0] AND ws[1]!
          ws[0] = std::distance(xlits[0].get_idxs_().begin(), std::lower_bound(xlits[0].get_idxs_().begin(), xlits[0].get_idxs_().end(), wl0));
          //if ptr_(0,ws[0]) is NOT wl0, then we need to rewrite xlits[0]
          if(ws[0] >= xlits[0].size() || ptr_(0,ws[0])!=wl0 ) {
            xlits[0].swap(shared_part);
            xlits[1].add_one();
            assert( xlits[1][wl1] );
            ws[0] = std::distance(xlits[0].get_idxs_().begin(), std::lower_bound(xlits[0].get_idxs_().begin(), xlits[0].get_idxs_().end(), wl0));
          }
          ws[1] = std::distance(xlits[1].get_idxs_().begin(), std::lower_bound(xlits[1].get_idxs_().begin(), xlits[1].get_idxs_().end(), wl1));
          if(ws[1] >= xlits[1].size() || ptr_(1,ws[1])!=wl1 ) {
            xlits[1].swap(shared_part);
            xlits[0].add_one();
            assert( xlits[0][wl0] );
            ws[1] = std::distance(xlits[1].get_idxs_().begin(), std::lower_bound(xlits[1].get_idxs_().begin(), xlits[1].get_idxs_().end(), wl1));
          }
          ptr_cache[0] = ptr_(0, ws[0]);
          ptr_cache[1] = ptr_(1, ws[1]);
          assert(ptr_cache[0] == wl0 && ptr_cache[1] == wl1);
          assert(!is_active(dl_count)); assert(!is_active(alpha));
          assert(is_sat(dl_count));
          assert(assert_data_struct());
          assert(assert_data_struct(alpha, dl_count));
          return {ptr_ws(0), xcls_upd_ret::SAT};
        }
        // now xlits[new_i] evaluates to 1 --> choose different new_i
        xlit_dl_count1[new_i] = {dl_assigned, dl_count[dl_assigned]};

        if (dl_assigned > alpha_dl[ptr_ws(0)])
        {
          assert(false);
          // swap xlits[new_i] to first position if it was assigned at higher dl than current watched literal
          // this is required when adding learnt cls!
          xlits[0].swap(xlits[new_i]); // ensures that no iterators are invalidated
          ws[0] = new_w;
          ptr_cache[0] = ptr_(0, ws[0]);
          std::swap(xlit_dl_count0[0], xlit_dl_count0[new_i]);
          std::swap(xlit_dl_count1[0], xlit_dl_count1[new_i]);
        }
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
    std::swap(xlit_dl_count0[0], xlit_dl_count0[1]);
    std::swap(xlit_dl_count1[0], xlit_dl_count1[1]);
    std::swap(ptr_cache[0], ptr_cache[1]);
  }

public:
  xcls_watch(){};

  xcls_watch(const xlit &l1, const xlit &l2) noexcept : xlits(vec<xlit>({l1.get_idxs_(), l2.get_idxs_()})) {
    assert(!l1.is_one() && !l1.is_zero());
    assert(!l2.is_one() && !l2.is_zero());
    init();
  };

  xcls_watch(const xcls &cl) noexcept {
    assert(cl.deg() >= 1);
    xlits.reserve(cl.deg());
    for (auto lit : cl.get_ass_VS().get_xlits()) {
      xlits.emplace_back(lit.add_one());
    }
    init();
  };

  xcls_watch(xcls &&cl) noexcept {
    assert(cl.deg() >= 1);
    xlits.reserve(cl.deg());
    for (auto lit : cl.get_ass_VS().get_xlits()) {
      xlits.emplace_back(std::move(lit.add_one()));
    }
    init();
  };

  xcls_watch(const xcls_watch &o) noexcept : xlits(o.xlits), shared_part(o.shared_part), xlit_dl_count1(o.xlit_dl_count1), xlit_dl_count0(o.xlit_dl_count0), irredundant(o.irredundant), delete_on_cleanup(o.delete_on_cleanup), assigning_lvl(o.assigning_lvl) {
    ws[0] = o.ws[0];
    ws[1] = o.ws[1];
    ptr_cache[0] = o.ptr_cache[0];
    ptr_cache[1] = o.ptr_cache[1];
  };

  xcls_watch(xcls_watch &&o) noexcept : xlits(std::move(o.xlits)), shared_part(std::move(o.shared_part)), xlit_dl_count1(std::move(o.xlit_dl_count1)), xlit_dl_count0(std::move(o.xlit_dl_count0)), irredundant(o.irredundant), delete_on_cleanup(o.delete_on_cleanup), assigning_lvl(std::move(o.assigning_lvl)) {
    ws[0] = o.ws[0];
    ws[1] = o.ws[1];
    ptr_cache[0] = o.ptr_cache[0];
    ptr_cache[1] = o.ptr_cache[1];
  };

  xcls_watch(const xlit_watch& lin, const vec<var_t>& alpha_dl) noexcept {
    irredundant = false;
    delete_on_cleanup = false;
    
    xlits.emplace_back( lin );
    // init xlit_dl_counts
    xlit_dl_count1.emplace_back(0,0);
    xlit_dl_count0.emplace_back(0,0);
    
    shared_part.clear();

    ws[0] = std::distance(xlits[0].get_idxs_().begin(), std::lower_bound(xlits[0].get_idxs_().begin(), xlits[0].get_idxs_().end(), lin.get_wl0()));
    ptr_cache[0] = lin.get_wl0();
    assigning_lvl = lin.get_assigning_lvl(alpha_dl);
  }

  xcls_watch(const xsys &lits) noexcept {
    assert(lits.dim() >= 1);
    xlits = vec<xlit>(lits.get_xlits().begin(), lits.get_xlits().end());
    std::for_each(xlits.begin(), xlits.end(), [](xlit &l) { l.add_one(); });
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
    return true ^ xlits[0].eval(alpha) ^ shared_part.eval(alpha);
  }

  /**
   * @brief evals the 1-th watched literal at alpha
   *
   * @param alpha current bool3-assignments
   *
   * @return true iff alpha( xlits[1]+shared_part ) = 0
   */
  bool eval1(const vec<bool3> &alpha) const {
    return true ^ xlits[1].eval(alpha) ^ shared_part.eval(alpha);
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
      return xcls_upd_ret::SAT; // NOTE here it might also be a UNIT, but it did not become one by this update!
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

      if (is_sat(dl_count)) {
        // ensure we watch the lineral with lowest dl!
        assert(false);
      } else if (is_unit(dl_count)) {
        // ensure we watch the lineral with highest dl!
        const var_t new_i = std::distance(xlit_dl_count1.begin(), std::max_element(xlit_dl_count1.begin(), xlit_dl_count1.end(), [](const auto &a, const auto &b)
                                                                                   { return a.first < b.first; }));
        xlits[0].swap(xlits[new_i]); // ensures that no iterators are invalidated
        // esnure we watch the variable with hightest dl!
        const var_t new_w = std::distance(xlits[0].begin(), std::max_element(xlits[0].begin(), xlits[0].end(), [&](const auto &a, const auto &b)
                                                                             { return alpha_dl[a] < alpha_dl[b]; }));
        ws[0] = new_w;
        ptr_cache[0] = ptr_(0, ws[0]);
        std::swap(xlit_dl_count0[0], xlit_dl_count0[new_i]);
        std::swap(xlit_dl_count1[0], xlit_dl_count1[new_i]);
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

  xcls_upd_ret resolve(const xcls_watch &rs_cls, const vec<bool3> &alpha, const vec<var_t> &alpha_dl, const vec<var_t> &alpha_trail_pos, const vec<dl_c_t> &dl_count, const vec<equivalence>& equiv_lits, const vec<var_t>& equiv_lits_dl) {
    // fix unit part ('resolving' part)
    if (deg() == 1) {
      xlits[0] += rs_cls.get_unit();
    } else {
      assert(xlits.size() > 0);
      xlits[1] += rs_cls.get_unit();
    }
    // add xlits from rs_cls to this
    if(rs_cls.deg() > 1) {
      std::copy(rs_cls.xlits.begin() + 2, rs_cls.xlits.end(), std::back_inserter(xlits));
      std::copy(rs_cls.xlit_dl_count0.begin() + 2, rs_cls.xlit_dl_count0.end(), std::back_inserter(xlit_dl_count0));
      std::copy(rs_cls.xlit_dl_count1.begin() + 2, rs_cls.xlit_dl_count1.end(), std::back_inserter(xlit_dl_count1));

      xlits.emplace_back(rs_cls.xlits[0] + rs_cls.shared_part);
      xlit_dl_count0.emplace_back(rs_cls.xlit_dl_count0[0]);
      xlit_dl_count1.emplace_back(rs_cls.xlit_dl_count1[0]);
    }
    const auto ret = init_unit(alpha, alpha_dl, alpha_trail_pos, dl_count, equiv_lits, equiv_lits_dl);
    assert(ret == xcls_upd_ret::UNIT);
    assert(is_unit(dl_count));
    assigning_lvl = std::max( get_unit_at_lvl(), compute_unit_assigning_lvl(alpha_dl) );
    return ret;
  }

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
  xcls_upd_ret init_unit(const vec<bool3> &alpha, const vec<var_t> &alpha_dl, const vec<var_t> &alpha_trail_pos, const vec<dl_c_t> &dl_count, const vec<equivalence>& equiv_lits, const vec<var_t>& equiv_lits_dl) {
    if (deg() == 1) {
      //reduce xlit[0]
      xlits[0].reduce(alpha, alpha_dl, 0);
      xlits[0].reduce(equiv_lits, equiv_lits_dl, 0, alpha);
      //update watched variable
      ws[0] = std::get<2>( xlits[0].get_watch_var(alpha_dl, alpha_trail_pos) );
      ptr_cache[0] = ptr_(0, ws[0]);
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
      perm[idxs[i]] = i + 1;
      perm_inv[i + 1] = idxs[i];
    }

    // TODO use M4RI instead?! (should be A LOT faster!)

    // map xlits into new ring
    vec<xlit> xlits_(xlits.size());
    for (var_t i = 0; i < xlits.size(); ++i) {
      vec<var_t> xlit_idxs;
      xlit_idxs.reserve(xlits[i].size());
      for (const auto &v : xlits[i].get_idxs_()) {
        xlit_idxs.push_back(perm[v]);
      }
      xlit xlit_(std::move(xlit_idxs), !xlits[i].has_constant());
      xlits_.push_back(xlit_);
    }
    // rref
    xsys sys(std::move(xlits_));

    // write reduced xlits back to xlits_
    xlits_.clear();
    for (const auto &[_, l_it] : sys.get_pivot_poly_idx()) {
      xlits_.emplace_back(*l_it);
    }

    // now the LTs (w.r.t to the alpha_dl induced order) of all xlits have highest dl, and we can easily check which xlits are evaluated at highest dl, by chcecking their LTs
    // compute the two xlits where the alpha_dl of LTs is the highest
    std::sort(xlits_.begin(), xlits_.end(), 
        [](const xlit &a, const xlit &b) { return a.LT() < b.LT(); });
    // std::sort(xlits_.begin(), xlits_.end(), [&alpha_dl,&alpha_trail_pos,&perm_inv](const xlit& a, const xlit& b){ return alpha_dl[perm_inv[a.LT()]]==0 || alpha_dl[perm_inv[a.LT()]] > alpha_dl[perm_inv[b.LT()]] || (alpha_dl[perm_inv[a.LT()]]==alpha_dl[perm_inv[b.LT()]] && alpha_trail_pos[perm_inv[a.LT()]] > alpha_trail_pos[perm_inv[b.LT()]]); } );

    // set xlit_dl_count1, since all except the first xlits must be satisfied by assumption
    for (var_t i = 1; i < xlits_.size(); ++i) {
      const var_t lvl = alpha_dl[perm_inv[xlits_[i].LT()]];
      if(lvl==(var_t)-1) { xlit_dl_count1[i] =  {0,0}; }
      else { xlit_dl_count1[i] = {lvl, dl_count[lvl]}; }
    }

    // now watch the first two xlits as usual
    var_t wl0 = perm_inv[xlits_[0].LT()];
    var_t wl1 = xlits_.size() > 1 ? perm_inv[xlits_[1].LT()] : -1;

    // translate xlits back AND recompute watched idxs
    for (auto &l : xlits_) {
      vec<var_t> xlit_idxs;
      xlit_idxs.reserve(l.size());
      for (const auto &v : l.get_idxs_()) { xlit_idxs.push_back(perm_inv[v]); }
      xlit xlit_(std::move(xlit_idxs), !l.has_constant());
      l = std::move(xlit_);
    }

    // replace xlits with xlits_
    std::swap(xlits_, xlits);

    // resize xlit_dl_counts
    xlit_dl_count0.resize(xlits.size());
    xlit_dl_count1.resize(xlits.size());

    assert(xlits.size()>0);

    // recompute the indices at which wl0 and wl1 are stored
    shared_part = xlits.size() > 1 ? xlits[0].shared_part(xlits[1]) : xlit();
    xlits[0] += shared_part;
    ws[0] = std::distance(xlits[0].get_idxs_().begin(), std::lower_bound(xlits[0].get_idxs_().begin(), xlits[0].get_idxs_().end(), wl0));
    ptr_cache[0] = ptr_(0, ws[0]);
    if (xlits.size() == 1) { return xcls_upd_ret::UNIT; }

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

    return xcls_upd_ret::UNIT;
  };

  std::string to_str(const vec<xlit> &assignments) const { return to_xcls().reduced(assignments).to_str(); };
  std::string to_str() const {
    if (xlits.empty())
      return "";
    if (xlits.size() == 1)
      return xlits[0].to_str();
    std::string out;
    out += (xlits[0] + shared_part).to_str() + " ";
    out += (xlits[1] + shared_part).to_str() + " ";
    for (var_t i = 2; i < xlits.size(); ++i)
    {
      out += xlits[i].to_str() + " ";
    }
    out.erase(out.end() - 1);
    return out;
  };

  xcls to_xcls() const {
    vec<xlit> xlits_cpy(xlits.begin(), xlits.end());
    xlits_cpy[0] += shared_part;
    if (xlits_cpy.size() > 1)
      xlits_cpy[1] += shared_part;
    return xcls(xlits_cpy);
  };

  const lit_watch &get_wl0() const { return ptr_ws(0); };
  const lit_watch &get_wl1() const { return ptr_ws(1); };

  var_t deg() const { return xlits.size(); };

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
  bool is_sat(const vec<dl_c_t> &dl_count) const {
    return (dl_count[xlit_dl_count0[0].first] == xlit_dl_count0[0].second); // || (dl_count[ xlit_dl_count0[1].first ] == xlit_dl_count0[1].second);
  }

  /**
   * @brief determines if xcls is unit
   *
   * @param dl_count current dl_count of solver
   * @return true iff xcls is evaluates to unit (including 1, i.e., unsat!)
   */
  bool is_unit(const vec<dl_c_t> &dl_count) const {
    return xlits.size()==1 || dl_count[xlit_dl_count1[0].first] == xlit_dl_count1[0].second; // || (dl_count[ xlit_dl_count1[1].first ] == xlit_dl_count1[1].second);
  }

  /**
   * @brief returns the lvl at which the xclss is unit
   * @note assumes that xcls is unit at current dl!
   *
   * @return var_t lvl at which xcls is unit
   */
  var_t get_unit_at_lvl() const {
    return xlits.size() == 1 ? 0 : xlit_dl_count1[0].first;
  }

  var_t compute_unit_assigning_lvl(const vec<var_t>& alpha_dl) const {
    return xlits.size() == 1 ? xlits[0].get_assigning_lvl(alpha_dl) : std::max( shared_part.get_assigning_lvl(alpha_dl), xlits[1].get_assigning_lvl(alpha_dl) );
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

  bool is_inactive(const vec<dl_c_t> &dl_count) const {
    return is_sat(dl_count) || is_unit(dl_count);
  }

  bool is_inactive(const vec<bool3> &alpha) const {
    return !is_active(alpha);
  }

  /**
   * @brief determines whether xcls is active
   *
   * @param dl_count current dl_count of solver
   * @return true iff both literal_watches point to unassigned variables
   */
  bool is_active(const vec<dl_c_t> &dl_count) const {
    // if it is satisfied, then ws[0] points to assigned variable!
    return !is_inactive(dl_count);
  }

  bool is_active(const vec<bool3> &alpha) const {
    // if it is satisfied, then ws[0] points to assigned variable!
    return alpha[ptr_ws(0)] == bool3::None; //&& alpha[ptr_ws(1)]==bool3::None;
  }

  /**
   * @brief determines if xcls is neither sat nor unit
   *
   * @param dl_count current dl_count of solver
   * @return true iff xcls is satisfied under current alpha
   */
  bool is_none(const vec<bool3> &alpha) const {
    return alpha[ptr_ws(0)] == bool3::None && alpha[ptr_ws(1)] == bool3::None;
  }

  bool is_none(const vec<dl_c_t> &dl_count) const {
    return !is_unit(dl_count) && !is_sat(dl_count);
  }

  /**
   * @brief check wether given ind is watched by xcls
   *
   * @param ind indet to check
   * @return true if and only if ind is watched by xcls
   */
  bool watches(const var_t &ind) const {
    return (ptr_ws(0) == ind) || (ptr_ws(1) == ind);
  }

  /**
   * @brief returns the unit if is_unit is true (i.e. returns the second xlit)
   *
   * @return xlit unit that this clause was reduced to
   */
  xlit get_unit() const { return xlits.size() > 1 ? xlits[1] + shared_part : xlits[0]; };

  bool unit_contains(const var_t &ind) const {
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
    if(xlits.size()==1) {
      xlits[0] += lin;
    } else {
      xlits[1] += lin;
    }
    // re-init watches!
    init_unit(alpha, alpha_dl, alpha_trail_pos, dl_count, equiv_lits, equiv_lits_dl);
    assigning_lvl = std::max( get_unit_at_lvl(), compute_unit_assigning_lvl(alpha_dl) );
  }

#ifndef NDEBUG
  /**
   * @brief given that xcls is a unit under given assignments, returns this (reduced) unit
   *
   * @param assignments current assignments
   * @return xlit unit
   */
  xlit get_unit(const vec<xlit> &assignments) const {
    const xcls cls = to_xcls().reduced(assignments);
    xlit unit = cls.get_unit();
    unit.reduce(assignments);
    return unit;
  }
#endif

  /**
   * @brief Get the dl at which the clause got inactive (i.e. unit or sat)
   *
   * @param dl_count current dl_count of solver
   * @return var_t lvl at which clause got inactive
   */
  var_t get_inactive_lvl(const vec<dl_c_t> &dl_count) const {
    assert(is_inactive(dl_count)); // implies is_unit(dl_count) OR is_sat(dl_count)
    // if(is_unit(dl_count)) return xlit_dl_count1[0].first;
    // assert(is_sat(dl_count));
    // return xlit_dl_count0[0].first;
    return is_unit(dl_count) ? xlit_dl_count1[0].first : xlit_dl_count0[0].first;
  }

  /**
   * @brief determines if xcls is unit under given assignments
   * @note is_unit(assignments) does NOT imply is_unit(dl_count) (!)
   *
   * @param assignments current assignments
   * @return true iff xcls is a unit under assignments
   */
  bool is_unit(const vec<xlit> &assignments) const {
    xcls cls = to_xcls().reduced(assignments);
    return cls.is_unit();
  }

  void set_assigning_lvl(const var_t &lvl) {
    assigning_lvl = lvl;
  }

  var_t size() const { return xlits.size(); };

  // vec<var_t> get_LTs() const { vec<var_t> lts; for(const auto& lit : xlits) lts.emplace_back(lit.LT()); return lts; };

  var_t LT(const cls_size_t i) const { return xlits[i].LT(); };

  const vec<xlit> &get_xlits() const { return xlits; };

  xlit get_first() const { return xlits[0] + shared_part; };

  bool assert_data_struct() const {
    assert(xlit_dl_count0.size() == xlits.size());
    assert(xlit_dl_count1.size() == xlits.size());
    // sanity check to see whether ws[i] is actually contained in xlits[i]
    assert(std::find(xlits[0].begin(), xlits[0].end(), ptr_ws(0)) != xlits[0].end());
    assert(std::find(xlits[1].begin(), xlits[1].end(), ptr_ws(1)) != xlits[1].end());

    assert(ptr_ws(0) != ptr_ws(1));

    assert(!xlits[0].is_constant() && !xlits[1].is_constant());

    // check that xlits[0] and xlits[1] share no inds!
    assert(xlits[0].shared_part(xlits[1]).is_zero());

    // check ptr_cache
    assert(ptr_cache[0] == ptr_(0, ws[0]));
    assert(ptr_cache[1] == ptr_(1, ws[1]));

    return true;
  };

  bool assert_data_struct(const vec<bool3> &alpha, const vec<dl_c_t> &dl_count) const {
    assert(assert_data_struct());
    // assert(is_unit(alpha) == is_unit(dl_count));
    assert(is_active(alpha) == is_active(dl_count));
    assert(is_inactive(alpha) == is_inactive(dl_count));

    // if( !( is_unit(dl_count) || is_sat(dl_count) || alpha[ ptr_ws(0) ]==bool3::None ) ) {
    //   assert(false);
    // }

    assert(is_unit(dl_count) || is_sat(dl_count) || alpha[ptr_ws(0)] == bool3::None);
    if (!is_unit(dl_count) && alpha[ptr_ws(0)] != bool3::None)
      assert(eval0(alpha) || (!eval0(alpha) && !eval1(alpha)));
    // if( alpha[ ptr_ws(1) ] != bool3::None ) assert( !xlits[1].eval(alpha) );

    return assert_data_struct();
  };

  bool eval(const vec<bool> &sol) const {
    return std::any_of(xlits.begin(), xlits.end(), 
        [&sol](const xlit l) { return l.eval(sol); });
  };

  void operator=(const xcls_watch &&o) {
    xlits = std::move(o.xlits);
    shared_part = std::move(o.shared_part);
    xlit_dl_count0 = std::move(o.xlit_dl_count0);
    xlit_dl_count1 = std::move(o.xlit_dl_count1);
    irredundant = o.irredundant;
    delete_on_cleanup = o.delete_on_cleanup;
    ws[0] = o.ws[0];
    ws[1] = o.ws[1];
    ptr_cache[0] = o.ptr_cache[0];
    ptr_cache[1] = o.ptr_cache[1];
  };
};
