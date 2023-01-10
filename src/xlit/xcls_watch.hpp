#pragma once

#include "../misc.hpp"
#include "xlit.hpp"
#include "xcls.hpp"
#include "xsys.hpp"
#include <list>

#include <ranges>


using lit_watch = var_t;
using watch_list_it = std::list<var_t>::const_iterator;



/**
 * @brief return type for update of xcls_watch
 */
enum class upd_ret { SAT, UNIT, NONE };

//watch xcls
class xcls_watch {
  private:
    /**
     * @brief lits in the xlits 
     */
    vec< xlit > xlits;
    //TODO would it be better to store xlits NOT as objects of class xlit, but as UNSORTED vecs of var_t's ??

    /**
     * @brief xlit_dl_counts_1[i] tells in which dl and at what count xlit[i] was last evaluated to be 1 ({0,0} default)
     */
    vec< std::pair<var_t,int> > xlit_dl_count1;
    
    /**
     * @brief xlit_dl_counts_0[i] tells in which dl and at what count xlit[i] was last evaluated to be 0 ({0,0} default)
     */
    vec< std::pair<var_t,int> > xlit_dl_count0;

    /**
     * @brief iterator pointing to index in watch_list (necessary for updating watch-lists in constant time)
     */
    watch_list_it wl_it[2];
    
    /**
     * @brief literal watches; offset into idxs-sets of xlits[0] and xlits[1]
     */
    lit_watch ws[2];

    /**
     * @brief initializes xlit_dl_count0, xlit_dl_count1, and ws[0], ws[1]
     * @note assumes that xlits are already set; wl_it must still be initiated!
     */
    void init() {
      assert(xlits.size()>1);
      //init xlit_dl_counts
      xlit_dl_count1.resize(xlits.size());
      xlit_dl_count0.resize(xlits.size());
      for (cls_size_t j = 0; j < xlits.size(); j++) {
        xlit_dl_count1[j] = {0,0};
        xlit_dl_count0[j] = {0,0};
      }
      //init ws
      ws[0] = 0;
      ws[1] = 0;
    }

    const var_t& ptr_(const cls_size_t& i, const var_t val) const {
      assert(i==0 || i==1);
      assert(0<=val && val<xlits[i].get_idxs_().size());
      //return xlits[i].get_idxs_().at(val);
      return xlits[i].get_idxs_()[val];
    }
    
    const var_t& ptr_ws(const cls_size_t& i) const {
      return ptr_(i,ws[i]);
    }
    

    /**
     * @brief update ws[i] to new_w and updates watch_list accordingly
     * 
     * @param i 0 or 1
     * @param new_w new literal-watch to replace ws[i] -- MUST be distinct!
     * @param watch_list current watch_list to be updated
     */
    void change_lit_watch(const cls_size_t& i, const lit_watch new_w, vec< std::list<var_t> >& watch_list) {
      assert(i==0 || i==1);
      assert(ws[i] != new_w); //only update if anything has changed!
      //add to new watchlist
      watch_list[ ptr_(i,new_w) ].push_back( *wl_it[i] );
      //rm from current watchlist
      watch_list[ ptr_(i,ws[i]) ].erase( wl_it[i] );
      //update ws[i] -- this should be the only direct assignment of ws[i] (!)
      ws[i] = new_w;
    };

    /**
     * @brief advances ws[i] if alpha[ *ws[i] ] not bool3::None, i.e., *ws[i] is assigned a truth value
     * 
     * @param i idx of literal-watch to advance
     * @param alpha current bool3-alpha
     * @param alpha_dl dl of alpha-assignments
     * @return upd_ret SAT if xcls became satisfied, UNIT if xcls became unit (includes UNSAT case, i.e., unit 1), NONE otherwise
     */
    upd_ret advance_lw(const cls_size_t& i, const vec<bool3>& alpha, const vec<var_t>& alpha_dl, const vec<var_t>& dl_count, const var_t& dl, vec< std::list<var_t> >& watch_list) {
      assert(i == (cls_size_t)0 || i == (cls_size_t)1);
      assert(alpha[ ptr_(i,ws[i]) ] != bool3::None);
      
      //TODO shorter & cleaner impl with c++20 ranges?
      //vec<std::ranges::subrange<lit_watch, xlit::iterator, std::ranges::subrange_kind::sized>> tmp{ std::ranges::subrange(ws[i], xlits[i].end()), std::ranges::subrange(xlits[i].begin(), ws[i]) };
      //auto r = tmp | std::ranges::views::join;

      //advance iterator as long as there is another unassigned idx to point to
      auto new_w = ws[i];
      while( (new_w < xlits[i].size()) && (alpha[ ptr_(i,new_w) ] != bool3::None) ) ++new_w;
      if(new_w == xlits[i].size()) /*wrap around end if necessary */ new_w = 0;
      while( (new_w != ws[i]) && (alpha[ptr_(i,new_w)] != bool3::None) ) ++new_w;
      //advancing done; now new_w points to ws[i] or at an unassigned idx

      //if new_w != ws[i] then a new unassigned idx was found
      if(new_w != ws[i]) {
        change_lit_watch(i, new_w, watch_list);
        return upd_ret::NONE;
      }
      //now we must have new_w == ws[i], i.e., no unassigned idx was found and the value of xlits[i] can be computed:
      if( xlits[i].eval(alpha) ) { //xlits[i] evaluates to 0
        //xlits[i] satisfied! --> xclause does not need to be watched any longer, leave ws where they are!
        xlit_dl_count0[i] = {dl, dl_count[dl]};
        assert( !is_active(dl_count) ); //clause is not active any longer!
        return upd_ret::SAT;
      }
      //now xlits[i] evaluates to 1 under alpha, i.e., we need to find a different xlit to watch
      xlit_dl_count1[i] = {dl, dl_count[dl]};

      //note that xlits[0] and xlits[1] are always the xlits that are watched, i.e., start search from xlits[2] (!)
      cls_size_t new_i = 2;
      for(; new_i<xlits.size(); ++new_i) {
        //skip xlits which evaluate to 1 in current search tree
        if(dl_count[ xlit_dl_count1[new_i].first ] == xlit_dl_count1[new_i].second) continue;

        //find lit that was assigned at highest dl (req for proper backtracking!) -- or find unassigned lit!
        new_w = 0;
        var_t max_w = 0;
        while( new_w<xlits[new_i].size() && alpha[ ptr_(new_i,new_w) ]!=bool3::None) {
          if(alpha_dl[ ptr_(new_i,new_w) ] > alpha_dl[ ptr_(new_i,max_w) ]) max_w = new_w;
          ++new_w;
        }
        //if new_w is not xlits[new_i].size(), then there is an unassigned literal, i.e., 
        if(new_w != xlits[new_i].size()) break;
        new_w = max_w;
        var_t dl_sat = alpha_dl[ ptr_(new_i,new_w) ];
        //otherwise eval and see whether it is satisfied
        if( xlits[new_i].eval(alpha) ) {
          //new xlit to be watched found (which luckily already renders xcls satisfied!) --> change watched xlit and return SAT
          xlits[i].swap(xlits[new_i]); //ensures that not iterators into xlits are invalidated
          new_w = 0;
          change_lit_watch(i, new_w, watch_list);
          std::swap(xlit_dl_count0[i], xlit_dl_count0[new_i]);
          std::swap(xlit_dl_count1[i], xlit_dl_count1[new_i]);
          xlit_dl_count0[i] = {dl_sat, dl_count[dl_sat]};
          assert( !is_active(dl_count) );
          return upd_ret::SAT;
        }
        //now xlits[new_i] evaluates to 1 --> choose different new_i
        xlit_dl_count1[new_i] = {dl_sat, dl_count[dl_sat]};
      }

      if(new_i != xlits.size()) {
        //new xlit to watch found! --> swap xlit[new_i] into correct position!
        xlits[i].swap(xlits[new_i]); //ensures that no iterators into xlits are invalidated
        change_lit_watch(i, new_w, watch_list);
        std::swap(xlit_dl_count0[i], xlit_dl_count0[new_i]);
        std::swap(xlit_dl_count1[i], xlit_dl_count1[new_i]);
        assert( is_active(dl_count) );
        return upd_ret::NONE;
      } else {
        //we have new_i == xlits.size(), i.e., no xlit to be watched found! --> all other xlits eval to 1 (!) --> learn unit!
        //swap xlits s.t. xlits[0] is unit; ws[i] can be left untouched!
        xlits[1-i].swap(xlits[0]); //ensures that not iterators into xlits are invalidated
        std::swap(ws[1-i], ws[0]);
        std::swap(wl_it[1-i], wl_it[0]);
        std::swap(xlit_dl_count0[1-i], xlit_dl_count0[0]);
        std::swap(xlit_dl_count1[1-i], xlit_dl_count1[0]);
        return upd_ret::UNIT;
      }
    };
    
  public:
    xcls_watch() {};
    
    xcls_watch(const xlit& l1, const xlit& l2) noexcept : xlits(vec< xlit >({l1.get_idxs(), l2.get_idxs()})) {
      assert(!l1.is_one() && !l1.is_zero());
      assert(!l2.is_one() && !l2.is_zero());
      init();
    };
    
    xcls_watch(const xcls& cl) noexcept {
      assert(cl.deg()>=2);
      xlits.reserve( cl.deg() ); 
      for(auto lit : cl.get_ass_VS().get_xlits()) { xlits.emplace_back( lit.add_one() ); }
      init();
    };

    //TODO implement using move-ctor -- simply move literals and add one?!
    xcls_watch(xcls&& cl) noexcept {
      if(cl.deg()<2) {
        std::cout << "!";
      }
      assert(cl.deg()>=2);
      xlits.reserve( cl.deg() ); 
      for(auto lit : cl.get_ass_VS().get_xlits()) { xlits.emplace_back( lit.add_one() ); }
      init();
    };

    xcls_watch(const xcls_watch& o) noexcept : xlits(o.xlits), xlit_dl_count1(o.xlit_dl_count1), xlit_dl_count0(o.xlit_dl_count0) { 
      ws[0] = o.ws[0]; ws[1] = o.ws[1]; wl_it[0] = o.wl_it[0]; wl_it[1] = o.wl_it[1];
    };
    
    xcls_watch(const xsys& lits) noexcept {
      assert(lits.dim()>=2);
      xlits = lits.get_xlits();
      std::for_each(xlits.begin(), xlits.end(), [](xlit& l){ l.add_one(); });
      init();
    };


    /**
     * @brief updates xcls_watch and watch_list according to the new assigned literal lit, dl_count, dl and alpha.
     * 
     * @param new_lit literal that was newly assigned
     * @param alpha current bool3-assignment
     * @param alpha_dl dl of alpha-assignments
     * @param dl_count current dl_count
     * @param dl current dl
     * @param watch_list current watch_list
     * @return upd_ret SAT if xcls does not need any further updates (i.e. it is a unit or satisfied), UNIT if xcls became unit just now (includes UNSAT case, i.e., unit 1), NONE otherwise
     */
    upd_ret update(const var_t& new_lit, const vec<bool3>& alpha, const vec<var_t>& alpha_dl, const vec<var_t>& dl_count, const var_t& dl, vec< std::list<var_t> >& watch_list) {
      //check if clause needs any processing
      if(!is_active(dl_count) ) {
        assert(is_sat(dl_count) || is_unit(dl_count));
        return upd_ret::SAT; //NOTE here it might also be a UNIT, but it did not become one by this update!
      }

      //at least one of { *ws[0], *ws[1] } must be new_lit by construction (update should only be called on watch_list elements...)
      assert( ptr_ws(0) == new_lit || ptr_ws(1) == new_lit );
      //update one of them, then call itself recursively!
      const auto i = ptr_ws(0) == new_lit ? 0 : 1;
      assert( ptr_ws(i) == new_lit );
      
      upd_ret upd = advance_lw(i, alpha, alpha_dl, dl_count, dl, watch_list);
      //note watch-lists are already updated! --> only need to deal with 
      //assert correct return value!
      if(upd == upd_ret::NONE) {
        assert( is_none(alpha) );
        //update ws[1] if necessary! (also updates upd)
        if(ptr_ws(1-i)==new_lit) upd = advance_lw(1-i, alpha, alpha_dl, dl_count, dl, watch_list);
        assert( (upd!=upd_ret::NONE) == is_none(alpha) );
      } else if(upd == upd_ret::SAT) {
        assert( is_sat(dl_count) );
      } else { assert(upd == upd_ret::UNIT);
        assert( is_unit(dl_count) );
      };

      return upd;
    };


    /**
     * @brief updates xcls_watch and watch_list according to current alpha, updates watch_list (and requires dl_count and dl)
     * 
     * @param alpha current bool3-assignment
     * @param alpha_dl dl of alpha-assignments
     * @param dl_count current dl_count
     * @param dl current dl
     * @param watch_list current watch_list
     * @return upd_ret SAT if xcls does not need any further updates (i.e. it is a unit or satisfied), UNIT if xcls became unit just now (includes UNSAT case, i.e., unit 1), NONE otherwise
     */
    upd_ret update(const vec<bool3>& alpha, const vec<var_t>& alpha_dl, const vec<var_t>& dl_count, const var_t& dl, vec< std::list<var_t> >& watch_list) {
      //check if clause needs any processing
      if( !is_active(dl_count) ) {
        assert(is_sat(dl_count) || is_unit(dl_count));
        return upd_ret::SAT; //NOTE here it might also be a UNIT, but it did not become one by this update!
      }

      //check if -- and which ws need to be updated
      if(alpha[ ptr_ws(0) ] == bool3::None && alpha[ ptr_ws(1) ] == bool3::None) {
        //nothing needs to be updated!
        if(is_none(alpha)) return upd_ret::NONE; //TODO these next two cases should never occur, or??
        else if(is_sat(dl_count)) return upd_ret::SAT;
        else if(is_unit(dl_count)) return upd_ret::UNIT;
        assert(false);
      }
      //at least one of { *ws[0], *ws[1] } can be advanced!
      assert( alpha[ptr_ws(0)] != bool3::None || alpha[ptr_ws(1)] != bool3::None );
      const auto i = alpha[ptr_ws(0)] != bool3::None ? 0 : 1;
      
      upd_ret upd = advance_lw(i, alpha, alpha_dl, dl_count, dl, watch_list);
      //note watch-lists are already updated! --> only need to deal with 
      //assert correct return value!
      if(upd == upd_ret::NONE) {
        assert( is_none(alpha) );
        //update ws[1] if necessary! (also updates upd)
        if(alpha[ptr_ws(1-i)]!=bool3::None) upd = advance_lw(1-i, alpha, alpha_dl, dl_count, dl, watch_list);
        assert( (upd==upd_ret::NONE) == is_none(alpha) );
      } else if(upd == upd_ret::SAT) {
        assert( is_sat(dl_count) );
      } else { assert(upd == upd_ret::UNIT);
        assert( is_unit(dl_count) );
      };

      assert( assert_data_struct() );

      return upd;
    };

    std::string to_str(const vec<xlit>& assignments) const;
    
    xcls to_xcls() const { return xcls( xlits ); };

    const lit_watch& get_wl0() const { return ptr_ws(0); };
    const lit_watch& get_wl1() const { return ptr_ws(1); };

    void set_wl_it0(watch_list_it wli) { wl_it[0] = wli; };
    void set_wl_it1(watch_list_it wli) { wl_it[1] = wli; };

    /**
     * @brief determines if xcls is currently satsified
     * 
     * @param dl_count current dl_count of solver
     * @return true iff xcls is satisfied under current alpha
     */
    bool is_sat(const vec<var_t>& dl_count) const { 
      return (dl_count[ xlit_dl_count0[0].first ] == xlit_dl_count0[0].second) || (dl_count[ xlit_dl_count0[1].first ] == xlit_dl_count0[1].second);
    }
    
    /**
     * @brief determines if xcls is unit
     * 
     * @param dl_count current dl_count of solver
     * @return true iff xcls is evaluates to unit (including 1, i.e., unsat!)
     */
    bool is_unit(const vec<var_t>& dl_count) const { 
      return (dl_count[ xlit_dl_count1[1].first ] == xlit_dl_count1[1].second) || (dl_count[ xlit_dl_count1[0].first ] == xlit_dl_count1[0].second);
      //TODO or based on *lw_it[1] being assigned?
    }
    
    bool is_inactive(const vec<var_t>& dl_count) const { 
      return is_sat(dl_count) || is_unit(dl_count);
    }
    /**
     * @brief determines whether xcls is active
     * 
     * @param dl_count current dl_count of solver
     * @return true iff both literal_watches point to unassigned variables
     */
    bool is_active(const vec<var_t>& dl_count) const {
      //if it is satisfied, then ws[0] points to assigned variable!
      return !is_inactive(dl_count);
    }


    /**
     * @brief determines if xcls is neither sat nor unit
     * 
     * @param dl_count current dl_count of solver
     * @return true iff xcls is satisfied under current alpha
     */
    bool is_none(const vec<bool3>& alpha) const { 
      return alpha[ ptr_ws(0) ] == bool3::None && alpha[ ptr_ws(1) ] == bool3::None;
    }

    /**
     * @brief check wether given ind is watched by xcls
     * 
     * @param ind indet to check
     * @return true if and only if ind is watched by xcls
     */
    bool watches(const var_t& ind) const {
      return (ptr_ws(0) == ind) || (ptr_ws(1) == ind);
    }

    
    /**
     * @brief returns the unit if is_unit is true (i.e. returns the first xlit)
     * 
     * @return xlit unit that this clause was reduced to
     */
    xlit get_unit() const { return xlits[0]; };

    /**
     * @brief given that xcls is a unit under given assignments, returns this (reduced) unit
     * 
     * @param assignments current assignments
     * @return xlit unit
     */
    xlit get_unit(const vec<xlit>& assignments) const {
      const xcls cls = to_xcls().reduce(assignments);
      xlit unit = cls.get_unit();
      unit.reduce(assignments);
      return unit;
    }

    /**
     * @brief determines if xcls is unit under given assignments
     * @note is_unit(assignments) does NOT imply is_unit(dl_count) (!)
     * 
     * @param assignments current assignments
     * @return true iff xcls is a unit under assignments
     */
    bool is_unit(const vec<xlit>& assignments) const {
      xcls cls = to_xcls().reduce(assignments);
      return cls.is_unit();
    }

    /**
     * @brief sets the xclss to be a unit, i.e., forces is_unit(dl_count) to return true, and ensures that get_unit() returns the correct xlit; assumes that xcls is a unit under the given assignment
     * 
     * @param assignments current assignments under which the clause is a unit!
     * @param dl_count current dl_count of solver
     * @param dl current dl
     */
    void set_unit(const vec<xlit>& assignments, const vec<var_t>& dl_count, const var_t& dl) {
      assert(is_unit(assignments));
      //find first xlit in cls that does NOT reduce to 1
      var_t i = 0;
      xlit l_;
      do {
        l_ = xlits[i];
        l_.reduce(assignments);
        ++i;
      } while (l_.is_one());
      //swap xlits[i] to first position
      xlits[i].swap(xlits[0]);
      std::swap(ws[i], ws[0]);
      std::swap(wl_it[i], wl_it[0]);
      std::swap(xlit_dl_count0[i], xlit_dl_count0[0]);
      std::swap(xlit_dl_count1[i], xlit_dl_count1[0]);
      //set dl_count of other watched literal!
      xlit_dl_count1[1] = {dl, dl_count[dl]};
      //now is_unit(dl_count) returns true!
      assert(is_unit(dl_count));
#ifndef NDEBUG
      //check that unit can be correctly retrieved!
      xlit unit = get_unit(assignments);
      xlit unit_ = get_unit();
      unit_.reduce(assignments);
      assert(unit == unit_);
#endif
    };

    var_t size() const { return xlits.size(); };
    
    //vec<var_t> get_LTs() const { vec<var_t> lts; for(const auto& lit : xlits) lts.emplace_back(lit.LT()); return lts; };

    var_t LT(const cls_size_t i) const { return xlits[i].LT(); };

    const vec<xlit>& get_xlits() const { return xlits; };
    
    xlit get_first() const { return xlits[0]; };
    
    bool assert_data_struct() const {
      assert( xlit_dl_count0.size() == xlits.size() );
      assert( xlit_dl_count1.size() == xlits.size() );
      //sanity check to see whether ws[i] is actually contained in xlits[i]
      assert( std::find( xlits[0].begin(), xlits[0].end(), ptr_ws(0)) != xlits[0].end() );
      assert( std::find( xlits[1].begin(), xlits[1].end(), ptr_ws(1)) != xlits[1].end() );

      return true;
    };

    bool eval(const vec<bool>& sol) const { return std::any_of(xlits.begin(), xlits.end(), [&sol](const xlit l){ return l.eval(sol); }); };
};
