#pragma once

#include "../misc.hpp"
#include "xlit.hpp"
#include "xcls.hpp"
#include "xsys.hpp"

using lit_watch = var_t;

/**
 * @brief return type for update of xcls_watch
 */
enum class xlit_upd_ret { ASSIGNING, UNIT };


class xlit_watch : public xlit
{
  private:
    /**
     * @brief literal watches; offset into idxs-set of idxs
     */
    lit_watch ws[3] = {0,0,0};

    /**
     * @brief dl_count when xlit_watch was instantiated, req to check if xlit is active!
     */
    std::pair<var_t,var_t> dl_c = {0,0};

    typedef std::list<xlit_watch>::iterator xlit_w_it;
    /**
     * @brief index of reason clause
     */
    std::list< xlit_w_it > reason_cls_idxs;
    var_t reason_cls_idx = -1;

  public:
    xlit_watch() {};
    xlit_watch(const xlit& lit, const vec<bool3>& alpha, const vec<var_t>& alpha_dl, const vec<dl_c_t>& dl_count) noexcept : xlit(lit) { init(alpha, alpha_dl, dl_count); }
    xlit_watch(xlit&& lit, const vec<bool3>& alpha, const vec<var_t>& alpha_dl, const vec<dl_c_t>& dl_count) noexcept : xlit(std::move(lit)) { init(alpha, alpha_dl, dl_count); };
    xlit_watch(const xlit& lit, const vec<bool3>& alpha, const vec<var_t>& alpha_dl, const vec<dl_c_t>& dl_count, const var_t& rs) noexcept : xlit(lit), reason_cls_idx(rs) { init(alpha, alpha_dl, dl_count); }
    xlit_watch(xlit&& lit, const vec<bool3>& alpha, const vec<var_t>& alpha_dl, const vec<dl_c_t>& dl_count, const var_t& rs) noexcept : xlit(std::move(lit)), reason_cls_idx(rs) { 
      init(alpha, alpha_dl, dl_count);
    };
    xlit_watch(const xlit& lit, const vec<bool3>& alpha, const vec<var_t>& alpha_dl, const vec<dl_c_t>& dl_count, const std::list< xlit_w_it >& rs) noexcept : xlit(lit), reason_cls_idxs(rs) { init(alpha, alpha_dl, dl_count); }
    xlit_watch(xlit&& lit, const vec<bool3>& alpha, const vec<var_t>& alpha_dl, const vec<dl_c_t>& dl_count, const std::list< xlit_w_it >& rs) noexcept : xlit(std::move(lit)), reason_cls_idxs(rs) { init(alpha, alpha_dl, dl_count); };
    //copy ctor
    xlit_watch(const xlit_watch& o) noexcept : xlit(o), dl_c(o.dl_c), reason_cls_idxs(o.reason_cls_idxs) {
      ws[0] = o.ws[0]; ws[1]=o.ws[1]; ws[2]=o.ws[2];
    }
    //mv ctor
    xlit_watch(xlit_watch&& o) noexcept : xlit(std::move(o)), dl_c(std::move(o.dl_c)), reason_cls_idxs(std::move(o.reason_cls_idxs)) {
      std::swap(ws, o.ws);
    }

    ~xlit_watch() = default;
    
    void init(const vec<bool3>& alpha, const vec<var_t>& alpha_dl, const vec<dl_c_t>& dl_count) {
      ws[0] = 0;
      ws[1] = 0;
      if(idxs.size()<2) return;

      //track two inds with highest dl (where 'unassigned' is (var_t) -1)
      var_t max_w1 = 0, max_dl1 = alpha_dl[idxs[max_w1]];
      var_t max_w2 = 1, max_dl2 = alpha_dl[idxs[max_w2]];
      if(max_dl1 < max_dl2) { std::swap(max_w1, max_w2); std::swap(max_dl1, max_dl2); }
      //init watches greedily
      for(var_t i=2; i<idxs.size(); ++i) {
        if(alpha_dl[idxs[i]] > max_dl1) {
          max_dl2 = max_dl1;
          max_w2 = max_w1;
          max_dl1 = alpha_dl[idxs[i]];
          max_w1 = i;
        } else if(alpha_dl[idxs[i]] > max_dl2) {
          max_dl2 = alpha_dl[idxs[i]];
          max_w2 = i;
        }
        if(max_dl2 == max_dl1 && max_dl1 == (var_t) -1) break;
      }
      //init watches, ws[0] gets the higher dl
      ws[0] = max_w1;
      ws[1] = max_w2;
      //if ws[0] is unassigned, swap! (to avoid that ws[0] is unassigned, but ws[1] is assigned)
      if(alpha[get_wl0()] == bool3::None) {
        std::swap(ws[0], ws[1]);
      } else {
        const var_t lvl = alpha_dl[get_wl0()];
        dl_c = {lvl, dl_count[lvl]};
      }
      assert( assert_data_struct(alpha) );
    }

    /**
     * @brief return the watched literal
     * @return xlit corr to watched xlit
     */
    xlit to_xlit() const { return xlit(idxs, p1, presorted::yes); };
    
    /**
     * @brief checks whether the polynomial is assigning
     * 
     * @param alpha current bool3-assignment
     * @return true if assigning
     */
    inline bool is_assigning(const vec<bool3>& alpha) const {
      return is_assigning() || alpha[get_wl0()] != bool3::None;
    };
    
    inline bool is_assigning() const {
      return xlit::is_assigning();
    };

    /**
     * @brief checks whether xlit_watch watches given lt
     * 
     * @param lt literal to check
     * @return true iff lt is watched
     */
    bool watches(const var_t& lt) const {
      return !idxs.empty() && (get_wl0() == lt || idxs[ws[1]] == lt);
    };


    inline bool is_one(const vec<bool3>& alpha) const { 
      //both watches are assigned
      return xlit::is_one() || ( is_assigning(alpha) && alpha[get_assigning_ind()] != bool3::None && eval(alpha) == false );
    };

    inline bool is_zero() const { return xlit::is_zero(); };

    inline bool is_zero(const vec<bool3>& alpha) const {
      const auto ret = xlit::is_zero() || ( is_assigning(alpha) && alpha[get_assigning_ind()] != bool3::None && eval(alpha) == true );
      assert(ret == reduced(alpha).is_zero());
      return ret;
    };
    
    inline bool is_active(const vec<bool3>& alpha) const {
      return !is_assigning(alpha);
    };

    inline bool is_active(const vec<dl_c_t>& dl_count) const {
      return dl_count[ dl_c.first ] != dl_c.second;
    };


    /**
     * @brief get the first watched literal
     * @return the first watched literal
     */
    var_t get_wl0() const { return idxs[ws[0]]; };
    
    /**
     * @brief get the second watched literal
     * @return the second watched literal
     */
    var_t get_wl1() const { return idxs[ws[1]]; };

    /**
     * @brief returns the equivalent lit, if this is an equivalence
     */
    var_t get_equiv_lit() const { return xlit::is_equiv() ? ( get_wl0()==LT() ? get_wl1() : get_wl0() ) : 0; }

    /**
     * @brief get assigning xlit
     * 
     * @param alpha current bool3-assignment
     * @return xlit assigning xlit
     */
    xlit get_assigning_xlit(const vec<bool3>& alpha) const {
      return xlit(get_assigning_ind(), get_assigning_val(alpha)==bool3::True);
    }
    
    /**
     * @brief get assigning xlit
     * 
     * @param alpha current bool3-assignment
     * @return var_t assigning ind
     */
    var_t get_assigning_ind() const {
      return idxs.size()==0 ? 0 : get_wl1();
    }

    /**
     * @brief get assigning val
     * 
     * @param alpha current bool3-assignment
     * @return bool3 assigning val, is bool3::None iff xlit is not assigning
     */
    bool3 get_assigning_val(const vec<bool3>& alpha) const {
      return is_assigning(alpha) ? to_bool3( (alpha[get_assigning_ind()]==bool3::True) ^ !partial_eval(alpha)) : bool3::None;
    }
    
    /**
     * @brief get assigning xlit
     * 
     * @param alpha current bool3-assignment
     * @return <ind,val> xlit is assigning iff val!=bool3::None; in that case we have x(ind) = val; otherwise val == bool3::None
     */
    std::tuple<var_t,bool3> get_assignment(const vec<bool3>& alpha) const {
      const var_t ass_ind = get_assigning_ind();
      const bool3 ass_val = get_assigning_val(alpha);
      if(alpha[ass_ind]==bool3::None || alpha[ass_ind]==ass_val) return {ass_ind, ass_val};
      return {0, bool3::True};
    }

    
    /**
     * @brief returns lvl at which the xlit became assigning. BEWARE: the lvl at which the literal was constructed might be higher than the assigning-level!
     * @note assumes that xlit is assigning
     * 
     * @param alpha current bool3-assignment
     * @param alpha_dl dl of alpha
     * @return var_t lvl at which the xlit became assigning
     */
    var_t get_assigning_lvl(const vec<var_t>& alpha_dl) const {
      return (idxs.size()==0 || alpha_dl[get_wl0()] == (var_t) -1) ? 0 : alpha_dl[get_wl0()];
    };

    /**

    /**
     * @brief returns list of xlit_watches whose reasones need to be resolved to get this lineral
     * @return list< xlit_w_it > list of xlit_watches
     */
    const std::list< xlit_w_it >& get_reason_idxs() const { return reason_cls_idxs; }
    
    /**
     * @brief returns the reason clause index, if this lineral was derived from an xcls_watch
     * @return var_t reason clause index
     */
    const var_t& get_reason_idx() const { return reason_cls_idx; }

    void set_reason_idx(const var_t& idx) { reason_cls_idxs.clear(); reason_cls_idx = idx; }

    /**
     * @brief removes literal upd_lt from lineral, if is present
     * 
     * @param lt literal to be removed
     * @param val value that is assigned to literal
     * @return true iff upd_lt was removed
     */
    bool rm(const var_t lt, const bool3 val) {
      if(idxs.empty()) return false;
      assert( !watches(lt) );
      const auto wl0 = idxs[ws[0]];
      const auto wl1 = idxs[ws[1]];
      if ( !xlit::rm(lt, val) ) return false;
      //adapt ws[0] and ws[1] accordingly:
      if(wl0 > lt) ws[0]--;
      if(wl1 > lt) ws[1]--;
      assert(idxs[ws[0]] == wl0);
      assert(idxs[ws[1]] == wl1);
      return true;
    }

    /**
     * @brief updates xlit_watch according to the new assigned literal new_lit, dl_count, dl and alpha.
     * 
     * @param new_lit literal that was newly assigned
     * @param alpha current bool3-assignment
     * @param lvl current dl
     * @param dl_count current dl_count
     * @return var_t,xlit_upd_ret xlit_upd_ret is ASSIGNING if xlit is assigning; UNIT otherwise; var_t is the new watched literal
     */
    std::pair<var_t,xlit_upd_ret> update(const var_t& new_lit, const vec<bool3>& alpha, const var_t& lvl, const vec<dl_c_t>& dl_count) {
      assert(idxs[ws[0]] == new_lit || idxs[ws[1]] == new_lit);
      assert(alpha[new_lit] != bool3::None);

      //only update if xlit is not assigning! (i.e. idxs[ws[0]] AND idxs[ws[1]] are unassigned)
      //if(is_assigning(alpha)) return {new_lit, xlit_upd_ret::ASSIGNING};
      //todo this leads to bugs when x1 and x2 are in x1+x2+x3+x4 are watched and x1 gets assigned; immediately stops here...

      //w.l.o.g. ws[0] needs to be updated -- also ensures that invariants are satisfied after update
      if(new_lit == idxs[ws[1]]) std::swap(ws[0], ws[1]);

      //choose new indet to watch
      var_t new_w = ws[0];
      while(new_w < idxs.size() && (alpha[ idxs[new_w] ] != bool3::None || new_w == ws[1])) new_w++;
      //wrap around if necessary
      if(new_w == idxs.size()) new_w = 0;
      while(new_w!=ws[0] && (alpha[ idxs[new_w] ] != bool3::None || new_w==ws[1])) new_w++;
      //new_w == ws iff all literals are assigned!
      std::swap(ws[0], new_w);
      assert( assert_data_struct(alpha) );
      if(ws[0]==new_w) {
        dl_c = {lvl, dl_count[lvl]};
        return {get_wl0(), xlit_upd_ret::ASSIGNING};
      }
      return {get_wl0(), xlit_upd_ret::UNIT};
    };

    bool assert_data_struct(const vec<bool3>& alpha) const {
      if(idxs.size()<2) return true;
      //assert(alpha_dl[idxs[ws[1]]]==0 || alpha_dl[idxs[ws[1]]] <= alpha_dl[idxs[ws[0]]]);
      assert(ws[0] != ws[1]);
      assert(ws[0] < idxs.size());
      assert(ws[1] < idxs.size());
      if(alpha[idxs[ws[1]]] != bool3::None) assert(alpha[idxs[ws[0]]] != bool3::None);
      //assert that the xlit is assigning under alpha iff ws[1] is assigned
      if(is_assigning(alpha)) assert(alpha[idxs[ws[0]]] != bool3::None);
      if(alpha[get_wl0()] != bool3::None) {
        for(var_t i=0; i<idxs.size(); ++i) {
          if(i!=ws[0] && i!=ws[1]) assert(alpha[idxs[i]] != bool3::None);
        }
      }
      return true;
    };
    
    bool assert_data_struct(const vec<bool3>& alpha, [[maybe_unused]] const vec<dl_c_t>& dl_count) const {
      assert(is_zero() || is_active(dl_count) || is_assigning(alpha));
      assert(reason_cls_idx == (var_t) -1 || reason_cls_idxs.empty());
      return assert_data_struct(alpha);
    }

    /**
     * @brief reduce with alpha
     * 
     * @param alpha current alpha-assignments
     * @param alpha_dl dl of alpha-assignments
     * @return true iff inds were removed
     * 
     * @note if it returns true, may invalidate dl_c, i.e., is_assigning(dl_count) (!)
     */
    bool reduce(const vec<bool3>& alpha, const vec<var_t>& alpha_dl, const vec<dl_c_t>& dl_count) {
      const bool ret = xlit::reduce(alpha);
      if( ret ) init(alpha, alpha_dl, dl_count);
      assert(assert_data_struct(alpha));
      return ret;
    };

    xlit_watch& operator=(xlit_watch&& other) noexcept {
      std::swap(ws, other.ws);
      dl_c = std::move(other.dl_c);
      reason_cls_idxs = std::move(other.reason_cls_idxs);
      reason_cls_idx = other.reason_cls_idx;
      xlit::operator=(other);
      return *this;
    }
    
    xlit_watch& operator=(const xlit_watch& other) noexcept {
      ws[0] = other.ws[0]; ws[1] = other.ws[1]; ws[2] = other.ws[2];
      dl_c = other.dl_c;
      reason_cls_idxs = other.reason_cls_idxs;
      reason_cls_idx = other.reason_cls_idx;
      xlit::operator=(other);
      return *this;
    }
};
