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
    lit_watch ws[2] = {0,0};

    /**
     * @brief dl_count when xlit_watch was instantiated, req to check if xlit is active!
     */
    std::pair<var_t,var_t> dl_c = {0,0};

    void init(const vec<bool3>& alpha, const vec<var_t>& alpha_dl) {
      assert(!xlit::is_zero());
      if(idxs.size()<2) return;
      if( to_str() == "x13+x19+x20+1") {
        assert(idxs.size()>0);
      }

      //track two inds with highest dl (where 'unassigned' has dl = alpha.size()+1, i.e., is prioritized)
      var_t max_w1 = 0, max_dl1 = alpha_dl[idxs[max_w1]]==0 ? alpha.size()+1 : alpha_dl[idxs[max_w1]];
      var_t max_w2 = 1, max_dl2 = alpha_dl[idxs[max_w2]]==0 ? alpha.size()+1 : alpha_dl[idxs[max_w2]];
      if(max_dl1 < max_dl2) { std::swap(max_w1, max_w2); std::swap(max_dl1, max_dl2); }
      //init watches greedily
      for(var_t i=2; i<idxs.size(); ++i) {
        if(alpha[idxs[i]] != bool3::None) {
          //idxs[i] already assigned! -- update max_w1, max_w2; in case dl is high enough
          if(alpha_dl[idxs[i]] > max_dl1) {
            max_dl2 = max_dl1;
            max_w2 = max_w1;
            max_dl1 = alpha_dl[idxs[i]];
            max_w1 = i;
          } else if(alpha_dl[idxs[i]] > max_dl2) {
            max_dl2 = alpha_dl[idxs[i]];
            max_w2 = i;
          }
        } else if (max_dl2 < alpha.size()+1) {
          //idxs[i] is unassigned; treat it as if it has dl = alpha.size()+1; (note that there is no higher dl; i.e., it suffies to update max_dl1)
          max_dl2 = max_dl1;
          max_w2 = max_w1;
          max_dl1 = alpha.size()+1;
          max_w1 = i;
        } else {
          //max_dl1 = max_dl2 = alpha.size()+1; i.e., both watches are unassigned; we can stop the search!
          break;
        }
      }
      //init watches, ws[0] gets the higher dl
      ws[0] = max_w1;
      ws[1] = max_w2;
      //if ws[0] is unassigned, swap! (to avoid that ws[0] is unassigned, but ws[1] is assigned)
      if(alpha[idxs[ws[0]]] == bool3::None) { std::swap(ws[0], ws[1]); }
      assert( assert_data_struct(alpha) );
    }

  public:
    xlit_watch() {};
    xlit_watch(xlit&& lit, const vec<bool3>& alpha, const vec<var_t>& alpha_dl, const var_t& lvl, const vec<var_t>& dl_count) : xlit(std::move(lit)), dl_c({lvl, dl_count[lvl]}) { init(alpha, alpha_dl); };
    xlit_watch(const xlit& lit, const vec<bool3>& alpha, const vec<var_t>& alpha_dl, const var_t& lvl, const vec<var_t>& dl_count) : xlit(lit), dl_c({lvl, dl_count[lvl]}) { init(alpha, alpha_dl); }

    ~xlit_watch() = default;

    /**
     * @brief return the watched literal
     * @return xlit corr to watched xlit
     */
    xlit to_xlit() const { return xlit(idxs, p1, true); };
    
    /**
     * @brief checks whether the polynomial is assigning
     * 
     * @param alpha current bool3-assignment
     * @return true if assigning
     */
    bool is_assigning(const vec<bool3>& alpha) const {
      return idxs.size()<2 || alpha[idxs[ws[0]]] != bool3::None;
    };

    /**
     * @brief checks whether xlit_watch watches given lt
     * 
     * @param lt literal to check
     * @return true iff lt is watched
     */
    bool watches(const var_t& lt) const {
      return idxs[ws[0]] == lt || idxs[ws[1]] == lt;
    };


    inline bool is_one(const vec<bool3>& alpha) const { 
      //both watches are assigned
      return xlit::is_one() || ( is_assigning(alpha) && alpha[get_assigning_ind()] != bool3::None && eval(alpha) == true );
    };

    inline bool is_zero(const vec<bool3>& alpha) const {
      return xlit::is_zero() || ( is_assigning(alpha) && alpha[get_assigning_ind()] != bool3::None && eval(alpha) == false );
    };

    inline bool is_active(const vec<var_t>& dl_count) const {
      return dl_count[ dl_c.first ] == dl_c.second;
    }


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
      return idxs.size()==0 ?  0 : idxs[ws[1]];
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
     * @return <ind,val> xlit is assigning iff val!=bool3::None; in that case we have x(ind) = val
     */
    std::tuple<var_t,bool3> get_assignment(const vec<bool3>& alpha) const {
      return {get_assigning_ind(), get_assigning_val(alpha)};
    }

    
    /**
     * @brief returns lvl at which the xlit became assigning
     * @note assumes that xlit is assigning
     * 
     * @param alpha current bool3-assignment
     * @param alpha_dl dl of alpha
     * @return var_t lvl at which the xlit became assigning
     */
    var_t get_assigning_lvl(const vec<var_t>& alpha_dl) const {
      return idxs.size()==0 ? dl_c.first : std::max( alpha_dl[idxs[ws[0]]], dl_c.first );
    };

    /**
     * @brief updates xlit_watch according to the new assigned literal new_lit, dl_count, dl and alpha.
     * 
     * @param new_lit literal that was newly assigned
     * @param alpha current bool3-assignment
     * @return var_t,xlit_upd_ret xlit_upd_ret is ASSIGNING if xlit is assigning; UNIT otherwise; var_t is the new watched literal
     */
    std::pair<var_t,xlit_upd_ret> update(const var_t& new_lit, const vec<bool3>& alpha) {
      assert(idxs[ws[0]] == new_lit || idxs[ws[1]] == new_lit);
      assert(alpha[new_lit] != bool3::None);

      //only update if xlit is not assigning! (i.e. idxs[ws[0]] AND idxs[ws[1]] are unassigned)
      //if(is_assigning(alpha)) return {new_lit, xlit_upd_ret::ASSIGNING};
      //todo this leads to bugs when x1 and x2 are in x1+x2+x3+x4 are watched and x1 gets assigned; immediately stops here...

      if(to_str() == "x12+x13+x14+x15+x16+x17+x18+x19" && new_lit==17) {
        assert( ws[0]!=ws[1] );
      }

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
      //assert( assert_data_struct(alpha) ); //note: data structures might be 'violated' if gcp_queue is NOT empty, i.e., update is not yet finished...

      return {idxs[ws[0]], ws[0]==new_w ? xlit_upd_ret::ASSIGNING : xlit_upd_ret::UNIT};
      //if(new_w == ws[1]) {
      //  //if all literals are assigned, then the xlit is assigning; ws remains the same
      //  return {idxs[ws[1]], xlit_upd_ret::ASSIGNING};
      //} else {
      //  //otherwise, update the watched literal
      //  ws[1] = new_w;
      //  return {idxs[ws[1]], xlit_upd_ret::UNIT};
      //}
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
      if(alpha[idxs[ws[0]]] != bool3::None) {
        for(var_t i=0; i<idxs.size(); ++i) {
          if(i!=ws[0] && i!=ws[1]) assert(alpha[idxs[i]] != bool3::None);
        }
      }
      return true;
    };
};
