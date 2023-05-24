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


class xlit_watch : private xlit
{
  private:
    /**
     * @brief literal watches; offset into idxs-set of idxs
     */
    lit_watch ws[2] = {0,0};

  public:
    xlit_watch() {};
    xlit_watch(xlit& lit, const vec<bool3>& alpha, const vec<var_t>& alpha_dl) : xlit(lit) {
      assert(!is_zero());
      if(idxs.size()<2) return;
      //track two inds with highest dl (where 'unassigned' has dl = alpha.size()+1, i.e., is prioritized)
      var_t max_w1 = 0, max_dl1 = alpha_dl[idxs[max_w1]];
      var_t max_w2 = 1, max_dl2 = alpha_dl[idxs[max_w2]];
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
    };
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
     * @brief get assigning xlit
     * 
     * @param alpha current bool3-assignment
     * @return xlit assigning xlit
     */
    xlit get_assigning_xlit(const vec<bool3>& alpha) const {
      return xlit(idxs[ws[1]], partial_eval(alpha));
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
      return alpha_dl[idxs[ws[0]]];
    };

    /**
     * @brief updates xlit_watch according to the new assigned literal new_lit, dl_count, dl and alpha.
     * 
     * @param new_lit literal that was newly assigned
     * @param alpha current bool3-assignment
     * @return var_t,xlit_upd_ret xlit_upd_ret is ASSIGNING if xlit is assigning; UNIT otherwise
     */
    std::pair<var_t,xlit_upd_ret> update(const var_t& new_lit, const vec<bool3>& alpha) {
      assert(idxs[ws[0]] == new_lit || idxs[ws[1]] == new_lit);
      assert(alpha[new_lit] != bool3::None);

      //only update if xlit is not assigning! (i.e. idxs[ws[0]] AND idxs[ws[1]] are unassigned)
      if(is_assigning(alpha)) return {new_lit, xlit_upd_ret::ASSIGNING};

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
