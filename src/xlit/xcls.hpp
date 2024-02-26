#pragma once

#include "../misc.hpp"
#include "xlit.hpp"
#include "xsys.hpp"

#include <memory>

class xcls {
  private:
    xsys assVS;

  public:
    xcls() noexcept : assVS(xsys(xlit({0}))) {};
    xcls(const xsys& _assVS) noexcept : assVS(_assVS) {};
    xcls(xsys&& _assVS) noexcept : assVS(std::move(_assVS)) {};
    xcls(xlit&& lin) noexcept { assVS = xsys( std::move( lin.add_one() ) ); };
    xcls(const vec<xlit>& lits_) noexcept {
      auto lits_p1(lits_);
      for(auto& l : lits_p1) l.add_one();
      assVS = xsys( std::move(lits_p1) );
    };
    xcls(vec<xlit>&& lits_) noexcept {
      for(auto& l : lits_) l.add_one();
      assVS = xsys( std::move(lits_) );
    };
    xcls(const list<xlit>& lits_) noexcept {
      auto lits_p1(lits_);
      for(auto& l : lits_p1) l.add_one();
      assVS = xsys( std::move(lits_) );
    };
    xcls(list<xlit>&& lits_) noexcept {
      for(auto& l : lits_) l.add_one();
      assVS = xsys( std::move(lits_) );
    };

    var_t deg() const { return !is_zero() ? assVS.dim() : 0; };

    bool is_zero() const { return assVS.get_pivot_poly_idx().contains(0); };

    bool is_unit() const { return deg()<=1; };

    xlit get_unit() const { assert(is_unit()); return deg()==1 ? assVS.get_non_zero_el().add_one() : xlit(0, false); };

    xcls& reduced(const vec<bool3>& alpha, const vec<var_t>& alpha_dl, const var_t& lvl) {
      list<xlit> lits;
      for(const auto& l : assVS.get_xlits() ) {
        xlit l_(l);
        l_.reduce(alpha, alpha_dl, lvl);
        if(!l_.is_zero()) lits.emplace_back( std::move(l_) );
      }
      assVS = xsys(lits);
      return *this;
    };
    
    xcls& reduced(const vec<bool3>& alpha) {
      list<xlit> lits;
      for(const auto& l : assVS.get_xlits() ) {
        xlit l_(l);
        l_.reduce(alpha);
        if(!l_.is_zero()) lits.emplace_back( std::move(l_) );
      }
      assVS = xsys(lits);
      return *this;
    };
    
    bool update(const xsys& L) {
      bool ret = false;
      for(const auto& l : L.get_xlits()) {
        ret |= assVS.lt_update(l);
      }
      return ret;
    };
    
    //only update if the result does not blow up the linerals!
    bool update_short(const xsys& L) {
      bool ret = false;
      for(const auto& l : L.get_xlits()) {
        ret |= assVS.lt_update_short(l);
      }
      return ret;
    };

    const xsys& get_ass_VS() const { return assVS; };
  
    std::string to_str() const;
};

std::pair<bool, xlit> intersectaffineVS(const xsys& U, const xsys& W);

vec<xlit> intersectVS(const xsys& U, const xsys& W);

xcls sres_opt(const xcls& cl1, const xcls& cl2);
