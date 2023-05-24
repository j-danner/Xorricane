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
    xcls(const vec<xlit>& lits_) noexcept {
      auto lits_p1(lits_);
      for(auto& l : lits_p1) l.add_one();
      assVS = xsys( std::move(lits_p1) );
    };
    xcls(vec<xlit>&& lits_) noexcept {
      for(auto& l : lits_) l.add_one();
      assVS = xsys( std::move(lits_) );
    };

    var_t deg() const { return !is_zero() ? assVS.dim() : 0; };

    bool is_zero() const { return assVS.get_pivot_poly_idx().contains(0) || assVS.size()==0; };

    bool is_unit() const { return deg()==1; };

    xlit get_unit() const { assert(is_unit()); return assVS.get_non_zero_el().add_one(); };

    xcls& reduce(const vec<xlit>& assignments) {
      std::list<xlit> lits;
      for(const auto& l : assVS.get_xlits() ) {
        xlit l_(l);
        l_.reduce(assignments);
        if(!l_.is_zero()) lits.emplace_back( std::move(l_) );
      }
      assVS = xsys(lits);
      return *this;
    };
    
    xcls update(const vec<xlit>& assignments) const {
      vec<xlit> lits;
      for(const auto& l : assVS.get_xlits() ) {
        xlit l_(l);
        l_.reduce(assignments);
        if(!l_.is_zero()) lits.emplace_back( std::move(l_) );
      }
      return xcls( xsys(lits) );
    };
    
    xcls update(const xsys L) const {
      vec<xlit> lits;
      for(const auto& l : assVS.get_xlits() ) {
        xlit l_(l);
        l_.reduce(L);
        if(!l_.is_zero()) lits.emplace_back( std::move(l_) );
      }
      return xcls( xsys(lits) );
    };

    const xsys& get_ass_VS() const { return assVS; };
  
    std::string to_str() const;
};

std::pair<bool, xlit> intersectaffineVS(const xsys& U, const xsys& W);

vec<xlit> intersectVS(const xsys& U, const xsys& W);

xcls sres_opt(xcls& cl1, xcls& cl2);
