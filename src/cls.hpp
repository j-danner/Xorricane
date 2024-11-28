#pragma once

#include "misc.hpp"
#include "lineral.hpp"
#include "lin_sys.hpp"

#include <memory>

class cls {
  private:
    lin_sys assVS;

  public:
    cls() noexcept : assVS(lin_sys(lineral({0}))) {};
    cls(const lin_sys& _assVS) noexcept : assVS(_assVS) {};
    cls(lin_sys&& _assVS) noexcept : assVS(std::move(_assVS)) {};
    explicit cls(lineral&& lin) noexcept { assVS = lin_sys( std::move( lin.add_one() ) ); };
    cls(const vec<lineral>& lits_) noexcept {
      auto lits_p1(lits_);
      for(auto& l : lits_p1) l.add_one();
      assVS = lin_sys( std::move(lits_p1) );
    };
    cls(vec<lineral>&& lits_) noexcept {
      for(auto& l : lits_) l.add_one();
      assVS = lin_sys( std::move(lits_) );
    };
    cls(const list<lineral>& lits_) noexcept {
      auto lits_p1(lits_);
      for(auto& l : lits_p1) l.add_one();
      assVS = lin_sys( std::move(lits_) );
    };
    cls(list<lineral>&& lits_) noexcept {
      for(auto& l : lits_) l.add_one();
      assVS = lin_sys( std::move(lits_) );
    };

    var_t deg() const { return !is_zero() ? assVS.dim() : 0; };

    bool is_zero() const { return assVS.get_pivot_poly_idx().contains(0); };
    
    bool is_one() const { return assVS.size()==0; };

    bool is_unit() const { return deg()<=1 || is_zero(); };

    lineral get_unit() const { assert(is_unit()); return deg()==1 ? assVS.get_non_zero_el().add_one() : lineral(0, false); };

    cls& reduced(const vec<bool3>& alpha, const vec<var_t>& alpha_dl, const var_t& lvl) {
      list<lineral> lits;
      for(const auto& l : assVS.get_linerals() ) {
        lineral l_(l);
        l_.reduce(alpha, alpha_dl, lvl);
        if(!l_.is_zero()) lits.emplace_back( std::move(l_) );
      }
      assVS = lin_sys(lits);
      return *this;
    };
    
    cls& reduced(const vec<bool3>& alpha) {
      list<lineral> lits;
      for(const auto& l : assVS.get_linerals() ) {
        lineral l_(l);
        l_.reduce(alpha);
        if(!l_.is_zero()) lits.emplace_back( std::move(l_) );
      }
      assVS = lin_sys(lits);
      return *this;
    };
    
    bool update(const lin_sys& L) {
      bool ret = false;
      for(const auto& l : L.get_linerals()) {
        ret |= assVS.lt_update(l);
      }
      return ret;
    };
    
    //only update if the result does not blow up the linerals!
    bool update_short(const lin_sys& L) {
      bool ret = false;
      for(const auto& l : L.get_linerals()) {
        ret |= assVS.lt_update_short(l);
      }
      return ret;
    };

    const lin_sys& get_ass_VS() const { return assVS; };
  
    std::string to_str() const {
      if(assVS.dim()==0) return "1";
      std::string result = "";
      for(const auto& lit : assVS.get_linerals()) result += lit.plus_one().to_str() + " ";
      result.resize( result.length()-1 );
      return result;
    };
};