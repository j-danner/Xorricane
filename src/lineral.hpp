// Copyright (c) 2022-2025 Julian Danner <julian@danner-web.de>
//
// Permission is hereby granted, free of charge, to any person obtaining a copy of
// this software and associated documentation files (the "Software"), to deal in
// the Software without restriction, including without limitation the rights to
// use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
// the Software, and to permit persons to whom the Software is furnished to do so,
// subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
// FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
// COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
// IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
// CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

#pragma once

#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <memory>

#include "bit/vector.h"
#include "misc.hpp"
//forward declaration of class lin_sys
class lin_sys;

enum class presorted { yes, no };

enum class cnst { zero, one };

//dense implementation of a xor-literal using bit::vector
//bit 0 = constant term (p1), bit i (i>=1) = variable i is present
class lineral
{
    friend class lineral_watch;

    protected:
        bit::vector<> bitvec_;  // bit 0 = constant, bit i (i>=1) = variable i

    private:
        void build_from_vec(const vec<var_t>& v, bool p1_) noexcept {
            const var_t max_v = v.empty() ? 0 : v.back();
            bitvec_.resize(max_v + 1);
            bitvec_.reset();
            if(p1_) bitvec_.set(0);
            for(const auto x : v) bitvec_.set(x);
        }

        //constructor for internal use only (presorted, no index-0 handling needed)
        lineral(const vec<var_t>& idxs_, const bool p1_) noexcept {
            build_from_vec(idxs_, p1_);
        }

    public:
        // Iterator over variable indices (skips bit 0 = constant)
        struct VarIter {
            using iterator_category = std::forward_iterator_tag;
            using value_type        = var_t;
            using difference_type   = std::ptrdiff_t;
            using pointer           = const var_t*;
            using reference         = var_t;
            const bit::vector<>* bv;
            std::size_t pos;
            var_t operator*() const { return static_cast<var_t>(pos); }
            VarIter& operator++() { pos = bv->next_set(pos); return *this; }
            VarIter operator++(int) { VarIter tmp = *this; ++(*this); return tmp; }
            bool operator!=(const VarIter& o) const { return pos != o.pos; }
            bool operator==(const VarIter& o) const { return pos == o.pos; }
        };
        using iterator = VarIter;

        iterator begin() const { return VarIter{&bitvec_, bitvec_.next_set(0)}; }
        iterator end()   const { return VarIter{&bitvec_, bit::vector<>::npos}; }

        // next variable strictly after v; returns (var_t)-1 if none
        inline var_t next_var_after(var_t v) const noexcept {
            auto p = bitvec_.next_set(static_cast<std::size_t>(v));
            return p == bit::vector<>::npos ? static_cast<var_t>(-1) : static_cast<var_t>(p);
        }
        // first variable (bit >= 1); returns (var_t)-1 if none
        inline var_t first_var() const noexcept {
            auto p = bitvec_.next_set(0);
            return p == bit::vector<>::npos ? static_cast<var_t>(-1) : static_cast<var_t>(p);
        }
        // last variable (bit >= 1); returns (var_t)-1 if none
        inline var_t last_var() const noexcept {
            auto p = bitvec_.final_set();
            return (p == bit::vector<>::npos || p == 0) ? static_cast<var_t>(-1) : static_cast<var_t>(p);
        }
        // previous variable strictly before v (skips bit 0 = constant); returns (var_t)-1 if none
        inline var_t prev_var_before(var_t v) const noexcept {
            if(v == 0) return static_cast<var_t>(-1);
            auto p = bitvec_.prev_set(static_cast<std::size_t>(v));
            return (p == bit::vector<>::npos || p == 0) ? static_cast<var_t>(-1) : static_cast<var_t>(p);
        }

        lineral() noexcept {}
        lineral(lineral&& l) noexcept : bitvec_(std::move(l.bitvec_)) {}
        lineral(const lineral& l) noexcept : bitvec_(l.bitvec_) {}

        // From sorted or unsorted vec<var_t>; index 0 in vec means toggle constant
        lineral(const vec<var_t>& idxs_, const presorted b = presorted::no) noexcept {
            if(b == presorted::no) {
                vec<var_t> tmp = idxs_;
                std::sort(tmp.begin(), tmp.end());
                bool p1_ = (!tmp.empty() && tmp[0] == 0);
                if(p1_) tmp.erase(tmp.begin());
                build_from_vec(tmp, p1_);
            } else {
                bool p1_ = (!idxs_.empty() && idxs_[0] == 0);
                if(p1_) {
                    vec<var_t> tmp(idxs_.begin()+1, idxs_.end());
                    build_from_vec(tmp, true);
                } else {
                    build_from_vec(idxs_, false);
                }
            }
        }
        lineral(vec<var_t>&& idxs_, const presorted b = presorted::no) noexcept {
            vec<var_t> tmp = std::move(idxs_);
            if(b == presorted::no) std::sort(tmp.begin(), tmp.end());
            bool p1_ = (!tmp.empty() && tmp[0] == 0);
            if(p1_) tmp.erase(tmp.begin());
            build_from_vec(tmp, p1_);
        }
        lineral(const vec<var_t>& idxs_, const bool p1_, const presorted b) noexcept {
            if(b == presorted::no) {
                vec<var_t> tmp = idxs_;
                std::sort(tmp.begin(), tmp.end());
                build_from_vec(tmp, p1_);
            } else {
                build_from_vec(idxs_, p1_);
            }
        }
        lineral(vec<var_t>&& idxs_, const bool p1_, const presorted b = presorted::no) noexcept {
            vec<var_t> tmp = std::move(idxs_);
            if(b == presorted::no) std::sort(tmp.begin(), tmp.end());
            build_from_vec(tmp, p1_);
        }
        // Single variable + optional constant; original: if idx==0 then p1^=true (so const = !p1_)
        lineral(const var_t& idx, const bool p1_) noexcept {
            if(idx == 0) {
                bitvec_.resize(1);
                bitvec_.reset();
                // original behaviour: idx 0 in idxs triggers p1^=true from false => p1=true, then erase.
                // So lineral(0,false) => p1=true, idxs empty => constant 1
                // And lineral(0,true) => p1=true XOR true = false, idxs empty => constant 0 = zero
                if(!p1_) bitvec_.set(0);
            } else {
                bitvec_.resize(idx + 1);
                bitvec_.reset();
                bitvec_.set(idx);
                if(p1_) bitvec_.set(0);
            }
        }
        explicit lineral(const cnst zero_one) noexcept {
            if(zero_one == cnst::one) { bitvec_.resize(1); bitvec_.set(0); }
        }

        ~lineral() = default;

        // init() is kept for API compatibility; bitvec_ IS the representation
        inline void init() noexcept {}

        inline void clear() noexcept { bitvec_.reset(); }

        inline bool is_one()      const { return bitvec_.count() == 1 && bitvec_.size() > 0 && bitvec_.test(0); }
        inline bool is_zero()     const { return bitvec_.none(); }
        inline bool is_constant() const { return first_var() == static_cast<var_t>(-1); }

        inline bool3 as_bool3() const { return (size()!=1 && !is_one()) ? bool3::None : (has_constant() ? bool3::True : bool3::False); }
        inline bool is_equiv()     const { return size()==2; }
        inline bool is_assigning() const { return size()<=1; }

        inline bool has_constant() const { return bitvec_.size() > 0 && bitvec_.test(0); }

        inline var_t LT() const {
            auto v = first_var();
            return v == static_cast<var_t>(-1) ? 0 : v;
        }

        size_t hash() const;

        inline lineral plus_one() const { lineral r(*this); r.add_one(); return r; }

        inline lineral& add_one() noexcept {
            if(bitvec_.size() == 0) bitvec_.resize(1);
            bitvec_.flip(0);
            return *this;
        }

        vec<var_t> support() const;

        bool reduce(const lin_sys& sys);
        bool reduce_short(const lin_sys& sys);
        bool reduce(const vec<lineral>& assignments, const vec<var_t>& assignments_dl, const var_t& lvl);
        bool reduce(const vec<equivalence>& equiv_lits);
        bool reduce(const vec<equivalence>& equiv_lits, const var_t& lvl);
        bool reduce(const vec<bool3>& alpha);
        bool reduce(const vec<bool3>& alpha, const vec<equivalence>& equiv_lits);
        bool reduce(const vec<bool3>& alpha, const vec<var_t>& alpha_dl, const var_t& lvl);
        bool reduce(const vec<lineral>& assignments);
        lineral reduced(const vec<lineral>& assignments) const { lineral ret(*this); ret.reduce(assignments); return ret; }
        lineral reduced(const vec<bool3>& alpha) const { lineral ret(*this); ret.reduce(alpha); return ret; }
        lineral reduced(const vec<bool3>& alpha, const vec<var_t>& alpha_dl, const var_t& lvl) const { lineral ret(*this); ret.reduce(alpha, alpha_dl, lvl); return ret; }
        lineral reduced(const vec<equivalence>& equiv_lits) { lineral ret(*this); ret.reduce(equiv_lits); return ret; }
        lineral reduced(const vec<bool3>& alpha, const vec<equivalence>& equiv_lits) const { lineral ret(*this); ret.reduce(alpha, equiv_lits); return ret; }
        vec<var_t> reducers(const vec<lineral>& assignments) const;

        inline var_t get_max_var() const {
            const auto p = bitvec_.final_set();
            return (p == bit::vector<>::npos || p == 0) ? 0 : static_cast<var_t>(p);
        }

        // Returns variable indices as a sorted vector (does NOT include index 0 for constant)
        inline vec<var_t> get_idxs_() const {
            vec<var_t> r;
            for(auto v = first_var(); v != static_cast<var_t>(-1); v = next_var_after(v)) r.push_back(v);
            return r;
        }
        // Returns all indices including 0 if constant is set
        inline vec<var_t> get_idxs() const {
            vec<var_t> r;
            if(has_constant()) r.push_back(0);
            for(auto v = first_var(); v != static_cast<var_t>(-1); v = next_var_after(v)) r.push_back(v);
            return r;
        }

        inline std::size_t size() const {
            return bitvec_.count() - (has_constant() ? 1 : 0);
        }

        std::string to_str() const;
        std::string to_xnf_str() const;
        std::string to_full_str(var_t num_vars) const;

        lineral operator+(const lineral &other) const;
        lineral& operator+=(const lineral& other);
        inline lineral& operator=(const lineral& other) noexcept { bitvec_ = other.bitvec_; return *this; }
        inline lineral& operator=(lineral&& other) noexcept { bitvec_ = std::move(other.bitvec_); return *this; }

        void swap(lineral& other) noexcept { bitvec_.swap(other.bitvec_); }

        lineral shared_part(const lineral& other) const;

        inline bool operator==(const lineral& other) const {
            // Content-aware comparison: ignore trailing zero bits from different allocation sizes.
            // Two linerals can be logically equal but have different bitvec_ sizes after reduce().
            const auto f1 = bitvec_.final_set();
            const auto f2 = other.bitvec_.final_set();
            if(f1 != f2) return false;
            if(f1 == bit::vector<>::npos) return true;  // both zero
            const std::size_t nb = bit::vector<>::block_index_for(f1) + 1;
            for(std::size_t i = 0; i < nb; ++i)
                if(bitvec_.block(i) != other.bitvec_.block(i)) return false;
            return true;
        }
        bool operator<(const lineral& other) const;
        inline bool operator[](const var_t idx) const { return idx < bitvec_.size() && bitvec_.test(idx); }
        std::ostream& operator<<(std::ostream& os) const;

        // Remove variable lt; val is the assigned value (True toggles constant)
        inline bool rm(const var_t lt, const bool3 val) {
            if(lt >= bitvec_.size() || !bitvec_.test(lt)) return false;
            bitvec_.reset(lt);
            if(val == bool3::True) {
                if(bitvec_.size() == 0) bitvec_.resize(1);
                bitvec_.flip(0);
            }
            return true;
        }

        inline bool eval(const vec<bool>& sol) const {
            bool out = !has_constant();
            for(auto v = first_var(); v != static_cast<var_t>(-1); v = next_var_after(v)) out ^= sol[v-1];
            return out;
        }
        inline bool eval(const vec<bool3>& sol) const {
            bool out = !has_constant();
            for(auto v = first_var(); v != static_cast<var_t>(-1); v = next_var_after(v)) {
                assert(sol[v] != bool3::None);
                out ^= (sol[v] == bool3::True);
            }
            return out;
        }
        inline bool partial_eval(const vec<bool3>& sol) const {
            bool out = !has_constant();
            for(auto v = first_var(); v != static_cast<var_t>(-1); v = next_var_after(v))
                out ^= (sol[v] == bool3::True);
            return out;
        }
        void solve(vec<bool>& sol_) const {
            if(LT()>0) { sol_[LT()-1] = eval(sol_) ? sol_[LT()-1] : !sol_[LT()-1]; }
        }

        var_t LBD(const vec<var_t>& alpha_dl) const {
            std::set<var_t> l;
            for(auto v = first_var(); v != static_cast<var_t>(-1); v = next_var_after(v)) l.insert(alpha_dl[v]);
            return l.size();
        }

        inline var_t get_assigning_lvl(const vec<var_t>& alpha_dl) const {
            var_t max_dl = 0, max_dl2 = 0;
            for(auto v = first_var(); v != static_cast<var_t>(-1); v = next_var_after(v)) {
                if(alpha_dl[v] > max_dl) { max_dl2 = max_dl; max_dl = alpha_dl[v]; }
                else if(alpha_dl[v] > max_dl2) { max_dl2 = alpha_dl[v]; }
            }
            return max_dl2;
        }

        // Returns {var, var_dl, trail_pos, var} — 4th element is the variable number (watch slot)
        inline std::tuple<var_t,var_t,var_t,var_t> get_watch_tuple(const vec<var_t>& alpha_dl, const vec<var_t>& alpha_trail_pos) const {
            if(size() == 0) return {(var_t)-1, 0, 0, (var_t)-1};
            assert(!is_constant());
            var_t max_v = first_var();
            var_t max_trail_pos = alpha_trail_pos[max_v];
            for(auto v = first_var(); v != static_cast<var_t>(-1); v = next_var_after(v)) {
                if(alpha_trail_pos[v] == static_cast<var_t>(-1)) return {v, (var_t)-1, (var_t)-1, v};
                if(alpha_trail_pos[v] > max_trail_pos) { max_trail_pos = alpha_trail_pos[v]; max_v = v; }
            }
            return {max_v, alpha_dl[max_v], max_trail_pos, max_v};
        }

        // Returns {max_trail_pos, variable_with_max_trail_pos}
        inline std::pair<var_t,var_t> get_watch_var(const vec<var_t>& alpha_trail_pos) const {
            if(size() == 0) return {0, (var_t)-1};
            var_t max_v = first_var();
            if(max_v == static_cast<var_t>(-1)) return {0, (var_t)-1};
            var_t max_trail_pos = alpha_trail_pos[max_v];
            for(auto v = first_var(); v != static_cast<var_t>(-1); v = next_var_after(v)) {
                if(alpha_trail_pos[v] == static_cast<var_t>(-1)) return {(var_t)-1, v};
                if(alpha_trail_pos[v] > max_trail_pos) { max_trail_pos = alpha_trail_pos[v]; max_v = v; }
            }
            return {max_trail_pos, max_v};
        }

        inline var_t get_watch_idx(const vec<var_t>& alpha_trail_pos) const {
            return get_watch_var(alpha_trail_pos).second;
        }
};

namespace std {
  template <>
  struct hash<lineral> {
    std::size_t operator()(const lineral& k) const {
      return k.hash();
    }
  };
}
