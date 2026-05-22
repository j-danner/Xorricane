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

#include <set>
#include <sstream>
#include <algorithm>

#include "misc.hpp"

#include "lineral.hpp"
#include "lineral_watch.hpp"
#include "lin_sys.hpp"

#include "gauss_elim/gauss_engine.hpp"

#undef DEBUG_SLOW
#undef DEBUG_SLOWER

// #define DEBUG_SLOW
// #define DEBUG_SLOWER

class lin_sys_lazy_GE
{
  private:
    GaussElimEngine* ge = nullptr;
    var_t num_vars;

    /**
     * @brief linerals in lin_sys
     */
    lin_sys linerals;

    /**
     * @brief assigning linerals (literals), not yet fetched
     */
    list<lineral> implied_literal_queue;

    /**
     * @brief initialises GaussElimEngine from linerals, fixes implied assignments
     *
     * @param alpha current alpha-assignment
     * @return number of implied new alpha assignments
     */
    var_t init_and_propagate(const vec<bool3>& alpha) {
        delete ge;
        ge = new GaussElimEngine();
        if(num_vars == (var_t)-1) {
            num_vars = 0;
            for(const auto& l : linerals.get_linerals())
                if(!l.is_constant()) num_vars = std::max(num_vars, l.get_max_var());
        }
        implied_literal_queue.clear();
        list<lineral> eng_implied;
        ge->init(linerals.get_linerals(), num_vars, alpha, eng_implied);

        var_t ct = 0;
        for(auto& lin : eng_implied) {
            if(!alpha.empty() && lin.is_assigning() && alpha[lin.LT()] != bool3::None) continue;
            implied_literal_queue.emplace_back(std::move(lin));
            ct++;
        }
        if(!ge->is_ok()) {
            implied_literal_queue.emplace_front(ge->get_conflict());
            ct++;
        }
        return ct;
    }

    /**
     * @brief propagate with GaussElimEngine and update implied_literal_queue
     *
     * @param alpha current alpha-assignments
     * @return number of entries in implied_literal_queue
     */
    var_t propagate_ge(const vec<bool3>& alpha) {
        ge->propagate();
        for(auto& [var, val] : ge->get_new_props()) {
            if(!alpha.empty() && alpha[var] != bool3::None) continue;
            implied_literal_queue.emplace_back(ge->get_reason(var));
        }
        ge->clear_new_props();
        if(!ge->is_ok() && ge->has_conflict()) {
            implied_literal_queue.emplace_back(ge->get_conflict());
        }
        return implied_literal_queue.size();
    }

  public:
    lin_sys_lazy_GE() {}

    lin_sys_lazy_GE(lin_sys&& sys, const var_t _num_vars) noexcept
        : num_vars(_num_vars), linerals(std::move(sys)) {
        vec<bool3> alpha;
        init_and_propagate(alpha);
    }

    lin_sys_lazy_GE(const vec<lineral>& linerals_, const var_t _num_vars = (var_t)-1) noexcept
        : num_vars(_num_vars), linerals(linerals_) {
        vec<bool3> alpha;
        init_and_propagate(alpha);
    }

    ~lin_sys_lazy_GE() { delete ge; }

    /**
     * @brief Returns reason lineral for given var
     *
     * @param var that is assigned by linerals under the current assignments
     * @return lineral which is the reason for the assignment of var
     */
    lineral get_reason(var_t var) {
        assert(ge);
        return ge->get_reason(var);
    }

    list<lineral>& get_implied_literal_queue() { return implied_literal_queue; }
    void clear_implied_literal_queue() { implied_literal_queue.clear(); }

    const list<lineral>& get_linerals() const { return linerals.get_linerals(); }

    /**
     * @brief assigns var, i.e., ensures it is not watched, and fixes row-echelon under alpha
     *
     * @param var newly assigned variable
     * @param alpha current alpha-assignment
     * @param dl current decision level
     * @return bool true iff new alpha assignments were deduced or queue still has implications
     */
    bool assign(const var_t var, const vec<bool3>& alpha, var_t dl) {
        assert(ge != nullptr);
        assert(implied_literal_queue.empty());
        if(ge->decision_level() > dl) ge->backtrack(dl);
        while(ge->decision_level() < dl) ge->push_decision_level();
        assert(ge->decision_level() == dl);

        if(dl == 0) {
            linerals.add_lineral(lineral(var, b3_to_bool(alpha[var])));
        }

        if(ge->enqueue(var, b3_to_bool(alpha[var]), dl)) {
            propagate_ge(alpha);
        }
        return !implied_literal_queue.empty();
    }

    /**
     * @brief add new lineral to lazy lin sys
     * @note may only be used at dl 0 (!)
     *
     * @param l lineral to be added
     * @param alpha current alpha-assignments
     * @return var_t number of implied new alpha assignments
     */
    inline var_t add_lineral(lineral&& l, const vec<bool3>& alpha) {
        return add_linerals({std::move(l)}, alpha);
    }

    /**
     * @brief add new linerals to lazy lin sys
     * @note may only be used at dl 0 (!)
     *
     * @param ls list of linerals to be added
     * @param alpha current alpha-assignments
     * @return var_t number of new alpha assignments
     */
    var_t add_linerals(vec<lineral>&& ls, const vec<bool3>& alpha) {
        assert(!ge || ge->decision_level() == 0);
        if(ls.empty()) return 0;
        delete ge; ge = nullptr;
        lin_sys new_lins(std::move(ls));
        linerals += new_lins;
        return init_and_propagate(alpha);
    }

    void backtrack(var_t lvl) {
        assert(ge != nullptr);
        ge->backtrack(lvl);
        implied_literal_queue.clear();
    }

    vec<lineral> get_recovered_linerals() const {
        assert(ge != nullptr);
        vec<lineral> result;
        for(uint32_t r = 0; r < ge->num_rows; r++) {
            auto l = ge->row_to_lineral(r);
            if(!l.is_zero()) result.push_back(l);
        }
        return result;
    }

    var_t size() const { return linerals.size(); }

    std::string to_str() const;
};
