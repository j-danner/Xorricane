#pragma once
#include <vector>
#include <list>
#include <cstdint>
#include <limits>
#include "../misc.hpp"
#include "../lineral.hpp"
#include "gj_types.hpp"

class GaussElimEngine {
public:
    static constexpr uint32_t UNASSIGNED_COL = std::numeric_limits<uint32_t>::max();

    ~GaussElimEngine() { free_temps(); }

    // Build from linerals at dl=0. Populates out_queue with immediately implied linerals.
    void init(const list<lineral>& lins, var_t num_vars_,
              const vec<bool3>& alpha, list<lineral>& out_queue);

    // Enqueue external assignment. Returns true if newly assigned.
    bool enqueue(var_t var, bool val, uint32_t dl_);

    // Run GJ propagation to fixpoint. Adds new_props entries.
    void propagate();

    void backtrack(uint32_t lvl);
    void push_decision_level();
    uint32_t decision_level() const { return dl; }
    bool is_ok() const { return ok; }
    bool has_conflict() const { return confl_row != UNASSIGNED_COL; }

    lineral get_reason(var_t var) const;
    lineral get_conflict() const;

    // New propagations since last clear (var, val pairs)
    const vec<std::pair<var_t,bool>>& get_new_props() const { return new_props; }
    void clear_new_props() { new_props.clear(); }

    uint32_t num_rows = 0, num_cols = 0;
    lineral row_to_lineral(uint32_t row_n) const;

private:
    var_t num_vars = 0;
    uint32_t dl = 0;
    bool ok = true;
    uint32_t confl_row = UNASSIGNED_COL;

    CMSat::PackedMatrix mat;
    vec<uint32_t> col_to_var;  // col → var (1-indexed)
    vec<uint32_t> var_to_col;  // var → col, UNASSIGNED_COL if absent

    vec<CMSat::lbool> assigns;  // inverted: l_False=TRUE, l_True=FALSE in XOR sense

    struct VarData {
        uint32_t level = 0;
        uint32_t row_n = UNASSIGNED_COL;  // UNASSIGNED_COL = decision
        bool assigned = false;
        bool val = false;
    };
    vec<VarData> var_data;

    struct TrailEntry { var_t var; bool val; uint32_t level; };
    vec<TrailEntry> trail;
    vec<uint32_t> trail_lim;  // trail_lim[i] = trail size at start of dl i+1
    uint32_t qhead = 0;

    vec<vec<CMSat::GaussWatched>> gwatches;  // gwatches[var]
    vec<char> var_has_resp_row;
    vec<uint32_t> row_to_var_non_resp;
    vec<char> satisfied_xors;

    CMSat::PackedRow *cols_vals  = nullptr;
    CMSat::PackedRow *cols_unset = nullptr;
    CMSat::PackedRow *tmp_col    = nullptr;
    CMSat::PackedRow *tmp_col2   = nullptr;
    vec<int64_t*> tofree;

    bool cancelled_since_val_update = true;

    vec<std::pair<var_t,bool>> new_props;

    void fill_matrix(const list<lineral>& lins);
    void eliminate();
    void init_adjust_matrix(const vec<bool3>& alpha, list<lineral>& out_queue);
    void create_temps();
    void free_temps();
    void update_cols_vals_set(bool force = false);
    void update_cols_vals_set_var(var_t var, bool val);
    bool find_truths(CMSat::GaussWatched*& i, CMSat::GaussWatched*& j,
                     var_t var, uint32_t row_n,
                     bool& do_eliminate, uint32_t& new_resp_var, uint32_t& new_resp_row);
    void eliminate_col(var_t p, uint32_t new_resp_var, uint32_t new_resp_row);
    void prop_lit(var_t var, bool val, uint32_t row_n, uint32_t level);
    void gauss_jordan_elim(var_t var);
    void clear_gwatches(var_t var);
    void delete_gausswatch(uint32_t row_n);
    void enqueue_internal(var_t var, bool val, uint32_t row_n, uint32_t level);
};
