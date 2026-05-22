#include "gauss_engine.hpp"
#include <algorithm>
#include <cstring>

using CMSat::l_True; using CMSat::l_False; using CMSat::l_Undef;
using CMSat::lbool;
using CMSat::GaussWatched;

void GaussElimEngine::fill_matrix(const std::list<lineral>& lins) {
    // Collect all vars using dense iterator — no get_idxs_()
    vec<uint32_t> vars_sorted;
    for(const auto& l : lins)
        if(!l.is_zero())
            for(var_t v : l)
                vars_sorted.push_back(static_cast<uint32_t>(v));
    std::sort(vars_sorted.begin(), vars_sorted.end());
    vars_sorted.erase(std::unique(vars_sorted.begin(), vars_sorted.end()), vars_sorted.end());

    col_to_var = vars_sorted;
    num_cols = col_to_var.size();

    uint32_t max_var = vars_sorted.empty() ? 0 : vars_sorted.back();
    var_to_col.assign(max_var + 1, UNASSIGNED_COL);
    for(uint32_t c = 0; c < num_cols; c++)
        var_to_col[col_to_var[c]] = c;

    // Count non-trivial rows
    num_rows = 0;
    for(const auto& l : lins) if(!l.is_zero()) num_rows++;
    if(num_rows == 0 || num_cols == 0) { num_rows = 0; return; }

    mat.resize(num_rows, num_cols);

    uint32_t row = 0;
    for(const auto& l : lins) {
        if(l.is_zero()) continue;
        mat[row].setZero();
        mat[row].rhs() = l.has_constant() ? 1 : 0;
        for(var_t v : l)    // dense iterator, no sparse materialization
            mat[row].setBit(var_to_col[v]);
        row++;
    }
}

void GaussElimEngine::eliminate() {
    if(num_rows == 0) return;
    uint32_t max_col_var = col_to_var.empty() ? 0 : col_to_var.back();
    var_has_resp_row.assign(max_col_var + 1, 0);
    auto end_row = mat.begin() + num_rows;
    auto rowI = mat.begin();
    uint32_t row_i = 0, col = 0;

    while(row_i != num_rows && col != num_cols) {
        auto row_with_1 = rowI;
        uint32_t row_with_1_n = row_i;
        for(; row_with_1 != end_row; ++row_with_1, row_with_1_n++)
            if((*row_with_1)[col]) break;

        if(row_with_1 != end_row) {
            var_has_resp_row[col_to_var[col]] = 1;
            if(row_with_1 != rowI) (*rowI).swapBoth(*row_with_1);
            // XOR into ALL other rows (Gauss-Jordan, not just Gauss)
            for(auto k_row = mat.begin(); k_row != end_row; ++k_row)
                if(k_row != rowI && (*k_row)[col]) (*k_row).xor_in(*rowI);
            row_i++; ++rowI;
        }
        col++;
    }
}

void GaussElimEngine::init(const std::list<lineral>& lins, var_t num_vars_,
                            const vec<bool3>& alpha, std::list<lineral>& out_queue) {
    num_vars = num_vars_;
    dl = 0; ok = true; qhead = 0;
    confl_row = UNASSIGNED_COL;
    trail.clear(); trail_lim.clear(); new_props.clear();

    assigns.assign(num_vars + 1, l_Undef);
    var_data.assign(num_vars + 1, VarData{});
    gwatches.assign(num_vars + 1, {});
    row_to_var_non_resp.clear();
    satisfied_xors.clear();

    fill_matrix(lins);
    if(num_rows == 0) return;
    eliminate();

    free_temps(); create_temps();
    update_cols_vals_set(true);
    init_adjust_matrix(alpha, out_queue);
}

void GaussElimEngine::init_adjust_matrix(const vec<bool3>&, std::list<lineral>&) {}
void GaussElimEngine::create_temps() {}
void GaussElimEngine::free_temps() {}
void GaussElimEngine::update_cols_vals_set(bool) {}
void GaussElimEngine::update_cols_vals_set_var(var_t, bool) {}
bool GaussElimEngine::find_truths(GaussWatched*&, GaussWatched*&, var_t, uint32_t,
                                   bool&, uint32_t&, uint32_t&) { return true; }
void GaussElimEngine::eliminate_col(var_t, uint32_t, uint32_t) {}
void GaussElimEngine::prop_lit(var_t, bool, uint32_t, uint32_t) {}
void GaussElimEngine::gauss_jordan_elim(var_t) {}
void GaussElimEngine::clear_gwatches(var_t v) { if(v < gwatches.size()) gwatches[v].clear(); }
void GaussElimEngine::delete_gausswatch(uint32_t) {}
void GaussElimEngine::enqueue_internal(var_t, bool, uint32_t, uint32_t) {}
bool GaussElimEngine::enqueue(var_t var, bool val, uint32_t dl_) {
    if(var >= assigns.size() || assigns[var] != l_Undef) return false;
    enqueue_internal(var, val, UNASSIGNED_COL, dl_);
    return true;
}
void GaussElimEngine::propagate() {}
void GaussElimEngine::backtrack(uint32_t) {}
void GaussElimEngine::push_decision_level() { trail_lim.push_back(trail.size()); dl++; }
lineral GaussElimEngine::get_reason(var_t) const { return lineral(); }
lineral GaussElimEngine::get_conflict() const { return lineral(cnst::one); }
lineral GaussElimEngine::row_to_lineral(uint32_t row_n) const {
    vec<var_t> vars;
    for(uint32_t col = 0; col < num_cols; col++)
        if(mat[row_n][col]) vars.push_back(col_to_var[col]);
    return lineral(vars, mat[row_n].rhs() & 1, presorted::yes);
}
