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

void GaussElimEngine::free_temps() {
    for(auto& x : tofree) delete[] x;
    tofree.clear();
    delete cols_unset; cols_unset = nullptr;
    delete cols_vals;  cols_vals  = nullptr;
    delete tmp_col;    tmp_col    = nullptr;
    delete tmp_col2;   tmp_col2   = nullptr;
}

void GaussElimEngine::create_temps() {
    assert(tofree.empty());
    uint32_t num_64b = num_cols/64 + (bool)(num_cols % 64);
    if(num_64b == 0) num_64b = 1;
    // PackedRow(size, mp): mp[-1] = rhs, mp[0..size-1] = data
    // So we allocate num_64b+1 words: x[0] = rhs slot, x[1..num_64b] = data
    // and pass x+1 so that (x+1)[-1] = x[0] is the rhs.
    auto alloc = [&]() {
        int64_t* x = new int64_t[num_64b + 1]();
        tofree.push_back(x);
        return new CMSat::PackedRow(num_64b, x);
    };
    cols_unset = alloc(); cols_vals = alloc();
    tmp_col    = alloc(); tmp_col2  = alloc();
    cols_unset->rhs() = 0; cols_vals->rhs() = 0;
    tmp_col->rhs()    = 0; tmp_col2->rhs()  = 0;
}

void GaussElimEngine::update_cols_vals_set(bool force) {
    if(!force && !cancelled_since_val_update) {
        return;
    }
    cols_vals->setZero();
    cols_unset->setOne();
    for(uint32_t col = 0; col < num_cols; col++) {
        var_t var = col_to_var[col];
        if(var >= assigns.size() || assigns[var] == l_Undef) continue;
        cols_unset->clearBit(col);
        if(assigns[var] == l_True)  // var=FALSE in XOR sense → set bit in cols_vals
            cols_vals->setBit(col);
    }
    cancelled_since_val_update = false;
}

void GaussElimEngine::update_cols_vals_set_var(var_t var, bool val) {
    if(var >= var_to_col.size() || var_to_col[var] == UNASSIGNED_COL) return;
    uint32_t col = var_to_col[var];
    cols_unset->clearBit(col);
    if(!val) cols_vals->setBit(col);  // val=false → var=FALSE in XOR sense → set bit
}

void GaussElimEngine::init_adjust_matrix(const vec<bool3>&, std::list<lineral>& out_queue) {
    satisfied_xors.assign(num_rows, 0);
    row_to_var_non_resp.clear();
    row_to_var_non_resp.reserve(num_rows);

    uint32_t adjust_zero = 0;
    vec<CMSat::Lit> tmp_clause;

    for(uint32_t row_i = 0; row_i < num_rows; row_i++) {
        uint32_t non_resp_var = UNASSIGNED_COL;
        uint32_t popcnt = mat[row_i].find_watchVar(
            tmp_clause, col_to_var, var_has_resp_row, non_resp_var);

        switch(popcnt) {
            case 0:
                adjust_zero++;
                if(mat[row_i].rhs()) {
                    ok = false; confl_row = row_i; return;
                }
                satisfied_xors[row_i] = 1;
                row_to_var_non_resp.push_back(UNASSIGNED_COL);
                break;

            case 1: {
                // Unit row: propagate immediately
                // rhs=1 → var=TRUE → val=true; rhs=0 → var=FALSE → val=false
                bool val = (bool)mat[row_i].rhs();
                var_t var = tmp_clause[0].var();
                var_has_resp_row[var] = 0;
                adjust_zero++;
                satisfied_xors[row_i] = 1;
                row_to_var_non_resp.push_back(UNASSIGNED_COL);
                out_queue.push_back(row_to_lineral(row_i));
                enqueue_internal(var, val, row_i, 0);
                new_props.push_back({var, val});
                break;
            }

            default:
                assert(non_resp_var != UNASSIGNED_COL);
                // tmp_clause[0].var() = pivot (responsible) var
                gwatches[tmp_clause[0].var()].push_back(CMSat::GaussWatched(row_i, 0));
                gwatches[non_resp_var].push_back(CMSat::GaussWatched(row_i, 0));
                row_to_var_non_resp.push_back(non_resp_var);
                break;
        }
    }

    // Shrink to exclude zero/unit rows
    num_rows -= adjust_zero;
    mat.resizeNumRows(num_rows);
}

void GaussElimEngine::enqueue_internal(var_t var, bool val, uint32_t row_n, uint32_t level) {
    assigns[var] = CMSat::boolToLBool(!val);  // inverted: val=TRUE → l_False
    var_data[var] = {level, row_n, true, val};
    trail.push_back({var, val, level});
    update_cols_vals_set_var(var, val);
}

bool GaussElimEngine::find_truths(GaussWatched*&, GaussWatched*&, var_t, uint32_t,
                                   bool&, uint32_t&, uint32_t&) { return true; }
void GaussElimEngine::eliminate_col(var_t, uint32_t, uint32_t) {}
void GaussElimEngine::prop_lit(var_t, bool, uint32_t, uint32_t) {}
void GaussElimEngine::gauss_jordan_elim(var_t) {}
void GaussElimEngine::clear_gwatches(var_t v) { if(v < gwatches.size()) gwatches[v].clear(); }
void GaussElimEngine::delete_gausswatch(uint32_t) {}
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
