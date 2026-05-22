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
                mat[row_i].setZero();  // already zero after GJ, but explicit
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
                out_queue.push_back(row_to_lineral(row_i));  // capture BEFORE zeroing
                mat[row_i].setZero();                         // zero AFTER capturing
                mat[row_i].rhs() = 0;
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
}

void GaussElimEngine::enqueue_internal(var_t var, bool val, uint32_t row_n, uint32_t level) {
    assigns[var] = CMSat::boolToLBool(!val);  // inverted: val=TRUE → l_False
    var_data[var] = {level, row_n, true, val};
    trail.push_back({var, val, level});
    update_cols_vals_set_var(var, val);
}

void GaussElimEngine::prop_lit(var_t var, bool val, uint32_t row_n, uint32_t level) {
    enqueue_internal(var, val, row_n, level);
    new_props.push_back({var, val});
}

bool GaussElimEngine::find_truths(
    CMSat::GaussWatched*& i, CMSat::GaussWatched*& j,
    var_t var, uint32_t row_n,
    bool& do_eliminate, uint32_t& new_resp_var_out, uint32_t& new_resp_row_out)
{
    if(satisfied_xors[row_n]) { *j++ = *i; return true; }

    bool was_resp_var = false;
    if(var_has_resp_row[var] == 1) {
        was_resp_var = true;
        var_has_resp_row[row_to_var_non_resp[row_n]] = 1;
        var_has_resp_row[var] = 0;
    }

    uint32_t new_resp_var = 0;
    CMSat::Lit ret_lit_prop;
    const CMSat::gret ret = mat[row_n].propGause(
        assigns, col_to_var, var_has_resp_row,
        new_resp_var, *tmp_col, *tmp_col2, *cols_vals, *cols_unset, ret_lit_prop);

    switch(ret) {
        case CMSat::gret::confl:
            *j++ = *i;
            if(was_resp_var) {
                var_has_resp_row[row_to_var_non_resp[row_n]] = 0;
                var_has_resp_row[var] = 1;
            }
            confl_row = row_n;
            return false;

        case CMSat::gret::prop:
            *j++ = *i;
            prop_lit(ret_lit_prop.var(), ret_lit_prop.sign(), row_n, dl);
            if(was_resp_var) {
                var_has_resp_row[row_to_var_non_resp[row_n]] = 0;
                var_has_resp_row[var] = 1;
            }
            satisfied_xors[row_n] = 1;
            return true;

        case CMSat::gret::nothing_fnewwatch:
            if(was_resp_var) {
                clear_gwatches(new_resp_var);
                gwatches[new_resp_var].push_back(CMSat::GaussWatched(row_n, 0));
                var_has_resp_row[row_to_var_non_resp[row_n]] = 0;
                var_has_resp_row[new_resp_var] = 1;
                do_eliminate     = true;
                new_resp_var_out = new_resp_var;
                new_resp_row_out = row_n;
            } else {
                gwatches[new_resp_var].push_back(CMSat::GaussWatched(row_n, 0));
                row_to_var_non_resp[row_n] = new_resp_var;
            }
            return true;

        case CMSat::gret::nothing_satisfied:
            *j++ = *i;
            if(was_resp_var) {
                var_has_resp_row[row_to_var_non_resp[row_n]] = 0;
                var_has_resp_row[var] = 1;
            }
            satisfied_xors[row_n] = 1;
            return true;

        default:
            assert(false);
            return true;
    }
}

void GaussElimEngine::eliminate_col(var_t p, uint32_t new_resp_var, uint32_t new_resp_row_n) {
    auto rowI = mat.begin();
    auto end  = mat.end();
    uint32_t new_resp_col = var_to_col[new_resp_var];
    uint32_t row_i = 0;

    while(rowI != end) {
        if(new_resp_row_n != row_i && (*rowI)[new_resp_col]) {
            if(satisfied_xors[row_i]) { ++rowI; row_i++; continue; }

            uint32_t orig_non_resp_var = row_to_var_non_resp[row_i];
            uint32_t orig_non_resp_col = var_to_col[orig_non_resp_var];

            (*rowI).xor_in(*(mat.begin() + new_resp_row_n));

            if(!(*rowI)[orig_non_resp_col]) {
                if(orig_non_resp_var != new_resp_var) delete_gausswatch(row_i);

                CMSat::Lit ret_lit_prop;
                uint32_t new_non_resp_var = 0;
                const CMSat::gret ret = (*rowI).propGause(
                    assigns, col_to_var, var_has_resp_row,
                    new_non_resp_var, *tmp_col, *tmp_col2, *cols_vals, *cols_unset,
                    ret_lit_prop);

                switch(ret) {
                    case CMSat::gret::confl:
                        gwatches[p].push_back(CMSat::GaussWatched(row_i, 0));
                        row_to_var_non_resp[row_i] = p;
                        confl_row = row_i;
                        break;

                    case CMSat::gret::prop:
                        if(confl_row != UNASSIGNED_COL) {
                            gwatches[p].push_back(CMSat::GaussWatched(row_i, 0));
                            row_to_var_non_resp[row_i] = p;
                            break;
                        }
                        gwatches[p].push_back(CMSat::GaussWatched(row_i, 0));
                        row_to_var_non_resp[row_i] = p;
                        prop_lit(ret_lit_prop.var(), ret_lit_prop.sign(), row_i, dl);
                        satisfied_xors[row_i] = 1;
                        break;

                    case CMSat::gret::nothing_fnewwatch:
                        gwatches[new_non_resp_var].push_back(CMSat::GaussWatched(row_i, 0));
                        row_to_var_non_resp[row_i] = new_non_resp_var;
                        break;

                    case CMSat::gret::nothing_satisfied:
                        gwatches[p].push_back(CMSat::GaussWatched(row_i, 0));
                        row_to_var_non_resp[row_i] = p;
                        satisfied_xors[row_i] = 1;
                        break;

                    default:
                        assert(false);
                }
            }
        }
        ++rowI; row_i++;
    }
}

void GaussElimEngine::gauss_jordan_elim(var_t var) {
    if(num_rows == 0) return;
    update_cols_vals_set();

    bool do_eliminate = false;
    uint32_t new_resp_var = 0, new_resp_row = 0;
    bool confl_in_gauss = false;

    auto& ws = gwatches[var];
    CMSat::GaussWatched* i = ws.data();
    CMSat::GaussWatched* j = i;
    const CMSat::GaussWatched* end = ws.data() + ws.size();

    for(; i != end; i++) {
        if(!find_truths(i, j, var, i->row_n, do_eliminate, new_resp_var, new_resp_row)) {
            confl_in_gauss = true;
            i++;
            break;
        }
    }
    for(; i != end; i++) *j++ = *i;
    ws.erase(ws.begin() + (j - ws.data()), ws.end());

    if(do_eliminate && !confl_in_gauss)
        eliminate_col(var, new_resp_var, new_resp_row);
}

void GaussElimEngine::clear_gwatches(var_t v) { if(v < gwatches.size()) gwatches[v].clear(); }

void GaussElimEngine::delete_gausswatch(uint32_t row_n) {
    auto& ws = gwatches[row_to_var_non_resp[row_n]];
    for(size_t k = 0; k < ws.size(); k++) {
        if(ws[k].row_n == row_n) {
            ws[k] = ws.back(); ws.pop_back(); return;
        }
    }
    assert(false);
}

bool GaussElimEngine::enqueue(var_t var, bool val, uint32_t dl_) {
    if(var >= assigns.size() || assigns[var] != l_Undef) return false;
    enqueue_internal(var, val, UNASSIGNED_COL, dl_);
    return true;
}

void GaussElimEngine::propagate() {
    while(qhead < trail.size() && confl_row == UNASSIGNED_COL) {
        var_t var = trail[qhead++].var;
        gauss_jordan_elim(var);
    }
    if(confl_row != UNASSIGNED_COL) ok = false;
}
void GaussElimEngine::backtrack(uint32_t lvl) {
    assert(lvl <= dl);
    if(lvl >= dl) return;

    // Unassign all vars added after lvl
    uint32_t new_trail_size = lvl < trail_lim.size() ? trail_lim[lvl] : 0;
    for(int k = (int)trail.size()-1; k >= (int)new_trail_size; k--) {
        var_t var = trail[k].var;
        assigns[var] = l_Undef;
        var_data[var] = VarData{};
    }
    trail.resize(new_trail_size);
    trail_lim.resize(lvl);
    qhead = new_trail_size;
    dl = lvl;
    ok = true;
    confl_row = UNASSIGNED_COL;
    cancelled_since_val_update = true;
    new_props.clear();
    std::fill(satisfied_xors.begin(), satisfied_xors.end(), 0);
}
void GaussElimEngine::push_decision_level() { trail_lim.push_back(trail.size()); dl++; }
lineral GaussElimEngine::get_reason(var_t) const { return lineral(); }
lineral GaussElimEngine::get_conflict() const { return lineral(cnst::one); }
lineral GaussElimEngine::row_to_lineral(uint32_t row_n) const {
    vec<var_t> vars;
    for(uint32_t col = 0; col < num_cols; col++)
        if(mat[row_n][col]) vars.push_back(col_to_var[col]);
    return lineral(vars, mat[row_n].rhs() & 1, presorted::yes);
}
