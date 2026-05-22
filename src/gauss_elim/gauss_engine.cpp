#include "gauss_engine.hpp"
#include <algorithm>
#include <cstring>

using CMSat::l_True; using CMSat::l_False; using CMSat::l_Undef;
using CMSat::lbool;
using CMSat::GaussWatched;

void GaussElimEngine::init(const std::list<lineral>& lins, var_t num_vars_,
                            const vec<bool3>& alpha, std::list<lineral>& out_queue) {
    // TODO: implement
}

void GaussElimEngine::fill_matrix(const std::list<lineral>&) {}
void GaussElimEngine::eliminate() {}
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
