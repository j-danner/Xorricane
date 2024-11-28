#include "cls_watch_resolver.hpp"

#include "solver.hpp"



bool cls_watch_resolver::minimize(const solver &s, const vec<bool3> &alpha, const vec<var_t> &alpha_dl, const vec<var_t> &alpha_trail_pos, const vec<lin_w_it>& alpha_lin, const vec<dl_c_t> &dl_count) noexcept {
    return false;
    bool ret = false;

    //ensure each lvl has at most one element!
    reduction(1, alpha_dl, alpha_trail_pos, dl_count);

    //for each lineral compute the reason clause and check whether its associated vector space is implied by the other linerals

    //iterate 'upwards' through t_pos_to_linerals -- since 'low'-level reasons have reasons only on 'lower' levels, i.e. we can update our lin_sys level-by-level
    lin_sys L;
    for(auto& [_, l] : t_pos_to_idxs) {
        assert(l.size()==1);
        var_t dl_ = lineral_dl_count0[l.front()].first;
        lineral_watch lin = lineral_watch(linerals[l.front()], alpha, alpha_dl, dl_count, dl_);
        //todo check if reduction with equivs simplifies lin!
        //lin.reduce(alpha, alpha_dl, dl_count, equiv_lits, dl_);

        //@todo optimize construction of clauses here!
        list<lin_w_it> rs_lins;
        vec<var_t> rs_clss_idxs;
        for(const auto& i : lin.get_idxs_()) {
            rs_lins.push_back(alpha_lin[i]);
        }
        auto rs = s.get_reason(rs_lins, rs_clss_idxs);
        assert(rs.get_unit()==lin.to_lineral());

        const auto cls = s.get_reason(rs_lins, rs_clss_idxs).to_cls();
        if( std::all_of(cls.get_ass_VS().get_linerals().begin(), cls.get_ass_VS().get_linerals().end(),
                [&L](const auto& lin){ return L.reduce(lin).is_zero(); })  ) {
            //remove lin!
            lin.clear();
            --num_nz_lins;
            l.clear();
        }
    }

    fix_watched_idx(alpha_dl, alpha_trail_pos, dl_count);

    return ret;
};
