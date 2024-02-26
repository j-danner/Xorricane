#include "xcls_watch_resolver.hpp"

#include "../solver.hpp"



bool xcls_watch_resolver::minimize(solver& s, const vec<bool3> &alpha, const vec<var_t> &alpha_dl, const vec<var_t> &alpha_trail_pos, const vec<dl_c_t> &dl_count) {
    bool ret = false;
    stats _;
    
    //prepare s
    if(s.dl_count.size()<xlits.size()) s.dl_count.resize(xlits.size(), 0);
    if(s.lineral_watches.size()<xlits.size()) s.lineral_watches.resize(xlits.size(), std::list<xlit_watch>());
    do {
        s.GCP(_);
    } while( s.no_conflict() && s.find_implications_from_linerals(_) );

    bool update_req = false;
    bool early_abort = false;

    xlit lin;
    
    for(var_t i = 0; i<xlits.size(); ++i) {
        if(xlits[i].is_zero()) continue;

        //reduce with alpha and equivs
        lin = xlits[i];
        bool changed = false;
        if(early_abort) {
            lin.clear();
            changed = true;
        } else {
            changed |= lin.reduce(s.equiv_lits);
            changed |= lin.reduce(s.alpha);
        }
        assert( (!changed || lin.to_str()!=xlits[i].to_str()) && (changed || lin.to_str()==xlits[i].to_str()) );
        //if(lin.is_one()) {
        //if(!early_abort && lin.is_one()) {
        if(!early_abort && lin.reduced(alpha).is_one()) {
            //early abort! as lin is reduced to 1 (under alpha); we know that lin+1 is already implied by previous 'decisions'
            //thus all 'guesses' + lin form a conflict clause!
            //rm all remaining lits & stop!
            early_abort = true;
            continue;
        } else if(changed) {
            const auto& [v, dl, t_pos, _idx] = lin.get_watch_tuple(alpha_dl, alpha_trail_pos);
            if(t_pos==xlit_t_pos[i]) continue;
            //watched_idx need to be fixed, if watched linerals change t_pos OR a new lineral has higher t_pos
            update_req |= (i==idx[0] || i==idx[1]) || (t_pos>xlit_t_pos[idx[1]]);
            //now t_pos!=k, i.e., lin needs to moved elsewhere in t_pos_to_idxs
            t_pos_to_idxs[xlit_t_pos[i]].remove( i );
            if(t_pos_to_idxs[xlit_t_pos[i]].empty()) { t_pos_to_idxs.erase(xlit_t_pos[i]); }
            xlit_t_pos[i] = t_pos;
            if(dl!=(var_t)-1) xlit_dl_count0[i] = {dl, dl_count[dl]};
            else              xlit_dl_count0[i] = {0,0};
            xlits[i] = std::move(lin);
            if(xlits[i].is_zero()) {
                ret |= changed;
                --num_nz_lins;
                continue;
            }
            filtration_add(i);
        }
        //increase dl
        ++s.dl;
        ++s.dl_count[s.dl];
        s.trails.emplace_back( std::list<trail_elem>() );
        s.active_cls_stack.emplace_back(s.active_cls);
        //add guess
        s.add_new_guess( xlits[i] );
        //GCP + linalg
        do {
            s.GCP(_);
        } while( s.no_conflict() && s.find_implications_from_linerals(_) );
        assert(!s.trails.back().empty());
        //if s is at conflict, then all processed clauses already make up a (shorter) conflict clause!
        if(!s.no_conflict()) {
            early_abort = true;
        }
    }

    //fix watched idxs if necessary
    if(update_req) {
        fix_watched_idx(alpha_dl, alpha_trail_pos, dl_count);
    }

    //reset s
    s.backtrack(0);

    return ret;
};
