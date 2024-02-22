#include "xcls_watch_resolver.hpp"

#include "../solver.hpp"



bool xcls_watch_resolver::minimize(solver& s, const vec<bool3> &alpha, const vec<var_t> &alpha_dl, const vec<var_t> &alpha_trail_pos, const vec<dl_c_t> &dl_count) {
    bool ret = false;
    stats _;
    
    //prepare s
    do {
        s.GCP(_);
    } while( s.no_conflict() && s.find_implications_from_linerals(_) );

    bool update_req = false;
    bool early_abort = false;

    for(auto it=t_pos_to_idxs.begin(); it!=t_pos_to_idxs.end(); ++it) {
        auto& [k,l] = *it;
        for(auto it2=l.begin(); it2!=l.end(); ++it2) {
            const var_t i = *it2;
            //skip if already 0
            if(xlits[i].is_zero()) continue;
            //reduce with alpha and equivs
            xlit lin = xlits[i];
            bool changed = false;
            if(early_abort) {
                lin.clear(); 
                changed = true;
            } else {
                changed |= lin.reduce(s.alpha); //@todo can we rm this line?
                changed |= lin.reduce(s.equiv_lits);
                changed |= lin.reduce(s.alpha);
            }
            assert((!changed || lin.to_str()!=xlits[i].to_str()) && (changed || lin.to_str()==xlits[i].to_str()));
            //if(lin.is_one()) {
            if(lin.eval(alpha)) {
                //early abort! as lin is reduced to 1 (under alpha); we know that lin+1 is already implied by previous 'decisions' + lin
                //rm all remaining lits & stop!
                early_abort = true;
                continue;
            }
            if(changed) {
                update_req |= (i==idx[0] || i==idx[1]);
                xlits[i] = std::move(lin);
                const auto& [v, dl, t_pos, _idx] = xlits[i].get_watch_tuple(alpha_dl, alpha_trail_pos);
                //assert(t_pos <= k);
                if(t_pos==k) continue;
                //now t_pos!=k, i.e., lin needs to moved elsewhere in t_pos_to_idxs
                //assert(t_pos < k);
                it2 = l.erase( it2 ); --it2;
                xlit_t_pos[i] = t_pos;
                if(dl!=(var_t)-1) xlit_dl_count0[i] = {dl, dl_count[dl]};
                else              xlit_dl_count0[i] = {0,0};
                if(xlits[i].is_zero()) {
                    ret |= changed;
                    --num_nz_lins;
                    continue;
                }
                filtration_add(i);
            }
            assert(!xlits[i].is_zero());
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
        }
        if(l.empty()) {
            it = t_pos_to_idxs.erase( it );
            if(it!=t_pos_to_idxs.begin()) --it;
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
