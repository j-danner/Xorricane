#include <sstream>

#include "xsys.hpp"


void xsys::rref() {
    pivot_poly_its.clear();
    for(xlits_it it = xlits.begin(); it!=xlits.end();) {
        //reduce new row (with non-zero pivot-rows)
        for (const auto &[lt,row] : pivot_poly_its)
        {
            if((*it)[lt]) {
                *it += *row;
            }
        }
        if(!(it->is_zero()) ) {
            //if non-zero, add to LT_to_row_idx-map
            const var_t new_lt = it->LT();
            //add new LT to map
            pivot_poly_its[ new_lt ] = it;
             
            //full-reduction of previous pivot-rows, i.e., reduce all previously found rows:
            for (auto &[lt,row] : pivot_poly_its)
            {
                if (lt!=new_lt && (*row)[new_lt]) *row += *it;
            }

            ++it;
        } else {
            //if zero, remove row from xlits + adjust running var i
            it = xlits.erase( it );
        }
    }
};

xlit xsys::reduce(const xlit& l) const {
    xlit l_(l);
    for (const auto &[lt,row] : pivot_poly_its) {
        if(l_[lt]) {
            l_ += *row;
        }
    }
    return l_;
}

//deprecated!
void xsys::lt_update(const xlit& l) {
    const auto search = pivot_poly_its.find( l.LT() );
    if(search != pivot_poly_its.end()) {
        const auto row = search->second;
        //LT found -- start reduction!
        *row += l;
        pivot_poly_its.erase( search );
        //rm from pivot_poly_its, then reduce with other eqs
        for (const auto &[lt,row_lt] : pivot_poly_its)
        {
            if((*row)[lt]) {
                *row += *row_lt;
            }
        }
        //if non-zero, add back to pivot_poly_its
        if(!(row->is_zero())) {
            pivot_poly_its[row->LT()] = row;
        }
    }
};

//deprecated!
void xsys::lt_update(const vec<xlit>& assignments) {
    for(auto& l : xlits) l.reduce(assignments);
    rref();
};


//deprecated!
void xsys::lt_update(const vec<xlit>& assignments, const vec<var_t>& assignments_dl, const var_t dl) {
    for(auto& l : xlits) l.reduce(assignments, assignments_dl, dl);
    rref();
    return;

    //pivot_map<var_t,var_t> ppi_cpy = pivot_poly_its;
    //for(const auto& [lt,r_idx] : ppi_cpy) {
    //    if(assignments[lt].is_zero() || assignments_dl[lt]>dl) continue;
    //    //rm from pivot_poly_its, then reduce with assignments
    //    pivot_poly_its.erase( lt );
    //    //reduce with assignments as long as possible!
    //    while( !assignments[ xlits[r_idx].LT() ].is_zero() && assignments_dl[xlits[r_idx].LT()] <= dl) {
    //        // (1) reduce with assignments
    //        while(!assignments[ xlits[r_idx].LT() ].is_zero() && assignments_dl[xlits[r_idx].LT()] <= dl) {
    //            xlits[r_idx] += assignments[xlits[r_idx].LT()];
    //        }
    //        // (2) reduce with other eqs in xlits -- if they have same LT
    //        const auto search = pivot_poly_its.find( xlits[r_idx].LT() );
    //        if(search != pivot_poly_its.end()){ xlits[r_idx] += xlits[search->second]; }
    //    }
    //    //if non-zero, add back to pivot_poly_its
    //    if(!xlits[r_idx].is_zero()) {
    //        assert( !pivot_poly_its.contains(xlits[r_idx].LT()) );
    //        pivot_poly_its[xlits[r_idx].LT()] = r_idx;
    //    }
    //}
};

void xsys::update(const vec<xlit>& assignments, const vec<var_t>& assignments_dl, const var_t dl) {
    for(auto& l : xlits) {
        l.reduce(assignments, assignments_dl, dl);
    }
    pivot_poly_its.clear();
    rref();
};


xsys xsys::operator+(const xsys &other) const {
    xsys cpy(*this);
    cpy += other;
    return cpy;
};

xsys& xsys::operator +=(const xsys& other) {
    xlits_it it = xlits.end();
    it--;
    auto other_xlits = other.get_xlits();
    xlits.splice(xlits.end(), std::move(other_xlits));
    it++; //now it points to first element in other.xlits
    while(it!=xlits.end()) {
        //reduce new row
        for (const auto &[lt,row] : pivot_poly_its)
        {
            if((*it)[lt]) {
                *it += *row;
            }
        }
        if(!(it->is_zero()) ) {
            //if non-zero, add to LT_to_row_idx-map
            const var_t new_lt = it->LT();
            //add new LT to map
            pivot_poly_its[ new_lt ] = it;
             
            //full-reduction of previous pivot-rows, i.e., reduce all previously found rows:
            for (auto &[lt,row] : pivot_poly_its)
            {
                if (lt!=new_lt && (*row)[new_lt]) *row += *it;
            }

            ++it;
        } else {
            //if zero, remove row from xlits + adjust running var i
            it = xlits.erase( it );
        }
    }
    return *this;
};


void xsys::add_reduced_lit(const xlit& l) {
    //assert that l is indeed reduced
    assert( reduce(l) == l );
    for(auto& r : xlits) {
        if(r[l.LT()]) r += l;
    }
    //append l to xlits
    xlits.push_back( l );
    //add to pivot_poly_its
    pivot_poly_its.insert( {xlits.back().LT(), std::prev(xlits.end())} );
};

bool xsys::eval(const vec<bool>& sol) const {
    return std::all_of(xlits.begin(), xlits.end(), [&sol](xlit l) { return l.eval(sol); } );
};

void xsys::solve(vec<bool>& sol_) const {
    if(xlits.size()==0) return;
    for (const auto &[lt,row] : pivot_poly_its) {
        sol_[lt-1] = row->eval(sol_) ? sol_[lt-1] : !sol_[lt-1];
    }
};

std::string xsys::to_str() const {
    vec< std::string > str_xlits( xlits.size() );
    auto to_str = [](const xlit l) -> std::string {return l.to_str();};
    std::transform(std::execution::par, xlits.begin(), xlits.end(), str_xlits.begin(), to_str);
    std::sort(std::execution::par, str_xlits.begin(), str_xlits.end());
    //rotate if 1 is first element
    if(str_xlits.size()>0 && str_xlits[0]=="1") std::rotate(str_xlits.begin(), str_xlits.begin()+1, str_xlits.end());
    std::stringstream ss;
    std::copy(str_xlits.begin(), str_xlits.end(), std::ostream_iterator<std::string>(ss, " "));
    std::string result = ss.str();
    if (!result.empty()) {
        result.resize(result.length() - 1); // trim trailing space
        return result;
    } else {
        return "0";
    }
};