#include <sstream>

#include "xsys.hpp"


void xsys::rref() {
    pivot_poly_idx.clear();
    for (var_t i = 0; i < xlits.size(); i++)
    {
        //reduce new row
        for (const auto &[lt,row_idx] : pivot_poly_idx)
        {
            if(xlits[i][lt]) {
                xlits[i] += xlits[ row_idx ];
            }
        }
        if(!xlits[i].is_zero() ) {
            //if non-zero, add to LT_to_row_idx-map
            const var_t new_lt = xlits[i].LT();
            //add new LT to map
            pivot_poly_idx[ new_lt ] = i;

            if (new_lt == 0) continue; //no full-reduction for constant!
            //full-reduction of previous pivot-rows, i.e., reduce all previously found rows:
            for (const auto &lt_row_idx : pivot_poly_idx)
            {
                const int r_idx = lt_row_idx.second;
                if( r_idx != i && (xlits[r_idx])[new_lt] ) xlits[r_idx] += xlits[i];
            }
        } else {
            //if zero, remove row from xlits + adjust running var i
            xlits.erase( xlits.begin()+i );
            i--;
        }
    }
};

xlit xsys::reduce(const xlit& l) const {
    //TODO optimize by reducing given row -- without need to create copy of row!
    xlit l_(l);
    for (const auto &lt_row_idx : pivot_poly_idx) {
        const var_t lt = lt_row_idx.first;
        if(l_[lt]) {
            const int row_idx = lt_row_idx.second;
            l_ += xlits[ row_idx ];
        }
    }
    return l_;
}


void xsys::lt_update(const xlit& l) {
    const auto search = pivot_poly_idx.find( l.LT() );
    if(search != pivot_poly_idx.end()) {
        const auto i = search->second;
        //LT found -- start reduction!
        xlits[i] += l;
        pivot_poly_idx.erase( search );
        //rm from pivot_poly_idx, then reduce with other eqs
        for (const auto &lt_row_idx : pivot_poly_idx)
        {
            const var_t lt = lt_row_idx.first;
            if(xlits[i][lt]) {
                const int row_idx = lt_row_idx.second;
                xlits[i] += xlits[ row_idx ];
            }
        }
        //if non-zero, add back to pivot_poly_idx
        if(!xlits[i].is_zero()) {
            pivot_poly_idx[xlits[i].LT()] = i;
        }
    }
};

void xsys::lt_update(const vec<xlit>& assignments) {
    for(auto& l : xlits) l.reduce(assignments);
    rref();
};


void xsys::lt_update(const vec<xlit>& assignments, const vec<var_t>& assignments_dl, const var_t dl) {
    for(auto& l : xlits) l.reduce(assignments, assignments_dl, dl);
    rref();
    return;

    pivot_map<var_t,var_t> ppi_cpy = pivot_poly_idx;
    for(const auto& [lt,r_idx] : ppi_cpy) {
        if(assignments[lt].is_zero() || assignments_dl[lt]>dl) continue;
        //rm from pivot_poly_idx, then reduce with assignments
        pivot_poly_idx.erase( lt );
        //reduce with assignments as long as possible!
        while( !assignments[ xlits[r_idx].LT() ].is_zero() && assignments_dl[xlits[r_idx].LT()] <= dl) {
            // (1) reduce with assignments
            while(!assignments[ xlits[r_idx].LT() ].is_zero() && assignments_dl[xlits[r_idx].LT()] <= dl) {
                xlits[r_idx] += assignments[xlits[r_idx].LT()];
            }
            // (2) reduce with other eqs in xlits -- if they have same LT
            const auto search = pivot_poly_idx.find( xlits[r_idx].LT() );
            if(search != pivot_poly_idx.end()){ xlits[r_idx] += xlits[search->second]; }
        }
        //if non-zero, add back to pivot_poly_idx
        if(!xlits[r_idx].is_zero()) {
            assert( !pivot_poly_idx.contains(xlits[r_idx].LT()) );
            pivot_poly_idx[xlits[r_idx].LT()] = r_idx;
        }
    }
};

void xsys::update(const vec<xlit>& assignments, const vec<var_t>& assignments_dl, const var_t dl) {
    for(auto& l : xlits) {
        l.reduce(assignments, assignments_dl, dl);
    }
    pivot_poly_idx.clear();
    rref();
};


xsys xsys::operator+(const xsys &other) const {
    xsys cpy(*this);
    cpy += other;
    return cpy;
};

xsys& xsys::operator +=(const xsys& other) {
    const auto orig_xlits_size = xlits.size();
    xlits.reserve( xlits.size() + other.xlits.size() );
    std::copy(other.xlits.begin(), other.xlits.end(), std::back_inserter(xlits));

    for (var_t i = orig_xlits_size; i < xlits.size(); i++) {
        //reduce new row
        for (const auto &[lt,row_idx] : pivot_poly_idx)
        {
            if(xlits[i][lt]) {
                xlits[i] += xlits[ row_idx ];
            }
        }
        if(!xlits[i].is_zero() ) {
            //if non-zero, add to LT_to_row_idx-map
            const var_t new_lt = xlits[i].LT();
            //add new LT to map
            pivot_poly_idx[ new_lt ] = i;

            //full-reduction of previous pivot-rows, i.e., reduce all previously found rows:
            for (const auto &lt_row_idx : pivot_poly_idx)
            {
                const int r_idx = lt_row_idx.second;
                if( r_idx != i && (xlits[r_idx])[new_lt] ) xlits[r_idx] += xlits[i];
            }
        } else {
            //if zero, remove row from xlits + adjust running var i
            xlits.erase( xlits.begin()+i );
            i--;
        }
    }
    return *this;
};


bool xsys::eval(const vec<bool>& sol) const {
    return std::all_of(xlits.begin(), xlits.end(), [&sol](xlit l) { return l.eval(sol); } );
};

void xsys::solve(vec<bool>& sol_) const {
    if(xlits.size()==0) return;
    //TODO can be done in parallel!!
    for (const auto &lt_row_idx : pivot_poly_idx) {
        const var_t lt = lt_row_idx.first;
        const int row_idx = lt_row_idx.second;
        //update sol_[lt]: if sol_ is a zero of the xlit do nothing, otherwise flip it
        sol_[lt-1] = xlits[row_idx].eval(sol_) ? sol_[lt-1] : !sol_[lt-1];
        //sol_[lt] = !sol_[lt] ^ xlits[row_idx].eval(sol_);
    };
};

std::string xsys::to_str() const {
    vec< std::string > str_xlits( xlits.size() );
    auto to_str = [](const xlit l) -> std::string {return l.to_str();};
    std::transform(std::execution::par, xlits.begin(), xlits.end(), str_xlits.begin(), to_str);
    std::sort(std::execution::par, str_xlits.begin(), str_xlits.end());
    //rotate if 1 is first element, i.e., if xsys is inconsistent!
    if(!is_consistent()) std::rotate(str_xlits.begin(), str_xlits.begin()+1, str_xlits.end());
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