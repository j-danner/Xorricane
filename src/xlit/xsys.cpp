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

bool xsys::lt_update(const xlit& l) {
    const auto search = pivot_poly_its.find( l.LT() );
    if(search == pivot_poly_its.end()) return false;
    const auto row = search->second;
    //LT found -- start reduction!
    *row += l;
    //rm from pivot_poly_its, then reduce with other eqs
    pivot_poly_its.erase( search );
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
    return true;
};

xlit tmp_lin;
bool xsys::lt_update_short(const xlit& l) {
    //complexity to find correct update xlits: O( log( this.size() ) * sys.size() )
    const auto search = pivot_poly_its.find( l.LT() );
    if(search == pivot_poly_its.end()) return false;
    const auto row = search->second;
    auto prev_sz = row->size();
    if(prev_sz <= 3) return false;
    //LT found -- start reduction!
    tmp_lin.clear();
    tmp_lin = *row + l;
    //update row -- if short enough
    if(tmp_lin.size() <= 1.50 * prev_sz) {
        row->swap(tmp_lin);
        prev_sz = row->size();
    }
    //rm from pivot_poly_its, then reduce with other eqs
    pivot_poly_its.erase( search );
    for (const auto &[lt,row_lt] : pivot_poly_its) {
        if((*row)[lt]) {
            *row += *row_lt;
        }
    }
    //if non-zero, add back to pivot_poly_its
    if(!(row->is_zero())) {
        pivot_poly_its[row->LT()] = row;
    }
    return true;
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