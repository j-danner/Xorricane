#include <sstream>

#include "lin_sys.hpp"


void lin_sys::rref() {
    pivot_poly_its.clear();
    for(linerals_it it = linerals.begin(); it!=linerals.end();) {
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
            //if zero, remove row from linerals + adjust running var i
            it = linerals.erase( it );
        }
    }
};

lineral lin_sys::reduce(const lineral& l) const {
    lineral l_(l);
    for (const auto &[lt,row] : pivot_poly_its) {
        if(l_[lt]) {
            l_ += *row;
        }
    }
    return l_;
}

bool lin_sys::lt_update(const lineral& l) {
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

lineral tmp_lin;
bool lin_sys::lt_update_short(const lineral& l) {
    //complexity to find correct update linerals: O( log( this.size() ) * sys.size() )
    const auto search = pivot_poly_its.find( l.LT() );
    if(search == pivot_poly_its.end()) return false;
    const auto row = search->second;
    //LT found -- start reduction!
    tmp_lin.clear();
    tmp_lin = *row + l;
    //update row -- if short enough
    if(tmp_lin.size() > 1.50 * row->size()) return false;
    row->swap(tmp_lin);
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

lin_sys lin_sys::operator+(const lin_sys &other) const {
    lin_sys cpy(*this);
    cpy += other;
    return cpy;
};

lin_sys& lin_sys::operator +=(const lin_sys& other) {
    linerals_it it = linerals.end();
    it--;
    auto other_linerals = other.get_linerals();
    linerals.splice(linerals.end(), std::move(other_linerals));
    it++; //now it points to first element in other.linerals
    while(it!=linerals.end()) {
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
            //if zero, remove row from linerals + adjust running var i
            it = linerals.erase( it );
        }
    }
    return *this;
};

void lin_sys::add_reduced_lit(lineral&& l) {
    if(l.is_zero()) return;
    //assert that l is indeed reduced
    assert( reduce(l) == l );
    for(auto& r : linerals) {
        if(r[l.LT()]) r += l;
    }
    //append l to linerals
    linerals.emplace_back( std::move(l) );
    //add to pivot_poly_its
    assert(!pivot_poly_its.contains(linerals.back().LT()));
    pivot_poly_its[linerals.back().LT()] = std::prev(linerals.end());
};

void lin_sys::add_reduced_lit(const lineral& l) {
    if(l.is_zero()) return;
    //assert that l is indeed reduced
    assert( reduce(l) == l );
    for(auto& r : linerals) {
        if(r[l.LT()]) r += l;
    }
    //append l to linerals
    linerals.push_back( l );
    //add to pivot_poly_its
    assert(!pivot_poly_its.contains(l.LT()));
    pivot_poly_its[linerals.back().LT()] = std::prev(linerals.end());
};

bool lin_sys::eval(const vec<bool>& sol) const {
    return std::all_of(linerals.begin(), linerals.end(), [&sol](lineral l) { return l.eval(sol); } );
};

void lin_sys::solve(vec<bool>& sol_) const {
    if(linerals.size()==0) return;
    for (const auto &[lt,row] : pivot_poly_its) {
        sol_[lt-1] = row->eval(sol_) ? sol_[lt-1] : !sol_[lt-1];
    }
};

std::string lin_sys::to_str() const {
    vec< std::string > str_linerals( linerals.size() );
    auto to_str = [](const lineral l) -> std::string {return l.to_str();};
    std::transform(linerals.begin(), linerals.end(), str_linerals.begin(), to_str);
    std::sort(str_linerals.begin(), str_linerals.end());
    //rotate if 1 is first element
    if(str_linerals.size()>0 && str_linerals[0]=="1") std::rotate(str_linerals.begin(), str_linerals.begin()+1, str_linerals.end());
    std::stringstream ss;
    std::copy(str_linerals.begin(), str_linerals.end(), std::ostream_iterator<std::string>(ss, " "));
    std::string result = ss.str();
    if (!result.empty()) {
        result.resize(result.length() - 1); // trim trailing space
        return result;
    } else {
        return "0";
    }
};