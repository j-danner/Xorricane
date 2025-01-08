#include "lin_sys_lazy.hpp"


//void lin_sys_lazy_GE::rref() {
//    pivot_poly.clear();
//    for(var_t idx = 0; idx<linerals.size(); ++idx) {
//        //reduce new row (with non-zero pivot-rows)
//        for (const auto &[lt,row] : pivot_poly) {
//            if(linerals[idx][lt]) {
//                linerals[idx] += linerals[row];
//            }
//        }
//        if(!(linerals[idx].is_zero()) ) {
//            //if non-zero, add to LT_to_row_idx-map
//            const var_t new_lt = linerals[idx].LT();
//            //add new LT to map
//            pivot_poly[ new_lt ] = idx;
//             
//            //full-reduction of previous pivot-rows, i.e., reduce all previously found rows:
//            for (auto &[lt,row] : pivot_poly) {
//                if (lt!=new_lt && linerals[row][new_lt]) linerals[row] += linerals[idx];
//            }
//        }
//    }
//};


std::string lin_sys_lazy_GE::to_str() const {
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
}