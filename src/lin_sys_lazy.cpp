#include "lin_sys_lazy.hpp"


std::string lin_sys_lazy_GE::to_str() const {
    //vec<lineral> linerals;
    //const auto& xors = cms->get_recovered_xors(false);
    //for(const auto& [rhs,_,__,vars] : xors) {
    //    vec<var_t>v_;
    //    for(const auto& i : vars) v_.emplace_back((var_t) i);
    //    linerals.push_back( lineral(v_, rhs, presorted::no) );
    //};

    vec< std::string > str_linerals( linerals.size() );
    auto to_str = [](const lineral l) -> std::string {return l.to_str();};
    const auto lins = linerals.get_linerals_vec();
    std::transform(lins.begin(), lins.end(), str_linerals.begin(), to_str);
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