#include "xcls_watch.hpp"

//TODO!
std::string xcls_watch::to_str(const vec<xlit>& assignments) const {
    return to_xcls().reduce(assignments).to_str();
};
