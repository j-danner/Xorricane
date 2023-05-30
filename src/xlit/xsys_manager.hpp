#pragma once

#include "../misc.hpp"
#include "xlit_watch.hpp"


class xsys_manager:
{
private:
public:
    /**
     * @brief create new xsys_manager
     * 
     * @param n_vars max number of variables in the xsys
     */
    xsys_manager(var_t n_vars);

    ~xsys_manager();

    /**
     * @brief add a new xlit to the xsys
     * 
     * @param lit xlit to be added
     * @param dl current decision level
     * @param rs reason cls-idx of the unit lit
     */
    void add_xlit(xlit lit, var_t dl, var_t rs);

    /**
     * @brief backtrack to a given dl
     * 
     * @param lvl dl to backtrack to
     */
    void backtrack(var_t lvl);
    
    /**
     * @brief get implied assignments
     * 
     * @return std::vector<xlit> 
     */
    std::vector<xlit> find_implied_alpha();
};