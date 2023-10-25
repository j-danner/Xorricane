#include "xcls.hpp"

#include <unordered_map>
#include <map>

#include <m4ri/m4ri.h>


std::string xcls::to_str() const {
    if(assVS.dim()==0) return "1";
    std::string result = "";
    for(const auto& lit : assVS.get_xlits()) result += lit.plus_one().to_str() + " ";
    result.resize( result.length()-1 );
    return result;
};


// SRES

vec<xlit> intersectVS(const xsys& U, const xsys& W) {
        //Zassenhaus Alg: Put U, W in Matrix [ U U \\ W 0 ] and compute rref [ A 0 \\ 0 B ]. Then B corr to basis of U \cap W.
    //NOTE assumes that n_vars is less than half of max val (of var_t type)

    //if U contains 1 return W and vice versa
    if(!U.is_consistent()) return W.get_xlits_vec();
    if(!W.is_consistent()) return U.get_xlits_vec();
    
    //rewrite xlits s.t. they have a continous range of idxs
    vec<var_t> supp = vec<var_t>({0});
    vec<var_t> tmp;
    for(const auto& l : U.get_xlits()) {
        std::set_union( supp.begin(), supp.end(), l.begin(), l.end(), std::back_insert_iterator(tmp) );
        std::swap(tmp, supp);
        tmp.clear();
    }
    for(const auto& l : W.get_xlits()) {
        std::set_union( supp.begin(), supp.end(), l.begin(), l.end(), std::back_insert_iterator(tmp) );
        std::swap(tmp, supp);
        tmp.clear();
    }
    //now supp contains all lits that occur in U and W
    std::unordered_map<var_t, var_t> Isupp;
    for(var_t i=0; i<supp.size(); ++i) Isupp[ supp[i] ] = i;
    const var_t n_vars = supp.size();

    rci_t nrows = U.dim() + W.dim();
    rci_t ncols = 2*(n_vars+1);

    mzd_t* M = mzd_init(nrows, ncols);
    assert( mzd_is_zero(M) );

    //fill with U
    rci_t r = 0;
    for(const auto& l : U.get_xlits()) {
        if(l.is_zero()) continue;
        if(l.has_constant()) {
            mzd_write_bit(M, r, 0, 1);
            mzd_write_bit(M, r, n_vars+1, 1);
        }
        for(const auto& i : l.get_idxs_()) {
            assert(i>0);
            assert(Isupp[i]+n_vars+1<(var_t) ncols);
            mzd_write_bit(M, r, Isupp[i], 1);
            mzd_write_bit(M, r, Isupp[i]+n_vars+1, 1);
        }
        ++r;
    }
    //fill with W
    for(const auto& l : W.get_xlits()) {
        if(l.is_zero()) continue;
        if(l.has_constant()) mzd_write_bit(M, r, 0, 1);
        for(const auto& i : l.get_idxs_()) {
            assert(i>0);
            mzd_write_bit(M, r, Isupp[i], 1);
        }
        ++r;
    }
    assert(r == nrows);

    //compute rref
    const rci_t rank = mzd_echelonize_pluq(M, true);
    //read results
    vec<xlit> int_lits;
    r = rank-1;
    while(r>0) {
        mzd_t* r_ = mzd_init_window(M, r, 0, r+1, n_vars+1);
        if(!mzd_is_zero(r_)) { mzd_free_window(r_); break;}
        mzd_free_window(r_);

        vec<var_t> idxs;
        for(rci_t c=(n_vars+1)+1; c<ncols; ++c) {
            if( mzd_read_bit(M, r, c) ) idxs.push_back(supp[c-n_vars-1]);
        }
        int_lits.emplace_back( std::move(idxs), (bool) mzd_read_bit(M, r, n_vars+1), presorted::yes );
        --r;
    }

    mzd_free(M);
    
    return int_lits;
}



std::pair<bool, xlit> intersectaffineVS(const xsys& U, const xsys& W) {
    //replace U and W with matrix representations; find l s.t. l in U and l+1 in W, i.e.,
    // if there is [a b] s.t. [U^T W^T] * [a \\ b] = 1
    //we compute M = [U^T W^T] and solve with righthandside 1
    
    //rewrite xlits s.t. they have a continous range of idxs
    vec<var_t> supp = vec<var_t>({0});
    vec<var_t> tmp;
    for(const auto& l : U.get_xlits()) {
        std::set_union( supp.begin(), supp.end(), l.begin(), l.end(), std::back_insert_iterator(tmp) );
        std::swap(tmp, supp);
        tmp.clear();
    }
    for(const auto& l : W.get_xlits()) {
        std::set_union( supp.begin(), supp.end(), l.begin(), l.end(), std::back_insert_iterator(tmp) );
        std::swap(tmp, supp);
        tmp.clear();
    }
    //now supp contains all lits that occur in U and W
    std::unordered_map<var_t, var_t> Isupp;
    for(var_t i=0; i<supp.size(); ++i) Isupp[ supp[i] ] = i;
    const var_t n_vars = supp.size();

    rci_t ncols = U.size() + W.size();
    rci_t nrows = n_vars;

    mzd_t* M = mzd_init(nrows, ncols);
    assert( mzd_is_zero(M) );

    //fill with U^T
    rci_t r = 0;
    for(const auto& l : U.get_xlits()) {
        if(l.has_constant()) {
            mzd_write_bit(M, 0, r, 1);
        }
        for(const auto& i : l.get_idxs_()) {
            assert(i>0);
            mzd_write_bit(M, Isupp[i], r, 1);
        }
        ++r;
    }
    //fill with W^T
    for(const auto& l : W.get_xlits()) {
        if(l.has_constant()) mzd_write_bit(M, 0, r, 1);
        for(const auto& i : l.get_idxs_()) {
            assert(i>0);
            mzd_write_bit(M, Isupp[i], r, 1);
        }
        ++r;
    }
    assert(r == ncols);

    //solve for M x = b for b =1
    mzd_t* b = mzd_init(std::max(ncols,nrows), 1);
    mzd_write_bit(b, 0, 0, 1); //uses that supp[0]==0

    //find solution
    //mzd_print(M);
    //std::cout << std::endl;
    //mzd_print(b);
    //std::cout << std::endl;
    const auto ret = mzd_solve_left(M, b, 0, true);
    if(ret==-1) { mzd_free(M); mzd_free(b); return {false, xlit()}; }
    assert(ret == 0);
    //mzd_print(b);

    //take first half of one solution

    //comp xlit l in U with l+1 in W
    xlit out = xlit();
    for(rci_t r = 0; (unsigned)r<U.size(); ++r) {
        if(mzd_read_bit(b, r, 0)) out += U.get_xlits(r);
    }

    mzd_free(b);
    mzd_free(M);

    assert( U.reduce(out).is_zero() );
    assert( W.reduce(out).is_one() );

    return {true,out};
}


vec<xlit> extend_basis(const vec<xlit>& B, const xsys& L) {
    xsys b(B);
    vec<xlit> out;
    for(const xlit& l : L.get_xlits()) {
        if(b.dim() == L.dim()) break; //correct dimension reached!
        xlit l_ = b.reduce(l);
        if(!l_.is_zero()) {
            //should we add b.reduce(l) instead of l (?)
            //out.push_back(l);
            out.push_back(l_);
            b += xsys(l_);
        }
    }
    assert(b.dim() == L.dim());
    return out;
}


xcls sres_opt(const xcls& cl1, const xcls& cl2) {
    //rewrite cl1 and cl2 s.t. we can do s-resolution
    //compute intersection of cl1.assVS and cl2.assVS

    if(cl1.is_zero()) return cl2;
    if(cl2.is_zero()) return cl1;

    const auto& [b,a] = intersectaffineVS( cl1.get_ass_VS(), cl2.get_ass_VS() );
    if(!b) {
        //no non-trivial reduction can be made --> concat ass_VS!
        xsys new_ass_xsys = cl1.get_ass_VS() + cl2.get_ass_VS();
        return xcls( new_ass_xsys );
    }
    //rewrite clauses to increase s-resolution!
    //compute intersection:
    vec<xlit> intVS = intersectVS( cl1.get_ass_VS(), cl2.get_ass_VS() );

    //compute partial bases and their extensions
    vec<xlit> &pB = intVS; //partial basis of cl1
    pB.push_back(a);
    //std::copy(intVS.begin(), intVS.end(), std::back_inserter(pB));
    //extend bases
    vec<xlit> cl1_ext = extend_basis(pB, cl1.get_ass_VS());
    pB.back().add_one();
    vec<xlit> cl2_ext = extend_basis(pB, cl2.get_ass_VS());

    //compute s-resulution: if intVS = {l1, ..., lk} and cl1_ext = {f1,...,fn} and cl2_ext = {g1,...,gm}, then
    //                      sres(cl1,cl2) = sres({ a, a+l1,...,a+lk, f1,...,fn },{ a+1, a+l1+1,...,a+lk+1, g1,...,gm })
    //                                    = { a+(a+l1+1)+1,..., a+l(k-1)+(a+lk+1)+1, f1,...,fn, g1,...,gm }
    //                                    = { l1,...,lk, f1,...,fn, g1,...,gm }

    vec<xlit> lits;
    std::move(cl1_ext.begin(), cl1_ext.end(), std::back_inserter(lits));
    std::move(cl2_ext.begin(), cl2_ext.end(), std::back_inserter(lits));
    std::move(intVS.begin(), intVS.end()-1, std::back_inserter(lits));

    return xcls( std::move(xsys(std::move(lits))) );
};