// Vendored from CryptoMiniSat — only find_watchVar, propGause, get_reason.
// Original license: MIT, Copyright (C) 2009-2020 Authors of CryptoMiniSat
#include "gj_types.hpp"

using namespace CMSat;

#ifdef _MSC_VER
#include <intrin.h>
#pragma intrinsic(_BitScanForward)
#pragma intrinsic(_BitScanForward64)
inline int scan_fwd_64b(int64_t value)
{
    unsigned long at;
    unsigned char ret = _BitScanForward64(&at, value);
    at++;
    if (!ret) at = 0;
    return at;
}
#else
inline int scan_fwd_64b(uint64_t value)
{
    return __builtin_ffsll(value);
}
#endif

uint32_t PackedRow::find_watchVar(
    vector<Lit>& tmp_clause,
    const vector<uint32_t>& col_to_var,
    vector<char>& var_has_resp_row,
    uint32_t& non_resp_var
) {
    uint32_t popcnt = 0;
    non_resp_var = numeric_limits<uint32_t>::max();
    tmp_clause.clear();

    for(int i = 0; i < size*64; i++) {
        if (this->operator[](i)) {
            popcnt++;
            uint32_t var = col_to_var[i];
            tmp_clause.push_back(Lit(var, false));
            if (!var_has_resp_row[var]) {
                non_resp_var = var;
            } else {
                std::swap(tmp_clause[0], tmp_clause.back());
            }
        }
    }
    assert(tmp_clause.size() == popcnt);
    assert(popcnt == 0 || var_has_resp_row[tmp_clause[0].var()]);
    return popcnt;
}

void PackedRow::get_reason(
    vector<Lit>& tmp_clause,
    [[maybe_unused]] const vector<lbool>& assigns,
    const vector<uint32_t>& col_to_var,
    PackedRow& cols_vals,
    PackedRow& tmp_col2,
    Lit prop
) {
    tmp_col2.set_and(*this, cols_vals);
    for (int i = 0; i < size; i++) if (mp[i]) {
        int64_t tmp = mp[i];
        unsigned long at;
        at = scan_fwd_64b(tmp);
        int extra = 0;
        while (at != 0) {
            uint32_t col = extra + at-1 + i*64;
            const uint32_t var = col_to_var[col];
            if (var == prop.var()) {
                tmp_clause.push_back(prop);
                std::swap(tmp_clause[0], tmp_clause.back());
            } else {
                const bool val_bool = tmp_col2[col];
                tmp_clause.push_back(Lit(var, val_bool));
            }
            extra += at;
            if (extra == 64) break;
            tmp >>= at;
            at = scan_fwd_64b(tmp);
        }
    }
}

gret PackedRow::propGause(
    const vector<lbool>& assigns,
    const vector<uint32_t>& col_to_var,
    vector<char>& var_has_resp_row,
    uint32_t& new_resp_var,
    PackedRow& tmp_col,
    PackedRow& tmp_col2,
    PackedRow& cols_vals,
    PackedRow& cols_unset,
    Lit& ret_lit_prop
) {
    uint32_t pop = tmp_col.set_and_until_popcnt_atleast2(*this, cols_unset);

    if (pop >= 2) {
        for (int i = 0; i < size; i++) if (tmp_col.mp[i]) {
            int64_t tmp = tmp_col.mp[i];
            unsigned long at;
            at = scan_fwd_64b(tmp);
            int extra = 0;
            while (at != 0) {
                uint32_t col = extra + at-1 + i*64;
                const uint32_t var = col_to_var[col];
                if (!var_has_resp_row[var]) {
                    new_resp_var = var;
                    return gret::nothing_fnewwatch;
                }
                extra += at;
                if (extra == 64) break;
                tmp >>= at;
                at = scan_fwd_64b(tmp);
            }
        }
        assert(false && "Should have found a new watch!");
    }

    tmp_col2.set_and(*this, cols_vals);
    const uint32_t pop_t = tmp_col2.popcnt() + rhs();

    if (pop == 1) {
        for (int i = 0; i < size; i++) if (tmp_col.mp[i]) {
            int at = scan_fwd_64b(tmp_col.mp[i]);
            uint32_t col = at-1 + i*64;
            const uint32_t var = col_to_var[col];
            assert(assigns[var] == l_Undef);
            ret_lit_prop = Lit(var, !(pop_t % 2));
            return gret::prop;
        }
        assert(false && "Should have found the propagating literal!");
    }

    assert(pop == 0);
    if (pop_t % 2 == 0) return gret::nothing_satisfied;
    return gret::confl;
}
