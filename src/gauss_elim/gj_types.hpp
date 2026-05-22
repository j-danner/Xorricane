// Vendored types from CryptoMiniSat for GaussElimEngine.
// Original license: MIT, Copyright (C) 2009-2020 Authors of CryptoMiniSat
#pragma once

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <cstring>
#include <vector>
#include <iostream>
#include <algorithm>
#include <limits>

// release_assert — used by PackedMatrix::resize
#if defined(_MSC_VER)
#define release_assert(a) \
    do { \
    __pragma(warning(push)) \
    __pragma(warning(disable:4127)) \
        if (!(a)) { \
    __pragma(warning(pop)) \
            fprintf(stderr, "*** ASSERTION FAILURE in %s() [%s:%d]: %s\n", \
            __FUNCTION__, __FILE__, __LINE__, #a); \
            abort(); \
        } \
    } while (0)
#else
#define release_assert(a) \
    do { \
        if (!(a)) { \
            fprintf(stderr, "*** ASSERTION FAILURE in %s() [%s:%d]: %s\n", \
            __FUNCTION__, __FILE__, __LINE__, #a); \
            abort(); \
        } \
    } while (0)
#endif

// Forward declaration required for PackedRow::friend class ::GaussElimEngine
class GaussElimEngine;

namespace CMSat {

using std::vector;
using std::numeric_limits;

// ---- Lit (from solvertypesmini.h) ----

constexpr uint32_t var_Undef(0xffffffffU >> 4);

class Lit
{
    uint32_t x;
    constexpr explicit Lit(uint32_t i) : x(i) { }
public:
    constexpr Lit() : x(var_Undef<<1) {}
    constexpr explicit Lit(uint32_t var, bool is_inverted) : x(var + var + is_inverted) {}

    constexpr const uint32_t& toInt() const { return x; }
    constexpr Lit  operator~() const { return Lit(x ^ 1); }
    constexpr Lit  operator^(const bool b) const { return Lit(x ^ (uint32_t)b); }
    Lit& operator^=(const bool b) { x ^= (uint32_t)b; return *this; }
    constexpr bool sign() const { return x & 1; }
    constexpr uint32_t  var() const { return x >> 1; }
    constexpr Lit  unsign() const { return Lit(x & ~1U); }
    constexpr bool operator==(const Lit& p) const { return x == p.x; }
    constexpr bool operator!= (const Lit& p) const { return x != p.x; }
    constexpr bool operator <  (const Lit& p) const { return x < p.x; }
    constexpr bool operator >  (const Lit& p) const { return x > p.x; }
    constexpr bool operator >= (const Lit& p) const { return x >= p.x; }
    constexpr static Lit toLit(uint32_t data) { return Lit(data); }
};

inline constexpr Lit lit_Undef(var_Undef, false);

inline std::ostream& operator<<(std::ostream& os, const Lit lit)
{
    if (lit == lit_Undef) { os << "lit_Undef"; }
    else { os << (lit.sign() ? "-" : "") << (lit.var() + 1); }
    return os;
}

// ---- lbool (from solvertypesmini.h) ----

class lbool {
    uint8_t value;
public:
    constexpr explicit lbool(uint8_t v) : value(v) { }
    constexpr lbool() : value(0) { }
    constexpr explicit lbool(bool x) : value(!x) { }

    constexpr bool  operator == (lbool b) const {
        return ((b.value & 2) & (value & 2)) | (!(b.value & 2) & (value == b.value));
    }
    constexpr bool  operator != (lbool b) const { return !(*this == b); }
    constexpr lbool operator ^  (bool  b) const { return lbool((uint8_t)(value ^ (uint8_t)b)); }

    lbool operator && (lbool b) const {
        uint8_t sel = (value << 1) | (b.value << 3);
        uint8_t v   = (0xF7F755F4 >> sel) & 3;
        return lbool(v);
    }
    lbool operator || (lbool b) const {
        uint8_t sel = (value << 1) | (b.value << 3);
        uint8_t v   = (0xFCFCF400 >> sel) & 3;
        return lbool(v);
    }

    constexpr uint8_t getValue() const { return value; }
    friend lbool toLbool(uint32_t v);
    constexpr friend uint32_t toInt(lbool l);
};

constexpr lbool l_True  = lbool((uint8_t)0);
constexpr lbool l_False = lbool((uint8_t)1);
constexpr lbool l_Undef = lbool((uint8_t)2);

inline lbool toLbool(uint32_t v) { lbool l; l.value = v; return l; }
constexpr inline uint32_t toInt(lbool l) { return l.value; }

inline lbool boolToLBool(const bool b) { return b ? l_True : l_False; }

inline std::ostream& operator<<(std::ostream& cout, const lbool val)
{
    if (val == l_True)  cout << "l_True";
    if (val == l_False) cout << "l_False";
    if (val == l_Undef) cout << "l_Undef";
    return cout;
}

// ---- gret (from solvertypes.h) ----

enum class gret { confl, prop, nothing_satisfied, nothing_fnewwatch };

// ---- GaussWatched (from gausswatched.h) ----

struct GaussWatched {
    GaussWatched(uint32_t r, uint32_t m) : row_n(r), matrix_num(m) {}
    static GaussWatched plain_xor(uint32_t at) { return GaussWatched(at, 1000); }

    uint32_t row_n;
    uint32_t matrix_num;

    bool operator<(const GaussWatched& other) const {
        if (matrix_num < other.matrix_num) return true;
        if (matrix_num > other.matrix_num) return false;
        return row_n < other.row_n;
    }
};

// ---- PackedRow (from packedrow.h) ----
// Note: set() template omitted (depends on Xor type).
// Note: get_reason_xorricane() and get_reason_xor() omitted (depend on Xor type).

class PackedMatrix;

class PackedRow
{
public:
    PackedRow() = delete;
    PackedRow& operator=(const PackedRow& b)
    {
        for (int i = -1; i < size; i++) *(mp + i) = *(b.mp + i);
        return *this;
    }
    PackedRow& operator^=(const PackedRow& b)
    {
        for (int i = -1; i < size; i++) *(mp + i) ^= *(b.mp + i);
        return *this;
    }
    void and_inv(const PackedRow& b)
    {
        for (int i = 0; i < size; i++) *(mp + i) &= ~(*(b.mp + i));
    }
    void set_and_inv(const PackedRow& a, const PackedRow& b)
    {
        for (int i = 0; i < size; i++) *(mp + i) = *(a.mp + i) & (~(*(b.mp + i)));
    }
    void set_and(const PackedRow& a, const PackedRow& b)
    {
        for (int i = 0; i < size; i++) *(mp + i) = *(a.mp + i) & *(b.mp + i);
    }
    uint32_t set_and_until_popcnt_atleast2(const PackedRow& a, const PackedRow& b)
    {
        uint32_t pop = 0;
        for (int i = 0; i < size && pop < 2; i++) {
            *(mp + i) = *(a.mp + i) & *(b.mp + i);
            pop += __builtin_popcountll((uint64_t)*(mp + i));
        }
        return pop;
    }
    void xor_in(const PackedRow& b)
    {
        rhs_internal ^= b.rhs_internal;
        for (int i = 0; i < size; i++) *(mp + i) ^= *(b.mp + i);
    }
    inline const int64_t& rhs() const { return rhs_internal; }
    inline int64_t& rhs() { return rhs_internal; }
    inline bool isZero() const
    {
        for (int i = 0; i < size; i++) if (mp[i]) return false;
        return true;
    }
    inline void setZero() { memset(mp, 0, sizeof(int64_t)*size); }
    inline void setOne()  { memset(mp, 0xff, sizeof(int64_t)*size); }
    inline void clearBit(const uint32_t i) { mp[i/64] &= ~(1LL << (i%64)); }
    inline void setBit(const uint32_t i)   { mp[i/64] |= (1LL << (i%64)); }
    inline void invert_rhs(const bool b = true) { rhs_internal ^= (int)b; }
    void swapBoth(PackedRow b)
    {
        int64_t* __restrict mp1 = mp-1;
        int64_t* __restrict mp2 = b.mp-1;
        uint32_t i = size+1;
        while(i != 0) { std::swap(*mp1, *mp2); mp1++; mp2++; i--; }
    }
    inline bool operator[](const uint32_t i) const
    {
        return (mp[i/64] >> (i%64)) & 1;
    }

    uint32_t find_watchVar(
        vector<Lit>& tmp_clause,
        const vector<uint32_t>& col_to_var,
        vector<char>& var_has_resp_row,
        uint32_t& non_resp_var);

    gret propGause(
        const vector<lbool>& assigns,
        const vector<uint32_t>& col_to_var,
        vector<char>& var_has_resp_row,
        uint32_t& new_resp_var,
        PackedRow& tmp_col,
        PackedRow& tmp_col2,
        PackedRow& cols_vals,
        PackedRow& cols_unset,
        Lit& ret_lit_prop);

    void get_reason(
        vector<Lit>& tmp_clause,
        const vector<lbool>& assigns,
        const vector<uint32_t>& col_to_var,
        PackedRow& cols_vals,
        PackedRow& tmp_col2,
        Lit prop);

    void collect_vars(const vector<uint32_t>& col_to_var, vector<uint32_t>& out) const;
    void collect_vars(const vector<uint32_t>& col_to_var, vector<std::uint_fast32_t>& out) const;

    uint32_t popcnt() const;
    uint32_t popcnt_at_least_2() const;

private:
    friend class PackedMatrix;
    friend class ::GaussElimEngine;
    friend std::ostream& operator<<(std::ostream& os, const PackedRow& m);

    PackedRow(const uint32_t _size, int64_t* const _mp) :
        mp(_mp+1), rhs_internal(*_mp), size(_size)
    {}

    int64_t* __restrict const mp;
    int64_t& rhs_internal;
    const int size;
};

inline std::ostream& operator<<(std::ostream& os, const PackedRow& m)
{
    for(int i = 0; i < m.size*64; i++) os << (int)m[i];
    os << " -- rhs: " << m.rhs();
    return os;
}

inline uint32_t PackedRow::popcnt_at_least_2() const
{
    uint32_t ret = 0;
    for (int i = 0; i < size && ret < 2; i++) ret += __builtin_popcountll((uint64_t)mp[i]);
    return ret;
}

inline uint32_t PackedRow::popcnt() const
{
    uint32_t ret = 0;
    for (int i = 0; i < size; i++) ret += __builtin_popcountll((uint64_t)mp[i]);
    return ret;
}

// ---- PackedMatrix (from packedmatrix.h) ----

class PackedMatrix
{
public:
    PackedMatrix() : mp(nullptr), numRows(0), numCols(0) {}

    ~PackedMatrix()
    {
        #ifdef _WIN32
        _aligned_free((void*)mp);
        #else
        free(mp);
        #endif
    }

    void resize(const uint32_t num_rows, uint32_t num_cols)
    {
        num_cols = num_cols / 64 + (bool)(num_cols % 64);
        if (numRows*(numCols+1) < (int)num_rows*((int)num_cols+1)) {
            size_t size = sizeof(int64_t) * num_rows*(num_cols+1);
            #ifdef _WIN32
            _aligned_free((void*)mp);
            mp = (int64_t*)_aligned_malloc(size, 16);
            #else
            free(mp);
            int ret = posix_memalign((void**)&mp, 16, size);
            release_assert(ret == 0);
            #endif
        }
        numRows = num_rows;
        numCols = num_cols;
    }

    void resizeNumRows(const uint32_t num_rows)
    {
        assert((int)num_rows <= numRows);
        numRows = num_rows;
    }

    PackedMatrix& operator=(const PackedMatrix& b)
    {
        if (numRows*(numCols+1) < b.numRows*(b.numCols+1)) {
            size_t size = sizeof(int64_t) * b.numRows*(b.numCols+1);
            #ifdef _WIN32
            _aligned_free((void*)mp);
            mp = (int64_t*)_aligned_malloc(size, 16);
            #else
            free(mp);
            int ret = posix_memalign((void**)&mp, 16, size);
            release_assert(ret == 0);
            #endif
        }
        numRows = b.numRows;
        numCols = b.numCols;
        memcpy(mp, b.mp, sizeof(int64_t)*numRows*(numCols+1));
        return *this;
    }

    inline PackedRow operator[](const uint32_t i)
    {
        return PackedRow(numCols, mp+i*(numCols+1));
    }
    inline PackedRow operator[](const uint32_t i) const
    {
        return PackedRow(numCols, mp+i*(numCols+1));
    }

    class iterator
    {
    public:
        friend class PackedMatrix;
        PackedRow operator*() { return PackedRow(numCols, mp); }
        iterator& operator++() { mp += (numCols+1); return *this; }
        iterator operator+(const uint32_t num) const
        { iterator ret(*this); ret.mp += (numCols+1)*num; return ret; }
        uint32_t operator-(const iterator& b) const { return (mp - b.mp)/((numCols+1)); }
        void operator+=(const uint32_t num) { mp += (numCols+1)*num; }
        bool operator!=(const iterator& it) const { return mp != it.mp; }
        bool operator==(const iterator& it) const { return mp == it.mp; }
    private:
        iterator(int64_t* _mp, const uint32_t _numCols) : mp(_mp), numCols(_numCols) {}
        int64_t* mp;
        const uint32_t numCols;
    };

    inline iterator begin() { return iterator(mp, numCols); }
    inline iterator end()   { return iterator(mp+numRows*(numCols+1), numCols); }
    inline uint32_t getSize() const { return numRows; }

private:
    int64_t* mp;
    int numRows;
    int numCols;
};

} // namespace CMSat
