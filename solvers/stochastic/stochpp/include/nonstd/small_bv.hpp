#ifndef __NONSTD_SMALL_BV_HPP_
#define __NONSTD_SMALL_BV_HPP_

#include "nonstd.hpp"

namespace stoch {

struct small_bv
{
    typedef int_least64_t signed_t;
    typedef uint_least64_t unsigned_t;

    small_bv() : len(1), x(0) {};

    small_bv(size_t len, unsigned_t x) : len(len), x(x)
    {
        assert (0 < len && len <= digits);
    }

    small_bv(const string& s) : len(0), x(0)
    {
        assert (2 < s.size());

        if (s[1] == 'b' || s[1] == 'B') {
            assert (s.size() - 2 <= digits);
            len = s.size() - 2;
            for (size_t i = 0; i + 2 < s.size(); i++) {
                if (s[s.size() - i - 1] == '1') {
                    x = (x | (1 << i));
                }
            }
        } else /* (s[1] == 'x' || s[1] == 'X') */ {
            assert (4 * (s.size() - 2) <= digits);
            len = 4 * s.size() - 8;
            std::istringstream in(s.substr(2));
            in >> std::hex >> x;
        }
    }

    string to_string() const
    {
        if (len % 4 == 0) {
            std::ostringstream oss;
            oss << std::hex << x;
            string res = string(len / 4, '0') + oss.str();
            return string("#x") + res.substr(res.size() - len / 4);
        } else {
            string res;
            unsigned_t tx = x;
            for (size_t i = 0; i < len; i++) {
                if (tx % 2 == 1) {
                    res = res + "1";
                } else {
                    res = res + "0";
                }
                tx /= 2;
            }
            res = res + "b#";
            std::reverse(res.begin(), res.end());
            return res;
        }
    }

    small_bv mask() const
    {
        if (len == digits) {
            return small_bv(len, -1);
        } else {
            unsigned_t mask((unsigned_t(1) << len) - 1);
            x = (x & mask);
            return small_bv(len, mask);
        }
    }

    small_bv neg_max() const
    {
        unsigned_t u1(1), lenm1(len - 1);
        return small_bv(len, u1 << lenm1);
    }

    bool msb() const
    {
        mask();
        unsigned_t u1(1), lenm1(len - 1);
        return x >= (u1 << lenm1);
    }

    size_t width() const
    {
        return digits;
    }

    size_t len;
    mutable unsigned_t x;
    static const size_t digits = std::numeric_limits <unsigned_t>::digits;
};

ostream& operator<<(ostream& out, const small_bv& v)
{
    return out << v.to_string();
}

small_bv bv_set_bit(const small_bv& v, size_t pos, bool val)
{
    assert (pos < v.len);
    small_bv ans(v);

    if (val) {
        ans.x = (ans.x | (1 << pos));
    } else {
        ans.x = (ans.x & ~(1 << pos));
    }

    return ans;
}

} // namespace stoch

#endif // __NONSTD_SMALL_BV_HPP_

