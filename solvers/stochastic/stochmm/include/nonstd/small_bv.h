#ifndef __SMALL_BV_H_
#define __SMALL_BV_H_

#include <algorithm>
#include <cassert>
#include <cstdint>
#include <limits>
#include <iostream>
#include <sstream>
#include <stdexcept>

#include <boost/lexical_cast.hpp>

#include "bv.h"

namespace stoch
{

struct small_bv
{
    typedef int_least64_t signed_t;
    typedef uint_least64_t unsigned_t;

    small_bv() : len(1), x(0) {};

    small_bv(size_t len, unsigned_t x) : len(len), x(x)
    {
        check_len();
    }

    small_bv(std::string s) : len(0), x(0)
    {
        assert (s.size() > 2);

        if (s[1] == 'b' || s[1] == 'B')
        {
            assert (s.size() - 2 <= digits);
            len = s.size() - 2;
            for (size_t i = 0; i + 2 < s.size(); i++)
            {
                if (s[s.size() - i - 1] == '1')
                {
                    x = (x | (1 << i));
                }
            }
        }
        else /* (s[1] == 'x' || s[1] == 'X') */
        {
            assert (4 * (s.size() - 2) <= digits);
            len = 4 * s.size() - 8;
            std::istringstream in(s.substr(2));
            in >> std::hex >> x;
        }
    }

    std::string to_string() const
    {
        if (len % 4 == 0)
        {
            std::ostringstream oss;
            oss << std::hex << x;
            std::string res = std::string(len / 4, '0') + oss.str();
            return std::string("#x") + res.substr(res.size() - len / 4);
        }
        else
        {
            std::string res;
            unsigned_t tx = x;
            for (size_t i = 0; i < len; i++)
            {
                if (tx % 2 == 1)
                {
                    res = res + "1";
                }
                else
                {
                    res = res + "0";
                }
                tx /= 2;
            }
            res = res + "b#";
            std::reverse(res.begin(), res.end());
            return res;
        }
    }

    void check_len() const
    {
        if (len == 0)
        {
            throw std::underflow_error("Bit-vectors cannot be of length 0.");
        }
        else if (len > digits)
        {
            throw std::overflow_error("Small bit-vectors cannot be " +
                                      boost::lexical_cast <std::string> (len) +
                                      " bits long. Recompile with macro [__BIG_BV_] defined.");
        }
    }

    small_bv mask() const
    {
        if (len == digits)
        {
            return small_bv(len, -1);
        }
        else
        {
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

std::ostream& operator<<(std::ostream& out, const small_bv& v)
{
    return out << v.to_string();
}

small_bv bv_set_bit(const small_bv& v, size_t pos, bool val)
{
    small_bv ans(v);

    if (val)
    {
        ans.x = (ans.x | (1 << pos));
    }
    else
    {
        ans.x = (ans.x & ~(1 << pos));
    }

    return ans;
}

} // namespace stoch

#endif // __SMALL_BV_H_
