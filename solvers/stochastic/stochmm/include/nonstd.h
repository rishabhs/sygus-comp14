#ifndef __NONSTD_H_
#define __NONSTD_H_

#include <cmath>
#include <string>

#include <boost/current_function.hpp>
#include <boost/lexical_cast.hpp>
#include <boost/optional.hpp>

#define __LOGSTR__ std::string(__FILE__ ": ") + \
	boost::lexical_cast <std::string> (__LINE__) + ". "
#define __F_LOGSTR__ std::string(__FILE__ ": ") + \
	boost::lexical_cast <std::string> (__LINE__) + ": " + \
	boost::lexical_cast <std::string> (BOOST_CURRENT_FUNCTION) + ". "

namespace stoch
{

bool verbose_mode = false;

} // namespace stoch

#include "nonstd/bv.h"

namespace stoch
{

#ifdef __BIG_Z_
    typedef mpz_class z_class;
#else
    typedef long z_class;
#endif

namespace nonstd
{

template <typename T1, typename T2, typename T3>
T1& get(T1& t1, T2& t2, T3& t3, z_class u)
{
    return t1;
}

template <typename T1, typename T2, typename T3>
T2& get(T1& t1, T2& t2, T3& t3, bool b)
{
    return t2;
}

template <typename T1, typename T2, typename T3>
T3& get(T1& t1, T2& t2, T3& t3, bv b)
{
    return t3;
}

template <typename T1, typename T2, typename T3>
T1 vget(T1 t1, T2 t2, T3 t3, z_class u)
{
    return t1;
}

template <typename T1, typename T2, typename T3>
T2 vget(T1 t1, T2 t2, T3 t3, bool b)
{
    return t2;
}

template <typename T1, typename T2, typename T3>
T3 vget(T1 t1, T2 t2, T3 t3, bv v)
{
    return t3;
}

size_t luby(size_t n)
{
    if ((n & (n + 1)) == 0)
    {
        return (n + 1) / 2;
    }
    else
    {
        double dn = static_cast <double> (n);
        size_t shift = static_cast <size_t> (floor(log2(dn)));
        size_t diff = size_t(1) << shift;
        assert(n - diff + 1 < n);
        return luby(n - diff + 1);
    }
}

} // namespace nonstd
} // namespace stoch

#include "nonstd/nonfunctional.h"

#endif // __NONSTD_H_

