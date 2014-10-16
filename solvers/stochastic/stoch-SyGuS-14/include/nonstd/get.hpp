#ifndef __NONSTD_GET_HPP_
#define __NONSTD_GET_HPP_

#include "nonstd.hpp"

namespace stoch {
namespace nonstd {

// The following is some domain specific template hackery I hold close to my
// heart. However, it should be expressible in a more idiomatic way using
// C++11 type-traits.
// TODO Find out how.

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
T1 vget(const T1& t1, const T2& t2, const T3& t3, z_class u)
{
    return t1;
}

template <typename T1, typename T2, typename T3>
T2 vget(const T1& t1, const T2& t2, const T3& t3, bool b)
{
    return t2;
}

template <typename T1, typename T2, typename T3>
T3 vget(const T1& t1, const T2& t2, const T3& t3, bv v)
{
    return t3;
}

} // namespace nonstd
} // namespace stoch

#endif // __NONSTD_GET_HPP_

