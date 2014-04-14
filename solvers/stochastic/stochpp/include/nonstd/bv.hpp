#ifndef __NONSTD_BV_HPP_
#define __NONSTD_BV_HPP_

#include "big_bv.hpp"
#include "small_bv.hpp"
#include "bv_ops.hpp"

namespace stoch {

#ifdef __BIG_BV_
    // TODO Implement [big_bv]
    // TODO Implement operator overloads for [big_bv]
    typedef big_bv bv;
#else
    typedef small_bv bv;
#endif

} // namespace stoch

#endif // __NONSTD_BV_HPP_

