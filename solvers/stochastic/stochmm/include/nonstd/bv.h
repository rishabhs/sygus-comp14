#ifndef __BV_H_
#define __BV_H_

#include "small_bv.h"
#include "big_bv.h"
#include "bv_ops.h"

namespace stoch
{

#ifdef __BIG_BV_
    // TODO Implement [big_bv]
    // TODO Implement operator overloads for [big_bv]
    typedef big_bv bv;
#else
    typedef small_bv bv;
#endif

} // namespace stoch

#endif // __BV_H_
