#ifndef __FEXPR_OPS_HPP_
#define __FEXPR_OPS_HPP_

#include "fexpr.hpp"

namespace stoch {

afexpr_p operator+(const afexpr_p& e1, const afexpr_p& e2)
{
    return afexpr_p(new stoch::fplus(e1, e2));
}

afexpr_p operator-(const afexpr_p& e1, const afexpr_p& e2)
{
    return afexpr_p(new stoch::fminus(e1, e2));
}

afexpr_p operator*(const afexpr_p& e1, const afexpr_p& e2)
{
    return afexpr_p(new stoch::fmultiplies(e1, e2));
}

afexpr_p operator/(const afexpr_p& e1, const afexpr_p& e2)
{
    return afexpr_p(new stoch::fdivides(e1, e2));
}

/* afexpr_p operator%(const afexpr_p& e1, const afexpr_p& e2)
{
    return afexpr_p(new stoch::fmodulus(e1, e2));
} */

afexpr_p operator-(const afexpr_p& e)
{
    return afexpr_p(new stoch::fnegate(e));
}

bfexpr_p operator==(const afexpr_p& e1, const afexpr_p& e2)
{
    return bfexpr_p(new stoch::fequal_to(e1, e2));
}

bfexpr_p operator!=(const afexpr_p& e1, const afexpr_p& e2)
{
    return bfexpr_p(new stoch::fnot_equal_to(e1, e2));
}

bfexpr_p operator>(const afexpr_p& e1, const afexpr_p& e2)
{
    return bfexpr_p(new stoch::fgreater(e1, e2));
}

bfexpr_p operator<(const afexpr_p& e1, const afexpr_p& e2)
{
    return bfexpr_p(new stoch::fless(e1, e2));
}

bfexpr_p operator>=(const afexpr_p& e1, const afexpr_p& e2)
{
    return bfexpr_p(new stoch::fgreater_equal(e1, e2));
}

bfexpr_p operator<=(const afexpr_p& e1, const afexpr_p& e2)
{
    return bfexpr_p(new stoch::fless_equal(e1, e2));
}

bfexpr_p operator&&(const bfexpr_p& e1, const bfexpr_p& e2)
{
    return bfexpr_p(new stoch::flogical_and(e1, e2));
}

bfexpr_p operator||(const bfexpr_p& e1, const bfexpr_p& e2)
{
    return bfexpr_p(new stoch::flogical_or(e1, e2));
}

bfexpr_p operator==(const bfexpr_p& e1, const bfexpr_p& e2)
{
    return bfexpr_p(new stoch::flogical_eq(e1, e2));
}

bfexpr_p operator!(const bfexpr_p& e)
{
    return bfexpr_p(new stoch::flogical_not(e));
}

bfexpr_p bfexpr_impl(const bfexpr_p& e1, const bfexpr_p& e2)
{
    return (!e1) || e2;
}

bvfexpr_p operator+(const bvfexpr_p& e1, const bvfexpr_p& e2)
{
    return bvfexpr_p(new stoch::fbv_add(e1, e2));
}

bvfexpr_p operator-(const bvfexpr_p& e1, const bvfexpr_p& e2)
{
    return bvfexpr_p(new stoch::fbv_sub(e1, e2));
}

bvfexpr_p operator*(const bvfexpr_p& e1, const bvfexpr_p& e2)
{
    return bvfexpr_p(new stoch::fbv_mul(e1, e2));
}

bvfexpr_p operator-(const bvfexpr_p& e)
{
    return bvfexpr_p(new stoch::fbv_neg(e));
}

bfexpr_p operator==(const bvfexpr_p& e1, const bvfexpr_p& e2)
{
    return bfexpr_p(new stoch::fbv_eq(e1, e2));
}

bfexpr_p operator<=(const bvfexpr_p& e1, const bvfexpr_p& e2)
{
    return bfexpr_p(new stoch::fbv_ule(e1, e2));
}

bfexpr_p operator<(const bvfexpr_p& e1, const bvfexpr_p& e2)
{
    return bfexpr_p(new stoch::fbv_ult(e1, e2));
}

bvfexpr_p operator!(const bvfexpr_p& e)
{
    return bvfexpr_p(new stoch::fbv_not(e));
}

bvfexpr_p operator&(const bvfexpr_p& e1, const bvfexpr_p& e2)
{
    return bvfexpr_p(new stoch::fbv_and(e1, e2));
}

bvfexpr_p operator|(const bvfexpr_p& e1, const bvfexpr_p& e2)
{
    return bvfexpr_p(new stoch::fbv_or(e1, e2));
}

bvfexpr_p operator^(const bvfexpr_p& e1, const bvfexpr_p& e2)
{
    return bvfexpr_p(new stoch::fbv_xor(e1, e2));
}

bvfexpr_p operator~(const bvfexpr_p& e)
{
    return bvfexpr_p(new stoch::fbv_not(e));
}

}

#endif // __FEXPR_OPS_HPP_

