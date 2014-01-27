#ifndef __EXPR_INFR_OPS_H_
#define __EXPR_INFR_OPS_H_

#include "expr_infr.h"

namespace stoch
{

aexpr_p operator+(const aexpr_p& e1, const aexpr_p& e2)
{
    return aexpr_p(new stoch::plus(e1, e2));
}

aexpr_p operator-(const aexpr_p& e1, const aexpr_p& e2)
{
    return aexpr_p(new stoch::minus(e1, e2));
}

aexpr_p operator*(const aexpr_p& e1, const aexpr_p& e2)
{
    return aexpr_p(new stoch::multiplies(e1, e2));
}

/* aexpr_p operator/(const aexpr_p& e1, const aexpr_p& e2) {
	return aexpr_p(new stoch::divides(e1, e2));
}

aexpr_p operator%(const aexpr_p& e1, const aexpr_p& e2) {
	return aexpr_p(new stoch::modulus(e1, e2));
} */

aexpr_p operator-(const aexpr_p& e)
{
    return aexpr_p(new stoch::negate(e));
}

bexpr_p operator==(const aexpr_p& e1, const aexpr_p& e2)
{
    return bexpr_p(new stoch::equal_to(e1, e2));
}

bexpr_p operator!=(const aexpr_p& e1, const aexpr_p& e2)
{
    return bexpr_p(new stoch::not_equal_to(e1, e2));
}

bexpr_p operator>(const aexpr_p& e1, const aexpr_p& e2)
{
    return bexpr_p(new stoch::greater(e1, e2));
}

bexpr_p operator<(const aexpr_p& e1, const aexpr_p& e2)
{
    return bexpr_p(new stoch::less(e1, e2));
}

bexpr_p operator>=(const aexpr_p& e1, const aexpr_p& e2)
{
    return bexpr_p(new stoch::greater_equal(e1, e2));
}

bexpr_p operator<=(const aexpr_p& e1, const aexpr_p& e2)
{
    return bexpr_p(new stoch::less_equal(e1, e2));
}

bexpr_p operator&&(const bexpr_p& e1, const bexpr_p& e2)
{
    return bexpr_p(new stoch::logical_and(e1, e2));
}

bexpr_p operator||(const bexpr_p& e1, const bexpr_p& e2)
{
    return bexpr_p(new stoch::logical_or(e1, e2));
}

bexpr_p operator==(const bexpr_p& e1, const bexpr_p& e2)
{
    return bexpr_p(new stoch::logical_eq(e1, e2));
}

bexpr_p operator!(const bexpr_p& e)
{
    return bexpr_p(new stoch::logical_not(e));
}

bexpr_p bexpr_impl(const bexpr_p& e1, const bexpr_p& e2)
{
    return (!e1) || e2;
}

bvexpr_p operator+(const bvexpr_p& e1, const bvexpr_p& e2)
{
    return bvexpr_p(new stoch::bv_add(e1, e2));
}

bvexpr_p operator-(const bvexpr_p& e1, const bvexpr_p& e2)
{
    return bvexpr_p(new stoch::bv_sub(e1, e2));
}

bvexpr_p operator*(const bvexpr_p& e1, const bvexpr_p& e2)
{
    return bvexpr_p(new stoch::bv_mul(e1, e2));
}

bvexpr_p operator-(const bvexpr_p& e)
{
    return bvexpr_p(new stoch::bv_neg(e));
}

bexpr_p operator==(const bvexpr_p& e1, const bvexpr_p& e2)
{
    return bexpr_p(new stoch::bv_eq(e1, e2));
}

bvexpr_p operator&(const bvexpr_p& e1, const bvexpr_p& e2)
{
    return bvexpr_p(new stoch::bv_and(e1, e2));
}

bvexpr_p operator|(const bvexpr_p& e1, const bvexpr_p& e2)
{
    return bvexpr_p(new stoch::bv_or(e1, e2));
}

bvexpr_p operator^(const bvexpr_p& e1, const bvexpr_p& e2)
{
    return bvexpr_p(new stoch::bv_xor(e1, e2));
}

bvexpr_p operator~(const bvexpr_p& e)
{
    return bvexpr_p(new stoch::bv_not(e));
}

} // namespace stoch

#endif // __EXPR_INFR_OPS_H_
