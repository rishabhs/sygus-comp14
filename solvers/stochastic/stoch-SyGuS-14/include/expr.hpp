#ifndef __EXPR_HPP_
#define __EXPR_HPP_

#include "nonstd.hpp"
#include "base.hpp"

namespace stoch {

template <typename U> struct expr
{
    typedef expr <U> eU;
    typedef fexpr <U> feU;
    typedef shared_ptr <const eU> eU_p;
    typedef shared_ptr <const feU> feU_p;

    virtual ostream& print(ostream& out) const = 0;
    virtual U eval(const val_t& val) const = 0;
    virtual eU_p subst(const subst_t& subst) const = 0;
    virtual z3::expr smt(z3::context& ctxt) const = 0;
    virtual feU_p f_lift() const = 0;

    virtual size_t bvlen() const = 0;
    virtual size_t size() const = 0;
    virtual eU_p deep_copy() const = 0;

    virtual ~expr() {};
};

template <typename U>
ostream& operator<<(ostream& out, const expr <U>& e)
{
    return e.print(out);
}

} // namespace stoch

#include "expr/const.hpp"
#include "expr/var.hpp"
#include "expr/unop.hpp"
#include "expr/binop.hpp"
#include "expr/ite.hpp"
#include "expr/let.hpp"
#include "expr/macro.hpp"
#include "expr/ops.hpp"

#include "fexpr.hpp"

#endif // __EXPR_H_

