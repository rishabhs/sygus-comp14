#ifndef __EXPR_ITE_HPP_
#define __EXPR_ITE_HPP_

#include "expr.hpp"

namespace stoch {

template <typename U> struct ite;
typedef ite <z_class> aite;
typedef ite <bool> bite;
typedef ite <bv> bvite;

template <typename U> struct fite;

template <typename U>
struct ite : public expr <U>
{
    typedef expr <U> eU;
    typedef fexpr <U> feU;
    typedef ite <U> this_t;
    typedef shared_ptr <const eU> eU_p;
    typedef shared_ptr <const feU> feU_p;

    ite(bexpr_p econd, eU_p e1, eU_p e2) : econd(econd), e1(e1), e2(e2) {};

    virtual ostream& print(ostream& out) const
    {
        return out << "(ite " << *econd << " " << *e1 << " " << *e2 << ")";
    }

    virtual U eval(const val_t& val) const
    {
        if (econd -> eval(val)) {
            return e1 -> eval(val);
        } else {
            return e2 -> eval(val);
        }
    }

    virtual eU_p subst(const subst_t& subst) const
    {
        bexpr_p ecs(econd -> subst(subst));
        eU_p e1s(e1 -> subst(subst));
        eU_p e2s(e2 -> subst(subst));
        return eU_p(new this_t(ecs, e1s, e2s));
    }

    virtual z3::expr smt(z3::context& ctxt) const
    {
        z3::expr ecs(econd -> smt(ctxt));
        z3::expr e1s(e1 -> smt(ctxt));
        z3::expr e2s(e2 -> smt(ctxt));
        return z3::to_expr(ctxt, Z3_mk_ite(ctxt, ecs, e1s, e2s));
    }

    virtual feU_p f_lift() const
    {
        return feU_p(new fite <U> (econd -> f_lift(), e1 -> f_lift(), e2 -> f_lift()));
    }

    virtual size_t bvlen() const
    {
        bool is_bv = std::is_same <U, bv>::value;
        assert(is_bv);
        return e1 -> bvlen();
    }

    virtual size_t size() const
    {
        return 1 + econd -> size() + e1 -> size() + e2 -> size();
    }

    virtual eU_p deep_copy() const
    {
        bexpr_p ecc(econd -> deep_copy());
        eU_p e1c(e1 -> deep_copy());
        eU_p e2c(e2 -> deep_copy());
        return eU_p(new this_t(ecc, e1c, e2c));
    }

    bexpr_p econd;
    eU_p e1, e2;
};

} // namespace stoch

#endif // __EXPR_ITE_HPP_

