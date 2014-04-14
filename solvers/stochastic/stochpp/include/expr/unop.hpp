#ifndef __EXPR_UNOP_HPP_
#define __EXPR_UNOP_HPP_

#include "expr.hpp"

namespace stoch {

template <typename U, typename V, template <typename, typename> class f>
struct unop;

typedef unop <z_class, z_class, nonstd::negate> negate;
typedef unop <bool, bool, nonstd::logical_not> logical_not;

typedef unop <bv, bv, nonstd::bv_not> bv_not;
typedef unop <bv, bv, nonstd::bv_neg> bv_neg;

template <typename U, typename V, template <typename, typename> class f>
struct funop;

template <typename U, typename V, template <typename, typename> class f>
struct unop : public expr <V>
{
    typedef expr <U> eU;
    typedef expr <V> eV;
    typedef fexpr <U> feU;
    typedef fexpr <V> feV;
    typedef unop <U, V, f> this_t;
    typedef shared_ptr <const eU> eU_p;
    typedef shared_ptr <const eV> eV_p;
    typedef shared_ptr <const feU> feU_p;
    typedef shared_ptr <const feV> feV_p;

    unop(eU_p e) : e(e) {};

    virtual ostream& print(ostream& out) const
    {
        return out << "(" << f <U, V>::op << " " << *e << ")";
    }

    virtual V eval(const val_t& val) const
    {
        return f <U, V> () (e -> eval(val));
    }

    virtual eV_p subst(const subst_t& subst) const
    {
        return eV_p(new this_t(e -> subst(subst)));
    }

    virtual z3::expr smt(z3::context& ctxt) const
    {
        return f <z3::expr, z3::expr> () (e -> smt(ctxt));
    }

    virtual feV_p f_lift() const
    {
        return feV_p(new funop <U, V, f> (e -> f_lift()));
    }

    virtual size_t bvlen() const
    {
        bool is_bv = std::is_same <V, bv>::value;
        assert(is_bv);
        return e -> bvlen();
    }

    virtual size_t size() const
    {
        return 1 + e -> size();
    }

    virtual eV_p deep_copy() const
    {
        return eV_p(new this_t(e -> deep_copy()));
    }

    eU_p e;
};

}

#endif // __EXPR_UNOP_HPP_

