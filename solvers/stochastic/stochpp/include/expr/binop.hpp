#ifndef __EXPR_BINOP_HPP_
#define __EXPR_BINOP_HPP_

#include "expr.hpp"

namespace stoch {

template <typename U, typename V, template <typename, typename> class f>
struct binop;

typedef binop <z_class, z_class, nonstd::plus> plus;
typedef binop <z_class, z_class, nonstd::minus> minus;
typedef binop <z_class, z_class, nonstd::multiplies> multiplies;
typedef binop <z_class, z_class, nonstd::divides> divides;
// typedef binop <z_class, z_class, nonstd::modulus> modulus;

typedef binop <z_class, bool, nonstd::equal_to> equal_to;
typedef binop <z_class, bool, nonstd::not_equal_to> not_equal_to;
typedef binop <z_class, bool, nonstd::greater> greater;
typedef binop <z_class, bool, nonstd::less> less;
typedef binop <z_class, bool, nonstd::greater_equal> greater_equal;
typedef binop <z_class, bool, nonstd::less_equal> less_equal;

struct logical_and;
struct logical_or;
typedef binop <bool, bool, nonstd::logical_eq> logical_eq;
typedef binop <bool, bool, nonstd::logical_xor> logical_xor;

typedef binop <bv, bool, nonstd::bv_ult> bv_ult;
typedef binop <bv, bool, nonstd::bv_slt> bv_slt;
typedef binop <bv, bool, nonstd::bv_ule> bv_ule;
typedef binop <bv, bool, nonstd::bv_sle> bv_sle;
typedef binop <bv, bool, nonstd::bv_eq> bv_eq;
typedef binop <bv, bool, nonstd::bv_uge> bv_uge;
typedef binop <bv, bool, nonstd::bv_sge> bv_sge;
typedef binop <bv, bool, nonstd::bv_ugt> bv_ugt;
typedef binop <bv, bool, nonstd::bv_sgt> bv_sgt;

typedef binop <bv, bv, nonstd::bv_and> bv_and;
typedef binop <bv, bv, nonstd::bv_or> bv_or;
typedef binop <bv, bv, nonstd::bv_xor> bv_xor;

typedef binop <bv, bv, nonstd::bv_add> bv_add;
typedef binop <bv, bv, nonstd::bv_sub> bv_sub;
typedef binop <bv, bv, nonstd::bv_mul> bv_mul;
typedef binop <bv, bv, nonstd::bv_udiv> bv_udiv;
typedef binop <bv, bv, nonstd::bv_urem> bv_urem;
typedef binop <bv, bv, nonstd::bv_sdiv> bv_sdiv;
typedef binop <bv, bv, nonstd::bv_srem> bv_srem;

typedef binop <bv, bv, nonstd::bv_shl> bv_shl;
typedef binop <bv, bv, nonstd::bv_lshr> bv_lshr;
typedef binop <bv, bv, nonstd::bv_ashr> bv_ashr;

template <typename U, typename V, template <typename, typename> class f>
struct fbinop;

template <typename U, typename V, template <typename, typename> class f>
struct binop : public expr <V>
{
    typedef expr <U> eU;
    typedef expr <V> eV;
    typedef fexpr <U> feU;
    typedef fexpr <V> feV;
    typedef binop <U, V, f> this_t;
    typedef shared_ptr <const eU> eU_p;
    typedef shared_ptr <const eV> eV_p;
    typedef shared_ptr <const feU> feU_p;
    typedef shared_ptr <const feV> feV_p;

    binop(eU_p e1, eU_p e2) : e1(e1), e2(e2) {};

    virtual ostream& print(ostream& out) const
    {
        return out << "(" << f <U, V>::op << " " << *e1 << " " << *e2 << ")";
    }

    virtual V eval(const val_t& val) const
    {
        U e1s(e1 -> eval(val));
        U e2s(e2 -> eval(val));
        return f <U, V> () (e1s, e2s);
    }

    virtual eV_p subst(const subst_t& subst) const
    {
        eU_p e1s(e1 -> subst(subst));
        eU_p e2s(e2 -> subst(subst));
        return eV_p(new this_t(e1s, e2s));
    }

    virtual z3::expr smt(z3::context& ctxt) const
    {
        auto e1s = e1 -> smt(ctxt);
        auto e2s = e2 -> smt(ctxt);
        return f <z3::expr, z3::expr> () (e1s, e2s);
    }

    virtual feV_p f_lift() const
    {
        return feV_p(new fbinop <U, V, f> (e1 -> f_lift(), e2 -> f_lift()));
    }

    virtual size_t bvlen() const
    {
        bool is_bv = std::is_same <V, bv>::value;
        assert(is_bv);
        return e1 -> bvlen();
    }

    virtual size_t size() const
    {
        return 1 + e1 -> size() + e2 -> size();
    }

    virtual eV_p deep_copy() const
    {
        eU_p e1c(e1 -> deep_copy());
        eU_p e2c(e2 -> deep_copy());
        return eV_p(new this_t(e1c, e2c));
    }

    eU_p e1, e2;
};

typedef binop <bool, bool, nonstd::logical_and> logical_and_base;
typedef binop <bool, bool, nonstd::logical_or> logical_or_base;

struct logical_and : public logical_and_base
{
    logical_and(bexpr_p e1, bexpr_p e2) : logical_and_base(e1, e2) {};

    virtual bool eval(const val_t& val) const override
    {
        return e1 -> eval(val) && e2 -> eval(val);
    }
};

struct logical_or : public logical_or_base
{
    logical_or(bexpr_p e1, bexpr_p e2) : logical_or_base(e1, e2) {};

    virtual bool eval(const val_t& val) const override
    {
        return e1 -> eval(val) || e2 -> eval(val);
    }
};

}

#endif // __EXPR_BINOP_HPP_

