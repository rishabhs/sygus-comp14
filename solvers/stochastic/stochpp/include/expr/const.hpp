#ifndef __EXPR_CONST_HPP_
#define __EXPR_CONST_HPP_

#include "expr.hpp"

namespace stoch {

template <typename U> struct constant;
typedef constant <z_class> cz;
typedef constant <bool> cb;
typedef constant <bv> cbv;

template <typename U> struct fconstant;

template <typename U>
struct constant : public expr <U>
{
    typedef expr <U> eU;
    typedef fexpr <U> feU;
    typedef constant <U> this_t;
    typedef shared_ptr <const eU> eU_p;
    typedef shared_ptr <const feU> feU_p;

    constant(U u) : u(u) {};

    virtual ostream& print(ostream& out) const
    {
        return out << u;
    }

    virtual U eval(const val_t& val) const
    {
        return u;
    }

    virtual eU_p subst(const subst_t& subst) const
    {
        return eU_p(new this_t(u));
    }

    virtual z3::expr smt(z3::context& ctxt) const
    {
        return smt(ctxt, u);
    }

    virtual feU_p f_lift() const
    {
        return feU_p(new fconstant <U> (u));
    }

    virtual size_t bvlen() const
    {
        bool is_bv = std::is_same <U, bv>::value;
        assert(is_bv);
        return nonstd::vget(bv(1, 0), bv(1, 0), u, U()).len;
    }

    virtual size_t size() const
    {
        return 1;
    }

    virtual eU_p deep_copy() const
    {
        return eU_p(new this_t(u));
    }

    U u;

    private:

    z3::expr smt(z3::context& ctxt, z_class c) const
    {
        string cs(lexical_cast <string> (c));
        return ctxt.int_val(cs.c_str());
    }

    z3::expr smt(z3::context& ctxt, bool b) const
    {
        return ctxt.bool_val(b);
    }

    z3::expr smt(z3::context& ctxt, const bv& v) const
    {
        v.mask();
        string vs(lexical_cast <string> (v.x));
        return ctxt.bv_val(vs.c_str(), v.len);
    }
};

}

#endif // __EXPR_CONST_HPP_

