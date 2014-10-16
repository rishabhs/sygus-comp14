#ifndef __EXPR_VAR_HPP_
#define __EXPR_VAR_HPP_

#include "expr.hpp"

namespace stoch {

template <typename U> struct variable;
typedef variable <z_class> zvar;
typedef variable <bool> bvar;
typedef variable <bv> bvvar;

template <typename U> struct fvariable;

template <typename U>
struct variable : public expr <U>
{
    typedef expr <U> eU;
    typedef fexpr <U> feU;
    typedef variable <U> this_t;
    typedef shared_ptr <const eU> eU_p;
    typedef shared_ptr <const feU> feU_p;

    variable(const id& x) : x(x), len(1)
    {
        bool is_bv = std::is_same <U, bv>::value;
        assert(!is_bv);
    }

    variable(const id& x, size_t len) : x(x), len(len)
    {
        bool is_bv = std::is_same <U, bv>::value;
        assert(is_bv);
        if (len == 0) {
            throw std::underflow_error("Bit-vectors cannot be of length 0.");
        }
    };

    virtual ostream& print(ostream& out) const
    {
        return out << nonstd::get("x", "b", "v", U()) << x.v;
    }

    virtual U eval(const val_t& val) const
    {
        const aval_t& aval = std::get <0> (val);
        const bval_t& bval = std::get <1> (val);
        const bvval_t& bvval = std::get <2> (val);
        return nonstd::get(aval, bval, bvval, U()).at(x);
    }

    virtual eU_p subst(const subst_t& subst) const
    {
        const asubst_t& asubst = std::get <0> (subst);
        const bsubst_t& bsubst = std::get <1> (subst);
        const bvsubst_t& bvsubst = std::get <2> (subst);
        return nonstd::get(asubst, bsubst, bvsubst, U()).at(x);
    }

    virtual z3::expr smt(z3::context& ctxt) const
    {
        string xs(lexical_cast <string> (*this));
        z3::expr zans = ctxt.int_const(xs.c_str());
        z3::expr bans = ctxt.bool_const(xs.c_str());
        z3::expr bvans = ctxt.bv_const(xs.c_str(), len);
        return nonstd::get(zans, bans, bvans, U());
    }

    virtual feU_p f_lift() const
    {
        bool is_bv = std::is_same <U, bv>::value;
        if (!is_bv) {
            return feU_p(new fvariable <U> (x));
        } else {
            return feU_p(new fvariable <U> (x, len));
        }
    }

    virtual size_t bvlen() const
    {
        bool is_bv = std::is_same <U, bv>::value;
        assert(is_bv);
        return len;
    }

    virtual size_t size() const
    {
        return 1;
    }

    virtual eU_p deep_copy() const
    {
        if (!std::is_same <U, bv>::value) {
            return eU_p(new this_t(x));
        } else {
            return eU_p(new this_t(x, len));
        }
    }

    id x;
    size_t len;
};

}

#endif // __EXPR_VAR_HPP_

