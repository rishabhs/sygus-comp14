#ifndef __FEXPR_VAR_HPP_
#define __FEXPR_VAR_HPP_

#include "fexpr.hpp"

namespace stoch {

template <typename U> struct fvariable;
typedef fvariable <z_class> fzvar;
typedef fvariable <bool> fbvar;
typedef fvariable <bv> fbvvar;

template <typename U>
struct fvariable : public fexpr <U>
{
    typedef expr <U> eU;
    typedef fexpr <U> feU;
    typedef fvariable <U> this_t;
    typedef shared_ptr <const eU> eU_p;
    typedef shared_ptr <const feU> feU_p;

    fvariable(const id& x) : x(x), len(1)
    {
        bool is_bv = std::is_same <U, bv>::value;
        assert(!is_bv);
    }

    fvariable(const id& x, size_t len) : x(x), len(len)
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

    virtual eU_p subst(const subst_t& subst) const
    {
        bool is_bv = std::is_same <U, bv>::value;
        if (!is_bv) {
            return eU_p(new variable <U> (x));
        } else {
            return eU_p(new variable <U> (x, len));
        }
    }

    virtual feU_p subst(const fsubst_t& fsubst) const
    {
        const afsubst_t& afsubst = std::get <0> (fsubst);
        const bfsubst_t& bfsubst = std::get <1> (fsubst);
        const bvfsubst_t& bvfsubst = std::get <2> (fsubst);
        return nonstd::get(afsubst, bfsubst, bvfsubst, U()).at(x);
    }

    virtual eU_p dsubst(const subst_t& subst) const
    {
        bool is_bv = std::is_same <U, bv>::value;
        if (!is_bv) {
            return eU_p(new variable <U> (x));
        } else {
            return eU_p(new variable <U> (x, len));
        }
    }

    virtual U eval(const subst_t& subst, const val_t& val, memo_t& memo) const
    {
        const aval_t& aval = std::get <0> (val);
        const bval_t& bval = std::get <1> (val);
        const bvval_t& bvval = std::get <2> (val);
        return nonstd::get(aval, bval, bvval, U()).at(x);
    }

    virtual void cs_elim(cs_elim_args_t& cs_elim_args) const {}

    virtual var_set free_variables() const
    {
        set_id free_zvar = nonstd::vget(set_id { x }, set_id(), set_id(), U());
        set_id free_bvar = nonstd::vget(set_id(), set_id { x }, set_id(), U());
        set_id free_bvvar = nonstd::vget(set_id(), set_id(), set_id { x }, U());
        return var_set(free_zvar, free_bvar, free_bvvar);
    }

    virtual var_set bound_variables() const
    {
        return var_set();
    }

    virtual var_set abound_vars(id s, const var_set& all_vars) const
    {
        return all_vars;
    }

    virtual var_set bbound_vars(id s, const var_set& all_vars) const
    {
        return all_vars;
    }

    virtual var_set bvbound_vars(id s, const var_set& all_vars) const
    {
        return all_vars;
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

    virtual feU_p deep_copy() const
    {
        return feU_p(new this_t(x));
    }

    id x;
    size_t len;
};

}

#endif // __FEXPR_VAR_HPP_

