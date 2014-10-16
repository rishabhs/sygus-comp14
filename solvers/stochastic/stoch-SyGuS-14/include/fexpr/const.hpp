#ifndef __FEXPR_CONST_HPP_
#define __FEXPR_CONST_HPP_

#include "fexpr.hpp"

namespace stoch {

template <typename U> struct fconstant;
typedef fconstant <z_class> fcz;
typedef fconstant <bool> fcb;
typedef fconstant <bv> fcbv;

template <typename U>
struct fconstant : public fexpr <U>
{
    typedef expr <U> eU;
    typedef fexpr <U> feU;
    typedef fconstant <U> this_t;
    typedef shared_ptr <const eU> eU_p;
    typedef shared_ptr <const feU> feU_p;

    fconstant(U u) : u(u) {};

    virtual ostream& print(ostream& out) const
    {
        return out << u;
    }

    virtual eU_p subst(const subst_t& subst) const
    {
        return eU_p(new constant <U> (u));
    }

    virtual feU_p subst(const fsubst_t& fsubst) const
    {
        return feU_p(new this_t(u));
    }

    virtual eU_p dsubst(const subst_t& subst) const
    {
        return eU_p(new constant <U> (u));
    }

    virtual U eval(const subst_t& subst, const val_t& val, memo_t& memo) const
    {
        return u;
    }

    virtual void cs_elim(cs_elim_args_t& cs_elim_args) const {}

    virtual var_set free_variables() const
    {
        return var_set();
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
        return nonstd::vget(bv(1, 0), bv(1, 0), u, U()).len;
    }

    virtual size_t size() const
    {
        return 1;
    }

    virtual feU_p deep_copy() const
    {
        return feU_p(new this_t(u));
    }

    U u;
};

}

#endif // __FEXPR_CONST_HPP_

