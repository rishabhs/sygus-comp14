#ifndef __FEXPR_HPP_
#define __FEXPR_HPP_

#include "nonstd.hpp"
#include "base.hpp"

namespace stoch {

template <typename U> struct fexpr
{
    typedef expr <U> eU;
    typedef fexpr <U> feU;
    typedef shared_ptr <const eU> eU_p;
    typedef shared_ptr <const feU> feU_p;

    virtual ostream& print(ostream& out) const = 0;
    // Given an fexpr, and an expression for each uninterpreted function, returns
    // an expr with the substitution performed
    virtual eU_p subst(const subst_t& subst) const = 0;
    // Given an fexpr, and an expression for each variable, returns an fexpr with
    // the substitution performed
    virtual feU_p subst(const fsubst_t& fsubst) const = 0;
    // A grammar expansion rule is an fexpr with uninterpreted function for each
    // child non-terminal. To expand such productions, we need a dumb substitution
    // rule
    virtual eU_p dsubst(const subst_t& subst) const = 0;
    // Given an fexpr, an expression for each uninterpreted function, and a value
    // for each variable, evaluates the expression
    virtual U eval(const subst_t& subst, const val_t& val, memo_t& memo) const = 0;
    virtual U eval(const subst_t& subst, const val_t& val) const
    {
        memo_t memo;
        return eval(subst, val, memo);
    }

    virtual void cs_elim() const
    {
        cs_elim_args_t memo;
        cs_elim(memo);
    }

    virtual void cs_elim(cs_elim_args_t& cs_elim_args) const = 0;
    virtual var_set free_variables() const = 0;
    virtual var_set bound_variables() const = 0;

    // Given a grammar expansion rule, and a child non-terminal s, determines the
    // largest set of variables that are bound in all occurrences of s
    virtual var_set abound_vars(id s, const var_set& all_vars) const = 0;
    virtual var_set bbound_vars(id s, const var_set& all_vars) const = 0;
    virtual var_set bvbound_vars(id s, const var_set& all_vars) const = 0;

    virtual size_t bvlen() const = 0;
    virtual size_t size() const = 0;
    virtual shared_ptr <const feU> deep_copy() const = 0;

    virtual ~fexpr() {};
};

template <typename U>
ostream& operator<<(ostream& out, const fexpr <U>& fe)
{
    return fe.print(out);
}

} // namespace stoch

#include "fexpr/const.hpp"
#include "fexpr/var.hpp"
#include "fexpr/unop.hpp"
#include "fexpr/binop.hpp"
#include "fexpr/ite.hpp"
#include "fexpr/call.hpp"
#include "fexpr/let.hpp"
#include "fexpr/macro.hpp"
#include "fexpr/ops.hpp"

#endif // __FEXPR_HPP_

