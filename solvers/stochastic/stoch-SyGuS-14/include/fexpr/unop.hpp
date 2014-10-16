#ifndef __FEXPR_UNOP_HPP_
#define __FEXPR_UNOP_HPP_

#include "fexpr.hpp"

namespace stoch {

template <typename U, typename V, template <typename, typename> class f>
struct funop;

typedef funop <z_class, z_class, nonstd::negate> fnegate;
typedef funop <bool, bool, nonstd::logical_not> flogical_not;

typedef funop <bv, bv, nonstd::bv_not> fbv_not;
typedef funop <bv, bv, nonstd::bv_neg> fbv_neg;

template <typename U, typename V, template <typename, typename> class f>
struct funop : public fexpr <V>
{
    typedef expr <U> eU;
    typedef expr <V> eV;
    typedef fexpr <U> feU;
    typedef fexpr <V> feV;
    typedef funop <U, V, f> this_t;
    typedef shared_ptr <const eU> eU_p;
    typedef shared_ptr <const eV> eV_p;
    typedef shared_ptr <const feU> feU_p;
    typedef shared_ptr <const feV> feV_p;

    funop(feU_p fe) : fe(fe) {};

    virtual ostream& print(ostream& out) const
    {
        return out << "(" << f <U, V>::op << " " << *fe << ")";
    }

    virtual eV_p subst(const subst_t& subst) const
    {
        return eV_p(new unop <U, V, f> (fe -> subst(subst)));
    }

    virtual feV_p subst(const fsubst_t& fsubst) const
    {
        return feV_p(new this_t(fe -> subst(fsubst)));
    }

    virtual eV_p dsubst(const subst_t& subst) const
    {
        return eV_p(new unop <U, V, f> (fe -> dsubst(subst)));
    }

    virtual V eval(const subst_t& subst, const val_t& val, memo_t& memo) const
    {
        /* auto& V_memo = nonstd::get(memo.zmemo, memo.bmemo, memo.bvmemo, V());

        if (cs_elim_index && V_memo.find(*cs_elim_index) != memo.end()) {
            return memo.at(*cs_elim_index);
        } */

        U fes(fe -> eval(subst, val, memo));
        V ans = f <U, V> () (fes);

        /* if (cs_elim_index) {
            V_memo[*cs_elim_index] = ans;
        } */

        return ans;
    }

    virtual void cs_elim(cs_elim_args_t& cs_elim_args) const {
        fe -> cs_elim(cs_elim_args);

        auto full_expr = this -> subst(cs_elim_args.fsubst);
        string me = lexical_cast <string> (full_expr);
        auto& memo = nonstd::get(cs_elim_args.amemo, cs_elim_args.bmemo,
            cs_elim_args.bvmemo, V());
        if (memo.find(me) == memo.end()) {
            size_t v = memo.size();
            memo[me] = v;
        }

        cs_elim_index = memo[me];
    }

    virtual var_set free_variables() const
    {
        return fe -> free_variables();
    }

    virtual var_set bound_variables() const
    {
        return fe -> bound_variables();
    }

    virtual var_set abound_vars(id s, const var_set& all_vars) const
    {
        return fe -> abound_vars(s, all_vars);
    }

    virtual var_set bbound_vars(id s, const var_set& all_vars) const
    {
        return fe -> bbound_vars(s, all_vars);
    }

    virtual var_set bvbound_vars(id s, const var_set& all_vars) const
    {
        return fe -> bvbound_vars(s, all_vars);
    }

    virtual size_t bvlen() const
    {
        bool is_bv = std::is_same <V, bv>::value;
        assert(is_bv);
        return fe -> bvlen();
    }

    virtual size_t size() const {
        return 1 + fe -> size();
    }

    virtual feV_p deep_copy() const {
        return feV_p(new this_t(fe -> deep_copy()));
    }

    feU_p fe;
    mutable optional <size_t> cs_elim_index;
};

}

#endif // __FEXPR_UNOP_HPP_

