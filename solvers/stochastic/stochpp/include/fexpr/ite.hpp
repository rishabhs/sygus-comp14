#ifndef __FEXPR_ITE_HPP_
#define __FEXPR_ITE_HPP_

#include "fexpr.hpp"

namespace stoch {

template <typename U> struct fite;
typedef fite <z_class> afite;
typedef fite <bool> bfite;
typedef fite <bv> bvfite;

template <typename U>
struct fite : public fexpr <U>
{
    typedef expr <U> eU;
    typedef fexpr <U> feU;
    typedef fite <U> this_t;
    typedef shared_ptr <const eU> eU_p;
    typedef shared_ptr <const feU> feU_p;

    fite(bfexpr_p fecond, feU_p fe1, feU_p fe2)
    : fecond(fecond), fe1(fe1), fe2(fe2) {};

    virtual ostream& print(ostream& out) const
    {
        return out << "(ite " << *fecond << " " << *fe1 << " " << *fe2 << ")";
    }

    virtual eU_p subst(const subst_t& subst) const
    {
        bexpr_p feconds(fecond -> subst(subst));
        eU_p fe1s(fe1 -> subst(subst));
        eU_p fe2s(fe2 -> subst(subst));
        return eU_p(new ite <U> (feconds, fe1s, fe2s));
    }

    virtual feU_p subst(const fsubst_t& fsubst) const
    {
        bfexpr_p fecc(fecond -> subst(fsubst));
        feU_p fe1c(fe1 -> subst(fsubst));
        feU_p fe2c(fe2 -> subst(fsubst));
        return feU_p(new this_t(fecc, fe1c, fe2c));
    }

    virtual eU_p dsubst(const subst_t& subst) const
    {
        bexpr_p feconds(fecond -> dsubst(subst));
        eU_p fe1s(fe1 -> dsubst(subst));
        eU_p fe2s(fe2 -> dsubst(subst));
        return eU_p(new ite <U> (feconds, fe1s, fe2s));
    }

    virtual U eval(const subst_t& subst, const val_t& val, memo_t& memo) const
    {
        /* auto& U_memo = nonstd::get(memo.zmemo, memo.bmemo, memo.bvmemo, U());

        if (cs_elim_index && U_memo.find(*cs_elim_index) != U_memo.end()) {
            return U_memo.at(*cs_elim_index);
        } */

        U ans;
        if (fecond -> eval(subst, val, memo)) {
            ans = fe1 -> eval(subst, val, memo);
        } else {
            ans = fe2 -> eval(subst, val, memo);
        }

        /* if (cs_elim_index) {
            U_memo[*cs_elim_index] = ans;
        } */

        return ans;
    }

    virtual void cs_elim(cs_elim_args_t& cs_elim_args) const {
        fecond -> cs_elim(cs_elim_args);
        fe1 -> cs_elim(cs_elim_args);
        fe2 -> cs_elim(cs_elim_args);

        auto full_expr = this -> subst(cs_elim_args.fsubst);
        string me = lexical_cast <string> (full_expr);
        auto& memo = nonstd::get(cs_elim_args.amemo, cs_elim_args.bmemo,
            cs_elim_args.bvmemo, U());
        if (memo.find(me) == memo.end()) {
            size_t v = memo.size();
            memo[me] = v;
        }

        cs_elim_index = memo[me];
    }

    virtual var_set free_variables() const
    {
        auto vsc = fecond -> free_variables();
        auto vs1 = fe1 -> free_variables();
        auto vs2 = fe2 -> free_variables();
        return var_set_union(vsc, var_set_union(vs1, vs2));
    }

    virtual var_set bound_variables() const
    {
        auto vsc = fecond -> bound_variables();
        auto vs1 = fe1 -> bound_variables();
        auto vs2 = fe2 -> bound_variables();
        return var_set_union(vsc, var_set_union(vs1, vs2));
    }

    virtual var_set abound_vars(id s, const var_set& all_vars) const
    {
        auto fec_abv = fecond -> abound_vars(s, all_vars);
        auto fe1_abv = fe1 -> abound_vars(s, all_vars);
        auto fe2_abv = fe2 -> abound_vars(s, all_vars);
        return var_set_intersection(fec_abv, fe1_abv, fe2_abv);
    }

    virtual var_set bbound_vars(id s, const var_set& all_vars) const
    {
        auto fec_bbv = fecond -> bbound_vars(s, all_vars);
        auto fe1_bbv = fe1 -> bbound_vars(s, all_vars);
        auto fe2_bbv = fe2 -> bbound_vars(s, all_vars);
        return var_set_intersection(fec_bbv, fe1_bbv, fe2_bbv);
    }

    virtual var_set bvbound_vars(id s, const var_set& all_vars) const
    {
        auto fec_bvbv = fecond -> bvbound_vars(s, all_vars);
        auto fe1_bvbv = fe1 -> bvbound_vars(s, all_vars);
        auto fe2_bvbv = fe2 -> bvbound_vars(s, all_vars);
        return var_set_intersection(fec_bvbv, fe1_bvbv, fe2_bvbv);
    }

    virtual size_t bvlen() const
    {
        bool is_bv = std::is_same <U, bv>::value;
        assert(is_bv);
        return fe1 -> bvlen();
    }

    virtual size_t size() const
    {
        return 1 + fecond -> size() + fe1 -> size() + fe2 -> size();
    }

    virtual feU_p deep_copy() const
    {
        bfexpr_p fecc(fecond -> deep_copy());
        feU_p fe1c(fe1 -> deep_copy());
        feU_p fe2c(fe2 -> deep_copy());
        return feU_p(new this_t(fecc, fe1c, fe2c));
    }

    bfexpr_p fecond;
    feU_p fe1, fe2;
    mutable optional <size_t> cs_elim_index;
};

}

#endif // __FEXPR_ITE_HPP_

