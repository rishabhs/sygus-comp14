#ifndef __FEXPR_BINOP_HPP_
#define __FEXPR_BINOP_HPP_

#include "fexpr.hpp"

namespace stoch {

template <typename U, typename V, template <typename, typename> class f>
struct fbinop;

typedef fbinop <z_class, z_class, nonstd::plus> fplus;
typedef fbinop <z_class, z_class, nonstd::minus> fminus;
typedef fbinop <z_class, z_class, nonstd::multiplies> fmultiplies;
typedef fbinop <z_class, z_class, nonstd::divides> fdivides;
// typedef fbinop <z_class, z_class, nonstd::modulus> fmodulus;

typedef fbinop <z_class, bool, nonstd::equal_to> fequal_to;
typedef fbinop <z_class, bool, nonstd::not_equal_to> fnot_equal_to;
typedef fbinop <z_class, bool, nonstd::greater> fgreater;
typedef fbinop <z_class, bool, nonstd::less> fless;
typedef fbinop <z_class, bool, nonstd::greater_equal> fgreater_equal;
typedef fbinop <z_class, bool, nonstd::less_equal> fless_equal;

struct flogical_and;
struct flogical_or;
typedef fbinop <bool, bool, nonstd::logical_eq> flogical_eq;
typedef fbinop <bool, bool, nonstd::logical_xor> flogical_xor;

typedef fbinop <bv, bool, nonstd::bv_ult> fbv_ult;
typedef fbinop <bv, bool, nonstd::bv_slt> fbv_slt;
typedef fbinop <bv, bool, nonstd::bv_ule> fbv_ule;
typedef fbinop <bv, bool, nonstd::bv_sle> fbv_sle;
typedef fbinop <bv, bool, nonstd::bv_eq> fbv_eq;
typedef fbinop <bv, bool, nonstd::bv_uge> fbv_uge;
typedef fbinop <bv, bool, nonstd::bv_sge> fbv_sge;
typedef fbinop <bv, bool, nonstd::bv_ugt> fbv_ugt;
typedef fbinop <bv, bool, nonstd::bv_sgt> fbv_sgt;

typedef fbinop <bv, bv, nonstd::bv_and> fbv_and;
typedef fbinop <bv, bv, nonstd::bv_or> fbv_or;
typedef fbinop <bv, bv, nonstd::bv_xor> fbv_xor;

typedef fbinop <bv, bv, nonstd::bv_add> fbv_add;
typedef fbinop <bv, bv, nonstd::bv_sub> fbv_sub;
typedef fbinop <bv, bv, nonstd::bv_mul> fbv_mul;
typedef fbinop <bv, bv, nonstd::bv_udiv> fbv_udiv;
typedef fbinop <bv, bv, nonstd::bv_urem> fbv_urem;
typedef fbinop <bv, bv, nonstd::bv_sdiv> fbv_sdiv;
typedef fbinop <bv, bv, nonstd::bv_srem> fbv_srem;

typedef fbinop <bv, bv, nonstd::bv_shl> fbv_shl;
typedef fbinop <bv, bv, nonstd::bv_lshr> fbv_lshr;
typedef fbinop <bv, bv, nonstd::bv_ashr> fbv_ashr;

template <typename U, typename V, template <typename, typename> class f>
struct fbinop : public fexpr <V>
{
    typedef expr <U> eU;
    typedef expr <V> eV;
    typedef fexpr <U> feU;
    typedef fexpr <V> feV;
    typedef fbinop <U, V, f> this_t;
    typedef shared_ptr <const eU> eU_p;
    typedef shared_ptr <const eV> eV_p;
    typedef shared_ptr <const feU> feU_p;
    typedef shared_ptr <const feV> feV_p;

    fbinop(feU_p fe1, feU_p fe2) : fe1(fe1), fe2(fe2) {};

    virtual ostream& print(ostream& out) const
    {
        return out << "(" << f <U, V>::op << " " << *fe1 << " " << *fe2 << ")";
    }

    virtual eV_p subst(const subst_t& subst) const
    {
        eU_p fe1s(fe1 -> subst(subst));
        eU_p fe2s(fe2 -> subst(subst));
        return eV_p(new binop <U, V, f> (fe1s, fe2s));
    }

    virtual feV_p subst(const fsubst_t& fsubst) const
    {
        auto fe1_s = fe1 -> subst(fsubst);
        auto fe2_s = fe2 -> subst(fsubst);
        return feV_p(new this_t(fe1_s, fe2_s));
    }

    virtual eV_p dsubst(const subst_t& subst) const
    {
        eU_p fe1s(fe1 -> dsubst(subst));
        eU_p fe2s(fe2 -> dsubst(subst));
        return eV_p(new binop <U, V, f> (fe1s, fe2s));
    }

    virtual V eval(const subst_t& subst, const val_t& val, memo_t& memo) const
    {
        /* auto& V_memo = nonstd::get(memo.zmemo, memo.bmemo, memo.bvmemo, V());

        if (cs_elim_index && V_memo.find(*cs_elim_index) != memo.end()) {
            return memo.at(*cs_elim_index);
        } */

        U fe1s(fe1 -> eval(subst, val, memo));
        U fe2s(fe2 -> eval(subst, val, memo));
        V ans = f <U, V> () (fe1s, fe2s);

        /* if (cs_elim_index) {
            V_memo[*cs_elim_index] = ans;
        } */

        return ans;
    }

    virtual void cs_elim(cs_elim_args_t& cs_elim_args) const
    {
        fe1 -> cs_elim(cs_elim_args);
        fe2 -> cs_elim(cs_elim_args);

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
        auto vs1 = fe1 -> free_variables();
        auto vs2 = fe2 -> free_variables();
        return var_set_union(vs1, vs2);
    }

    virtual var_set bound_variables() const
    {
        auto vs1 = fe1 -> bound_variables();
        auto vs2 = fe2 -> bound_variables();
        return var_set_union(vs1, vs2);
    }

    virtual var_set abound_vars(id s, const var_set& all_vars) const
    {
        auto fe1_abv = fe1 -> abound_vars(s, all_vars);
        auto fe2_abv = fe2 -> abound_vars(s, all_vars);
        return var_set_intersection(fe1_abv, fe2_abv);
    }

    virtual var_set bbound_vars(id s, const var_set& all_vars) const
    {
        auto fe1_bbv = fe1 -> bbound_vars(s, all_vars);
        auto fe2_bbv = fe2 -> bbound_vars(s, all_vars);
        return var_set_intersection(fe1_bbv, fe2_bbv);
    }

    virtual var_set bvbound_vars(id s, const var_set& all_vars) const
    {
        auto fe1_bvbv = fe1 -> bvbound_vars(s, all_vars);
        auto fe2_bvbv = fe2 -> bvbound_vars(s, all_vars);
        return var_set_intersection(fe1_bvbv, fe2_bvbv);
    }

    virtual size_t bvlen() const
    {
        bool is_bv = std::is_same <V, bv>::value;
        assert(is_bv);
        return fe1 -> bvlen();
    }

    virtual size_t size() const
    {
        return 1 + fe1 -> size() + fe2 -> size();
    }

    virtual feV_p deep_copy() const
    {
        feU_p fe1c(fe1 -> deep_copy());
        feU_p fe2c(fe2 -> deep_copy());
        return feV_p(new this_t(fe1c, fe2c));
    }

    feU_p fe1, fe2;
    mutable optional <size_t> cs_elim_index;
};

typedef fbinop <bool, bool, nonstd::logical_and> flogical_and_base;

struct flogical_and : public flogical_and_base
{
    flogical_and(bfexpr_p fe1, bfexpr_p fe2) : flogical_and_base(fe1, fe2) {};

    virtual bool eval(const subst_t& subst, const val_t& val, memo_t& memo) const
    {
        /* auto& V_memo = nonstd::get(memo.zmemo, memo.bmemo, memo.bvmemo, bool());

        if (cs_elim_index && V_memo.find(*cs_elim_index) != memo.end()) {
            return memo.at(*cs_elim_index);
        } */

        bool ans = fe1 -> eval(subst, val, memo) && fe2 -> eval(subst, val, memo);

        /* if (cs_elim_index) {
            V_memo[*cs_elim_index] = ans;
        } */

        return ans;
    }
};

typedef fbinop <bool, bool, nonstd::logical_or> flogical_or_base;

struct flogical_or : public flogical_or_base
{
    flogical_or(bfexpr_p fe1, bfexpr_p fe2) : flogical_or_base(fe1, fe2) {};

    virtual bool eval(const subst_t& subst, const val_t& val, memo_t& memo) const
    {
        /* auto& V_memo = nonstd::get(memo.zmemo, memo.bmemo, memo.bvmemo, bool());

        if (cs_elim_index && V_memo.find(*cs_elim_index) != memo.end()) {
            return memo.at(*cs_elim_index);
        } */

        bool ans = fe1 -> eval(subst, val, memo) || fe2 -> eval(subst, val, memo);

        /* if (cs_elim_index) {
            V_memo[*cs_elim_index] = ans;
        } */

        return ans;
    }
};

}

#endif // __FEXPR_BINOP_HPP_

