#ifndef __FEXPR_LET_HPP_
#define __FEXPR_LET_HPP_

#include "fexpr.hpp"

namespace stoch {

template <typename U> struct flet;
typedef flet <z_class> aflet;
typedef flet <bool> bflet;
typedef flet <bv> bvflet;

template <typename U>
struct flet : public fexpr <U>
{
    typedef expr <U> eU;
    typedef fexpr <U> feU;
    typedef flet <U> this_t;
    typedef shared_ptr <const eU> eU_p;
    typedef shared_ptr <const feU> feU_p;

    flet(fsubst_t fbindings, feU_p fe)
    : fbindings(fbindings), fe(fe) {};

    virtual ostream& print(ostream& out) const
    {
        out << "(let ";
        print_args(out);
        out << " " << *fe << ")";
        return out;
    }

    virtual eU_p subst(const subst_t& subst) const
    {
        subst_t bs;
        for (auto& zvar : std::get <0> (fbindings)) {
            std::get <0> (bs)[zvar.first] = zvar.second -> subst(subst);
        }
        for (auto& bvar : std::get <1> (fbindings)) {
            std::get <1> (bs)[bvar.first] = bvar.second -> subst(subst);
        }
        for (auto& bvvar : std::get <2> (fbindings)) {
            std::get <2> (bs)[bvvar.first] = bvvar.second -> subst(subst);
        }
        eU_p fes(fe -> subst(subst));
        return eU_p(new let <U> (bs, fes));
    }

    virtual feU_p subst(const fsubst_t& fsubst) const
    {
        fsubst_t bp(fbindings), fsubstp(fsubst);
        for (auto& zvar : std::get <0> (fbindings)) {
            std::get <0> (bp)[zvar.first] = zvar.second -> subst(fsubst);
            std::get <0> (bp)[zvar.first] = afexpr_p(new fzvar(zvar.first));
        }
        for (auto& bvar : std::get <1> (fbindings)) {
            std::get <1> (bp)[bvar.first] = bvar.second -> subst(fsubst);
            std::get <1> (bp)[bvar.first] = bfexpr_p(new fbvar(bvar.first));
        }
        for (auto& bvvar : std::get <2> (fbindings)) {
            std::get <2> (bp)[bvvar.first] = bvvar.second -> subst(fsubst);
            std::get <2> (bp)[bvvar.first] = bvfexpr_p(new fbvvar(bvvar.first));
        }
        return feU_p(new this_t(bp, fe -> subst(fsubstp)));
    }

    virtual eU_p dsubst(const subst_t& subst) const
    {
        subst_t bs;
        for (auto& zvar : std::get <0> (fbindings)) {
            std::get <0> (bs)[zvar.first] = zvar.second -> dsubst(subst);
        }
        for (auto& bvar : std::get <1> (fbindings)) {
            std::get <1> (bs)[bvar.first] = bvar.second -> dsubst(subst);
        }
        for (auto& bvvar : std::get <2> (fbindings)) {
            std::get <2> (bs)[bvvar.first] = bvvar.second -> dsubst(subst);
        }
        eU_p fes(fe -> dsubst(subst));
        return eU_p(new let <U> (bs, fes));
    }

    virtual U eval(const subst_t& subst, const val_t& val, memo_t& memo) const
    {
        /* auto& U_memo = nonstd::get(memo.zmemo, memo.bmemo, memo.bvmemo, U());

        if (cs_elim_index && U_memo.find(*cs_elim_index) != U_memo.end()) {
            return U_memo.at(*cs_elim_index);
        } */

        val_t valp(val);
        for (auto& zvar : std::get <0> (fbindings)) {
            std::get <0> (valp)[zvar.first] = zvar.second -> eval(subst, val, memo);
        }
        for (auto& bvar : std::get <1> (fbindings)) {
            std::get <1> (valp)[bvar.first] = bvar.second -> eval(subst, val, memo);
        }
        for (auto& bvvar : std::get <2> (fbindings)) {
            std::get <2> (valp)[bvvar.first] = bvvar.second -> eval(subst, val, memo);
        }

        U ans = fe -> eval(subst, valp, memo);

        /* if (cs_elim_index) {
            U_memo[*cs_elim_index] = ans;
        } */

        return ans;
    }

    virtual void cs_elim(cs_elim_args_t& cs_elim_args) const {
        auto full_expr = this -> subst(fbindings) -> subst(cs_elim_args.fsubst);
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
        var_set ans = fe -> free_variables();
        var_set ansp;
        for (auto& zvar : std::get <0> (fbindings)) {
            std::get <0> (ans).erase(zvar.first);
            ansp = var_set_union(ansp, zvar.second -> free_variables());
        }
        for (auto& bvar : std::get <1> (fbindings)) {
            std::get <1> (ans).erase(bvar.first);
            ansp = var_set_union(ansp, bvar.second -> free_variables());
        }
        for (auto& bvvar : std::get <2> (fbindings)) {
            std::get <2> (ans).erase(bvvar.first);
            ansp = var_set_union(ansp, bvvar.second -> free_variables());
        }
        return var_set_union(ans, ansp);
    }

    virtual var_set bound_variables() const
    {
        var_set ans = fe -> bound_variables();
        for (auto& zvar : std::get <0> (fbindings)) {
            std::get <0> (ans).insert(zvar.first);
            ans = var_set_union(ans, zvar.second -> bound_variables());
        }
        for (auto& bvar : std::get <1> (fbindings)) {
            std::get <1> (ans).insert(bvar.first);
            ans = var_set_union(ans, bvar.second -> bound_variables());
        }
        for (auto& bvvar : std::get <2> (fbindings)) {
            std::get <2> (ans).insert(bvvar.first);
            ans = var_set_union(ans, bvvar.second -> bound_variables());
        }
        return ans;
    }

    virtual var_set abound_vars(id s, const var_set& all_vars) const
    {
        auto fe_abv = fe -> abound_vars(s, all_vars);
        var_set bind_abv = all_vars;
        for (auto& avar : std::get <0> (fbindings)) {
            std::get <0> (fe_abv).insert(avar.first);
            bind_abv = var_set_intersection(bind_abv,
                avar.second -> abound_vars(s, all_vars));
        }
        for (auto& bvar : std::get <1> (fbindings)) {
            std::get <1> (fe_abv).insert(bvar.first);
            bind_abv = var_set_intersection(bind_abv,
                bvar.second -> abound_vars(s, all_vars));
        }
        for (auto& bvvar : std::get <2> (fbindings)) {
            std::get <2> (fe_abv).insert(bvvar.first);
            bind_abv = var_set_intersection(bind_abv,
                bvvar.second -> abound_vars(s, all_vars));
        }
        return var_set_intersection(fe_abv, bind_abv);
    }

    virtual var_set bbound_vars(id s, const var_set& all_vars) const
    {
        auto fe_bbv = fe -> bbound_vars(s, all_vars);
        var_set bind_bbv = all_vars;
        for (auto& avar : std::get <0> (fbindings)) {
            std::get <0> (fe_bbv).insert(avar.first);
            bind_bbv = var_set_intersection(bind_bbv,
                avar.second -> bbound_vars(s, all_vars));
        }
        for (auto& bvar : std::get <1> (fbindings)) {
            std::get <1> (fe_bbv).insert(bvar.first);
            bind_bbv = var_set_intersection(bind_bbv,
                bvar.second -> bbound_vars(s, all_vars));
        }
        for (auto& bvvar : std::get <2> (fbindings)) {
            std::get <2> (fe_bbv).insert(bvvar.first);
            bind_bbv = var_set_intersection(bind_bbv,
                bvvar.second -> bbound_vars(s, all_vars));
        }
        return var_set_intersection(fe_bbv, bind_bbv);
    }

    virtual var_set bvbound_vars(id s, const var_set& all_vars) const
    {
        auto fe_bvbv = fe -> bvbound_vars(s, all_vars);
        var_set bind_bvbv = all_vars;
        for (auto& avar : std::get <0> (fbindings)) {
            std::get <0> (fe_bvbv).insert(avar.first);
            bind_bvbv = var_set_intersection(bind_bvbv,
                avar.second -> bvbound_vars(s, all_vars));
        }
        for (auto& bvar : std::get <1> (fbindings)) {
            std::get <1> (fe_bvbv).insert(bvar.first);
            bind_bvbv = var_set_intersection(bind_bvbv,
                bvar.second -> bvbound_vars(s, all_vars));
        }
        for (auto& bvvar : std::get <2> (fbindings)) {
            std::get <2> (fe_bvbv).insert(bvvar.first);
            bind_bvbv = var_set_intersection(bind_bvbv,
                bvvar.second -> bvbound_vars(s, all_vars));
        }
        return var_set_intersection(fe_bvbv, bind_bvbv);
    }

    virtual size_t bvlen() const
    {
        bool is_bv = std::is_same <U, bool>::value;
        assert(is_bv);
        return fe -> bvlen();
    }

    virtual size_t size() const
    {
        size_t ans = 1;
        for (auto& zvar : std::get <0> (fbindings)) {
            ans += zvar.second -> size();
        }
        for (auto& bvar : std::get <1> (fbindings)) {
            ans += bvar.second -> size();
        }
        for (auto& bvvar : std::get <2> (fbindings)) {
            ans += bvvar.second -> size();
        }
        ans += fe -> size();
        return ans;
    }

    virtual feU_p deep_copy() const
    {
        fsubst_t bc(fbindings);
        for (auto& zvar : std::get <0> (fbindings)) {
            const afsubst_t& afbindings = std::get <0> (fbindings);
            auto zfec = afbindings.at(zvar.first) -> deep_copy();
            std::get <0> (bc)[zvar.first] = zfec;
        }
        for (auto& bvar : std::get <1> (fbindings)) {
            const bfsubst_t& bfbindings = std::get <1> (fbindings);
            auto bfec = bfbindings.at(bvar.first) -> deep_copy();
            std::get <1> (bc)[bvar.first] = bfec;
        }
        for (auto& bvvar : std::get <2> (fbindings)) {
            const bvfsubst_t& bvfbindings = std::get <2> (fbindings);
            auto bvfec = bvfbindings.at(bvvar.first) -> deep_copy();
            std::get <2> (bc)[bvvar.first] = bvfec;
        }
        feU_p fec = fe -> deep_copy();
        return feU_p(new this_t(bc, fec));
    }

    fsubst_t fbindings;
    feU_p fe;
    mutable optional <size_t> cs_elim_index;

    private:

    void print_args(ostream& out) const
    {
        out << "(";
        for (auto& zvar : std::get <0> (fbindings)) {
            out << "(x" << zvar.first.v << " Int " << *zvar.second << ") ";
        }
        for (auto& bvar : std::get <1> (fbindings)) {
            out << "(b" << bvar.first.v << " Bool " << *bvar.second << ") ";
        }
        for (auto& bvvar : std::get <2> (fbindings)) {
            out << "(bv" << bvvar.first.v << " (BitVec " << bvvar.second -> bvlen()
                << ") " << *bvvar.second << ") ";
        }
        out << ")";
    }
};

} // namespace stoch

#endif // __FEXPR_ITE_HPP_
