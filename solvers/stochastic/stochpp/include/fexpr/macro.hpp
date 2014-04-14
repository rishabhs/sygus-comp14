#ifndef __FEXPR_MACRO_HPP_
#define __FEXPR_MACRO_HPP_

#include "fexpr.hpp"

namespace stoch {

template <typename U> struct fmacro;
typedef fmacro <z_class> afmacro;
typedef fmacro <bool> bfmacro;
typedef fmacro <bv> bvfmacro;

template <typename U>
struct fmacro : public fexpr <U>
{
    typedef expr <U> eU;
    typedef fexpr <U> feU;
    typedef fmacro <U> this_t;
    typedef shared_ptr <const eU> eU_p;
    typedef shared_ptr <const feU> feU_p;

    fmacro(const string& name, eU_p e, const fsubst_t& fargs)
    : name(name), e(e), fes(e -> f_lift() -> subst(fargs)), fargs(fargs) {};

    virtual ostream& print(ostream& out) const
    {
        out << "(" << name;
        for (size_t i = 0; i < fsubst_size(fargs); i++) {
            if (std::get <0> (fargs).find(i) != std::get <0> (fargs).end()) {
               out << " " << *std::get <0> (fargs).at(i);
            } else if (std::get <1> (fargs).find(i) != std::get <1> (fargs).end()) {
               out << " " << *std::get <1> (fargs).at(i);
            } else if (std::get <2> (fargs).find(i) != std::get <2> (fargs).end()) {
               out << " " << *std::get <2> (fargs).at(i);
            }
        }
        out << ")";
        return out;
    }

    virtual eU_p subst(const subst_t& subst) const
    {
        subst_t args;
        for (auto& zvar : std::get <0> (fargs)) {
            std::get <0> (args)[zvar.first] = zvar.second -> subst(subst);
        }
        for (auto& bvar : std::get <1> (fargs)) {
            std::get <1> (args)[bvar.first] = bvar.second -> subst(subst);
        }
        for (auto& bvvar : std::get <2> (fargs)) {
            std::get <2> (args)[bvvar.first] = bvvar.second -> subst(subst);
        }
        return eU_p(new macro <U> (name, e, args));
    }

    virtual feU_p subst(const fsubst_t& fsubst) const
    {
        fsubst_t fargsp;
        for (auto& zvar : std::get <0> (fargs)) {
            std::get <0> (fargsp)[zvar.first] = zvar.second -> subst(fsubst);
        }
        for (auto& bvar : std::get <1> (fargs)) {
            std::get <1> (fargsp)[bvar.first] = bvar.second -> subst(fsubst);
        }
        for (auto& bvvar : std::get <2> (fargs)) {
            std::get <2> (fargsp)[bvvar.first] = bvvar.second -> subst(fsubst);
        }
        return feU_p(new this_t(name, e, fargsp));
    }

    virtual eU_p dsubst(const subst_t& subst) const
    {
        subst_t argsp;
        for (auto& zvar : std::get <0> (fargs)) {
            std::get <0> (argsp)[zvar.first] = zvar.second -> dsubst(subst);
        }
        for (auto& bvar : std::get <1> (fargs)) {
            std::get <1> (argsp)[bvar.first] = bvar.second -> dsubst(subst);
        }
        for (auto& bvvar : std::get <2> (fargs)) {
            std::get <2> (argsp)[bvvar.first] = bvvar.second -> dsubst(subst);
        }
        return eU_p(new macro <U> (name, e, argsp));
    }

    virtual U eval(const subst_t& subst, const val_t& val, memo_t& memo) const
    {
        return fes -> eval(subst, val, memo);
    }

    virtual void cs_elim(cs_elim_args_t& cs_elim_args) const {
        fes -> cs_elim(cs_elim_args);
    }

    virtual var_set free_variables() const
    {
        return fes -> free_variables();
    }

    virtual var_set bound_variables() const
    {
        var_set ans;
        for (auto& zvar : std::get <0> (fargs)) {
            ans = var_set_union(ans, zvar.second -> bound_variables());
        }
        for (auto& bvar : std::get <1> (fargs)) {
            ans = var_set_union(ans, bvar.second -> bound_variables());
        }
        for (auto& bvvar : std::get <2> (fargs)) {
            ans = var_set_union(ans, bvvar.second -> bound_variables());
        }
        return ans;
    }

    virtual var_set abound_vars(id s, const var_set& all_vars) const
    {
        var_set ans = all_vars;
        for (auto& avar : std::get <0> (fargs)) {
            ans = var_set_intersection(ans, avar.second -> abound_vars(s, all_vars));
        }
        for (auto& bvar : std::get <1> (fargs)) {
            ans = var_set_intersection(ans, bvar.second -> abound_vars(s, all_vars));
        }
        for (auto& bvvar : std::get <2> (fargs)) {
            ans = var_set_intersection(ans, bvvar.second -> abound_vars(s, all_vars));
        }
        return ans;
    }

    virtual var_set bbound_vars(id s, const var_set& all_vars) const
    {
        var_set ans = all_vars;
        for (auto& avar : std::get <0> (fargs)) {
            ans = var_set_intersection(ans, avar.second -> bbound_vars(s, all_vars));
        }
        for (auto& bvar : std::get <1> (fargs)) {
            ans = var_set_intersection(ans, bvar.second -> bbound_vars(s, all_vars));
        }
        for (auto& bvvar : std::get <2> (fargs)) {
            ans = var_set_intersection(ans, bvvar.second -> bbound_vars(s, all_vars));
        }
        return ans;
    }

    virtual var_set bvbound_vars(id s, const var_set& all_vars) const
    {
        var_set ans = all_vars;
        for (auto& avar : std::get <0> (fargs)) {
            ans = var_set_intersection(ans, avar.second -> bvbound_vars(s, all_vars));
        }
        for (auto& bvar : std::get <1> (fargs)) {
            ans = var_set_intersection(ans, bvar.second -> bvbound_vars(s, all_vars));
        }
        for (auto& bvvar : std::get <2> (fargs)) {
            ans = var_set_intersection(ans, bvvar.second -> bvbound_vars(s, all_vars));
        }
        return ans;
    }

    virtual size_t bvlen() const
    {
        bool is_bv = std::is_same <U, bool>::value;
        assert(is_bv);
        return fes -> bvlen();
    }

    virtual size_t size() const
    {
        return fes -> size();
    }

    virtual feU_p deep_copy() const
    {
        fsubst_t fargsp(fargs);
        for (auto& zvar : std::get <0> (fargs)) {
            std::get <0> (fargsp)[zvar.first] = zvar.second -> deep_copy();
        }
        for (auto& bvar : std::get <1> (fargs)) {
            std::get <1> (fargsp)[bvar.first] = bvar.second -> deep_copy();
        }
        for (auto& bvvar : std::get <2> (fargs)) {
            std::get <2> (fargsp)[bvvar.first] = bvvar.second -> deep_copy();
        }
        return feU_p(new this_t(name, e -> deep_copy(), fargsp));
    }

    string name;
    eU_p e;
    feU_p fes;
    fsubst_t fargs;
    mutable optional <size_t> cs_elim_index;
};

} // namespace stoch

#endif // __FEXPR_MACRO_HPP_

