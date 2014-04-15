#ifndef __FEXPR_CALL_HPP_
#define __FEXPR_CALL_HPP_

#include "fexpr.hpp"

namespace stoch {

template <typename U> struct fcall;
typedef fcall <z_class> fzcall;
typedef fcall <bool> fbcall;
typedef fcall <bv> fbvcall;

template <typename U>
struct fcall : public fexpr <U>
{
    typedef expr <U> eU;
    typedef fexpr <U> feU;
    typedef fcall <U> this_t;
    typedef shared_ptr <const eU> eU_p;
    typedef shared_ptr <const feU> feU_p;

    typedef vector <afexpr_p> zargs_v_t;
    typedef vector <bfexpr_p> bargs_v_t;
    typedef vector <bvfexpr_p> bvargs_v_t;

    fcall(const id& x) : x(x), len(1)
    {
        bool is_bv = std::is_same <U, bv>::value;
        assert(!is_bv);
    }

    fcall(const id& x, size_t len) : x(x), len(len)
    {
        bool is_bv = std::is_same <U, bv>::value;
        assert(is_bv);
        if (len == 0) {
            throw std::underflow_error("Bit-vectors cannot be of length 0.");
        }
    }

    fcall(const id& x, const zargs_v_t& zargs, const bargs_v_t& bargs,
        const bvargs_v_t& bvargs)
        : x(x), zargs(zargs), bargs(bargs), bvargs(bvargs), len(1)
    {
        bool is_bv = std::is_same <U, bv>::value;
        assert(!is_bv);
    }

    fcall(const id& x, const zargs_v_t& zargs, const bargs_v_t& bargs,
        const bvargs_v_t& bvargs, size_t len)
        : x(x), zargs(zargs), bargs(bargs), bvargs(bvargs), len(len)
    {
        bool is_bv = std::is_same <U, bv>::value;
        assert(is_bv);
        if (len == 0) {
            throw std::underflow_error("Bit-vectors cannot be of length 0.");
        }
    }

    virtual ostream& print(ostream& out) const
    {
        out << "(f" << nonstd::get("z", "b", "bv", U()) << x.v;
        for (size_t i = 0; i < zargs.size(); i++) {
            out << " " << *zargs[i];
        }
        for (size_t i = 0; i < bargs.size(); i++) {
            out << " " << *bargs[i];
        }
        for (size_t i = 0; i < bvargs.size(); i++) {
            out << " " << *bvargs[i];
        }
        return out << ")";
    }

    virtual eU_p subst(const subst_t& subst) const
    {
        asubst_t zargs_s;
        for (size_t i = 0; i < zargs.size(); i++) {
            zargs_s[i] = zargs[i] -> subst(subst);
        }

        bsubst_t bargs_s;
        for (size_t i = 0; i < bargs.size(); i++) {
            bargs_s[i] = bargs[i] -> subst(subst);
        }

        bvsubst_t bvargs_s;
        for (size_t i = 0; i < bvargs.size(); i++) {
            bvargs_s[i] = bvargs[i] -> subst(subst);
        }

        subst_t args_s(zargs_s, bargs_s, bvargs_s);

        const asubst_t& asubst = std::get <0> (subst);
        const bsubst_t& bsubst = std::get <1> (subst);
        const bvsubst_t& bvsubst = std::get <2> (subst);

        return nonstd::get(asubst, bsubst, bvsubst, U()).at(x) -> subst(args_s);
    }

    virtual feU_p subst(const fsubst_t& fsubst) const
    {
        vector <afexpr_p> zargs_s(zargs);
        vector <bfexpr_p> bargs_s(bargs);
        vector <bvfexpr_p> bvargs_s(bvargs);

        transform(zargs.begin(), zargs.end(), zargs_s.begin(),
            [&](const afexpr_p& fe) -> afexpr_p {
                return fe -> subst(fsubst);
            });
        transform(bargs.begin(), bargs.end(), bargs_s.begin(),
            [&](const bfexpr_p& fe) -> bfexpr_p {
                return fe -> subst(fsubst);
            });
        transform(bvargs.begin(), bvargs.end(), bvargs_s.begin(),
            [&](const bvfexpr_p& fe) -> bvfexpr_p {
                return fe -> subst(fsubst);
            });

        return feU_p(new fcall <U> (x, zargs_s, bargs_s, bvargs_s));
    }

    virtual eU_p dsubst(const subst_t& subst) const
    {
        auto& asubst = std::get <0> (subst);
        auto& bsubst = std::get <1> (subst);
        auto& bvsubst = std::get <2> (subst);
        return nonstd::get(asubst, bsubst, bvsubst, U()).at(x);
    }

    virtual U eval(const subst_t& subst, const val_t& val, memo_t& memo) const
    {
        auto& U_memo = nonstd::get(memo.zmemo, memo.bmemo, memo.bvmemo, U());

        if (cs_elim_index && U_memo.find(*cs_elim_index) != U_memo.end()) {
            return U_memo.at(*cs_elim_index);
        }

        aval_t zargs_s;
        for (size_t i = 0; i < zargs.size(); i++) {
            zargs_s[i] = zargs[i] -> eval(subst, val, memo);
        }

        bval_t bargs_s;
        for (size_t i = 0; i < bargs.size(); i++) {
            bargs_s[i] = bargs[i] -> eval(subst, val, memo);
        }

        bvval_t bvargs_s;
        for (size_t i = 0; i < bvargs.size(); i++) {
            bvargs_s[i] = bvargs[i] -> eval(subst, val, memo);
        }

        val_t args_s(zargs_s, bargs_s, bvargs_s);

        const asubst_t& asubst = std::get <0> (subst);
        const bsubst_t& bsubst = std::get <1> (subst);
        const bvsubst_t& bvsubst = std::get <2> (subst);

        U ans = nonstd::get(asubst, bsubst, bvsubst, U()).at(x) -> eval(args_s);

        if (cs_elim_index) {
            U_memo[*cs_elim_index] = ans;
        }

        return ans;
    }

    virtual void cs_elim(cs_elim_args_t& cs_elim_args) const {
        for (auto& e : zargs) {
            e -> cs_elim(cs_elim_args);
        }
        for (auto& e : bargs) {
            e -> cs_elim(cs_elim_args);
        }
        for (auto& e : bvargs) {
            e -> cs_elim(cs_elim_args);
        }

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
        return var_set();
    }

    virtual var_set bound_variables() const
    {
        return var_set();
    }

    virtual var_set abound_vars(id s, const var_set& all_vars) const
    {
        if (nonstd::vget(true, false, false, U()) && s.v == x.v) {
            return var_set();
        } else {
            return all_vars;
        }
    }

    virtual var_set bbound_vars(id s, const var_set& all_vars) const
    {
        if (nonstd::vget(false, true, false, U()) && s.v == x.v) {
            return var_set();
        } else {
            return all_vars;
        }
    }

    virtual var_set bvbound_vars(id s, const var_set& all_vars) const
    {
        if (nonstd::vget(false, false, true, U()) && s.v == x.v) {
            return var_set();
        } else {
            return all_vars;
        }
    }

    virtual size_t bvlen() const
    {
        bool is_bv = std::is_same <U, bv>::value;
        assert(is_bv);
        return len;
    }

    virtual size_t size() const {
        vector <size_t> zargs_s(zargs.size());
        vector <size_t> bargs_s(bargs.size());
        vector <size_t> bvargs_s(bvargs.size());

        transform(zargs.begin(), zargs.end(), zargs_s.begin(),
            [](const afexpr_p& e) {
                return e -> size();
            });
        transform(bargs.begin(), bargs.end(), bargs_s.begin(),
            [](const bfexpr_p& e) {
                return e -> size();
            });
        transform(bvargs.begin(), bvargs.end(), bvargs_s.begin(),
            [](const bvfexpr_p& e) {
                return e -> size();
            });

        size_t ans = accumulate(zargs_s.begin(), zargs_s.end(), 1);
        ans = accumulate(bargs_s.begin(), bargs_s.end(), ans);
        ans = accumulate(bvargs_s.begin(), bvargs_s.end(), ans);
        return ans;
    }

    virtual feU_p deep_copy() const {
        return feU_p(new this_t(x, zargs, bargs, bvargs));
    }

    id x;
    zargs_v_t zargs;
    bargs_v_t bargs;
    bvargs_v_t bvargs;
    size_t len;
    mutable optional <size_t> cs_elim_index;
};

}

#endif // __FEXPR_VAR_HPP_

