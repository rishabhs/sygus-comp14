#ifndef __EXPR_LET_HPP_
#define __EXPR_LET_HPP_

#include "expr.hpp"

namespace stoch {

template <typename U> struct let;
typedef let <z_class> zlet;
typedef let <bool> blet;
typedef let <bv> bvlet;

template <typename U> struct flet;

template <typename U>
struct let : public expr <U>
{
    typedef expr <U> eU;
    typedef fexpr <U> feU;
    typedef let <U> this_t;
    typedef shared_ptr <const eU> eU_p;
    typedef shared_ptr <const feU> feU_p;

    let(const subst_t& bindings, eU_p e) : bindings(bindings), e(e) {};

    virtual ostream& print(ostream& out) const
    {
        out << "(let ";
        print_args(out);
        out << " " << *e << ")";
        return out;
    }

    virtual U eval(const val_t& val) const
    {
        val_t valp(val);
        for (auto& zvar : std::get <0> (bindings)) {
            std::get <0> (valp)[zvar.first] = zvar.second -> eval(val);
        }
        for (auto& bvar : std::get <1> (bindings)) {
            std::get <1> (valp)[bvar.first] = bvar.second -> eval(val);
        }
        for (auto& bvvar : std::get <2> (bindings)) {
            std::get <2> (valp)[bvvar.first] = bvvar.second -> eval(val);
        }
        return e -> eval(valp);
    }

    virtual eU_p subst(const subst_t& subst) const
    {
        subst_t bp(bindings);
        subst_t substp(subst);
        for (auto& var : std::get <0> (bindings)) {
            std::get <0> (bp)[var.first] = var.second -> subst(subst);
            std::get <0> (substp)[var.first] = aexpr_p(new zvar(var.first));
        }
        for (auto& var : std::get <1> (bindings)) {
            std::get <1> (bp)[var.first] = var.second -> subst(subst);
            std::get <1> (substp)[var.first] = bexpr_p(new bvar(var.first));
        }
        for (auto& var : std::get <2> (bindings)) {
            std::get <2> (bp)[var.first] = var.second -> subst(subst);
            std::get <2> (substp)[var.first] = bvexpr_p(new bvvar(var.first, var.second -> bvlen()));
        }

        return eU_p(new this_t(bp, e -> subst(substp)));
    }

    virtual z3::expr smt(z3::context& ctxt) const
    {
        // TODO. The following is the stupidest thing that could possibly work.
        return e -> subst(bindings) -> smt(ctxt);
    }

    virtual feU_p f_lift() const
    {
        fsubst_t fb;
        for (auto& zvar : std::get <0> (bindings)) {
            std::get <0> (fb)[zvar.first] = zvar.second -> f_lift();
        }
        for (auto& bvar : std::get <1> (bindings)) {
            std::get <1> (fb)[bvar.first] = bvar.second -> f_lift();
        }
        for (auto& bvvar : std::get <2> (bindings)) {
            std::get <2> (fb)[bvvar.first] = bvvar.second -> f_lift();
        }
        return feU_p(new flet <U> (fb, e -> f_lift()));
    }

    virtual size_t bvlen() const
    {
        bool is_bv = std::is_same <U, bool>::value;
        assert(is_bv);
        return e -> bvlen();
    }

    virtual size_t size() const
    {
        size_t ans = 1;
        for (auto& zvar : std::get <0> (bindings)) {
            ans += zvar.second -> size();
        }
        for (auto& bvar : std::get <1> (bindings)) {
            ans += bvar.second -> size();
        }
        for (auto& bvvar : std::get <2> (bindings)) {
            ans += bvvar.second -> size();
        }
        ans += e -> size();
        return ans;
    }

    virtual eU_p deep_copy() const
    {
        subst_t bp(bindings);
        for (auto& zvar : std::get <0> (bindings)) {
            std::get <0> (bp)[zvar.first] = zvar.second -> deep_copy();
        }
        for (auto& bvar : std::get <1> (bindings)) {
            std::get <1> (bp)[bvar.first] = bvar.second -> deep_copy();
        }
        for (auto& bvvar : std::get <2> (bindings)) {
            std::get <2> (bp)[bvvar.first] = bvvar.second -> deep_copy();
        }
        eU_p ec(e -> deep_copy());
        return eU_p(new this_t(bp, ec));
    }

    subst_t bindings;
    eU_p e;

    private:

    void print_args(ostream& out) const
    {
        out << "(";
        for (auto& zvar : std::get <0> (bindings)) {
            out << "(x" << zvar.first.v << " Int " << *zvar.second << ") ";
        }
        for (auto& bvar : std::get <1> (bindings)) {
            out << "(b" << bvar.first.v << " Bool " << *bvar.second << ") ";
        }
        for (auto& bvvar : std::get <2> (bindings)) {
            out << "(bv" << bvvar.first.v << " (BitVec " << bvvar.second -> bvlen()
                << ") " << *bvvar.second << ") ";
        }
        out << ")";
    }
};

} // namespace stoch

#endif // __EXPR_LET_HPP_

