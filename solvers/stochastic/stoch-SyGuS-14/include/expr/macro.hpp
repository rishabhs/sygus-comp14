#ifndef __EXPR_MACRO_HPP_
#define __EXPR_MACRO_HPP_

#include "expr.hpp"

namespace stoch {

template <typename U> struct macro;
typedef macro <z_class> zmacro;
typedef macro <bool> bmacro;
typedef macro <bv> bvmacro;

template <typename U> struct fmacro;

template <typename U>
struct macro : public expr <U>
{
    typedef expr <U> eU;
    typedef fexpr <U> feU;
    typedef macro <U> this_t;
    typedef shared_ptr <const eU> eU_p;
    typedef shared_ptr <const feU> feU_p;

    macro(const string& name, eU_p e, const subst_t& args)
    : name(name), e(e), es(e -> subst(args)), args(args) {};

    virtual ostream& print(ostream& out) const
    {
        out << "(" << name;
        for (size_t i = 0; i < subst_size(args); i++) {
            if (std::get <0> (args).find(i) != std::get <0> (args).end()) {
               out << " " << *std::get <0> (args).at(i);
            } else if (std::get <1> (args).find(i) != std::get <1> (args).end()) {
               out << " " << *std::get <1> (args).at(i);
            } else if (std::get <2> (args).find(i) != std::get <2> (args).end()) {
               out << " " << *std::get <2> (args).at(i);
            }
        }
        out << ")";
        return out;
    }

    virtual U eval(const val_t& val) const
    {
        return es -> eval(val);
    }

    virtual eU_p subst(const subst_t& subst) const
    {
        subst_t argsp;
        for (auto& arg : std::get <0> (args)) {
            std::get <0> (argsp)[arg.first] = arg.second -> subst(subst);
        }
        for (auto& arg : std::get <1> (args)) {
            std::get <1> (argsp)[arg.first] = arg.second -> subst(subst);
        }
        for (auto& arg : std::get <2> (args)) {
            std::get <2> (argsp)[arg.first] = arg.second -> subst(subst);
        }
        return eU_p(new macro(name, e, argsp));
    }

    virtual z3::expr smt(z3::context& ctxt) const
    {
        return es -> smt(ctxt);
    }

    virtual feU_p f_lift() const
    {
        fsubst_t fargs;
        for (auto& arg : std::get <0> (args)) {
            std::get <0> (fargs)[arg.first] = arg.second -> f_lift();
        }
        for (auto& arg : std::get <1> (args)) {
            std::get <1> (fargs)[arg.first] = arg.second -> f_lift();
        }
        for (auto& arg : std::get <2> (args)) {
            std::get <2> (fargs)[arg.first] = arg.second -> f_lift();
        }
        return feU_p(new fmacro <U> (name, e, fargs));
    }

    virtual size_t bvlen() const
    {
        bool is_bv = std::is_same <U, bool>::value;
        assert(is_bv);
        return e -> bvlen();
    }

    virtual size_t size() const
    {
        return es -> size();
    }

    virtual eU_p deep_copy() const
    {
        subst_t argsp;
        for (auto& arg : std::get <0> (args)) {
            std::get <0> (argsp)[arg.first] = arg.second -> deep_copy();
        }
        for (auto& arg : std::get <1> (args)) {
            std::get <1> (argsp)[arg.first] = arg.second -> deep_copy();
        }
        for (auto& arg : std::get <2> (args)) {
            std::get <2> (argsp)[arg.first] = arg.second -> deep_copy();
        }
        return eU_p(new this_t(name, e -> deep_copy(), argsp));
    }

    string name;
    eU_p e, es;
    subst_t args;
};

} // namespace stoch

#endif // __EXPR_MACRO_HPP_

