#ifndef __GRAMMAR_HPP_
#define __GRAMMAR_HPP_

#include "nonstd.hpp"
#include "base.hpp"
#include "expr.hpp"
#include "fexpr.hpp"

namespace stoch {

template <typename U> struct prod_rule
{
    typedef fexpr <U> feU;
    typedef prod_rule <U> this_t;
    typedef shared_ptr <const feU> feU_p;
    typedef shared_ptr <this_t> this_t_p;

    prod_rule() {};
    prod_rule(const vector <agsymb_t>& achild_v, const vector <bgsymb_t>& bchild_v,
        const vector <bvgsymb_t>& bvchild_v, const feU_p& expand)
        : achild_v(achild_v), bchild_v(bchild_v), bvchild_v(bvchild_v),
        expand(expand) {};
    prod_rule(const feU_p& expand) : expand(expand) {};

    this_t_p unroll(const map <tuple <agsymb_t, var_set>, agsymb_t>& antp,
        const map <tuple <bgsymb_t, var_set>, bgsymb_t>& bntp,
        const map <tuple <bvgsymb_t, var_set>, bvgsymb_t>& bvntp,
        const var_set& all_vars, const var_set& prebound_vars) const
    {
        vector <agsymb_t> acvp;
        vector <bgsymb_t> bcvp;
        vector <bvgsymb_t> bvcvp;

        for (size_t i = 0; i < achild_v.size(); i++) {
            var_set aci_bvars = expand -> abound_vars(i, all_vars);
            aci_bvars = var_set_union(aci_bvars, prebound_vars);
            acvp.push_back(antp.at(make_tuple(achild_v[i], aci_bvars)));
        }

        for (size_t i = 0; i < bchild_v.size(); i++) {
            var_set bci_bvars = expand -> bbound_vars(i, all_vars);
            bci_bvars = var_set_union(bci_bvars, prebound_vars);
            bcvp.push_back(bntp.at(make_tuple(bchild_v[i], bci_bvars)));
        }

        for (size_t i = 0; i < bvchild_v.size(); i++) {
            var_set bvci_bvars = expand -> bvbound_vars(i, all_vars);
            bvci_bvars = var_set_union(bvci_bvars, prebound_vars);
            bvcvp.push_back(bvntp.at(make_tuple(bvchild_v[i], bvci_bvars)));
        }

        return this_t_p(new prod_rule(acvp, bcvp, bvcvp, expand));
    }

    ostream& print(ostream& out) const
    {
        out << *expand << ". ";
        for (auto& agsymb : achild_v) {
            out << "a" << agsymb.v << " ";
        }
        out << ". ";
        for (auto& bgsymb : bchild_v) {
            out << "b" << bgsymb.v << " ";
        }
        out << ". ";
        for (auto& bvgsymb : bvchild_v) {
            out << "bv" << bvgsymb.v << " ";
        }
        return out << ".";
    }

    vector <agsymb_t> achild_v;
    vector <bgsymb_t> bchild_v;
    vector <bvgsymb_t> bvchild_v;
    feU_p expand;
};

template <typename U, typename T>
prod_rule <U>& operator<<(prod_rule <U>& p, const gsymb_t <T>& s)
{
    auto& v = nonstd::get(p.achild_v, p.bchild_v, p.bvchild_v, T());
    v.push_back(s);
    return p;
}

template <typename U> struct production
{
    typedef expr <U> eU;
    typedef prod_rule <U> prod_ruleU;
    typedef production <U> prdnU;

    typedef shared_ptr <const eU> eU_p;
    typedef shared_ptr <const prod_ruleU> prod_ruleU_p;
    typedef shared_ptr <const prdnU> prdnU_p;

    production(const gsymb_t <U>& s, prod_ruleU_p rule, const vector <aprodn_p>& achild_v,
        const vector <bprodn_p>& bchild_v, const vector <bvprodn_p>& bvchild_v)
        : s(s), rule(rule), achild_v(achild_v), bchild_v(bchild_v), bvchild_v(bvchild_v) {}

    eU_p produce() const
    {
        if (expr_memo) {
            return expr_memo;
        }

        subst_t children;
        for (size_t i = 0; i < achild_v.size(); i++) {
            std::get <0> (children)[i] = achild_v[i] -> produce();
        }
        for (size_t i = 0; i < bchild_v.size(); i++) {
            std::get <1> (children)[i] = bchild_v[i] -> produce();
        }
        for (size_t i = 0; i < bvchild_v.size(); i++) {
            std::get <2> (children)[i] = bvchild_v[i] -> produce();
        }

        expr_memo = rule -> expand -> dsubst(children);
        return rule -> expand -> dsubst(children);
    }

    size_t size() const
    {
        if (prod_size) {
            return *prod_size;
        }

        size_t ans = 1;
        ans = accumulate(achild_v.begin(), achild_v.end(), ans,
            [&](size_t z, const aprodn_p& p) -> size_t {
                return z + p -> size();
            });
        ans = accumulate(bchild_v.begin(), bchild_v.end(), ans,
            [&](size_t z, const bprodn_p& p) -> size_t {
                return z + p -> size();
            });
        ans = accumulate(bvchild_v.begin(), bvchild_v.end(), ans,
            [&](size_t z, const bvprodn_p& p) -> size_t {
                return z + p -> size();
            });

        prod_size = ans;
        return ans;
    }

    gsymb_t <U> s;
    prod_ruleU_p rule;
    vector <aprodn_p> achild_v;
    vector <bprodn_p> bchild_v;
    vector <bvprodn_p> bvchild_v;

    mutable boost::optional <size_t> prod_size;
    mutable eU_p expr_memo;
};

struct grammar
{
    typedef map <agsymb_t, vector <aprod_rule_p>> arules_t;
    typedef map <bgsymb_t, vector <bprod_rule_p>> brules_t;
    typedef map <bvgsymb_t, vector <bvprod_rule_p>> bvrules_t;

    grammar() {};

    grammar(const arules_t& arules, const brules_t& brules, const bvrules_t& bvrules,
        const variant <agsymb_t, bgsymb_t, bvgsymb_t>& start)
        : arules(arules), brules(brules), bvrules(bvrules), start(start) {};

    tuple <set <agsymb_t>, set <bgsymb_t>, set <bvgsymb_t>> nonterm_set() const
    {
        set <agsymb_t> agsymb_s;
        set <bgsymb_t> bgsymb_s;
        set <bvgsymb_t> bvgsymb_s;

        for (auto& agsymb : arules) {
            agsymb_s.insert(agsymb.first);
        }
        for (auto& bgsymb : brules) {
            bgsymb_s.insert(bgsymb.first);
        }
        for (auto& bvgsymb : bvrules) {
            bvgsymb_s.insert(bvgsymb.first);
        }

        return make_tuple(agsymb_s, bgsymb_s, bvgsymb_s);
    }

    ostream& print(ostream& out) const
    {
        if (auto ps = boost::get <agsymb_t> (&start)) {
            out << "Start: a" << ps -> v << endl;
        } else if (auto ps = boost::get <bgsymb_t> (&start)) {
            out << "Start: b" << ps -> v << endl;
        } else if (auto ps = boost::get <bvgsymb_t> (&start)) {
            out << "Start: bv" << ps -> v << endl;
        }

        for (auto& gsymb : arules) {
            out << "a" << gsymb.first.v << " {" << endl;
            for (auto& rule : gsymb.second) {
                out << "a" << gsymb.first.v << " ::= ";
                rule -> print(out) << endl;
            }
            out << "} a" << gsymb.first.v << ";" << endl;
        }
        for (auto& gsymb : brules) {
            out << "b" << gsymb.first.v << " {" << endl;
            for (auto& rule : gsymb.second) {
                out << "b" << gsymb.first.v << " ::= ";
                rule -> print(out) << endl;
            }
            out << "} b" << gsymb.first.v << ";" << endl;
        }
        for (auto& gsymb : bvrules) {
            out << "bv" << gsymb.first.v << " {" << endl;
            for (auto& rule : gsymb.second) {
                out << "bv" << gsymb.first.v << " ::= ";
                rule -> print(out) << endl;
            }
            out << "} bv" << gsymb.first.v << ";" << endl;
        }
        return out;
    }

    arules_t arules;
    brules_t brules;
    bvrules_t bvrules;
    variant <agsymb_t, bgsymb_t, bvgsymb_t> start;
};

}

#include "grammar/std.hpp"
#include "grammar/sample.hpp"
#include "grammar/unroll.hpp"
#include "grammar/combine.hpp"

#endif // __GRAMMAR_HPP_

