#ifndef __GRAMMAR_UNROLL_HPP_
#define __GRAMMAR_UNROLL_HPP_

#include "grammar.hpp"

namespace stoch {

// Declarations

grammar unroll(const grammar& g, const var_set& scope);

var_set all_bound_variables(const grammar& g);

// Implementation

grammar unroll(const grammar& g, const var_set& scope)
{
    grammar::arules_t ap;
    grammar::brules_t bp;
    grammar::bvrules_t bvp;

    var_set vset = var_set_union(all_bound_variables(g), scope);
    set <set_id> apset(nonstd::powerset(std::get <0> (vset)));
    set <set_id> bpset(nonstd::powerset(std::get <1> (vset)));
    set <set_id> bvpset(nonstd::powerset(std::get <2> (vset)));
    set <var_set> pset = nonstd::cart(apset, bpset, bvpset);

    auto nonterminals = g.nonterm_set();
    set <agsymb_t> ant = std::get <0> (nonterminals);
    set <bgsymb_t> bnt = std::get <1> (nonterminals);
    set <bvgsymb_t> bvnt = std::get <2> (nonterminals);

    map <tuple <agsymb_t, var_set>, agsymb_t> antp;
    map <tuple <bgsymb_t, var_set>, bgsymb_t> bntp;
    map <tuple <bvgsymb_t, var_set>, bvgsymb_t> bvntp;

    for (auto& agsymb : nonstd::cart(ant, pset)) {
        auto symb = agsymb_t(antp.size());
        antp[agsymb] = symb;
    }
    for (auto& bgsymb : nonstd::cart(bnt, pset)) {
        auto symb = bgsymb_t(bntp.size());
        bntp[bgsymb] = symb;
    }
    for (auto& bvgsymb : nonstd::cart(bvnt, pset)) {
        auto symb = bvgsymb_t(bvntp.size(), std::get <0> (bvgsymb).len);
        // bvntp[bvgsymb] = symb;
        bvntp.insert(pair <tuple <bvgsymb_t, var_set>, bvgsymb_t> (bvgsymb, symb));
    }

    for (auto& agsymb : nonstd::cart(ant, pset)) {
        auto prebound_vars = var_set_union(std::get <1> (agsymb), scope);
        ap[antp[agsymb]].clear();
        for (auto& rule : g.arules.at(std::get <0> (agsymb))) {
            if (var_set_subset(rule -> expand -> free_variables(), prebound_vars)) {
                // auto rulep = rule -> unroll(antp, bntp, bvntp, std::get <1> (agsymb));
                auto rulep = rule -> unroll(antp, bntp, bvntp, vset, prebound_vars);
                ap[antp[agsymb]].push_back(rulep);
            }
        }
    }

    for (auto& bgsymb : nonstd::cart(bnt, pset)) {
        auto prebound_vars = var_set_union(std::get <1> (bgsymb), scope);
        bp[bntp[bgsymb]].clear();
        for (auto& rule : g.brules.at(std::get <0> (bgsymb))) {
            if (var_set_subset(rule -> expand -> free_variables(), prebound_vars)) {
                // auto rulep = rule -> unroll(antp, bntp, bvntp, std::get <1> (bgsymb));
                auto rulep = rule -> unroll(antp, bntp, bvntp, vset, std::get <1> (bgsymb));
                bp[bntp[bgsymb]].push_back(rulep);
            }
        }
    }

    for (auto& bvgsymb : nonstd::cart(bvnt, pset)) {
        auto prebound_vars = var_set_union(std::get <1> (bvgsymb), scope);
        bvp[bvntp[bvgsymb]].clear();
        for (auto& rule : g.bvrules.at(std::get <0> (bvgsymb))) {
            if (var_set_subset(rule -> expand -> free_variables(), prebound_vars)) {
                // auto rulep = rule -> unroll(antp, bntp, bvntp, std::get <1> (bvgsymb));
                auto rulep = rule -> unroll(antp, bntp, bvntp, vset, std::get <1> (bvgsymb));
                bvp[bvntp[bvgsymb]].push_back(rulep);
            }
        }
    }

    if (auto start = boost::get <agsymb_t> (&g.start)) {
        auto startp = antp.at(make_tuple(*start, scope));
        return grammar(ap, bp, bvp, startp);
    } else if (auto start = boost::get <bgsymb_t> (&g.start)) {
        auto startp = bntp.at(make_tuple(*start, scope));
        return grammar(ap, bp, bvp, startp);
    } else if (auto start = boost::get <bvgsymb_t> (&g.start)) {
        auto startp = bvntp.at(make_tuple(*start, scope));
        return grammar(ap, bp, bvp, startp);
    } else {
        assert (false);
    }

    /* auto startp = nonstd::get(antp, bntp, bvntp, U()).at(make_tuple(start, scope));
    return grammar(ap, bp, bvp, startp); */
}

var_set all_bound_variables(const grammar& g)
{
    var_set s;

    for (auto& symb : g.arules) {
        for (auto& rule : symb.second) {
            var_set sp = rule -> expand -> bound_variables();
            s = var_set_union(s, sp);
        }
    }

    for (auto& symb : g.brules) {
        for (auto& rule : symb.second) {
            var_set sp = rule -> expand -> bound_variables();
            s = var_set_union(s, sp);
        }
    }

    for (auto& symb : g.bvrules) {
        for (auto& rule : symb.second) {
            var_set sp = rule -> expand -> bound_variables();
            s = var_set_union(s, sp);
        }
    }

    return s;
}

} // namespace stoch

#endif // __GRAMMAR_UNROLL_HPP_

