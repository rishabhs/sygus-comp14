#ifndef __GRAMMAR_COMBINE_HPP_
#define __GRAMMAR_COMBINE_HPP_

#include "grammar.hpp"

namespace stoch {

template <typename U>
shared_ptr <prod_rule <U>> offset_prod_rule(shared_ptr <prod_rule <U>> rule,
    size_t zoff, size_t boff, size_t bvoff)
{
    typedef prod_rule <U> prod_rule_U;
    typedef shared_ptr <prod_rule_U> prod_rule_U_p;

    vector <agsymb_t> acvp(rule -> achild_v);
    vector <bgsymb_t> bcvp(rule -> bchild_v);
    vector <bvgsymb_t> bvcvp(rule -> bvchild_v);

    transform(acvp.begin(), acvp.end(), acvp.begin(),
        [=](const agsymb_t& symb) -> agsymb_t { return agsymb_t(symb.v + zoff); });
    transform(bcvp.begin(), bcvp.end(), bcvp.begin(),
        [=](const bgsymb_t& symb) -> bgsymb_t { return bgsymb_t(symb.v + boff); });
    transform(bvcvp.begin(), bvcvp.end(), bvcvp.begin(),
        [=](const bvgsymb_t& symb) -> bvgsymb_t { return bvgsymb_t(symb.v + bvoff, symb.len); });

    return prod_rule_U_p(new prod_rule_U(acvp, bcvp, bvcvp, rule -> expand));
}

template <typename U>
vector <shared_ptr <prod_rule <U>>> offset_prod_rules(
    const vector <shared_ptr <prod_rule <U>>>& rules,
    size_t zoff, size_t boff, size_t bvoff)
{
    vector <shared_ptr <prod_rule <U>>> ans;
    for (auto& rule : rules) {
        ans.push_back(offset_prod_rule(rule, zoff, boff, bvoff));
    }
    return ans;
}

void offset_grammar(grammar& gp, const grammar& g, size_t zoff, size_t boff, size_t bvoff)
{
    for (auto& symb_rules : g.arules) {
        auto& symb = symb_rules.first;
        auto& rules = symb_rules.second;
        gp.arules[agsymb_t(symb.v + zoff)] = offset_prod_rules(rules, zoff, boff, bvoff);
    }
    for (auto& symb_rules : g.brules) {
        auto& symb = symb_rules.first;
        auto& rules = symb_rules.second;
        gp.brules[bgsymb_t(symb.v + boff)] = offset_prod_rules(rules, zoff, boff, bvoff);
    }
    for (auto& symb_rules : g.bvrules) {
        auto& symb = symb_rules.first;
        auto& rules = symb_rules.second;
        gp.bvrules[bvgsymb_t(symb.v + bvoff, symb.len)] = offset_prod_rules(rules, zoff, boff, bvoff);
    }
}

tuple <grammar, agsymb_t, vector <id>, vector <id>, vector <id>>
    combine(const map <id, tuple <grammar, agsymb_t>>& afuns,
    const map <id, tuple <grammar, bgsymb_t>>& bfuns,
    const map <id, tuple <grammar, bvgsymb_t>>& bvfuns)
{
    grammar gp;
    vector <agsymb_t> achild_v;
    vector <bgsymb_t> bchild_v;
    vector <bvgsymb_t> bvchild_v;

    vector <id> afun_v, bfun_v, bvfun_v;

    size_t zoff = 0, boff = 0, bvoff = 0;

    for (auto& fun : afuns) {
        auto& fun_g = std::get <0> (fun.second);
        auto& fun_s = std::get <1> (fun.second);
        offset_grammar(gp, fun_g, zoff, boff, bvoff);
        achild_v.push_back(agsymb_t(fun_s.v + zoff));
        afun_v.push_back(fun.first);
        zoff = gp.arules.size();
        boff = gp.brules.size();
        bvoff = gp.bvrules.size();
    }

    for (auto& fun : bfuns) {
        auto& fun_g = std::get <0> (fun.second);
        auto& fun_s = std::get <1> (fun.second);
        offset_grammar(gp, fun_g, zoff, boff, bvoff);
        bchild_v.push_back(bgsymb_t(fun_s.v + boff));
        bfun_v.push_back(fun.first);
        zoff = gp.arules.size();
        boff = gp.brules.size();
        bvoff = gp.bvrules.size();
    }

    for (auto& fun : bvfuns) {
        auto& fun_g = std::get <0> (fun.second);
        auto& fun_s = std::get <1> (fun.second);
        offset_grammar(gp, fun_g, zoff, boff, bvoff);
        bvchild_v.push_back(bvgsymb_t(fun_s.v + bvoff, fun_s.len));
        bvfun_v.push_back(fun.first);
        zoff = gp.arules.size();
        boff = gp.brules.size();
        bvoff = gp.bvrules.size();
    }

    shared_ptr <aprod_rule> start_rule_p(new aprod_rule(achild_v, bchild_v,
        bvchild_v, afexpr_p(new fcz(0))));
    gp.arules[agsymb_t(zoff)].push_back(start_rule_p);

    return make_tuple(gp, agsymb_t(zoff), afun_v, bfun_v, bvfun_v);
}

subst_t uncombine(const aprodn& prodn, const vector <id>& afun_v,
    const vector <id>& bfun_v, const vector <id>& bvfun_v)
{
    subst_t ans;

    for (size_t i = 0; i < prodn.achild_v.size(); i++) {
        auto& afun = prodn.achild_v[i];
        std::get <0> (ans)[afun_v[i]] = afun -> produce();
    }

    for (size_t i = 0; i < prodn.bchild_v.size(); i++) {
        auto& bfun = prodn.bchild_v[i];
        std::get <1> (ans)[bfun_v[i]] = bfun -> produce();
    }

    for (size_t i = 0; i < prodn.bvchild_v.size(); i++) {
        auto& bvfun = prodn.bvchild_v[i];
        std::get <2> (ans)[bvfun_v[i]] = bvfun -> produce();
    }

    return ans;
}

} // namespace stoch

#endif // __GRAMMAR_COMBINE_HPP_

