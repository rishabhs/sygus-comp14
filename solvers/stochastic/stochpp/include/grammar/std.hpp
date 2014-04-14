#ifndef __GRAMMAR_STD_HPP_
#define __GRAMMAR_STD_HPP_

#include "grammar.hpp"

namespace stoch {

// Declarations

grammar lia(size_t n);
grammar plia(size_t nz, size_t nb, bool eq = false, bool inc = false, size_t nlet = 0);
grammar simple_bv_grammar(size_t nbv, size_t len);

// Implementation

grammar lia(size_t n)
{
    agsymb_t a(0);
    map <agsymb_t, vector <aprod_rule_p>> arules;
    map <bgsymb_t, vector <bprod_rule_p>> brules;
    map <bvgsymb_t, vector <bvprod_rule_p>> bvrules;

    // Non-terminal placeholders
    afexpr_p as0(new fzcall(0)), as1(new fzcall(1));
    bfexpr_p bs0(new fbcall(0)), bs1(new fbcall(1));

    // a ::= 0 | 1
    aprod_rule_p c0(new aprod_rule(afexpr_p(new fcz(0))));
    arules[a].push_back(c0);
    aprod_rule_p c1(new aprod_rule(afexpr_p(new fcz(1))));
    arules[a].push_back(c1);

    // a ::= xi, 0 <= i < n
    for (size_t i = 0; i < n; i++) {
        aprod_rule_p xi(new aprod_rule(afexpr_p(new fzvar(i))));
        arules[a].push_back(xi);
    }

    // a ::= a1 +/- a2
    aprod_rule_p a1pa2(new aprod_rule(as0 + as1));
    *a1pa2 << a << a;
    arules[a].push_back(a1pa2);
    aprod_rule_p a1ma2(new aprod_rule(as0 - as1));
    *a1ma2 << a << a;
    arules[a].push_back(a1ma2);

    return grammar(arules, brules, bvrules, a);
}

grammar plia(size_t nz, size_t nb, bool eq, bool inc, size_t nlet)
{
    agsymb_t a(0);
    bgsymb_t b(0);
    map <agsymb_t, vector <aprod_rule_p>> arules;
    map <bgsymb_t, vector <bprod_rule_p>> brules;
    map <bvgsymb_t, vector <bvprod_rule_p>> bvrules;

    // Non-terminal placeholders
    afexpr_p as0(new fzcall(0)), as1(new fzcall(1));
    bfexpr_p bs0(new fbcall(0)), bs1(new fbcall(1));

    // a ::= 0 | 1
    aprod_rule_p c0(new aprod_rule(afexpr_p(new fcz(0))));
    arules[a].push_back(c0);
    aprod_rule_p c1(new aprod_rule(afexpr_p(new fcz(1))));
    arules[a].push_back(c1);

    // a ::= xi, 0 <= i < nz
    for (size_t i = 0; i < nz; i++) {
        aprod_rule_p xi(new aprod_rule(afexpr_p(new fzvar(i))));
        arules[a].push_back(xi);
    }

    // a ::= a1 +/- a2
    aprod_rule_p a1pa2(new aprod_rule(as0 + as1));
    *a1pa2 << a << a;
    arules[a].push_back(a1pa2);
    aprod_rule_p a1ma2(new aprod_rule(as0 - as1));
    *a1ma2 << a << a;
    arules[a].push_back(a1ma2);

    // a ::= b ? a1 : a2
    aprod_rule_p aite(new aprod_rule(afexpr_p(new afite(bs0, as0, as1))));
    *aite << b << a << a;
    arules[a].push_back(aite);

    if (inc) { // a ::= a1 + 1 | a1 - 1
        aprod_rule_p ainc(new aprod_rule(as0 + afexpr_p(new fcz(1))));
        *ainc << a;
        arules[a].push_back(ainc);
        aprod_rule_p adec(new aprod_rule(as0 - afexpr_p(new fcz(1))));
        *adec << a;
        arules[a].push_back(adec);
    }

    // a ::= let xi = a1 in a2, 0 <= i < nlet
    for (size_t i = 0; i < nlet; i++) {
        afsubst_t aleti_s;
        aleti_s[id(i)] = as0;
        bfsubst_t bleti_s;
        bvfsubst_t bvleti_s;
        fsubst_t leti_s(aleti_s, bleti_s, bvleti_s);
        aprod_rule_p aleti(new aprod_rule(afexpr_p(new aflet(leti_s, as1))));
        *aleti << a << a;
        arules[a].push_back(aleti);
    }

    // b ::= true | false
    bprod_rule_p btrue(new bprod_rule(bfexpr_p(new fcb(true))));
    brules[b].push_back(btrue);
    bprod_rule_p bfalse(new bprod_rule(bfexpr_p(new fcb(false))));
    brules[b].push_back(bfalse);

    // b ::= bi, 0 <= i < nb
    for (size_t i = 0; i < nb; i++) {
        bprod_rule_p bi(new bprod_rule(bfexpr_p(new fbvar(i))));
        brules[b].push_back(bi);
    }

    // b ::= a1 <= a2
    bprod_rule_p ble(new bprod_rule(bfexpr_p(as0 <= as1)));
    *ble << a << a;
    brules[b].push_back(ble);

    if (eq) { // b ::= a1 == a2 | a1 < a2
        bprod_rule_p beq(new bprod_rule(bfexpr_p(as0 == as1)));
        *beq << a << a;
        brules[b].push_back(beq);

        bprod_rule_p blt(new bprod_rule(bfexpr_p(as0 < as1)));
        *blt << a << a;
        brules[b].push_back(blt);
    }

    // b ::= !b
    bprod_rule_p bnot(new bprod_rule(!bs0));
    *bnot << b;
    brules[b].push_back(bnot);

    // b ::= b1 &&/|| b2
    bprod_rule_p band(new bprod_rule(bs0 && bs1));
    *band << b << b;
    brules[b].push_back(band);
    bprod_rule_p bor(new bprod_rule(bs0 || bs1));
    *bor << b << b;
    brules[b].push_back(bor);

    return grammar(arules, brules, bvrules, a);
}

grammar simple_bv_grammar(size_t nbv, size_t len)
{
    agsymb_t a(0);
    bgsymb_t b(0);
    bvgsymb_t v(0);
    map <agsymb_t, vector <aprod_rule_p>> arules;
    map <bgsymb_t, vector <bprod_rule_p>> brules;
    map <bvgsymb_t, vector <bvprod_rule_p>> bvrules;

    // Non-terminal placeholders
    afexpr_p as0(new fzcall(0)), as1(new fzcall(1));
    bfexpr_p bs0(new fbcall(0)), bs1(new fbcall(1));
    bvfexpr_p bvs0(new fbvcall(0, len)), bvs1(new fbvcall(1, len));

    // v ::= i(len), -1 <= i <= 1
    for (int i = -1; i <= 1; i++) {
        bvprod_rule_p bvi(new bvprod_rule(bvfexpr_p(new fcbv(bv(len, i)))));
        bvrules[v].push_back(bvi);
    }

    // v ::= len
    bvprod_rule_p bvlen(new bvprod_rule(bvfexpr_p(new fcbv(bv(len, len)))));
    bvrules[v].push_back(bvlen);

    // v ::= vi, 0 <= i < nbv
    for (size_t i = 0; i < nbv; i++) {
        bvprod_rule_p bvvi(new bvprod_rule(bvfexpr_p(new fbvvar(i, len))));
        bvrules[v].push_back(bvvi);
    }

    // Comparison operators
    // v ::= v1 u< v2 | v1 u<= v2 | v1 == v2

    bprod_rule_p bvult(new bprod_rule(bvs0 < bvs1));
    *bvult << v << v;
    brules[b].push_back(bvult);

    bprod_rule_p bvule(new bprod_rule(bvs0 <= bvs1));
    *bvule << v << v;
    brules[b].push_back(bvule);

    bprod_rule_p bveq(new bprod_rule(bvs0 == bvs1));
    *bveq << v << v;
    brules[b].push_back(bveq);

    // Bit-vector ite
    // v ::= b ? v1 : v2

    bvprod_rule_p bvite(new bvprod_rule(bvfexpr_p(new bvfite(bs0, bvs0, bvs1))));
    *bvite << b << v << v;
    bvrules[v].push_back(bvite);

    // Bitwise logic
    // v ::= ~v1 | v1 & v2 | v1 `|' v2 | v1 ^ v2

    bvprod_rule_p bvnot(new bvprod_rule(!bvs0));
    *bvnot << v;
    bvrules[v].push_back(bvnot);

    bvprod_rule_p bvand(new bvprod_rule(bvs0 & bvs1));
    *bvand << v << v;
    bvrules[v].push_back(bvand);

    bvprod_rule_p bvor(new bvprod_rule(bvs0 | bvs1));
    *bvor << v << v;
    bvrules[v].push_back(bvor);

    bvprod_rule_p bvxor(new bvprod_rule(bvs0 ^ bvs1));
    *bvxor << v << v;
    bvrules[v].push_back(bvxor);

    // Arithmetic
    // v ::= v1 + v2 | v1 - v2 | -v1 | v1 * v2

    bvprod_rule_p bvplus(new bvprod_rule(bvs0 + bvs1));
    *bvplus << v << v;
    bvrules[v].push_back(bvplus);

    bvprod_rule_p bvminus(new bvprod_rule(bvs0 - bvs1));
    *bvminus << v << v;
    bvrules[v].push_back(bvor);

    bvprod_rule_p bvneg(new bvprod_rule(-bvs0));
    *bvneg << v;
    bvrules[v].push_back(bvneg);

    bvprod_rule_p bvmul(new bvprod_rule(bvs0 * bvs1));
    *bvmul << v << v;
    bvrules[v].push_back(bvmul);

    // Shift operators
    // v ::= v1 << v2 | v1 l>> v2 | v1 a>> v2

    bvprod_rule_p bvshl(new bvprod_rule(bvfexpr_p(new fbv_shl(bvs0, bvs1))));
    *bvshl << v << v;
    bvrules[v].push_back(bvshl);

    bvprod_rule_p bvlshr(new bvprod_rule(bvfexpr_p(new fbv_lshr(bvs0, bvs1))));
    *bvlshr << v << v;
    bvrules[v].push_back(bvlshr);

    bvprod_rule_p bvashr(new bvprod_rule(bvfexpr_p(new fbv_ashr(bvs0, bvs1))));
    *bvashr << v << v;
    bvrules[v].push_back(bvashr);

    return grammar(arules, brules, bvrules, v);
}

}

#endif // __GRAMMAR_STD_HPP_

