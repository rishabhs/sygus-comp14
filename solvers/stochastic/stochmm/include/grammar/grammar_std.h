#ifndef __GRAMMAR_STD_H_
#define __GRAMMAR_STD_H_

#include "grammar_infr.h"

namespace stoch {

// Declarations

grammar lia(size_t n);
grammar plia(size_t nz, size_t nb, bool eq = false, bool inc = false);

// Implementation

grammar lia(size_t n) {
	agsymb_t a(0);
	std::map <agsymb_t, std::vector <aprod_rule>> arules;
	std::map <bgsymb_t, std::vector <bprod_rule>> brules;
	std::map <bvgsymb_t, std::vector <bvprod_rule>> bvrules;

	// a ::= 0 | 1
	aprod_rule c0([](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return aexpr_p(new cz(0));
		});
	arules[a].push_back(c0);
	aprod_rule c1([](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return aexpr_p(new cz(1));
		});
	arules[a].push_back(c1);

	// a ::= xi, 0 <= i < n
	for (size_t i = 0; i < n; i++) {
		aprod_rule xi([=](const std::vector <aexpr_p>& achild_v,
					const std::vector <bexpr_p>& bchild_v,
					const std::vector <bvexpr_p>& bvchild_v) {
				return aexpr_p(new zvar(i));
			});
		arules[a].push_back(xi);
	}

	// a ::= a1 +/- a2
	aprod_rule a1pa2([](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return achild_v[0] + achild_v[1];
		});
	a1pa2 << a << a;
	arules[a].push_back(a1pa2);
	aprod_rule a1ma2([](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return achild_v[0] - achild_v[1];
		});
	a1ma2 << a << a;
	arules[a].push_back(a1ma2);

	auto arules_f = gsymbfunc(arules);
	auto brules_f = gsymbfunc(brules);
	auto bvrules_f = gsymbfunc(bvrules);
	return grammar(arules_f, brules_f, bvrules_f);
}

grammar plia(size_t nz, size_t nb, bool eq, bool inc) {
	agsymb_t a(0);
	bgsymb_t b(0);
	std::map <agsymb_t, std::vector <aprod_rule>> arules;
	std::map <bgsymb_t, std::vector <bprod_rule>> brules;
	std::map <bvgsymb_t, std::vector <bvprod_rule>> bvrules;

	// a ::= 0 | 1
	aprod_rule c0([](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return aexpr_p(new cz(0));
		});
	arules[a].push_back(c0);
	aprod_rule c1([](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return aexpr_p(new cz(1));
		});
	arules[a].push_back(c1);

	// a ::= xi, 0 <= i < nz
	for (size_t i = 0; i < nz; i++) {
		aprod_rule xi([=](const std::vector <aexpr_p>& achild_v,
					const std::vector <bexpr_p>& bchild_v,
					const std::vector <bvexpr_p>& bvchild_v) {
				return aexpr_p(new zvar(i));
			});
		arules[a].push_back(xi);
	}

	// a ::= a1 +/- a2
	aprod_rule a1pa2([](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return achild_v[0] + achild_v[1];
		});
	arules[a].push_back(a1pa2 << a << a);
	aprod_rule a1ma2([](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return achild_v[0] - achild_v[1];
		});
	arules[a].push_back(a1ma2 << a << a);

	// a ::= b ? a1 : a2
	aprod_rule aite([](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return aexpr_p(new stoch::aite(bchild_v[0], achild_v[0], achild_v[1]));
		});
	arules[a].push_back(aite << b << a << a);

	if (inc) { // a ::= a1 + 1 | a1 - 1
		aprod_rule ainc([=](const std::vector <aexpr_p>& achild_v,
					const std::vector <bexpr_p>& bchild_v,
					const std::vector <bvexpr_p>& bvchild_v) {
				return aexpr_p(achild_v[0] + aexpr_p(new cz(1)));
			});
		arules[a].push_back(ainc << a);
		aprod_rule adec([=](const std::vector <aexpr_p>& achild_v,
					const std::vector <bexpr_p>& bchild_v,
					const std::vector <bvexpr_p>& bvchild_v) {
				return aexpr_p(achild_v[0] - aexpr_p(new cz(1)));
			});
		arules[a].push_back(adec << a);
	}

	// b ::= true | false
	bprod_rule btrue([](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bexpr_p(new cb(true));
		});
	brules[b].push_back(btrue);
	bprod_rule bfalse([](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bexpr_p(new cb(false));
		});
	brules[b].push_back(bfalse);

	// b ::= bi, 0 <= i < nb
	for (size_t i = 0; i < nb; i++) {
		bprod_rule bi([=](const std::vector <aexpr_p>& achild_v,
					const std::vector <bexpr_p>& bchild_v,
					const std::vector <bvexpr_p>& bvchild_v) {
				return bexpr_p(new bvar(i));
			});
		brules[b].push_back(bi);
	}

	// b ::= a1 <= a2
	bprod_rule ble([](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return achild_v[0] <= achild_v[1];
		});
	brules[b].push_back(ble << a << a);

	if (eq) { // b ::= a1 == a2 | a1 < a2
		bprod_rule beq([](const std::vector <aexpr_p>& achild_v,
					const std::vector <bexpr_p>& bchild_v,
					const std::vector <bvexpr_p>& bvchild_v) {
				return achild_v[0] == achild_v[1];
			});
		brules[b].push_back(beq << a << a);
		bprod_rule blt([](const std::vector <aexpr_p>& achild_v,
					const std::vector <bexpr_p>& bchild_v,
					const std::vector <bvexpr_p>& bvchild_v) {
				return achild_v[0] < achild_v[1];
			});
		brules[b].push_back(blt << a << a);
	}

	// b ::= !b
	bprod_rule bnot([](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return !bchild_v[0];
		});
	brules[b].push_back(bnot << b);

	// b ::= b1 &&/|| b2
	bprod_rule band([](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bchild_v[0] && bchild_v[1];
		});
	brules[b].push_back(band << b << b);
	bprod_rule bor([](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bchild_v[0] || bchild_v[1];
		});
	brules[b].push_back(bor << b << b);

	auto arules_f = gsymbfunc(arules);
	auto brules_f = gsymbfunc(brules);
	auto bvrules_f = gsymbfunc(bvrules);
	return grammar(arules_f, brules_f, bvrules_f);
}

grammar simple_bv_grammar(size_t nbv, size_t len) {
	agsymb_t a(0);
	bgsymb_t b(0);
	bvgsymb_t v(0);
	std::map <agsymb_t, std::vector <aprod_rule>> arules;
	std::map <bgsymb_t, std::vector <bprod_rule>> brules;
	std::map <bvgsymb_t, std::vector <bvprod_rule>> bvrules;

	// v ::= i(len), -1 <= i <= 1
	for (int i = -1; i <= 1; i++) {
		bvprod_rule bvi([=](const std::vector <aexpr_p>& achild_v,
					const std::vector <bexpr_p>& bchild_v,
					const std::vector <bvexpr_p>& bvchild_v) {
				size_t si = static_cast <size_t> (i);
				return bvexpr_p(new cbv(bv(len, si)));
			});
		bvrules[v].push_back(bvi);
	}

	// v ::= len
	bvprod_rule bvlen([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bvexpr_p(new cbv(bv(len, len)));
		});
	bvrules[v].push_back(bvlen);

	// v ::= vi, 0 <= i < nbv
	for (size_t i = 0; i < nbv; i++) {
		bvprod_rule bvvi([=](const std::vector <aexpr_p>& achild_v,
					const std::vector <bexpr_p>& bchild_v,
					const std::vector <bvexpr_p>& bvchild_v) {
				return bvexpr_p(new bvvar(i, len));
			});
		bvrules[v].push_back(bvvi);
	}

	// Comparison operators
	// v ::= v1 u< v2 | v1 u<= v2 | v1 == v2

	bprod_rule bvult([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bexpr_p(new bv_ult(bvchild_v[0], bvchild_v[1]));
		});
	brules[b].push_back(bvult << v << v);

	bprod_rule bvule([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bexpr_p(new bv_ule(bvchild_v[0], bvchild_v[1]));
		});
	brules[b].push_back(bvule << v << v);

	bprod_rule bveq([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bexpr_p(new bv_eq(bvchild_v[0], bvchild_v[1]));
		});
	brules[b].push_back(bveq << v << v);

	// Bit-vector ite
	// v ::= b ? v1 : v2

	bvprod_rule bv_ite([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bvexpr_p(new bvite(bchild_v[0], bvchild_v[0], bvchild_v[1]));
		});
	bvrules[v].push_back(bv_ite << b << v << v);

	// Bitwise logic
	// v ::= ~v1 | v1 & v2 | v1 `|' v2 | v1 ^ v2

	bvprod_rule bvnot([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bvexpr_p(~bvchild_v[0]);
		});
	bvrules[v].push_back(bvnot << v);

	bvprod_rule bvand([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bvexpr_p(bvchild_v[0] & bvchild_v[1]);
		});
	bvrules[v].push_back(bvand << v << v);

	bvprod_rule bvor([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bvexpr_p(bvchild_v[0] | bvchild_v[1]);
		});
	bvrules[v].push_back(bvor << v << v);

	bvprod_rule bvxor([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bvexpr_p(bvchild_v[0] ^ bvchild_v[1]);
		});
	bvrules[v].push_back(bvxor << v << v);

	// Arithmetic
	// v ::= v1 + v2 | v1 - v2 | -v1 | v1 * v2

	bvprod_rule bvplus([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bvexpr_p(bvchild_v[0] + bvchild_v[1]);
		});
	bvrules[v].push_back(bvplus << v << v);

	bvprod_rule bvminus([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bvexpr_p(bvchild_v[0] - bvchild_v[1]);
		});
	bvrules[v].push_back(bvminus << v << v);

	bvprod_rule bvneg([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bvexpr_p(-bvchild_v[0]);
		});
	bvrules[v].push_back(bvneg << v);

	bvprod_rule bvmul([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bvexpr_p(bvchild_v[0] * bvchild_v[1]);
		});
	bvrules[v].push_back(bvmul << v << v);

	// Shift operators
	// v ::= v1 << v2 | v1 l>> v2 | v1 a>> v2

	bvprod_rule bvshl([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bvexpr_p(new bv_shl(bvchild_v[0], bvchild_v[1]));
		});
	bvrules[v].push_back(bvshl << v << v);

	bvprod_rule bvlshr([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bvexpr_p(new bv_lshr(bvchild_v[0], bvchild_v[1]));
		});
	bvrules[v].push_back(bvlshr << v << v);

	bvprod_rule bvashr([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bvexpr_p(new bv_ashr(bvchild_v[0], bvchild_v[1]));
		});
	bvrules[v].push_back(bvashr << v << v);

	auto arules_f = gsymbfunc(arules);
	auto brules_f = gsymbfunc(brules);
	auto bvrules_f = gsymbfunc(bvrules);
	return grammar(arules_f, brules_f, bvrules_f);
}

grammar bv_sets_grammar(size_t nbv, size_t len) {
	agsymb_t a(0);
	bgsymb_t b(0);
	bvgsymb_t v(0);
	std::map <agsymb_t, std::vector <aprod_rule>> arules;
	std::map <bgsymb_t, std::vector <bprod_rule>> brules;
	std::map <bvgsymb_t, std::vector <bvprod_rule>> bvrules;

	// v ::= i, -1 <= i <= 1

	for (size_t i = -1; i <= 1; i++) {
		bvprod_rule bvi([=](const std::vector <aexpr_p>& achild_v,
					const std::vector <bexpr_p>& bchild_v,
					const std::vector <bvexpr_p>& bvchild_v) {
				return bvexpr_p(new cbv(bv(len, i)));
			});
		bvrules[v].push_back(bvi);
	}

	// v ::= vi, 0 <= i < nbv
	for (size_t i = 0; i < nbv; i++) {
		bvprod_rule bvvi([=](const std::vector <aexpr_p>& achild_v,
					const std::vector <bexpr_p>& bchild_v,
					const std::vector <bvexpr_p>& bvchild_v) {
				return bvexpr_p(new bvvar(i, len));
			});
		bvrules[v].push_back(bvvi);
	}

	// Comparison operators
	// v ::= v1 == v2 | v1 $\subseteq$ v2

	bprod_rule bveq([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bexpr_p(new bv_eq(bvchild_v[0], bvchild_v[1]));
		});
	brules[b].push_back(bveq << v << v);

	bprod_rule bvsubseteq([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bexpr_p(new bv_eq(bvchild_v[0] & bvchild_v[1], bvchild_v[0]));
		});
	brules[b].push_back(bvsubseteq << v << v);

	// Bitwise logic
	// v ::= ~v1 | v1 & v2 | v1 `|' v2 | v1 ^ v2

	bvprod_rule bvnot([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bvexpr_p(~bvchild_v[0]);
		});
	bvrules[v].push_back(bvnot << v);

	bvprod_rule bvand([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bvexpr_p(bvchild_v[0] & bvchild_v[1]);
		});
	bvrules[v].push_back(bvand << v << v);

	bvprod_rule bvor([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bvexpr_p(bvchild_v[0] | bvchild_v[1]);
		});
	bvrules[v].push_back(bvor << v << v);

	bvprod_rule bvxor([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bvexpr_p(bvchild_v[0] ^ bvchild_v[1]);
		});
	bvrules[v].push_back(bvxor << v << v);

	auto arules_f = gsymbfunc(arules);
	auto brules_f = gsymbfunc(brules);
	auto bvrules_f = gsymbfunc(bvrules);
	return grammar(arules_f, brules_f, bvrules_f);
}

grammar synth_ashr_grammar(size_t nbv, size_t len) {
	agsymb_t a(0);
	bgsymb_t b(0);
	bvgsymb_t v(1), S(0);
	std::map <agsymb_t, std::vector <aprod_rule>> arules;
	std::map <bgsymb_t, std::vector <bprod_rule>> brules;
	std::map <bvgsymb_t, std::vector <bvprod_rule>> bvrules;

	// S ::= if (v0 u< (1 << (len - 1)) then v0 l>> v1 else v fi

	bvprod_rule bvs([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			bvexpr_p vc1(new cbv(bv(len, 1)));
			bvexpr_p vcs(new cbv(bv(len, len - 1)));
			bvexpr_p cond_r(new bv_shl(vc1, vcs));
			bvexpr_p v0(new bvvar(0, len)), v1(new bvvar(1, len));
			bexpr_p cond(new bv_ult(v0, cond_r));
			bvexpr_p e1(new bv_lshr(v0, v1));
			return bvexpr_p(new bvite(cond, e1, bvchild_v[0]));
		});
	bvrules[S].push_back(bvs << v);

	// v ::= i(len), -1 <= i <= 1
	std::vector <size_t> c_v {static_cast <size_t> (-1), 0, 1};
	for (auto i : c_v) {
		bvprod_rule bvi([=](const std::vector <aexpr_p>& achild_v,
					const std::vector <bexpr_p>& bchild_v,
					const std::vector <bvexpr_p>& bvchild_v) {
				return bvexpr_p(new cbv(bv(len, i)));
			});
		bvrules[v].push_back(bvi);
	}

	// v ::= len
	bvprod_rule bvlen([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bvexpr_p(new cbv(bv(len, len)));
		});
	bvrules[v].push_back(bvlen);

	// v ::= vi, 0 <= i < nbv
	for (size_t i = 0; i < nbv; i++) {
		bvprod_rule bvvi([=](const std::vector <aexpr_p>& achild_v,
					const std::vector <bexpr_p>& bchild_v,
					const std::vector <bvexpr_p>& bvchild_v) {
				return bvexpr_p(new bvvar(i, len));
			});
		bvrules[v].push_back(bvvi);
	}

	// Comparison operators
	// v ::= v1 u< v2 | v1 u<= v2 | v1 == v2

	bprod_rule bvult([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bexpr_p(new bv_ult(bvchild_v[0], bvchild_v[1]));
		});
	brules[b].push_back(bvult << v << v);

	bprod_rule bvule([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bexpr_p(new bv_ule(bvchild_v[0], bvchild_v[1]));
		});
	brules[b].push_back(bvule << v << v);

	bprod_rule bveq([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bexpr_p(new bv_eq(bvchild_v[0], bvchild_v[1]));
		});
	brules[b].push_back(bveq << v << v);

	// Bitwise logic
	// v ::= ~v1 | v1 & v2 | v1 `|' v2 | v1 ^ v2

	bvprod_rule bvnot([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bvexpr_p(~bvchild_v[0]);
		});
	bvrules[v].push_back(bvnot << v);

	bvprod_rule bvand([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bvexpr_p(bvchild_v[0] & bvchild_v[1]);
		});
	bvrules[v].push_back(bvand << v << v);

	bvprod_rule bvor([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bvexpr_p(bvchild_v[0] | bvchild_v[1]);
		});
	bvrules[v].push_back(bvor << v << v);

	bvprod_rule bvxor([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bvexpr_p(bvchild_v[0] ^ bvchild_v[1]);
		});
	bvrules[v].push_back(bvxor << v << v);

	// Arithmetic
	// v ::= v1 + v2 | v1 - v2 | -v1 | v1 * v2

	bvprod_rule bvplus([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bvexpr_p(bvchild_v[0] + bvchild_v[1]);
		});
	bvrules[v].push_back(bvplus << v << v);

	bvprod_rule bvminus([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bvexpr_p(bvchild_v[0] - bvchild_v[1]);
		});
	bvrules[v].push_back(bvminus << v << v);

	bvprod_rule bvneg([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bvexpr_p(-bvchild_v[0]);
		});
	bvrules[v].push_back(bvneg << v);

	bvprod_rule bvmul([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bvexpr_p(bvchild_v[0] * bvchild_v[1]);
		});
	bvrules[v].push_back(bvmul << v << v);

	// Shift operators
	// v ::= v1 << v2 | v1 l>> v2

	bvprod_rule bvshl([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bvexpr_p(new bv_shl(bvchild_v[0], bvchild_v[1]));
		});
	bvrules[v].push_back(bvshl << v << v);

	bvprod_rule bvlshr([=](const std::vector <aexpr_p>& achild_v,
				const std::vector <bexpr_p>& bchild_v,
				const std::vector <bvexpr_p>& bvchild_v) {
			return bvexpr_p(new bv_lshr(bvchild_v[0], bvchild_v[1]));
		});
	bvrules[v].push_back(bvlshr << v << v);

	auto arules_f = gsymbfunc(arules);
	auto brules_f = gsymbfunc(brules);
	auto bvrules_f = gsymbfunc(bvrules);
	return grammar(arules_f, brules_f, bvrules_f);
}

}

#endif // __GRAMMAR_STD_H_

