#ifndef __EXPR_INFR_H_
#define __EXPR_INFR_H_

#include <functional>
#include <map>
#include <vector>

#include "../expr.h"

namespace stoch {

bool operator<(const id& x, const id& y);
template <typename T>
std::function <const T&(const id&)> idfunc(const std::vector <T>& t, bool byval = true);
template <typename T>
std::function <const T&(const id&)> idfunc(const std::map <id, T>& t, bool byval = true);

bool operator<(const id& x, const id& y) {
	return x.v < y.v;
}

template <typename T>
std::function <const T&(const id&)> idfunc(const std::vector <T>& t, bool byval) {
	if (byval) {
		return [=](const id& x) -> const T& { return t[x.v]; };
	} else {
		return [&](const id& x) -> const T& {
			return t[x.v];
		};
	}
}

template <>
std::function <const z_class&(const id&)> idfunc <z_class> (const std::vector <z_class>& t, bool byval) {
	if (byval) {
		return [=](const id& x) -> const z_class& { return t[x.v]; };
	} else {
		return [&](const id& x) -> const z_class& { return t[x.v]; };
	}
}

template <typename T>
std::function <const T&(const id&)> idfunc(const std::map <id, T>& t, bool byval) {
	if (byval) {
		return [=](const id& x) -> const T& { return t.at(x); };
	} else {
		return [&](const id& x) -> const T& { return t.at(x); };
	}
}

template <typename U>
std::ostream& operator<<(std::ostream& out, const expr <U>& e) {
	return e.print(out);
}

struct leval_args_t {
	typedef typename aexpr::aval_t aval_t;
	typedef typename aexpr::bval_t bval_t;
	typedef typename aexpr::bvval_t bvval_t;

	leval_args_t(const aval_t& aval, const bval_t& bval, const bvval_t& bvval,
			std::map <size_t, z_class>& zmemo,
			std::map <size_t, bool>& bmemo,
			std::map <size_t, bv>& bvmemo)
		: aval(aval), bval(bval), bvval(bvval), zmemo(zmemo), bmemo(bmemo),
		bvmemo(bvmemo) {}

	const aval_t& aval;
	const bval_t& bval;
	const bvval_t& bvval;
	std::map <size_t, z_class> zmemo;
	std::map <size_t, bool> bmemo;
	std::map <size_t, bv> bvmemo;
};

}

#include "expr_infr_const.h"
#include "expr_infr_var.h"
#include "expr_infr_unop.h"
#include "expr_infr_binop.h"
#include "expr_infr_ite.h"
#include "expr_infr_ops.h"

#endif // __EXPR_INFR_H_

