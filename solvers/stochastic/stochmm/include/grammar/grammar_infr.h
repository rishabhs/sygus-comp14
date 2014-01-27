#ifndef __GRAMMAR_INFR_H_
#define __GRAMMAR_INFR_H_

#include "../grammar.h"

namespace stoch {

template <typename T, typename U>
std::function <const T&(const gsymb_t <U>&)> gsymbfunc(const std::vector <T>& t, bool byval = true) {
	if (byval) {
		return [=](const gsymb_t <U>& x) -> const T& { return t[x.v]; };
	} else {
		return [&](const gsymb_t <U>& x) -> const T& { return t[x.v]; };
	}
}

template <typename T, typename U>
std::function <const T&(const gsymb_t <U>&)> gsymbfunc(const std::map <gsymb_t <U>, T>& t, bool byval = true) {
	if (byval) {
		return [=](const gsymb_t <U>& x) -> const T& { return t.at(x); };
	} else {
		return [&](const gsymb_t <U>& x) -> const T& { return t.at(x); };
	}
}

template <typename U, typename T>
prod_rule <U>& operator<<(prod_rule <U>& p, const gsymb_t <T>& s) {
	auto& v = nonstd::get(p.achild_v, p.bchild_v, p.bvchild_v, T());
	v.push_back(s);
	return p;
}

}

#include "grammar_std.h"
#include "grammar_sample.h"

#endif // __GRAMMAR_INFR_H_

