#ifndef __GRAMMAR_H_
#define __GRAMMAR_H_

#include <algorithm>
#include <functional>
#include <memory>
#include <vector>
#include "expr.h"

namespace stoch {

template <typename U> struct gsymb_t : public id {
	gsymb_t() : id(0) {};
	gsymb_t(size_t v) : id(v) {};
	gsymb_t(id v) : id(v) {};
};

typedef gsymb_t <z_class> agsymb_t;
typedef gsymb_t <bool> bgsymb_t;
typedef gsymb_t <bv> bvgsymb_t;

template <typename U> struct prod_rule;
typedef prod_rule <z_class> aprod_rule;
typedef prod_rule <bool> bprod_rule;
typedef prod_rule <bv> bvprod_rule;

template <typename U> struct prod_rule {
	typedef expr <U> eU;
	typedef std::shared_ptr <const eU> eU_p;
	typedef std::vector <aexpr_p> aexpr_p_v;
	typedef std::vector <bexpr_p> bexpr_p_v;
	typedef std::vector <bvexpr_p> bvexpr_p_v;
	typedef std::function <eU_p(const aexpr_p_v&, const bexpr_p_v&, const bvexpr_p_v&)> expand_t;

	prod_rule() {};
	prod_rule(const std::vector <agsymb_t>& achild_v,
			const std::vector <bgsymb_t>& bchild_v,
			const std::vector <bvgsymb_t>& bvchild_v,
			const expand_t& expand)
		: achild_v(achild_v), bchild_v(bchild_v), bvchild_v(bvchild_v),
		expand(expand) {};
	prod_rule(const expand_t& expand) : expand(expand) {};

	std::vector <agsymb_t> achild_v;
	std::vector <bgsymb_t> bchild_v;
	std::vector <bvgsymb_t> bvchild_v;
	expand_t expand;
};

struct grammar {
	typedef std::vector <aprod_rule> aprod_rule_v;
	typedef std::vector <bprod_rule> bprod_rule_v;
	typedef std::vector <bvprod_rule> bvprod_rule_v;
	typedef std::function <const aprod_rule_v&(const agsymb_t&)> arules_t;
	typedef std::function <const bprod_rule_v&(const bgsymb_t&)> brules_t;
	typedef std::function <const bvprod_rule_v&(const bvgsymb_t&)> bvrules_t;

	grammar() {};

	grammar(const arules_t& arules, const brules_t& brules, const bvrules_t& bvrules)
		: arules(arules), brules(brules), bvrules(bvrules) {};

	arules_t arules;
	brules_t brules;
	bvrules_t bvrules;
};

template <typename U> struct production;
typedef production <z_class> aprodn;
typedef production <bool> bprodn;
typedef production <bv> bvprodn;

template <typename U> struct production {
	typedef expr <U> eU;
	typedef prod_rule <U> prU;

	typedef production <z_class> prodnz;
	typedef production <bool> prodnb;
	typedef production <bv> prodnbv;

	typedef std::shared_ptr <const eU> eU_p;
	typedef std::shared_ptr <prodnz> prodnz_p;
	typedef std::shared_ptr <prodnb> prodnb_p;
	typedef std::shared_ptr <prodnbv> prodnbv_p;

	production(const gsymb_t <U>& s, const prU *prod,
			const std::vector <prodnz_p>& achild_v,
			const std::vector <prodnb_p>& bchild_v,
			const std::vector <prodnbv_p>& bvchild_v)
		: s(s), prod(prod), achild_v(achild_v), bchild_v(bchild_v),
		bvchild_v(bvchild_v) {};

	eU_p produce() const {
		if (expr_memo) {
			return expr_memo;
		}

		std::vector <aexpr_p> ac_v_prod(achild_v.size());
		std::vector <bexpr_p> bc_v_prod(bchild_v.size());
		std::vector <bvexpr_p> bvc_v_prod(bvchild_v.size());

		std::transform(achild_v.begin(), achild_v.end(), ac_v_prod.begin(),
			[&](const prodnz_p& p) -> aexpr_p {
				return p -> produce();
			});
		std::transform(bchild_v.begin(), bchild_v.end(), bc_v_prod.begin(),
			[&](const prodnb_p& p) -> bexpr_p {
				return p -> produce();
			});
		std::transform(bvchild_v.begin(), bvchild_v.end(), bvc_v_prod.begin(),
			[&](const prodnbv_p& p) -> bvexpr_p {
				return p -> produce();
			});

		expr_memo = prod -> expand(ac_v_prod, bc_v_prod, bvc_v_prod);
		return expr_memo;
	}

	size_t size() const {
		if (prod_size) {
			return *prod_size;
		}

		size_t ans = 1;
		ans = std::accumulate(achild_v.begin(), achild_v.end(), ans,
			[&](size_t z, const prodnz_p& p) -> size_t {
				return z + p -> size();
			});
		ans = std::accumulate(bchild_v.begin(), bchild_v.end(), ans,
			[&](size_t z, const prodnb_p& p) -> size_t {
				return z + p -> size();
			});
		ans = std::accumulate(bvchild_v.begin(), bvchild_v.end(), ans,
			[&](size_t z, const prodnbv_p& p) -> size_t {
				return z + p -> size();
			});

		prod_size = ans;
		return ans;
	}

	gsymb_t <U> s;
	const prU *prod;
	std::vector <prodnz_p> achild_v;
	std::vector <prodnb_p> bchild_v;
	std::vector <prodnbv_p> bvchild_v;

	mutable boost::optional <size_t> prod_size;
	mutable eU_p expr_memo;
};

}

#include "grammar/grammar_infr.h"

#endif // __GRAMMAR_H_

