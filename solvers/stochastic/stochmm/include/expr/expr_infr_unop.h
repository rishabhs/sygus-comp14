#ifndef __EXPR_INFR_UNOP_H_
#define __EXPR_INFR_UNOP_H_

#include <algorithm>
#include <memory>
#include <ostream>
#include <vector>

#include <z3++.h>

#include "nonstd.h"
#include "expr_infr.h"

namespace stoch {

template <typename U, typename V, template <typename, typename> class f>
struct unop;

typedef unop <z_class, z_class, nonstd::negate> negate;
typedef unop <bool, bool, nonstd::logical_not> logical_not;

typedef unop <bv, bv, nonstd::bv_not> bv_not;
typedef unop <bv, bv, nonstd::bv_neg> bv_neg;

template <typename U, typename V, template <typename, typename> class f>
struct funop;

template <typename U, typename V, template <typename, typename> class f>
struct unop : public expr <V> {
	typedef expr <U> eU;
	typedef expr <V> eV;
	typedef fexpr <U> feU;
	typedef fexpr <V> feV;
	typedef unop <U, V, f> this_t;
	typedef std::shared_ptr <const eU> eU_p;
	typedef std::shared_ptr <const eV> eV_p;
	typedef std::shared_ptr <const feU> feU_p;
	typedef std::shared_ptr <const feV> feV_p;

	unop(eU_p e) : e(e) {};

	virtual std::ostream& print(std::ostream& out) const {
		return out << f <U, V>::op << "(" << *e << ")";
	}

	virtual V eval(const typename eU::aval_t& aval,
			const typename eU::bval_t& bval,
			const typename eU::bvval_t& bvval) const {
		return f <U, V> () (e -> eval(aval, bval, bvval));
	}

	virtual std::vector <V> eval(const typename eU::avalp_t& aval,
			const typename eU::bvalp_t& bval,
			const typename eU::bvvalp_t& bvval, size_t n) const {
		std::vector <U> v(e -> eval(aval, bval, bvval, n));
		std::vector <V> ans(n);
		std::transform(v.begin(), v.end(), ans.begin(), f <U, V> ());
		return ans;
	}

	virtual eV_p subst(const typename eU::asubst_t& asubst,
			const typename eU::bsubst_t& bsubst,
			const typename eU::bvsubst_t& bvsubst) const {
		return eV_p(new this_t(e -> subst(asubst, bsubst, bvsubst)));
	}

	virtual z3::expr smt(z3::context& ctxt) const {
		return f <z3::expr, z3::expr> () (e -> smt(ctxt));
	}

	virtual feV_p f_lift() const {
		return feV_p(new funop <U, V, f> (e -> f_lift()));
	}

	virtual size_t size() const {
		return 1 + e -> size();
	}

	virtual eV_p deep_copy() const {
		return eV_p(new this_t(e -> deep_copy()));
	}

	eU_p e;
};

}

#endif // __EXPR_INFR_UNOP_H_
