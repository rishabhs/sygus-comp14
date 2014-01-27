#ifndef __EXPR_INFR_ITE_H_
#define __EXPR_INFR_ITE_H_

#include <memory>
#include <ostream>
#include <vector>

#include <z3++.h>

#include "nonstd.h"
#include "expr_infr.h"

namespace stoch {

template <typename U> struct ite;
typedef ite <z_class> aite;
typedef ite <bool> bite;
typedef ite <bv> bvite;

template <typename U> struct fite;

template <typename U>
struct ite : public expr <U> {
	typedef expr <U> eU;
	typedef fexpr <U> feU;
	typedef ite <U> this_t;
	typedef std::shared_ptr <const bexpr> bexpr_p;
	typedef std::shared_ptr <const eU> eU_p;
	typedef std::shared_ptr <const fexpr <bool>> bfexpr_p;
	typedef std::shared_ptr <const feU> feU_p;

	ite(bexpr_p econd, eU_p e1, eU_p e2) : econd(econd), e1(e1), e2(e2) {};

	virtual std::ostream& print(std::ostream& out) const {
		return out << "if " << *econd
			<< " then " << *e1
			<< " else " << *e2 << " fi";
	}

	virtual U eval(const typename eU::aval_t& aval,
			const typename eU::bval_t& bval,
			const typename eU::bvval_t& bvval) const {
		if (econd -> eval(aval, bval, bvval)) {
			return e1 -> eval(aval, bval, bvval);
		} else {
			return e2 -> eval(aval, bval, bvval);
		}
	}

	virtual std::vector <U> eval(const typename eU::avalp_t& aval,
			const typename eU::bvalp_t& bval,
			const typename eU::bvvalp_t& bvval, size_t n) const {
		std::vector <bool> vc(econd -> eval(aval, bval, bvval, n));
		std::vector <U> v1(e1 -> eval(aval, bval, bvval, n));
		std::vector <U> v2(e2 -> eval(aval, bval, bvval, n));
		for (size_t i = 0; i < n; i++) {
			v1[i] = vc[i] ? v1[i] : v2[i];
		}
		return v1;
	}

	virtual eU_p subst(const typename eU::asubst_t& asubst,
			const typename eU::bsubst_t& bsubst,
			const typename eU::bvsubst_t& bvsubst) const {
		bexpr_p ecs(econd -> subst(asubst, bsubst, bvsubst));
		eU_p e1s(e1 -> subst(asubst, bsubst, bvsubst));
		eU_p e2s(e2 -> subst(asubst, bsubst, bvsubst));
		return eU_p(new this_t(ecs, e1s, e2s));
	}

	virtual z3::expr smt(z3::context& ctxt) const {
		z3::expr ecs(econd -> smt(ctxt));
		z3::expr e1s(e1 -> smt(ctxt));
		z3::expr e2s(e2 -> smt(ctxt));
		return z3::to_expr(ctxt, Z3_mk_ite(ctxt, ecs, e1s, e2s));
	}

	virtual feU_p f_lift() const {
		return feU_p(new fite <U> (econd -> f_lift(), e1 -> f_lift(), e2 -> f_lift()));
	}

	virtual size_t size() const {
		return 1 + econd -> size() + e1 -> size() + e2 -> size();
	}

	virtual eU_p deep_copy() const {
		bexpr_p ecc(econd -> deep_copy());
		eU_p e1c(e1 -> deep_copy());
		eU_p e2c(e2 -> deep_copy());
		return eU_p(new this_t(ecc, e1c, e2c));
	}

	bexpr_p econd;
	eU_p e1, e2;
};

} // namespace stoch

#endif // __EXPR_INFR_ITE_H_
