#ifndef __EXPR_INFR_BINOP_H_
#define __EXPR_INFR_BINOP_H_

#include <algorithm>
#include <memory>
#include <ostream>
#include <vector>

#include <z3++.h>

#include "nonstd.h"
#include "expr_infr.h"

namespace stoch {

template <typename U, typename V, template <typename, typename> class f>
struct binop;

typedef binop <z_class, z_class, nonstd::plus> plus;
typedef binop <z_class, z_class, nonstd::minus> minus;
typedef binop <z_class, z_class, nonstd::multiplies> multiplies;
/* typedef binop <z_class, z_class, nonstd::divides> divides;
typedef binop <z_class, z_class, nonstd::modulus> modulus; */

typedef binop <z_class, bool, nonstd::equal_to> equal_to;
typedef binop <z_class, bool, nonstd::not_equal_to> not_equal_to;
typedef binop <z_class, bool, nonstd::greater> greater;
typedef binop <z_class, bool, nonstd::less> less;
typedef binop <z_class, bool, nonstd::greater_equal> greater_equal;
typedef binop <z_class, bool, nonstd::less_equal> less_equal;

struct logical_and;
struct logical_or;
typedef binop <bool, bool, nonstd::logical_eq> logical_eq;
typedef binop <bool, bool, nonstd::logical_xor> logical_xor;

typedef binop <bv, bool, nonstd::bv_ult> bv_ult;
typedef binop <bv, bool, nonstd::bv_slt> bv_slt;
typedef binop <bv, bool, nonstd::bv_ule> bv_ule;
typedef binop <bv, bool, nonstd::bv_sle> bv_sle;
typedef binop <bv, bool, nonstd::bv_eq> bv_eq;
typedef binop <bv, bool, nonstd::bv_uge> bv_uge;
typedef binop <bv, bool, nonstd::bv_sge> bv_sge;
typedef binop <bv, bool, nonstd::bv_ugt> bv_ugt;
typedef binop <bv, bool, nonstd::bv_sgt> bv_sgt;

typedef binop <bv, bv, nonstd::bv_and> bv_and;
typedef binop <bv, bv, nonstd::bv_or> bv_or;
typedef binop <bv, bv, nonstd::bv_xor> bv_xor;

typedef binop <bv, bv, nonstd::bv_add> bv_add;
typedef binop <bv, bv, nonstd::bv_sub> bv_sub;
typedef binop <bv, bv, nonstd::bv_mul> bv_mul;
typedef binop <bv, bv, nonstd::bv_udiv> bv_udiv;
typedef binop <bv, bv, nonstd::bv_urem> bv_urem;
typedef binop <bv, bv, nonstd::bv_sdiv> bv_sdiv;
typedef binop <bv, bv, nonstd::bv_srem> bv_srem;

typedef binop <bv, bv, nonstd::bv_shl> bv_shl;
typedef binop <bv, bv, nonstd::bv_lshr> bv_lshr;
typedef binop <bv, bv, nonstd::bv_ashr> bv_ashr;

template <typename U, typename V, template <typename, typename> class f>
struct fbinop;

template <typename U, typename V, template <typename, typename> class f>
struct binop : public expr <V> {
	typedef expr <U> eU;
	typedef expr <V> eV;
	typedef fexpr <U> feU;
	typedef fexpr <V> feV;
	typedef binop <U, V, f> this_t;
	typedef std::shared_ptr <const eU> eU_p;
	typedef std::shared_ptr <const eV> eV_p;
	typedef std::shared_ptr <const feU> feU_p;
	typedef std::shared_ptr <const feV> feV_p;

	binop(eU_p e1, eU_p e2) : e1(e1), e2(e2) {};

	virtual std::ostream& print(std::ostream& out) const {
		return out << "(" << *e1 << ") " << f <U, V>::op << " (" << *e2 << ")";
	}

	virtual V eval(const typename eU::aval_t& aval,
			const typename eU::bval_t& bval,
			const typename eU::bvval_t& bvval) const {
		U e1s(e1 -> eval(aval, bval, bvval));
		U e2s(e2 -> eval(aval, bval, bvval));
		return f <U, V> () (e1s, e2s);
	}

	virtual std::vector <V> eval(const typename eU::avalp_t& aval,
			const typename eU::bvalp_t& bval,
			const typename eU::bvvalp_t& bvval, size_t n) const {
		std::vector <U> v1(e1 -> eval(aval, bval, bvval, n));
		std::vector <U> v2(e2 -> eval(aval, bval, bvval, n));
		std::vector <V> ans(n);
		std::transform(v1.begin(), v1.end(), v2.begin(), ans.begin(), f <U, V> ());
		return ans;
	}

	virtual eV_p subst(const typename eU::asubst_t& asubst,
			const typename eU::bsubst_t& bsubst,
			const typename eU::bvsubst_t& bvsubst) const {
		eU_p e1s(e1 -> subst(asubst, bsubst, bvsubst));
		eU_p e2s(e2 -> subst(asubst, bsubst, bvsubst));
		return eV_p(new this_t(e1s, e2s));
	}

	virtual z3::expr smt(z3::context& ctxt) const {
		auto e1s = e1 -> smt(ctxt);
		auto e2s = e2 -> smt(ctxt);
		return f <z3::expr, z3::expr> () (e1s, e2s);
	}

	virtual feV_p f_lift() const {
		return feV_p(new fbinop <U, V, f> (e1 -> f_lift(), e2 -> f_lift()));
	}

	virtual size_t size() const {
		return 1 + e1 -> size() + e2 -> size();
	}

	virtual eV_p deep_copy() const {
		eU_p e1c(e1 -> deep_copy());
		eU_p e2c(e2 -> deep_copy());
		return eV_p(new this_t(e1c, e2c));
	}

	eU_p e1, e2;
};

typedef binop <bool, bool, nonstd::logical_and> logical_and_base;
typedef binop <bool, bool, nonstd::logical_or> logical_or_base;

struct logical_and : public logical_and_base {
	logical_and(bexpr_p e1, bexpr_p e2) : logical_and_base(e1, e2) {};

	virtual bool eval(const typename bexpr::aval_t& aval,
			const typename bexpr::bval_t& bval,
			const typename bexpr::bvval_t& bvval) const {
		return e1 -> eval(aval, bval, bvval) &&
			e2 -> eval(aval, bval, bvval);
	}
};

struct logical_or : public logical_or_base {
	logical_or(bexpr_p e1, bexpr_p e2) : logical_or_base(e1, e2) {};

	virtual bool eval(const typename bexpr::aval_t& aval,
			const typename bexpr::bval_t& bval,
			const typename bexpr::bvval_t& bvval) const {
		return e1 -> eval(aval, bval, bvval) ||
			e2 -> eval(aval, bval, bvval);
	}
};

}

#endif // __EXPR_INFR_BINOP_H_

