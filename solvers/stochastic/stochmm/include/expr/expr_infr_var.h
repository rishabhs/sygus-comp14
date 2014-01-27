#ifndef __EXPR_INFR_VAR_H_
#define __EXPR_INFR_VAR_H_

#include <memory>
#include <ostream>
#include <stdexcept>
#include <vector>

#include <boost/lexical_cast.hpp>
#include <z3++.h>

#include "nonstd.h"
#include "expr_infr.h"

namespace stoch {

template <typename U> struct variable;
typedef variable <z_class> zvar;
typedef variable <bool> bvar;
typedef variable <bv> bvvar;

template <typename U> struct fvariable;

template <typename U>
struct variable : public expr <U> {
	typedef expr <U> eU;
	typedef fexpr <U> feU;
	typedef variable <U> this_t;
	typedef std::shared_ptr <const eU> eU_p;
	typedef std::shared_ptr <const feU> feU_p;

	variable(const id& x) : x(x), len(1) {};
	variable(const id& x, size_t len) : x(x), len(len) {
		if (len == 0) {
			throw std::underflow_error("Bit-vectors cannot be of length 0.");
		}
	};

	virtual std::ostream& print(std::ostream& out) const {
		return out << nonstd::get("x", "b", "v", U()) << x.v;
	}

	virtual U eval(const typename eU::aval_t& aval,
			const typename eU::bval_t& bval,
			const typename eU::bvval_t& bvval) const {
		return nonstd::get(aval, bval, bvval, U())[x.v];
	}

	virtual std::vector <U> eval(const typename eU::avalp_t& aval,
			const typename eU::bvalp_t& bval,
			const typename eU::bvvalp_t& bvval, size_t n) const {
		return nonstd::get(aval, bval, bvval, U())(x);
	}

	virtual eU_p subst(const typename eU::asubst_t& asubst,
			const typename eU::bsubst_t& bsubst,
			const typename eU::bvsubst_t& bvsubst) const {
		return nonstd::get(asubst, bsubst, bvsubst, U())(x);
	}

	virtual z3::expr smt(z3::context& ctxt) const {
		std::string xs(boost::lexical_cast <std::string> (*this));
		z3::expr zans = ctxt.int_const(xs.c_str());
		z3::expr bans = ctxt.bool_const(xs.c_str());
		z3::expr bvans = ctxt.bv_const(xs.c_str(), len);
		return nonstd::get(zans, bans, bvans, U());
	}

	virtual feU_p f_lift() const {
		return feU_p(new fvariable <U> (x));
	}

	virtual size_t size() const {
		return 1;
	}

	virtual eU_p deep_copy() const {
		return eU_p(new this_t(x));
	}

	id x;
	size_t len;
};

}

#endif // __EXPR_INFR_VAR_H_

