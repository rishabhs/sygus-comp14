#ifndef __EXPR_INFR_CONST_H_
#define __EXPR_INFR_CONST_H_

#include <memory>
#include <ostream>
#include <vector>

#include <boost/lexical_cast.hpp>
#include <z3++.h>

#include "nonstd.h"
#include "expr_infr.h"

namespace stoch {

template <typename U> struct constant;
typedef constant <z_class> cz;
typedef constant <bool> cb;
typedef constant <bv> cbv;

template <typename U> struct fconstant;

template <typename U>
struct constant : public expr <U> {
	typedef expr <U> eU;
	typedef fexpr <U> feU;
	typedef constant <U> this_t;
	typedef std::shared_ptr <const eU> eU_p;
	typedef std::shared_ptr <const feU> feU_p;

	constant(U u) : u(u) {};

	virtual std::ostream& print(std::ostream& out) const {
		return out << u;
	}

	virtual U eval(const typename eU::aval_t& aval,
			const typename eU::bval_t& bval,
			const typename eU::bvval_t& bvval) const {
		return u;
	}

	virtual std::vector <U> eval(const typename eU::avalp_t& aval,
			const typename eU::bvalp_t& bval,
			const typename eU::bvvalp_t& bvval, size_t n) const {
		return std::vector <U> (n, u);
	}

	virtual eU_p subst(const typename eU::asubst_t& asubst,
			const typename eU::bsubst_t& bsubst,
			const typename eU::bvsubst_t& bvsubst) const {
		return eU_p(new this_t(u));
	}

	virtual z3::expr smt(z3::context& ctxt) const {
		return smt(ctxt, u);
	}

	virtual feU_p f_lift() const {
		return feU_p(new fconstant <U> (u));
	}

	virtual size_t size() const {
		return 1;
	}

	virtual eU_p deep_copy() const {
		return eU_p(new this_t(u));
	}

	U u;

	private:

	z3::expr smt(z3::context& ctxt, z_class c) const {
		std::string cs(boost::lexical_cast <std::string> (c));
		return ctxt.int_val(cs.c_str());
	}

	z3::expr smt(z3::context& ctxt, bool b) const {
		return ctxt.bool_val(b);
	}

	z3::expr smt(z3::context& ctxt, const bv& v) const {
		v.mask();
		std::string vs(boost::lexical_cast <std::string> (v.x));
		return ctxt.bv_val(vs.c_str(), v.len);
	}
};

}

#endif // __EXPR_INFR_CONST_H_

