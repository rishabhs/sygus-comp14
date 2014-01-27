#ifndef __EXPR_H_
#define __EXPR_H_

#include <functional>
#include <map>
#include <memory>
#include <ostream>
#include <tuple>
#include <vector>

#include <gmpxx.h>
#include <z3++.h>

#include "nonstd.h"

namespace stoch {

typedef std::vector <z_class> z_class_v;
typedef std::vector <bool> bool_v;
typedef std::vector <bv> bv_v;

struct id {
	id() : v(0) {};
	id(size_t v) : v(v) {};
	size_t v;
};

template <typename U> struct expr;
typedef expr <z_class> aexpr;
typedef expr <bool> bexpr;
typedef expr <bv> bvexpr;

typedef std::shared_ptr <const aexpr> aexpr_p;
typedef std::shared_ptr <const bexpr> bexpr_p;
typedef std::shared_ptr <const bvexpr> bvexpr_p;

struct leval_args_t;

template <typename U> struct fexpr;

template <typename U> struct expr {
	typedef expr <U> eU;
	typedef fexpr <U> feU;
	typedef std::shared_ptr <const eU> eU_p;
	typedef std::shared_ptr <const feU> feU_p;

	typedef std::vector <z_class> aval_t;
	typedef std::vector <bool> bval_t;
	typedef std::vector <bv> bvval_t;

	typedef std::function <const z_class_v& (const id&)> avalp_t;
	typedef std::function <const bool_v& (const id&)> bvalp_t;
	typedef std::function <const bv_v& (const id&)> bvvalp_t;

	typedef std::function <aexpr_p(const id&)> asubst_t;
	typedef std::function <bexpr_p(const id&)> bsubst_t;
	typedef std::function <bvexpr_p(const id&)> bvsubst_t;

	virtual std::ostream& print(std::ostream& out) const = 0;
	virtual U eval(const aval_t& aval, const bval_t& bval,
		const bvval_t& bvval) const = 0;
	virtual std::vector <U> eval(const avalp_t& aval, const bvalp_t& bval,
		const bvvalp_t& bvval, size_t n) const = 0;
	virtual eU_p subst(const asubst_t& asubst, const bsubst_t& bsubst,
		const bvsubst_t& bvsubst) const = 0;
	virtual z3::expr smt(z3::context& ctxt) const = 0;
	virtual feU_p f_lift() const = 0;

	virtual size_t size() const = 0;
	virtual eU_p deep_copy() const = 0;

	virtual ~expr() {};
};

}

#include "expr/expr_infr.h"
#include "fexpr.h"

#endif // __EXPR_H_

