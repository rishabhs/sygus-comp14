#ifndef __FEXPR_H_
#define __FEXPR_H_

#include <functional>
#include <map>
#include <memory>
#include <ostream>
#include <string>
#include <vector>

#include "expr.h"

namespace stoch {

template <typename U> struct fexpr;
typedef fexpr <z_class> afexpr;
typedef fexpr <bool> bfexpr;
typedef fexpr <bv> bvfexpr;

typedef std::shared_ptr <const afexpr> afexpr_p;
typedef std::shared_ptr <const bfexpr> bfexpr_p;
typedef std::shared_ptr <const bvfexpr> bvfexpr_p;

template <typename U> struct fexpr {
	typedef expr <U> eU;
	typedef fexpr <U> feU;
	typedef std::shared_ptr <const eU> eU_p;
	typedef std::shared_ptr <const feU> feU_p;

	typedef std::function <aexpr_p(const id&)> asubst_t;
	typedef std::function <bexpr_p(const id&)> bsubst_t;
	typedef std::function <bvexpr_p(const id&)> bvsubst_t;

	typedef std::function <afexpr_p(const id&)> afsubst_t;
	typedef std::function <bfexpr_p(const id&)> bfsubst_t;
	typedef std::function <bvfexpr_p(const id&)> bvfsubst_t;

	typedef typename eU::aval_t aval_t;
	typedef typename eU::bval_t bval_t;
	typedef typename eU::bvval_t bvval_t;
	typedef typename eU::avalp_t avalp_t;
	typedef typename eU::bvalp_t bvalp_t;
	typedef typename eU::bvvalp_t bvvalp_t;

	virtual std::ostream& print(std::ostream& out) const = 0;
	virtual eU_p subst(const asubst_t& asubst, const bsubst_t& bsubst,
			const bvsubst_t& bvsubst) const = 0;

	virtual U eval(const asubst_t& asubst, const bsubst_t& bsubst,
			const bvsubst_t& bvsubst, leval_args_t& args) const = 0;

	virtual std::vector <U> eval(const asubst_t& asubst,
			const bsubst_t& bsubst, const bvsubst_t& bvsubst,
			const avalp_t& aval, const bvalp_t& bval,
			const bvvalp_t& bvval, size_t n) const {
		std::map <size_t, std::vector <z_class>> amemo;
		std::map <size_t, std::vector <bool>> bmemo;
		std::map <size_t, std::vector <bv>> bvmemo;
		return eval(asubst, bsubst, bvsubst, aval, bval, bvval, n, amemo, bmemo, bvmemo);
	}

	virtual std::vector <U> eval(const asubst_t& asubst,
			const bsubst_t& bsubst, const bvsubst_t& bvsubst,
			const avalp_t& aval, const bvalp_t& bval,
			const bvvalp_t& bvval, size_t n,
			std::map <size_t, std::vector <z_class>>& amemo,
			std::map <size_t, std::vector <bool>>& bmemo,
			std::map <size_t, std::vector <bv>>& bvmemo) const = 0;

	virtual feU_p fsubst(const afsubst_t& afsubst, const bfsubst_t& bfsubst,
		const bvfsubst_t& bvfsubst) const = 0;

	virtual void cs_elim() const {
		std::map <std::string, size_t> amemo, bmemo, bvmemo;
		cs_elim(amemo, bmemo, bvmemo);
	}

	virtual void cs_elim(std::map <std::string, size_t>& amemo,
			std::map <std::string, size_t>& bmemo,
			std::map <std::string, size_t>& bvmemo) const = 0;

	virtual size_t size() const = 0;
	virtual std::shared_ptr <const feU> deep_copy() const = 0;

	virtual ~fexpr() {};
};

template <typename U>
std::ostream& operator<<(std::ostream& out, const fexpr <U>& fe) {
	return fe.print(out);
}

}

#include "fexpr/fexpr_infr.h"

#endif // __FEXPR_H_

