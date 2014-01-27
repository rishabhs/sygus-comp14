#ifndef __FEXPR_INFR_VAR_H_
#define __FEXPR_INFR_VAR_H_

#include <map>
#include <memory>
#include <ostream>
#include <stdexcept>
#include <vector>

#include "nonstd.h"

#include "fexpr_infr.h"

namespace stoch {

template <typename U> struct fvariable;
typedef fvariable <z_class> fzvar;
typedef fvariable <bool> fbvar;
typedef fvariable <bv> fbvvar;

template <typename U>
struct fvariable : public fexpr <U> {
	typedef expr <U> eU;
	typedef fexpr <U> feU;
	typedef fvariable <U> this_t;
	typedef std::shared_ptr <const eU> eU_p;
	typedef std::shared_ptr <const feU> feU_p;

	fvariable(const id& x) : x(x), len(1) {};
	fvariable(const id& x, size_t len) : x(x), len(len) {
		if (len == 0) {
			throw std::underflow_error("Bit-vectors cannot be of length 0.");
		}
	};

	virtual std::ostream& print(std::ostream& out) const {
		return out << nonstd::get("x", "b", "v", U()) << x.v;
	}

	virtual eU_p subst(const typename eU::asubst_t& asubst,
			const typename eU::bsubst_t& bsubst,
			const typename eU::bvsubst_t& bvsubst) const {
		return eU_p(new variable <U> (x, len));
	}

	virtual U eval(const typename feU::asubst_t& asubst,
			const typename feU::bsubst_t& bsubst,
			const typename feU::bvsubst_t& bvsubst,
			leval_args_t& args) const {
		return nonstd::get(args.aval, args.bval, args.bvval, U())[x.v];
	}

	virtual std::vector <U> eval(const typename feU::asubst_t& asubst,
			const typename feU::bsubst_t& bsubst,
			const typename feU::bvsubst_t& bvsubst,
			const typename feU::avalp_t& aval,
			const typename feU::bvalp_t& bval,
			const typename feU::bvvalp_t& bvval, size_t n,
			std::map <size_t, std::vector <z_class>>& amemo,
			std::map <size_t, std::vector <bool>>& bmemo,
			std::map <size_t, std::vector <bv>>& bvmemo) const {
		std::vector <U> ans(nonstd::get(aval, bval, bvval, U())(x));
		return ans;
	}

	virtual feU_p fsubst(const typename feU::afsubst_t& afsubst,
			const typename feU::bfsubst_t& bfsubst,
			const typename feU::bvfsubst_t& bvfsubst) const {
		return nonstd::get(afsubst, bfsubst, bvfsubst, U())(x);
	}

	virtual void cs_elim(std::map <std::string, size_t>& amemo,
			std::map <std::string, size_t>& bmemo,
			std::map <std::string, size_t>& bvmemo) const {}

	virtual size_t size() const {
		return 1;
	}

	virtual feU_p deep_copy() const {
		return feU_p(new this_t(x));
	}

	id x;
	size_t len;
};

}

#endif // __FEXPR_INFR_VAR_H_

