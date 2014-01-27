#ifndef __FEXPR_INFR_CONST_H_
#define __FEXPR_INFR_CONST_H_

#include <map>
#include <memory>
#include <ostream>
#include <vector>

#include "nonstd.h"

#include "fexpr_infr.h"

namespace stoch {

template <typename U> struct fconstant;
typedef fconstant <z_class> fcz;
typedef fconstant <bool> fcb;
typedef fconstant <bv> fcbv;

template <typename U>
struct fconstant : public fexpr <U> {
	typedef expr <U> eU;
	typedef fexpr <U> feU;
	typedef fconstant <U> this_t;
	typedef std::shared_ptr <const eU> eU_p;
	typedef std::shared_ptr <const feU> feU_p;

	fconstant(U u) : u(u) {};

	virtual std::ostream& print(std::ostream& out) const {
		return out << u;
	}

	virtual eU_p subst(const typename feU::asubst_t& asubst,
			const typename feU::bsubst_t& bsubst,
			const typename feU::bvsubst_t& bvsubst) const {
		return eU_p(new constant <U> (u));
	}

	virtual U eval(const typename feU::asubst_t& asubst,
			const typename feU::bsubst_t& bsubst,
			const typename feU::bvsubst_t& bvsubst,
			leval_args_t& args) const {
		return u;
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
		return std::vector <U> (n, u);
	}

	virtual feU_p fsubst(const typename feU::afsubst_t& afsubst,
			const typename feU::bfsubst_t& bfsubst,
			const typename feU::bvfsubst_t& bvfsubst) const {
		return feU_p(new this_t(u));
	}

	virtual void cs_elim(std::map <std::string, size_t>& amemo,
		std::map <std::string, size_t>& bmemo,
		std::map <std::string, size_t>& bvmemo) const {}

	virtual size_t size() const {
		return 1;
	}

	virtual feU_p deep_copy() const {
		return feU_p(new this_t(u));
	}

	U u;
};

}

#endif // __FEXPR_INFR_CONST_H_

