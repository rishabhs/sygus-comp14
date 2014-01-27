#ifndef __FEXPR_INFR_ITE_H_
#define __FEXPR_INFR_ITE_H_

#include <map>
#include <memory>
#include <ostream>
#include <stdexcept>
#include <vector>

#include "nonstd.h"

#include "fexpr_infr.h"

namespace stoch {

template <typename U> struct fite;
typedef fite <z_class> afite;
typedef fite <bool> bfite;
typedef fite <bv> bvfite;

template <typename U>
struct fite : public fexpr <U> {
	typedef expr <U> eU;
	typedef fexpr <U> feU;
	typedef fite <U> this_t;
	typedef std::shared_ptr <const eU> eU_p;
	typedef std::shared_ptr <const feU> feU_p;

	fite(bfexpr_p fecond, feU_p fe1, feU_p fe2)
		: fecond(fecond), fe1(fe1), fe2(fe2) {};

	virtual std::ostream& print(std::ostream& out) const {
		return out << "if " << *fecond
			<< " then " << *fe1
			<< " else " << *fe2 << " fi";
	}

	virtual eU_p subst(const typename feU::asubst_t& asubst,
			const typename feU::bsubst_t& bsubst,
			const typename feU::bvsubst_t& bvsubst) const {
		bexpr_p feconds(fecond -> subst(asubst, bsubst, bvsubst));
		eU_p fe1s(fe1 -> subst(asubst, bsubst, bvsubst));
		eU_p fe2s(fe2 -> subst(asubst, bsubst, bvsubst));
		return eU_p(new ite <U> (feconds, fe1s, fe2s));
	}

	virtual U eval(const typename feU::asubst_t& asubst,
			const typename feU::bsubst_t& bsubst,
			const typename feU::bvsubst_t& bvsubst,
			leval_args_t& args) const {
		/* auto& memo = nonstd::get(args.zmemo, args.bmemo, args.bvmemo, U());

		if (cs_elim_index && memo.find(*cs_elim_index) != memo.end()) {
			return memo[*cs_elim_index];
		} */

		U ans;
		if (fecond -> eval(asubst, bsubst, bvsubst, args)) {
			ans = fe1 -> eval(asubst, bsubst, bvsubst, args);
		} else {
			ans = fe2 -> eval(asubst, bsubst, bvsubst, args);
		}

		/* if (cs_elim_index) {
			memo[*cs_elim_index] = ans;
		} */

		return ans;
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
		auto& memo = nonstd::get(amemo, bmemo, bvmemo, U());

		if (cs_elim_index) {
			if (memo.find(*cs_elim_index) != memo.end()) {
				return memo[*cs_elim_index];
			}
		}

		std::vector <bool> vc(fecond -> eval(asubst, bsubst, bvsubst,
			aval, bval, bvval, n, amemo, bmemo, bvmemo));
		std::vector <U> v1(fe1 -> eval(asubst, bsubst, bvsubst,
			aval, bval, bvval, n, amemo, bmemo, bvmemo));
		std::vector <U> v2(fe2 -> eval(asubst, bsubst, bvsubst,
			aval, bval, bvval, n, amemo, bmemo, bvmemo));

		for (size_t i = 0; i < vc.size(); i++) {
			v1[i] = vc[i] ? v1[i] : v2[i];
		}

		if (cs_elim_index) {
			memo[*cs_elim_index] = v1;
		}

		return v1;
	}

	virtual feU_p fsubst(const typename feU::afsubst_t& afsubst,
			const typename feU::bfsubst_t& bfsubst,
			const typename feU::bvfsubst_t& bvfsubst) const {
		bfexpr_p fecc(fecond -> fsubst(afsubst, bfsubst, bvfsubst));
		feU_p fe1c(fe1 -> fsubst(afsubst, bfsubst, bvfsubst));
		feU_p fe2c(fe2 -> fsubst(afsubst, bfsubst, bvfsubst));
		return feU_p(new this_t(fecc, fe1c, fe2c));
	}

	virtual void cs_elim(std::map <std::string, size_t>& amemo,
			std::map <std::string, size_t>& bmemo,
			std::map <std::string, size_t>& bvmemo) const {
		fecond -> cs_elim(amemo, bmemo, bvmemo);
		fe1 -> cs_elim(amemo, bmemo, bvmemo);
		fe2 -> cs_elim(amemo, bmemo, bvmemo);

		std::string me = boost::lexical_cast <std::string> (*this);
		auto& memo = nonstd::get(amemo, bmemo, bvmemo, U());
		if (memo.find(me) == memo.end()) {
			size_t v = memo.size();
			memo[me] = v;
		}

		cs_elim_index = memo[me];
	}

	virtual size_t size() const {
		return 1 + fecond -> size() + fe1 -> size() + fe2 -> size();
	}

	virtual feU_p deep_copy() const {
		bfexpr_p fecc(fecond -> deep_copy());
		feU_p fe1c(fe1 -> deep_copy());
		feU_p fe2c(fe2 -> deep_copy());
		return feU_p(new this_t(fecc, fe1c, fe2c));
	}

	bfexpr_p fecond;
	feU_p fe1, fe2;
	mutable boost::optional <size_t> cs_elim_index;
};

}

#endif // __FEXPR_INFR_ITE_H_

