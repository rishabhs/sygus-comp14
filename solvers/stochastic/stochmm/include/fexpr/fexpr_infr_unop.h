#ifndef __FEXPR_INFR_UNOP_H_
#define __FEXPR_INFR_UNOP_H_

#include <map>
#include <memory>
#include <ostream>
#include <stdexcept>
#include <vector>

#include <boost/optional.hpp>

#include "nonstd.h"

#include "fexpr_infr.h"

namespace stoch {

template <typename U, typename V, template <typename, typename> class f>
struct funop;

typedef funop <z_class, z_class, nonstd::negate> fnegate;
typedef funop <bool, bool, nonstd::logical_not> flogical_not;

typedef funop <bv, bv, nonstd::bv_not> fbv_not;
typedef funop <bv, bv, nonstd::bv_neg> fbv_neg;

template <typename U, typename V, template <typename, typename> class f>
struct funop : public fexpr <V> {
	typedef expr <U> eU;
	typedef expr <V> eV;
	typedef fexpr <U> feU;
	typedef fexpr <V> feV;
	typedef funop <U, V, f> this_t;
	typedef std::shared_ptr <const eU> eU_p;
	typedef std::shared_ptr <const eV> eV_p;
	typedef std::shared_ptr <const feU> feU_p;
	typedef std::shared_ptr <const feV> feV_p;

	funop(feU_p fe) : fe(fe) {};

	virtual std::ostream& print(std::ostream& out) const {
		return out << f <U, V>::op << "(" << *fe << ")";
	}

	virtual eV_p subst(const typename eU::asubst_t& asubst,
			const typename eU::bsubst_t& bsubst,
			const typename eU::bvsubst_t& bvsubst) const {
		return eV_p(new unop <U, V, f> (fe -> subst(asubst, bsubst, bvsubst)));
	}

	virtual V eval(const typename feU::asubst_t& asubst,
			const typename feU::bsubst_t& bsubst,
			const typename feU::bvsubst_t& bvsubst,
			leval_args_t& args) const {
		/* auto& memo = nonstd::get(args.zmemo, args.bmemo, args.bvmemo, V());

		if (cs_elim_index && memo.find(*cs_elim_index) != memo.end()) {
			return memo[*cs_elim_index];
		} */

		U fes(fe -> eval(asubst, bsubst, bvsubst, args));
		V ans = f <U, V> () (fes);

		/* if (cs_elim_index) {
			memo[*cs_elim_index] = ans;
		} */

		return ans;
	}

	virtual std::vector <V> eval(const typename feU::asubst_t& asubst,
			const typename feU::bsubst_t& bsubst,
			const typename feU::bvsubst_t& bvsubst,
			const typename feU::avalp_t& aval,
			const typename feU::bvalp_t& bval,
			const typename feU::bvvalp_t& bvval, size_t n,
			std::map <size_t, std::vector <z_class>>& amemo,
			std::map <size_t, std::vector <bool>>& bmemo,
			std::map <size_t, std::vector <bv>>& bvmemo) const {
		auto& memo = nonstd::get(amemo, bmemo, bvmemo, V());

		if (cs_elim_index) {
			if (memo.find(*cs_elim_index) != memo.end()) {
				return memo[*cs_elim_index];
			}
		}

		std::vector <U> v(fe -> eval(asubst, bsubst, bvsubst,
			aval, bval, bvval, n, amemo, bmemo, bvmemo));
		std::vector <V> ans(n);
		std::transform(v.begin(), v.end(), ans.begin(), f <U, V> ());

		if (cs_elim_index) {
			memo[*cs_elim_index] = ans;
		}

		return ans;
	}

	virtual feV_p fsubst(const typename feV::afsubst_t& afsubst,
			const typename feV::bfsubst_t& bfsubst,
			const typename feV::bvfsubst_t& bvfsubst) const {
		auto fe_s = fe -> fsubst(afsubst, bfsubst, bvfsubst);
		return feV_p(new this_t(fe_s));
	}

	virtual void cs_elim(std::map <std::string, size_t>& amemo,
			std::map <std::string, size_t>& bmemo,
			std::map <std::string, size_t>& bvmemo) const {
		fe -> cs_elim(amemo, bmemo, bvmemo);

		std::string me = boost::lexical_cast <std::string> (*this);
		auto& memo = nonstd::get(amemo, bmemo, bvmemo, V());
		if (memo.find(me) == memo.end()) {
			size_t v = memo.size();
			memo[me] = v;
		}

		cs_elim_index = memo[me];
	}

	virtual size_t size() const {
		return 1 + fe -> size();
	}

	virtual feV_p deep_copy() const {
		return feV_p(new this_t(fe -> deep_copy()));
	}

	feU_p fe;
	mutable boost::optional <size_t> cs_elim_index;
};

}

#endif // __FEXPR_INFR_UNOP_H_

