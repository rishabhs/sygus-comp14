#ifndef __FEXPR_INFR_BINOP_H_
#define __FEXPR_INFR_BINOP_H_

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
struct fbinop;

typedef fbinop <z_class, z_class, nonstd::plus> fplus;
typedef fbinop <z_class, z_class, nonstd::minus> fminus;
typedef fbinop <z_class, z_class, nonstd::multiplies> fmultiplies;
typedef fbinop <z_class, z_class, nonstd::divides> fdivides;
typedef fbinop <z_class, z_class, nonstd::modulus> fmodulus;

typedef fbinop <z_class, bool, nonstd::equal_to> fequal_to;
typedef fbinop <z_class, bool, nonstd::not_equal_to> fnot_equal_to;
typedef fbinop <z_class, bool, nonstd::greater> fgreater;
typedef fbinop <z_class, bool, nonstd::less> fless;
typedef fbinop <z_class, bool, nonstd::greater_equal> fgreater_equal;
typedef fbinop <z_class, bool, nonstd::less_equal> fless_equal;

struct flogical_and;
struct flogical_or;
typedef fbinop <bool, bool, nonstd::logical_eq> flogical_eq;
typedef fbinop <bool, bool, nonstd::logical_xor> flogical_xor;

typedef fbinop <bv, bool, nonstd::bv_ult> fbv_ult;
typedef fbinop <bv, bool, nonstd::bv_slt> fbv_slt;
typedef fbinop <bv, bool, nonstd::bv_ule> fbv_ule;
typedef fbinop <bv, bool, nonstd::bv_sle> fbv_sle;
typedef fbinop <bv, bool, nonstd::bv_eq> fbv_eq;
typedef fbinop <bv, bool, nonstd::bv_uge> fbv_uge;
typedef fbinop <bv, bool, nonstd::bv_sge> fbv_sge;
typedef fbinop <bv, bool, nonstd::bv_ugt> fbv_ugt;
typedef fbinop <bv, bool, nonstd::bv_sgt> fbv_sgt;

typedef fbinop <bv, bv, nonstd::bv_and> fbv_and;
typedef fbinop <bv, bv, nonstd::bv_or> fbv_or;
typedef fbinop <bv, bv, nonstd::bv_xor> fbv_xor;

typedef fbinop <bv, bv, nonstd::bv_add> fbv_add;
typedef fbinop <bv, bv, nonstd::bv_sub> fbv_sub;
typedef fbinop <bv, bv, nonstd::bv_mul> fbv_mul;
typedef fbinop <bv, bv, nonstd::bv_udiv> fbv_udiv;
typedef fbinop <bv, bv, nonstd::bv_urem> fbv_urem;
typedef fbinop <bv, bv, nonstd::bv_sdiv> fbv_sdiv;
typedef fbinop <bv, bv, nonstd::bv_srem> fbv_srem;

typedef fbinop <bv, bv, nonstd::bv_shl> fbv_shl;
typedef fbinop <bv, bv, nonstd::bv_lshr> fbv_lshr;
typedef fbinop <bv, bv, nonstd::bv_ashr> fbv_ashr;

template <typename U, typename V, template <typename, typename> class f>
struct fbinop : public fexpr <V> {
	typedef expr <U> eU;
	typedef expr <V> eV;
	typedef fexpr <U> feU;
	typedef fexpr <V> feV;
	typedef fbinop <U, V, f> this_t;
	typedef std::shared_ptr <const eU> eU_p;
	typedef std::shared_ptr <const eV> eV_p;
	typedef std::shared_ptr <const feU> feU_p;
	typedef std::shared_ptr <const feV> feV_p;

	fbinop(feU_p fe1, feU_p fe2) : fe1(fe1), fe2(fe2) {};

	virtual std::ostream& print(std::ostream& out) const {
		return out << "(" << *fe1 << ") " << f <U, V>::op
			<< " (" << *fe2 << ")";
	}

	virtual eV_p subst(const typename feV::asubst_t& asubst,
			const typename feV::bsubst_t& bsubst,
			const typename feV::bvsubst_t& bvsubst) const {
		eU_p fe1s(fe1 -> subst(asubst, bsubst, bvsubst));
		eU_p fe2s(fe2 -> subst(asubst, bsubst, bvsubst));
		return eV_p(new binop <U, V, f> (fe1s, fe2s));
	}

	virtual V eval(const typename feU::asubst_t& asubst,
			const typename feU::bsubst_t& bsubst,
			const typename feU::bvsubst_t& bvsubst,
			leval_args_t& args) const {
		/* auto& memo = nonstd::get(args.zmemo, args.bmemo, args.bvmemo, V());

		if (cs_elim_index && memo.find(*cs_elim_index) != memo.end()) {
			return memo[*cs_elim_index];
		} */

		U fe1s(fe1 -> eval(asubst, bsubst, bvsubst, args));
		U fe2s(fe2 -> eval(asubst, bsubst, bvsubst, args));
		V ans = f <U, V> () (fe1s, fe2s);

		/* if (cs_elim_index) {
			memo[*cs_elim_index] = ans;
		} */

		return ans;
	}

	virtual std::vector <V> eval(const typename feV::asubst_t& asubst,
			const typename feV::bsubst_t& bsubst,
			const typename feV::bvsubst_t& bvsubst,
			const typename feV::avalp_t& aval,
			const typename feV::bvalp_t& bval,
			const typename feV::bvvalp_t& bvval, size_t n,
			std::map <size_t, std::vector <z_class>>& amemo,
			std::map <size_t, std::vector <bool>>& bmemo,
			std::map <size_t, std::vector <bv>>& bvmemo) const {
		auto& memo = nonstd::get(amemo, bmemo, bvmemo, V());

		if (cs_elim_index) {
			if (memo.find(*cs_elim_index) != memo.end()) {
				return memo[*cs_elim_index];
			}
		}

		std::vector <U> v1(fe1 -> eval(asubst, bsubst, bvsubst,
			aval, bval, bvval, n, amemo, bmemo, bvmemo));
		std::vector <U> v2(fe2 -> eval(asubst, bsubst, bvsubst,
			aval, bval, bvval, n, amemo, bmemo, bvmemo));
		std::vector <V> ans(n);
		std::transform(v1.begin(), v1.end(), v2.begin(), ans.begin(), f <U, V> ());

		if (cs_elim_index) {
			memo[*cs_elim_index] = ans;
		}

		return ans;
	}

	virtual feV_p fsubst(const typename feV::afsubst_t& afsubst,
			const typename feV::bfsubst_t& bfsubst,
			const typename feV::bvfsubst_t& bvfsubst) const {
		auto fe1_s = fe1 -> fsubst(afsubst, bfsubst, bvfsubst);
		auto fe2_s = fe2 -> fsubst(afsubst, bfsubst, bvfsubst);
		return feV_p(new this_t(fe1_s, fe2_s));
	}

	virtual void cs_elim(std::map <std::string, size_t>& amemo,
			std::map <std::string, size_t>& bmemo,
			std::map <std::string, size_t>& bvmemo) const {
		fe1 -> cs_elim(amemo, bmemo, bvmemo);
		fe2 -> cs_elim(amemo, bmemo, bvmemo);

		std::string me = boost::lexical_cast <std::string> (*this);
		auto& memo = nonstd::get(amemo, bmemo, bvmemo, V());
		if (memo.find(me) == memo.end()) {
			size_t v = memo.size();
			memo[me] = v;
		}

		cs_elim_index = memo[me];
	}

	virtual size_t size() const {
		return 1 + fe1 -> size() + fe2 -> size();
	}

	virtual feV_p deep_copy() const {
		feU_p fe1c(fe1 -> deep_copy());
		feU_p fe2c(fe2 -> deep_copy());
		return feV_p(new this_t(fe1c, fe2c));
	}

	feU_p fe1, fe2;
	mutable boost::optional <size_t> cs_elim_index;
};

typedef fbinop <bool, bool, nonstd::logical_and> flogical_and_base;

struct flogical_and : public flogical_and_base {
	flogical_and(bfexpr_p fe1, bfexpr_p fe2) : flogical_and_base(fe1, fe2) {};

	virtual bool eval(const typename bfexpr::asubst_t& asubst,
			const typename bfexpr::bsubst_t& bsubst,
			const typename bfexpr::bvsubst_t& bvsubst,
			leval_args_t& args) const {
		/* auto& memo = args.bmemo;

		if (cs_elim_index && memo.find(*cs_elim_index) != memo.end()) {
			return memo[*cs_elim_index];
		} */

		bool ans(fe1 -> eval(asubst, bsubst, bvsubst, args));
		if (ans) {
			ans = fe2 -> eval(asubst, bsubst, bvsubst, args);
		}

		/* if (cs_elim_index) {
			memo[*cs_elim_index] = ans;
		} */

		return ans;
	}
};

typedef fbinop <bool, bool, nonstd::logical_or> flogical_or_base;

struct flogical_or : public flogical_or_base {
	flogical_or(bfexpr_p fe1, bfexpr_p fe2) : flogical_or_base(fe1, fe2) {};

	virtual bool eval(const typename bfexpr::asubst_t& asubst,
			const typename bfexpr::bsubst_t& bsubst,
			const typename bfexpr::bvsubst_t& bvsubst,
			leval_args_t& args) const {
		/* auto& memo = args.bmemo;

		if (cs_elim_index && memo.find(*cs_elim_index) != memo.end()) {
			return memo[*cs_elim_index];
		} */

		bool ans(fe1 -> eval(asubst, bsubst, bvsubst, args));
		if (!ans) {
			ans = fe2 -> eval(asubst, bsubst, bvsubst, args);
		}

		/* if (cs_elim_index) {
			memo[*cs_elim_index] = ans;
		} */

		return ans;
	}
};

}

#endif // __FEXPR_INFR_BINOP_H_

