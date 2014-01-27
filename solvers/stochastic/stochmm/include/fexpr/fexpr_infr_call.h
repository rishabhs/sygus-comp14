#ifndef __FEXPR_INFR_CALL_H_
#define __FEXPR_INFR_CALL_H_

#include <map>
#include <memory>
#include <ostream>
#include <stdexcept>
#include <vector>

#include "nonstd.h"

#include "fexpr_infr.h"

namespace stoch {

template <typename U> struct fcall;
typedef fcall <z_class> fzcall;
typedef fcall <bool> fbcall;
typedef fcall <bv> fbvcall;

template <typename U>
struct fcall : public fexpr <U> {
	typedef expr <U> eU;
	typedef fexpr <U> feU;
	typedef fcall <U> this_t;
	typedef std::shared_ptr <const eU> eU_p;
	typedef std::shared_ptr <const feU> feU_p;

	typedef std::vector <afexpr_p> zargs_v_t;
	typedef std::vector <bfexpr_p> bargs_v_t;
	typedef std::vector <bvfexpr_p> bvargs_v_t;

	fcall(const id& x, const zargs_v_t& zargs, const bargs_v_t& bargs,
			const bvargs_v_t& bvargs)
		: x(x), zargs(zargs), bargs(bargs), bvargs(bvargs) {};

	virtual std::ostream& print(std::ostream& out) const {
		out << "f" << nonstd::get("z", "b", "bv", U()) << x.v;
		out << "(";
		for (size_t i = 0; i < zargs.size() + bargs.size() + bvargs.size(); i++) {
			if (i < zargs.size()) {
				out << *zargs[i];
			} else if (i < zargs.size() + bargs.size()) {
				out << *bargs[i - zargs.size()];
			} else {
				out << *bvargs[i - zargs.size() - bargs.size()];
			}

			if (i + 1 < zargs.size() + bargs.size() + bvargs.size()) {
				out << ", ";
			}
		}
		return out << ")";
	}

	virtual eU_p subst(const typename eU::asubst_t& asubst,
			const typename eU::bsubst_t& bsubst,
			const typename eU::bvsubst_t& bvsubst) const {
		std::vector <aexpr_p> zargs_s(zargs.size());
		std::vector <bexpr_p> bargs_s(bargs.size());
		std::vector <bvexpr_p> bvargs_s(bvargs.size());

		std::transform(zargs.begin(), zargs.end(), zargs_s.begin(),
			[&](const afexpr_p& e) -> aexpr_p {
				return e -> subst(asubst, bsubst, bvsubst);
			});
		std::transform(bargs.begin(), bargs.end(), bargs_s.begin(),
			[&](const bfexpr_p& e) -> bexpr_p {
				return e -> subst(asubst, bsubst, bvsubst);
			});
		std::transform(bvargs.begin(), bvargs.end(), bvargs_s.begin(),
			[&](const bvfexpr_p& e) -> bvexpr_p {
				return e -> subst(asubst, bsubst, bvsubst);
			});

		return nonstd::get(asubst, bsubst, bvsubst, U())(x) ->
			subst(idfunc(zargs_s, false), idfunc(bargs_s, false),
			idfunc(bvargs_s, false));
	}

	virtual U eval(const typename feU::asubst_t& asubst,
			const typename feU::bsubst_t& bsubst,
			const typename feU::bvsubst_t& bvsubst,
			leval_args_t& args) const {
		auto& memo = nonstd::get(args.zmemo, args.bmemo, args.bvmemo, U());

		if (cs_elim_index && memo.find(*cs_elim_index) != memo.end()) {
			return memo[*cs_elim_index];
		}

		std::vector <z_class> zargs_s(zargs.size());
		std::vector <bool> bargs_s(bargs.size());
		std::vector <bv> bvargs_s(bvargs.size());

		for (size_t i = 0; i < zargs.size(); i++) {
			zargs_s[i] = zargs[i] -> eval(asubst, bsubst, bvsubst, args);
		}
		for (size_t i = 0; i < bargs.size(); i++) {
			bargs_s[i] = bargs[i] -> eval(asubst, bsubst, bvsubst, args);
		}
		for (size_t i = 0; i < bvargs.size(); i++) {
			bvargs_s[i] = bvargs[i] -> eval(asubst, bsubst, bvsubst, args);
		}

		U ans = nonstd::get(asubst, bsubst, bvsubst, U())(x) ->
			eval(zargs_s, bargs_s, bvargs_s);

		if (cs_elim_index) {
			memo[*cs_elim_index] = ans;
		}

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

		std::vector <std::vector <z_class>> zargs_s(zargs.size());
		std::vector <std::vector <bool>> bargs_s(bargs.size());
		std::vector <std::vector <bv>> bvargs_s(bvargs.size());

		std::transform(zargs.begin(), zargs.end(), zargs_s.begin(),
			[&](const afexpr_p& e) -> std::vector <z_class> {
				return e -> eval(asubst, bsubst, bvsubst,
					aval, bval, bvval, n, amemo, bmemo, bvmemo);
			});
		std::transform(bargs.begin(), bargs.end(), bargs_s.begin(),
			[&](const bfexpr_p& e) -> std::vector <bool> {
				return e -> eval(asubst, bsubst, bvsubst,
					aval, bval, bvval, n, amemo, bmemo, bvmemo);
			});
		std::transform(bvargs.begin(), bvargs.end(), bvargs_s.begin(),
			[&](const bvfexpr_p& e) -> std::vector <bv> {
				return e -> eval(asubst, bsubst, bvsubst,
					aval, bval, bvval, n, amemo, bmemo, bvmemo);
			});

		std::vector <U> ans(nonstd::get(asubst, bsubst, bvsubst, U())(x) ->
			eval(idfunc(zargs_s, false), idfunc(bargs_s, false),
				idfunc(bvargs_s, false), n));

		if (cs_elim_index) {
			memo[*cs_elim_index] = ans;
		}

		return ans;
	}

	virtual feU_p fsubst(const typename feU::afsubst_t& afsubst,
			const typename feU::bfsubst_t& bfsubst,
			const typename feU::bvfsubst_t& bvfsubst) const {
		std::vector <afexpr_p> zargs_p(zargs);
		std::vector <bfexpr_p> bargs_p(bargs);
		std::vector <bvfexpr_p> bvargs_p(bvargs);

		std::transform(zargs.begin(), zargs.end(), zargs_p.begin(),
			[&](const afexpr_p& fe) -> afexpr_p {
				return fe -> fsubst(afsubst, bfsubst, bvfsubst);
			});
		std::transform(bargs.begin(), bargs.end(), bargs_p.begin(),
			[&](const bfexpr_p& fe) -> bfexpr_p {
				return fe -> fsubst(afsubst, bfsubst, bvfsubst);
			});
		std::transform(bvargs.begin(), bvargs.end(), bvargs_p.begin(),
			[&](const bvfexpr_p& fe) -> bvfexpr_p {
				return fe -> fsubst(afsubst, bfsubst, bvfsubst);
			});

		return feU_p(new fcall <U> (x, zargs_p, bargs_p, bvargs_p));
	}

	virtual void cs_elim(std::map <std::string, size_t>& amemo,
			std::map <std::string, size_t>& bmemo,
			std::map <std::string, size_t>& bvmemo) const {
		for (auto& e : zargs) {
			e -> cs_elim(amemo, bmemo, bvmemo);
		}
		for (auto& e : bargs) {
			e -> cs_elim(amemo, bmemo, bvmemo);
		}
		for (auto& e : bvargs) {
			e -> cs_elim(amemo, bmemo, bvmemo);
		}

		std::string me = boost::lexical_cast <std::string> (*this);
		auto& memo = nonstd::get(amemo, bmemo, bvmemo, U());
		if (memo.find(me) == memo.end()) {
			size_t v = memo.size();
			memo[me] = v;
		}

		cs_elim_index = memo[me];
	}

	virtual size_t size() const {
		std::vector <size_t> zargs_s(zargs.size());
		std::vector <size_t> bargs_s(bargs.size());
		std::vector <size_t> bvargs_s(bvargs.size());

		std::transform(zargs.begin(), zargs.end(), zargs_s.begin(),
			[](const afexpr_p& e) {
				return e -> size();
			});
		std::transform(bargs.begin(), bargs.end(), bargs_s.begin(),
			[](const bfexpr_p& e) {
				return e -> size();
			});
		std::transform(bvargs.begin(), bvargs.end(), bvargs_s.begin(),
			[](const bvfexpr_p& e) {
				return e -> size();
			});

		size_t ans = std::accumulate(zargs_s.begin(), zargs_s.end(), 1);
		ans = std::accumulate(bargs_s.begin(), bargs_s.end(), ans);
		ans = std::accumulate(bvargs_s.begin(), bvargs_s.end(), ans);
		return ans;
	}

	virtual feU_p deep_copy() const {
		return feU_p(new this_t(x, zargs, bargs, bvargs));
	}

	id x;
	zargs_v_t zargs;
	bargs_v_t bargs;
	bvargs_v_t bvargs;
	mutable boost::optional <size_t> cs_elim_index;
};

}

#endif // __FEXPR_INFR_VAR_H_

