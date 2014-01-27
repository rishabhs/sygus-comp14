#ifndef __EXPR_SEARCH_INFR_H_
#define __EXPR_SEARCH_INFR_H_

#include <random>

#include "expr_search.h"

namespace stoch {

template <typename U>
size_t score(bfexpr_p spec, std::shared_ptr <const expr <U>> proposal,
		const std::vector <std::vector <z_class>>& aval,
		const std::vector <std::vector <bool>>& bval,
		const std::vector <std::vector <bv>>& bvval,
		size_t nval, size_t nslack = -1);

template <typename D>
void populate(std::vector <std::vector <z_class>>& zconcrete,
		std::vector <std::vector <bool>>& bconcrete,
		std::vector <std::vector <bv>>& bvconcrete,
		size_t nz, size_t nb, const std::vector <size_t>& nbv,
		size_t nsamples, D& rndm_dev);

size_t number_eval = 0;

template <typename U>
size_t score(bfexpr_p spec, std::shared_ptr <const expr <U>> proposal,
		const std::vector <std::vector <z_class>>& aval,
		const std::vector <std::vector <bool>>& bval,
		const std::vector <std::vector <bv>>& bvval,
		size_t nval, size_t nslack) {
	typedef expr <U> eU;
	typedef std::shared_ptr <const eU> eU_p;

	std::vector <eU_p> prop_v {proposal};
	std::vector <aexpr_p> aexpr_p_v;
	std::vector <bexpr_p> bexpr_p_v;
	std::vector <bvexpr_p> bvexpr_p_v;

	auto asubst = idfunc(nonstd::get(prop_v, aexpr_p_v, aexpr_p_v, U()), false);
	auto bsubst = idfunc(nonstd::get(bexpr_p_v, prop_v, bexpr_p_v, U()), false);
	auto bvsubst = idfunc(nonstd::get(bvexpr_p_v, bvexpr_p_v, prop_v, U()), false);

	size_t score = 0, fail = 0;
	for (size_t i = 0; i < nval; i++) {
		std::map <size_t, z_class> zmemo;
		std::map <size_t, bool> bmemo;
		std::map <size_t, bv> bvmemo;

		leval_args_t args(aval[i], bval[i], bvval[i], zmemo, bmemo, bvmemo);
		number_eval++;

		if (spec -> eval(asubst, bsubst, bvsubst, args)) {
			score++;
		} else {
			fail++;
		}

		if (fail > nslack) {
			return 0;
		}
	}

	return score;
}

template <typename D>
void populate(std::vector <std::vector <z_class>>& zconcrete,
		std::vector <std::vector <bool>>& bconcrete,
		std::vector <std::vector <bv>>& bvconcrete,
		size_t nz, size_t nb, const std::vector <size_t>& nbv,
		size_t nsamples, D& rndm_dev) {
	for (size_t i = 0; i < nsamples; i++) {
		std::vector <z_class> zex(nz);
		std::vector <bool> bex(nb);
		std::vector <bv> bvex(nbv.size());

		for (size_t i = 0; i < nz; i++) {
			std::uniform_int_distribution <int> distr(-10, 10);
			zex[i] = distr(rndm_dev);
		}

		for (size_t i = 0; i < nb; i++) {
			std::uniform_int_distribution <int> distr(0, 1);
			bex[i] = (distr(rndm_dev) == 1);
		}

		for (size_t i = 0; i < nbv.size(); i++) {
			bvex[i] = bv(nbv[i], 0);
			assert(typeid(bv) == typeid(small_bv));
			size_t distr_max = bvex[i].mask().x;
			std::uniform_int_distribution <small_bv::unsigned_t> distr(0, distr_max);
			bvex[i].x = distr(rndm_dev);
			/* for (size_t j = 0; j < nbv[i]; j++) {
				std::uniform_int_distribution <int> distr(0, 1);
				bvex[i] = bv_set_bit(bvex[i], j, distr(rndm_dev) == 1);
			} */
		}

		zconcrete.push_back(zex);
		bconcrete.push_back(bex);
		bvconcrete.push_back(bvex);
	}
}

template <typename U>
void print_concrete(const std::vector <std::vector <z_class>>& zconcrete,
		const std::vector <std::vector <bool>>& bconcrete,
		const std::vector <std::vector <bv>>& bvconcrete,
		bfexpr_p spec, std::shared_ptr <const expr <U>> proposal) {
	typedef expr <U> eU;
	typedef std::shared_ptr <const eU> eU_p;

	for (size_t i = 0; i < bvconcrete.size(); i++) {
		std::cout << __LOGSTR__;
		for (size_t j = 0; j < zconcrete[i].size(); j++) {
			std::cout << zconcrete[i][j] << " ";
		}
		for (size_t j = 0; j < bconcrete[i].size(); j++) {
			std::cout << bconcrete[i][j] << " ";
		}
		for (size_t j = 0; j < bvconcrete[i].size(); j++) {
			std::cout << bvconcrete[i][j] << " ";
		}

		std::vector <eU_p> prop_v {proposal};
		std::vector <aexpr_p> aexpr_p_v;
		std::vector <bexpr_p> bexpr_p_v;
		std::vector <bvexpr_p> bvexpr_p_v;

		auto asubst = idfunc(nonstd::get(prop_v, aexpr_p_v, aexpr_p_v, U()), false);
		auto bsubst = idfunc(nonstd::get(bexpr_p_v, prop_v, bexpr_p_v, U()), false);
		auto bvsubst = idfunc(nonstd::get(bvexpr_p_v, bvexpr_p_v, prop_v, U()), false);

		std::map <size_t, z_class> zmemo;
		std::map <size_t, bool> bmemo;
		std::map <size_t, bv> bvmemo;

		leval_args_t args(zconcrete[i], bconcrete[i], bvconcrete[i], zmemo, bmemo, bvmemo);

		/* if (condition) {
			verbose_mode = true;
		} */

		std::cout << spec -> eval(asubst, bsubst, bvsubst, args) << std::endl;

		verbose_mode = false;
	}

}

} // namespace stoch

#include "expr_search_sizefree.h"

#endif // __EXPR_SEARCH_H_
