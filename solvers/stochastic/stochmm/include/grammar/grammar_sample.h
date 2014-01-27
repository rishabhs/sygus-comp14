#ifndef __GRAMMAR_SAMPLE_H_
#define __GRAMMAR_SAMPLE_H_

#include <algorithm>
#include <functional>
#include <map>
#include <random>
#include <tuple>
#include <vector>

#include <boost/none.hpp>
#include <boost/optional.hpp>

#include "grammar_infr.h"

namespace stoch {

struct grammar_sample;

template <typename U, typename D>
std::shared_ptr <production <U>> sample(grammar_sample& gs, const gsymb_t <U>& S,
	size_t n, D& rndm_dev);

template <typename U, typename D>
production <U> mutate(const production <U>& p, grammar_sample& gs, D& rndm_dev);

template <typename U, typename D>
std::tuple <bool, size_t> get_prod(grammar_sample& gs, const gsymb_t <U>& S,
	size_t n, D& rndm_dev);
template <typename U, typename D>
std::vector <size_t> get_split(grammar_sample& gs, const gsymb_t <U>& S, size_t j,
	size_t n, D& rndm_dev);

struct grammar_sample {
	grammar_sample(const grammar& g) : g(g) {};

	template <typename U>
	std::vector <size_t>& get_f(const gsymb_t <U>& S, size_t n);
	template <typename U>
	std::vector <size_t>& get_fp(const gsymb_t <U>& S, size_t j, size_t k, size_t n);

	// f(a/b/bv)[S][n][j] is the number of strings of length [n] produced by
	// the [j]th production rule of symbol [S]
	typedef std::tuple <agsymb_t, size_t> faindex_t;
	typedef std::tuple <bgsymb_t, size_t> fbindex_t;
	typedef std::tuple <bvgsymb_t, size_t> fbvindex_t;
	std::map <faindex_t, std::vector <size_t>> fa;
	std::map <fbindex_t, std::vector <size_t>> fb;
	std::map <fbvindex_t, std::vector <size_t>> fbv;

	// fp(a/b/bv)[S][j][k][n][l]: Consider the [j]th production for symbol [S].
	// Consider non-terminals [k], [k + 1], ... in this production. Assuming
	// non-terminal [k] evaluates to [l] symbols, and the remaining evaluate
	// to [n - l] symbols, in how many ways can this happen?
	typedef std::tuple <agsymb_t, size_t, size_t, size_t> fpaindex_t;
	typedef std::tuple <bgsymb_t, size_t, size_t, size_t> fpbindex_t;
	typedef std::tuple <bvgsymb_t, size_t, size_t, size_t> fpbvindex_t;
	std::map <fpaindex_t, std::vector <size_t>> fpa;
	std::map <fpbindex_t, std::vector <size_t>> fpb;
	std::map <fpbvindex_t, std::vector <size_t>> fpbv;

	// The following contain memoized random distributions
	std::map <faindex_t, std::discrete_distribution <size_t>> fa_distr;
	std::map <fbindex_t, std::discrete_distribution <size_t>> fb_distr;
	std::map <fbvindex_t, std::discrete_distribution <size_t>> fbv_distr;
	std::map <fpaindex_t, std::discrete_distribution <size_t>> fpa_distr;
	std::map <fpbindex_t, std::discrete_distribution <size_t>> fpb_distr;
	std::map <fpbvindex_t, std::discrete_distribution <size_t>> fpbv_distr;

	const grammar& g;
};

template <typename U>
std::vector <size_t>& grammar_sample::get_f(const gsymb_t <U>& S, size_t n) {
	auto& f = nonstd::get(fa, fb, fbv, U());
	auto& rule = nonstd::get(g.arules, g.brules, g.bvrules, U())(S);
	std::tuple <gsymb_t <U>, size_t> indx(S, n);

	auto it = f.find(indx);
	if (it != f.end()) {
		return it -> second;
	}

	f[indx] = std::vector <size_t> (rule.size(), 0);

	if (n == 1) {
		std::transform(rule.begin(), rule.end(), f[indx].begin(),
			[](const prod_rule <U>& p) -> size_t {
				return p.achild_v.empty() && p.bchild_v.empty()
					&& p.bvchild_v.empty() ? 1 : 0;
			});
	} else if (n > 1) {
		for (size_t j = 0; j < rule.size(); j++) {
			auto& v = get_fp(S, j, 0, n - 1);
			f[indx][j] = std::accumulate(v.begin(), v.end(), 0);
		}
	}

	return f[indx];
}

template <typename U>
std::vector <size_t>& grammar_sample::get_fp(const gsymb_t <U>& S, size_t j, size_t k, size_t n) {
	auto& fp = nonstd::get(fpa, fpb, fpbv, U());
	auto& rule = nonstd::get(g.arules, g.brules, g.bvrules, U())(S);
	std::tuple <gsymb_t <U>, size_t, size_t, size_t> indx(S, j, k, n);

	auto it = fp.find(indx);
	if (it != fp.end()) {
		return it -> second;
	}

	const prod_rule <U>& p = rule[j];
	fp[indx] = std::vector <size_t> ();
	size_t tSj = p.achild_v.size() + p.bchild_v.size() + p.bvchild_v.size();

	if (k < tSj && tSj <= n + k + 1) {
		for (size_t l = 0; l <= n + k + 1 - tSj; l++) {
			size_t fSjkl = 0;
			if (k < p.achild_v.size()) {
				auto& v = get_f(p.achild_v[k], l);
				fSjkl = std::accumulate(v.begin(), v.end(), 0);
			} else if (k - p.achild_v.size() < p.bchild_v.size()) {
				auto& v = get_f(p.bchild_v[k - p.achild_v.size()], l);
				fSjkl = std::accumulate(v.begin(), v.end(), 0);
			} else if (k - p.achild_v.size() - p.bchild_v.size() < p.bvchild_v.size()) {
				auto& v = get_f(p.bvchild_v[k - p.achild_v.size() - p.bchild_v.size()], l);
				fSjkl = std::accumulate(v.begin(), v.end(), 0);
			}

			if (k + 1 == tSj) {
				fp[indx].push_back(n == l ? fSjkl : 0);
			} else {
				auto& v = get_fp(S, j, k + 1, n - l);
				fp[indx].push_back(fSjkl * std::accumulate(v.begin(), v.end(), 0));
			}
		}
	}

	return fp[indx];
}

template <typename U, typename D>
std::tuple <bool, size_t> get_prod(grammar_sample& gs, const gsymb_t <U>& S,
	size_t n, D& rndm_dev) {
	std::tuple <gsymb_t <U>, size_t> indx(S, n);
	auto& v = gs.get_f(S, n);
	const auto is_positive = [](size_t v) -> bool { return v > 0; };

	auto& f_distr = nonstd::get(gs.fa_distr, gs.fb_distr, gs.fbv_distr, U());
	if (f_distr.find(indx) == f_distr.end()) {
		f_distr[indx] = std::discrete_distribution <size_t> (v.begin(), v.end());
	}

	bool ans1 = (find_if(v.begin(), v.end(), is_positive) != v.end());
	size_t ans2 = f_distr[indx](rndm_dev);
	return std::tuple <bool, size_t> (ans1, ans2);
}

template <typename U, typename D>
std::vector <size_t> get_split(grammar_sample& gs, const gsymb_t <U>& S,
	size_t j, size_t n, D& rndm_dev) {
	std::vector <size_t> ans;
	auto& p = nonstd::get(gs.g.arules, gs.g.brules, gs.g.bvrules, U())(S)[j];
	size_t tSj = p.achild_v.size() + p.bchild_v.size() + p.bvchild_v.size();

	for (size_t k = 0; k < tSj; k++) {
		std::tuple <gsymb_t <U>, size_t, size_t, size_t> indx(S, j, k, n);
		auto& fp_distr = nonstd::get(gs.fpa_distr, gs.fpb_distr, gs.fpbv_distr, U());
		if (fp_distr.find(indx) == fp_distr.end()) {
			auto& v = gs.get_fp(S, j, k, n);
			fp_distr[indx] = std::discrete_distribution <size_t> (v.begin(), v.end());
		}
		size_t l = fp_distr[indx](rndm_dev);
		ans.push_back(l);
		n = n - l;
	}

	return ans;
}

template <typename U, typename D>
std::shared_ptr <production <U>> sample(grammar_sample& gs, const gsymb_t <U>& S,
	size_t n, D& rndm_dev) {
	typedef production <U> prU;

	bool prod_exists;
	size_t j;
	std::tie (prod_exists, j) = get_prod(gs, S, n, rndm_dev);

	if (!prod_exists) {
		return std::shared_ptr <prU> ();
	}

	auto& p = nonstd::get(gs.g.arules, gs.g.brules, gs.g.bvrules, U())(S)[j];
	std::vector <typename prU::prodnz_p> achild_v;
	std::vector <typename prU::prodnb_p> bchild_v;
	std::vector <typename prU::prodnbv_p> bvchild_v;

	if (n > 1) {
		std::vector <size_t> split = get_split(gs, S, j, n - 1, rndm_dev);

		for (size_t k = 0; k < p.achild_v.size(); k++) {
			achild_v.push_back(sample(gs, p.achild_v[k],
				split[k], rndm_dev));
		}
		for (size_t k = 0; k < p.bchild_v.size(); k++) {
			bchild_v.push_back(sample(gs, p.bchild_v[k],
				split[k + p.achild_v.size()], rndm_dev));
		}
		for (size_t k = 0; k < p.bvchild_v.size(); k++) {
			bvchild_v.push_back(sample(gs, p.bvchild_v[k],
				split[k + p.achild_v.size() + p.bchild_v.size()], rndm_dev));
		}
	}

	return std::shared_ptr <prU> (new prU(S, &p, achild_v, bchild_v, bvchild_v));
}

template <typename U, typename D>
production <U> mutate(const production <U>& p, grammar_sample& gs, D& rndm_dev) {
	typedef production <U> prU;

	p.expr_memo.reset();

	auto& achild_v = p.achild_v;
	auto& bchild_v = p.bchild_v;
	auto& bvchild_v = p.bvchild_v;

	size_t tSj = achild_v.size() + bchild_v.size() + bvchild_v.size();
	std::vector <size_t> child_size(tSj);
	std::transform(achild_v.begin(), achild_v.end(), child_size.begin(),
		[](const typename prU::prodnz_p& p) {
			return p -> size();
		});
	std::transform(bchild_v.begin(), bchild_v.end(),
		child_size.begin() + achild_v.size(),
		[](const typename prU::prodnb_p& p) {
			return p -> size();
		});
	std::transform(bvchild_v.begin(), bvchild_v.end(),
		child_size.begin() + achild_v.size() + bchild_v.size(),
		[](const typename prU::prodnbv_p& p) {
			return p -> size();
		});
	child_size.push_back(1);

	size_t n = std::accumulate(child_size.begin(), child_size.end(), 0);
	std::discrete_distribution <size_t> distr(child_size.begin(), child_size.end());
	size_t mutation_point = distr(rndm_dev);

	if (mutation_point == tSj) {
		return *sample(gs, p.s, n, rndm_dev);
	} else if (mutation_point < achild_v.size()) {
		prU ans(p.s, p.prod, achild_v, bchild_v, bvchild_v);
		aprodn change(mutate(*ans.achild_v[mutation_point], gs, rndm_dev));
		ans.achild_v[mutation_point] = std::shared_ptr <aprodn> (new aprodn(change));
		return ans;
	} else if (mutation_point - achild_v.size() < bchild_v.size()) {
		size_t index = mutation_point - achild_v.size();
		prU ans(p.s, p.prod, achild_v, bchild_v, bvchild_v);
		bprodn change(mutate(*ans.bchild_v[index], gs, rndm_dev));
		ans.bchild_v[index] = std::shared_ptr <bprodn> (new bprodn(change));
		return ans;
	} else {
		size_t index = mutation_point - achild_v.size() - bchild_v.size();
		prU ans(p.s, p.prod, achild_v, bchild_v, bvchild_v);
		bvprodn change(mutate(*ans.bvchild_v[index], gs, rndm_dev));
		ans.bvchild_v[index] = std::shared_ptr <bvprodn> (new bvprodn(change));
		return ans;
	}
}

template <typename U, typename D>
production <U> small_production(grammar_sample& gs, const gsymb_t <U>& S,
		size_t& n, D& rndm_dev) {
	auto optional_candidate = sample(gs, S, n, rndm_dev);
	while (!optional_candidate) {
		n++;
		optional_candidate = sample(gs, S, n, rndm_dev);
	}
	return *optional_candidate;
}

} // namespace stoch

#endif // __GRAMMAR_SAMPLE_H_

