#ifndef __SEARCH_SIZEFREE_HPP_
#define __SEARCH_SIZEFREE_HPP_

#include "search.hpp"
#include "search/sizeful.hpp"

namespace stoch {

template <typename D>
boost::optional <subst_t> sizefree_search(bfexpr_p spec,
    const map <id, tuple <grammar, agsymb_t>>& afuns,
    const map <id, tuple <grammar, bgsymb_t>>& bfuns,
    const map <id, tuple <grammar, bvgsymb_t>>& bvfuns,
    const set <id>& zfree, const set <id>& bfree, const set <tuple <id, size_t>>& bvfree,
    double move_probability, double beta, size_t nseed, size_t niter, D& rndm_dev)
{
    assert (0 <= move_probability && move_probability <= 1);
    assert (0 <= beta);

    grammar g;
    agsymb_t start;
    vector <id> afun_v, bfun_v, bvfun_v;

    tie(g, start, afun_v, bfun_v, bvfun_v) = combine(afuns, bfuns, bvfuns);
    g.print(*streams.log << __LOGSTR__ << "Printing combined grammar!" << endl);

    grammar_sample gs(g);
    uniform_real_distribution <double> distr01(0, 1);
    geometric_distribution <size_t> distr_move(move_probability);

    vector <search_state> state_memo;
    size_t expr_size = 0;

    for (size_t nmutations = 0; nmutations < niter;) {
        if (expr_size == 0 || distr01(rndm_dev) <= 0.5) {
            expr_size++;
        } else {
            expr_size--;
        }

        while (state_memo.size() <= expr_size) {
            aprodn_p candidate = small_production(gs, start, expr_size, rndm_dev);
            state_memo.push_back(search_state(spec, nseed, zfree, bfree, bvfree,
                *candidate, afun_v, bfun_v, bvfun_v, rndm_dev));
        }

        *streams.log << __LOGSTR__ << "Proceeding to expression size: " << expr_size << endl;

        size_t size_iter = distr_move(rndm_dev);
        auto search_ans = sizeful_search(spec, zfree, bfree, bvfree, gs, start,
            state_memo[expr_size], beta, size_iter, rndm_dev);
        nmutations += size_iter;

        if (search_ans) {
            *streams.log << __LOGSTR__ << "Solution found after processing "
                << nmutations << " iterations." << endl << state_memo[expr_size].nmutations
                << " mutations and " << state_memo[expr_size].ngenerations
                << " generations processed at expression size " << expr_size << endl;
            print_subst(*streams.log, *search_ans);
            return search_ans;
        }
    }

    return boost::none;
}

} // namespace stoch

#endif // __SEARCH_SIZEFREE_HPP_

