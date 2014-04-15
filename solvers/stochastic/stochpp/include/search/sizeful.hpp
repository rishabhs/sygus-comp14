#ifndef __SEARCH_SIZEFUL_HPP_
#define __SEARCH_SIZEFUL_HPP_

#include "search.hpp"

namespace stoch {

template <typename D>
boost::optional <subst_t> sizeful_search(bfexpr_p spec,
    const map <id, tuple <grammar, agsymb_t>>& afuns,
    const map <id, tuple <grammar, bgsymb_t>>& bfuns,
    const map <id, tuple <grammar, bvgsymb_t>>& bvfuns,
    const set <id>& zfree, const set <id>& bfree, const set <tuple <id, size_t>>& bvfree,
    size_t expr_size, double beta, size_t nseed, size_t niter, D& rndm_dev)
{
    grammar g;
    agsymb_t start;
    vector <id> afun_v, bfun_v, bvfun_v;

    tie(g, start, afun_v, bfun_v, bvfun_v) = combine(afuns, bfuns, bvfuns);

    grammar_sample gs(g);
    auto initial_candidate = sample(gs, start, expr_size, rndm_dev);

    if (initial_candidate) {
        search_state state(spec, nseed, zfree, bfree, bvfree, *initial_candidate,
            afun_v, bfun_v, bvfun_v, rndm_dev);
        return sizeful_search(spec, zfree, bfree, bvfree, gs, start, state,
            beta, niter, rndm_dev);
    }

    return boost::none;
}

template <typename D>
boost::optional <subst_t> sizeful_search(bfexpr_p spec,
    const set <id>& zfree, const set <id>& bfree, const set <tuple <id, size_t>>& bvfree,
    grammar_sample& gs, agsymb_t& start, search_state& state, double beta, size_t niter,
    D& rndm_dev)
{
    assert (0 <= beta);

    std::uniform_real_distribution <double> distr01(0, 1);

    for (size_t i = 0; i < niter; i++) {
        if (state.candidate_score == state.cex_s.size()) {
            if (auto cex = smt_check(spec, state.produce(), zfree, bfree, bvfree)) {
                // SMT check produced counterexample. Debug point.
                state.cex_s.push_back(*cex);
            } else {
                *streams.log << __LOGSTR__ << "Solution found after processing "
                    << state.nmutations << " mutations and " << state.ngenerations
                    << " generations at expression size " << state.candidate.size() << endl;
                print_subst(*streams.log, state.produce());
                return state.produce();
            }
        }

        double logp = log(distr01(rndm_dev));
        size_t nslack = state.cex_s.size() - state.candidate_score - (logp / beta);

        auto mutant = mutate(state.candidate, gs, rndm_dev);
        auto m_prop = uncombine(mutant, state.afun_v, state.bfun_v, state.bvfun_v);
        size_t mutant_score = score(spec, m_prop, state.cex_s, nslack);

        if (mutant_score > state.hi_score) {
            state.hi_score = mutant_score;
            *streams.log << __LOGSTR__ << "High score (" << state.hi_score << "): ";
            print_subst(*streams.log, m_prop);
        }

        // *streams.log << __LOGSTR__ << *m_prop << " --- " << mutant_score << endl;

        if (mutant_score > 0 || state.candidate_score == 0) {
            state.candidate = mutant;
            state.candidate_score = mutant_score;
            state.ngenerations++;

            if (state.ngenerations && !(state.ngenerations & (state.ngenerations - 1))) {
                *streams.log << __LOGSTR__ << state.ngenerations << "/" << state.nmutations << endl;
            }
        } else {
            // *streams.log << __LOGSTR__ << " Mutant rejected!" << endl;
        }

        state.nmutations++;
        if (state.nmutations && !(state.nmutations & (state.nmutations - 1))) {
            *streams.log << __LOGSTR__ << state.ngenerations << "/" << state.nmutations << endl;
        }
    }

    *streams.log << __LOGSTR__ << "Iteration count reached. Exiting unsuccessfully." << endl;
    return boost::none;
}

} // namespace stoch

#endif // __SEARCH_SIZEFUL_HPP_
