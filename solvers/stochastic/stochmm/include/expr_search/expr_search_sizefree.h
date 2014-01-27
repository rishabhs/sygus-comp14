#ifndef __EXPR_SEARCH_SIZEFREE_H_
#define __EXPR_SEARCH_SIZEFREE_H_

#include "expr_search/expr_search_infr.h"

namespace stoch
{

template <typename U>
struct search_state
{
    typedef expr <U> eU;
    typedef std::shared_ptr <const eU> eU_p;

    template <typename D>
    search_state(bfexpr_p spec, size_t expr_size, size_t n_seed,
                 size_t nz_free, size_t nb_free, const std::vector <size_t>& nbv,
                 D& rndm_dev, grammar_sample& gs, const gsymb_t <U>& S,
                 const production <U>& candidate)
    : expr_size(expr_size), nconcrete(n_seed), n_mutations(0), n_generations(0),
      candidate(candidate)
    {
        populate(zconcrete, bconcrete, bvconcrete, nz_free, nb_free, nbv, n_seed, rndm_dev);

        eU_p cp = candidate.produce();
        candidate_score = score(spec, cp, zconcrete, bconcrete, bvconcrete, nconcrete);
        hi_score = candidate_score;

        std::cout << __LOGSTR__ << "Proposal(" << expr_size << "): " << *cp << std::endl;
        std::cout << __LOGSTR__ << "Initial cadidate(" << expr_size << ") scores " << candidate_score << std::endl;
    }

    size_t expr_size, nconcrete;
    size_t n_mutations, n_generations;

    std::vector <std::vector <z_class>> zconcrete;
    std::vector <std::vector <bool>> bconcrete;
    std::vector <std::vector <bv>> bvconcrete;

    production <U> candidate;
    size_t candidate_score, hi_score;
};

template <typename U, typename D>
std::shared_ptr <const expr <U>> sizefree_search(bfexpr_p spec, const grammar& g,
                                                 const gsymb_t <U>& S, size_t nz_free, size_t nb_free, const std::vector <size_t>& nbv,
                                                 double move_probability, double beta, D& rndm_dev, size_t n_seed, size_t n_iter)
{
    assert(0 <= move_probability && move_probability <= 1);
    assert(0 <= beta);

    typedef expr <U> eU;
    typedef std::shared_ptr <const eU> eU_p;

    grammar_sample gs(g);
    std::uniform_real_distribution <double> distr01(0, 1);

    std::vector <search_state <U>> state_memo;
    size_t expr_size = 0, n_mutations = 0;
    while (true)
    {
        if (distr01(rndm_dev) <= move_probability)
        {
            if (distr01(rndm_dev) <= 0.5)
            {
                ++expr_size;
            }
            else if (expr_size > 0)
            {
                --expr_size;
            }
            else
            {
                assert(expr_size == 0);
                ++expr_size;
            }
            std::cout << __LOGSTR__ << "Proceeding to expression size: " << expr_size << std::endl;
        }
        if (state_memo.size() <= expr_size)
        {
            size_t expr_size_p1 = 1 + expr_size;
            production <U> candidate = small_production(gs, S, expr_size_p1, rndm_dev);
            state_memo.push_back(search_state <U> (spec, expr_size_p1, n_seed,
                                                   nz_free, nb_free, nbv, rndm_dev,
                                                   gs, S, candidate));
        }

        search_state <U>& state = state_memo[expr_size];

        if (state.candidate_score == state.nconcrete)
        {
            if (smt_check(spec, state.candidate.produce(), state.zconcrete,
                          state.bconcrete, state.bvconcrete, state.nconcrete,
                          nz_free, nb_free, nbv))
            {
                std::cout << __LOGSTR__ << "Solution found after processing " << n_mutations << " mutations. "
                          << state.n_mutations << " mutations and "
                          << state.n_generations << " generations processed at size " << expr_size << "." << std::endl;
                return state.candidate.produce();
            }
            else
            {
                // SMT check failed. Debug point.
                /* print_concrete(state.zconcrete, state.bconcrete, state.bvconcrete,
                	spec, state.candidate.produce()); */
            }
        }
        else
        {
            double logp = log(distr01(rndm_dev));
            size_t nslack = state.nconcrete - state.candidate_score - (logp / beta);

            auto mutant = mutate(state.candidate, gs, rndm_dev);
            auto m_prop = mutant.produce();
            auto mutant_score = score(spec, m_prop, state.zconcrete,
                                      state.bconcrete, state.bvconcrete, state.nconcrete, nslack);

            if (mutant_score > state.hi_score)
            {
                state.hi_score = mutant_score;
                std::cout << __LOGSTR__ << "High score ("
                          << state.hi_score << ") @ size " << expr_size << ": " << *m_prop << std::endl;
            }

            // std::cout << __LOGSTR__ << *m_prop << " --- " << mutant_score << std::endl;

            if (mutant_score > 0 || state.candidate_score == 0)
            {
                state.candidate = mutant;
                state.candidate_score = mutant_score;
                state.n_generations++;
                if (state.n_generations && !(state.n_generations & (state.n_generations - 1)))
                {
                    std::cout << __LOGSTR__	<< "Size: " << expr_size << ". "
                              << state.n_generations << "/" << state.n_mutations << std::endl;
                }
            }
            else
            {
                // std::cout << __LOGSTR__ << " Mutant rejected!" << std::endl;
            }
            ++state.n_mutations;
            ++n_mutations;
            if (state.n_mutations && !(state.n_mutations & (state.n_mutations - 1)))
            {
                std::cout << __LOGSTR__ << state.n_generations << "/" << state.n_mutations << std::endl;
            }

            if (n_mutations >= n_iter)
            {
                std::cout << __LOGSTR__
                          << "Iteration count reached. Exiting unsuccessfully." << std::endl;
                return eU_p();
            }
        }
    }
}

} // namespace stoch

#endif // __EXPR_SEARCH_SIZEFREE_H_
