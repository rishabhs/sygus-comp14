#ifndef __EXPR_SEARCH_H_
#define __EXPR_SEARCH_H_

#include <algorithm>
#include <cassert>
#include <map>
#include <memory>
#include <random>
#include <vector>

#include <boost/lexical_cast.hpp>
#include <boost/optional.hpp>
#include <z3++.h>

#include "nonstd/nonfunctional.h"
#include "expr.h"
#include "fexpr.h"
#include "grammar.h"

#include "expr_search/expr_search_infr.h"

namespace stoch
{

template <typename U>
bool smt_check(bfexpr_p spec, std::shared_ptr <const expr <U>> proposal,
               std::vector <std::vector <z_class>>& zconcrete,
               std::vector <std::vector <bool>>& bconcrete,
               std::vector <std::vector <bv>>& bvconcrete, size_t& nconcrete,
               size_t nz, size_t nb, const std::vector <size_t>& nbv)
{
    typedef expr <U> eU;
    typedef std::shared_ptr <const eU> eU_p;

    z3::context ctxt;
    z3::solver slvr(ctxt);

    std::vector <eU_p> prop_v {proposal};
    std::vector <aexpr_p> aexpr_p_v;
    std::vector <bexpr_p> bexpr_p_v;
    std::vector <bvexpr_p> bvexpr_p_v;

    auto asubst = idfunc(nonstd::get(prop_v, aexpr_p_v, aexpr_p_v, U()), false);
    auto bsubst = idfunc(nonstd::get(bexpr_p_v, prop_v, bexpr_p_v, U()), false);
    auto bvsubst = idfunc(nonstd::get(bvexpr_p_v, bvexpr_p_v, prop_v, U()), false);

    auto claim = spec -> subst(asubst, bsubst, bvsubst);

    slvr.add(!claim -> smt(ctxt));
    if (slvr.check() != z3::check_result::unsat)
    {
        z3::model model = slvr.get_model();

        std::vector <z_class> zex(nz);
        std::vector <bool> bex(nb);
        std::vector <bv> bvex(nbv.size());

        for (size_t i = 0; i < nz; i++)
        {
            aexpr_p xi(new zvar(i));
            z3::expr exi = xi -> smt(ctxt);
            auto vxi_s = Z3_get_numeral_string(ctxt, model.eval(exi, true));
            z_class vxi = boost::lexical_cast <z_class> (vxi_s);
            std::cout << vxi << " ";
            zex[i] = vxi;
        }
        for (size_t i = 0; i < nb; i++)
        {
            bexpr_p bi(new bvar(i));
            z3::expr ebi = bi -> smt(ctxt);
            bool vbi = (Z3_get_bool_value(ctxt, model.eval(ebi, true)) == Z3_L_TRUE);
            std::cout << vbi << " ";
            bex[i] = vbi;
        }
        for (size_t i = 0; i < nbv.size(); i++)
        {
            bvexpr_p bvi(new bvvar(i, nbv[i]));
            z3::expr ebvi = bvi -> smt(ctxt);
            model.eval(ebvi, true);
            std::string bvexi_s(Z3_ast_to_string(ctxt, model.eval(ebvi, true)));
            bvex[i] = bv(bvexi_s);
            std::cout << bvex[i] << " ";
        }
        std::cout << std::endl;

        zconcrete.push_back(zex);
        bconcrete.push_back(bex);
        bvconcrete.push_back(bvex);
        nconcrete++;
        std::cout << __LOGSTR__ << "SMT Proposal: " << *proposal << std::endl;
        std::cout << __LOGSTR__ << "Counter-example added. " << nconcrete << std::endl;
    }

    return slvr.check() == z3::check_result::unsat;
}

template <typename U, typename D>
std::shared_ptr <const expr <U>> search(bfexpr_p spec, const grammar& g,
                                        const gsymb_t <U>& S, size_t nz_free, size_t nb_free, const std::vector <size_t>& nbv,
                                        size_t expr_size, double beta, D& rndm_dev, size_t n_seed, size_t n_iter)
{
    typedef expr <U> eU;
    typedef std::shared_ptr <const eU> eU_p;

    grammar_sample gs(g);
    std::uniform_real_distribution <double> distr01(0, 1);

    std::vector <std::vector <z_class>> zconcrete;
    std::vector <std::vector <bool>> bconcrete;
    std::vector <std::vector <bv>> bvconcrete;
    populate(zconcrete, bconcrete, bvconcrete, nz_free, nb_free, nbv, n_seed, rndm_dev);

    production <U> candidate = small_production(gs, S, expr_size, rndm_dev);
    eU_p cp = candidate.produce();
    std::cout << __LOGSTR__ << "Proposal: " << *cp << std::endl;

    size_t nconcrete = n_seed;
    size_t candidate_score = score(spec, cp, zconcrete, bconcrete, bvconcrete, nconcrete);
    size_t hi_score = candidate_score;
    std::cout << __LOGSTR__ << "Initial candidate scores " << candidate_score << std::endl;

    spec -> cs_elim();

    size_t n_mutations = 0, n_generations = 0;
    while (true)
    {
        if (candidate_score == nconcrete)
        {
            if (smt_check(spec, candidate.produce(), zconcrete,
                          bconcrete, bvconcrete, nconcrete, nz_free, nb_free, nbv))
            {
                break;
            }
            else
            {
                // SMT check failed. Debug point.
                /* print_concrete(zconcrete, bconcrete, bvconcrete,
                	spec, candidate.produce()); */
            }
        }
        else
        {
            double logp = log(distr01(rndm_dev));
            size_t nslack = nconcrete - candidate_score - (logp / beta);

            auto mutant = mutate(candidate, gs, rndm_dev);
            auto m_prop = mutant.produce();
            auto mutant_score = score(spec, m_prop, zconcrete,
                                      bconcrete, bvconcrete, nconcrete, nslack);

            if (mutant_score > hi_score)
            {
                hi_score = mutant_score;
                std::cout << __LOGSTR__ << "High score ("
                          << hi_score << "): " << *m_prop << std::endl;
            }

            // std::cout << __LOGSTR__ << *m_prop << " --- " << mutant_score << std::endl;

            if (mutant_score > 0 || candidate_score == 0)
            {
                candidate = mutant;
                candidate_score = mutant_score;
                n_generations++;
                if (n_generations && !(n_generations & (n_generations - 1)))
                {
                    std::cout << __LOGSTR__	<< n_generations << "/" << n_mutations << std::endl;
                }
            }
            else
            {
                // std::cout << __LOGSTR__ << " Mutant rejected!" << std::endl;
            }
            n_mutations++;
            if (n_mutations && !(n_mutations & (n_mutations - 1)))
            {
                std::cout << __LOGSTR__ << n_generations << "/" << n_mutations << std::endl;
            }

            if (n_mutations >= n_iter)
            {
                std::cout << __LOGSTR__
                          << "Iteration count reached. Exiting unsuccessfully." << std::endl;
                return eU_p();
            }
        }
    }

    std::cout << __LOGSTR__ << "Solution found after examining " << n_mutations
              << " mutations over " << n_generations << " generations." << std::endl;
    return candidate.produce();
}

} // namespace stoch

#endif // __EXPR_SEARCH_H_
