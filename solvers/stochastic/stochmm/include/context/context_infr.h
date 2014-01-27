#ifndef __CONTEXT_INFR_H_
#define __CONTEXT_INFR_H_

#include <algorithm>
#include <cassert>
#include <cstdlib>
#include <functional>
#include <random>
#include <string>
#include <vector>

#include <boost/lexical_cast.hpp>
#include <boost/optional.hpp>

#include "parser/iface.h"
#include "context.h"

namespace stoch
{
namespace context
{

std::string parse_loc(const sl2p::ASTBase *b)
{
    return std::string("At line ") + boost::lexical_cast <std::string> (b -> LineNum)
           + std::string(", column ") + boost::lexical_cast <std::string> (b -> ColNum)
           + ". ";
}

std::string to_string(const sort& s)
{
    switch (s.sc)
    {
    case sort_class::Integer:
    {
        return "Int";
    }
    case sort_class::Boolean:
    {
        return "Bool";
    }
    case sort_class::BV:
    {
        return std::string("BV") + boost::lexical_cast <std::string> (s.len);
    }
    default:
    {
        assert(false);
    }
    }
}

std::string to_string(const std::vector <sort>& arg_types)
{
    std::vector <std::string> arg_types_s(arg_types.size());
    std::transform(arg_types.begin(), arg_types.end(), arg_types_s.begin(),
                   std::ptr_fun <const sort&, std::string> (to_string));
    return std::accumulate(arg_types_s.begin(), arg_types_s.end(), std::string());
}

template <typename T>
void set_option(boost::optional <T>& opt, const std::string& val,
                const std::string& opt_name, const std::string& loc)
{
    T tval = boost::lexical_cast <T> (val.substr(1, val.size() - 2));

    if (opt)
    {
        std::cerr << __LOGSTR__ << loc << "Warning. Overriding previously defined "
                  << opt_name << ". New value " << tval << ".";
    }

    opt = tval;
}

int set_options(context& ctxt, const sl2p::SetOptsCmd *cmd)
{
    for (auto& p : cmd -> Opts)
    {
        const std::string& option(p.first);
        const std::string& value(p.second);

        if (option == "expr-size")
        {
            set_option(ctxt.expr_size, value, "expr-size", parse_loc(cmd));
        }
        else if (option == "beta")
        {
            set_option(ctxt.beta, value, "beta", parse_loc(cmd));
        }
        else if (option == "mutation-limit")
        {
            set_option(ctxt.mutation_limit, value, "mutation-limit", parse_loc(cmd));
        }
        else if (option == "samples")
        {
            set_option(ctxt.samples, value, "samples", parse_loc(cmd));
        }
        else if (option == "random-seed")
        {
            set_option(ctxt.random_seed, value, "random-seed", parse_loc(cmd));
        }
        else if (option == "move-probability")
        {
            set_option(ctxt.move_probability, value, "move-probability", parse_loc(cmd));
        }
        else
        {
            std::cerr << __LOGSTR__ << parse_loc(cmd)
                      << "Warning. Ignoring unrecognized option "
                      << option << "." << std::endl;
        }
    }

    return 0;
}

sort eval_sort(const context& ctxt, const sl2p::SortExpr *e)
{
    switch (e -> BSort)
    {
    case sl2p::BaseSort::SORT_BV:
    {
        return sort(sort_class::BV, e -> BVSize);
    }
    case sl2p::BaseSort::SORT_INT:
    {
        return sort(sort_class::Integer);
    }
    case sl2p::BaseSort::SORT_BOOL:
    {
        return sort(sort_class::Boolean);
    }
    case sl2p::BaseSort::SORT_ENUM:
    {
        std::cerr << __LOGSTR__ << parse_loc(e)
                  << "Error. Enumeration types unimplemented. Exiting."
                  << std::endl;
        exit(EXIT_FAILURE);
    }
    case sl2p::BaseSort::SORT_SYMBOL:
    {
        auto& symbol_table = ctxt.symbol_table_sort;
        if (symbol_table.find(e -> Symbol) != symbol_table.end())
        {
            return symbol_table.at(e -> Symbol);
        }
        else
        {
            std::cerr << __LOGSTR__ << parse_loc(e)
                      << "Error. Sort symbol " << e -> Symbol
                      << " undefined. Exiting." << std::endl;
            exit(EXIT_FAILURE);
        }
    }
    default:
    {
        assert(false);
    }
    }
}

int define_sort(context& ctxt, const sl2p::SortDefCmd *cmd)
{
    auto& symbol_table = ctxt.symbol_table_sort;
    if (symbol_table.find(cmd -> Symbol) != symbol_table.end())
    {
        std::cerr << __LOGSTR__ << parse_loc(cmd)
                  << "Error. Attempting to redefine sort symbol "
                  << cmd -> Symbol << ". Exiting." << std::endl;
        exit(EXIT_FAILURE);
    }

    auto s = eval_sort(ctxt, cmd -> Expr);
    symbol_table[cmd -> Symbol] = s;
    return 0;
}

int declare_var(context& ctxt, const sl2p::VarDeclCmd *cmd)
{
    auto& symbol_table = ctxt.symbol_table_var;
    auto& symbol_table_zconst = ctxt.symbol_table_zfun[""];
    auto& symbol_table_bconst = ctxt.symbol_table_bfun[""];
    auto& symbol_table_bvconst = ctxt.symbol_table_bvfun[""];

    bool already_var = (symbol_table.find(cmd -> VarName) != symbol_table.end());
    bool already_zconst = (symbol_table_zconst.find(cmd -> VarName) != symbol_table_zconst.end());
    bool already_bconst = (symbol_table_bconst.find(cmd -> VarName) != symbol_table_bconst.end());
    bool already_bvconst = (symbol_table_bvconst.find(cmd -> VarName) != symbol_table_bvconst.end());

    if (already_var || already_zconst || already_bconst || already_bvconst)
    {
        std::cerr << __LOGSTR__ << parse_loc(cmd)
                  << "Error. Attempting to redefine variable " << cmd -> VarName << ". ";
        if (already_zconst || already_bconst || already_bvconst)
        {
            std::cerr << "Previously defined as "
                      << (already_zconst ? "integer" : (already_bconst ? "boolean" : "bitvector"))
                      << " constant. ";
        }
        std::cerr << "Exiting." << std::endl;
        exit(EXIT_FAILURE);
    }

    auto s = eval_sort(ctxt, cmd -> VarType);
    switch (s.sc)
    {
    case sort_class::Integer:
    {
        symbol_table[cmd -> VarName] = std::make_pair(id(ctxt.nz), s);
        ctxt.nz++;
        break;
    }
    case sort_class::Boolean:
    {
        symbol_table[cmd -> VarName] = std::make_pair(id(ctxt.nb), s);
        ctxt.nb++;
        break;
    }
    case sort_class::BV:
    {
        symbol_table[cmd -> VarName] = std::make_pair(id(ctxt.nbv.size()), s);
        ctxt.nbv.push_back(s.len);
        break;
    }
    default:
    {
        assert(false);
    }
    }

    return 0;
}

} // namespace context
} // namespace stoch

#include "context_infr_logic.h"

namespace stoch
{
namespace context
{

int set_logic(context& ctxt, const sl2p::SetLogicCmd *cmd)
{
    if (cmd -> LogicName == "LIA")
    {
        set_logic_lia(ctxt, cmd);
    }
    else if (cmd -> LogicName == "BV")
    {
        set_logic_bv(ctxt, cmd);
    }
    else
    {
        std::cerr << __LOGSTR__ << parse_loc(cmd)
                  << "Error. Unrecognized logic " << cmd -> LogicName
                  << ". Exiting." << std::endl;
        exit(EXIT_FAILURE);
    }
    return 0;
}

} // namespace context
} // namespace stoch

#include "context_infr_term.h"
#include "context_infr_fterm.h"
#include "context_infr_grammar.h"

namespace stoch
{
namespace context
{

template <typename U, typename D>
int solve(context& ctxt, D& rndm_dev, U u)
{
    auto ans = ctxt.expr_size ? search(*ctxt.spec, ctxt.g, boost::get <gsymb_t <U>> (ctxt.start_symbol),
                                       ctxt.nz, ctxt.nb, ctxt.nbv, *ctxt.expr_size,
                                       *ctxt.beta, rndm_dev, *ctxt.samples, *ctxt.mutation_limit)
                              : sizefree_search(*ctxt.spec, ctxt.g, boost::get <gsymb_t <U>> (ctxt.start_symbol),
                                                ctxt.nz, ctxt.nb, ctxt.nbv, *ctxt.move_probability,
                                                *ctxt.beta, rndm_dev, *ctxt.samples, *ctxt.mutation_limit);
    if (ans)
    {
        std::cout << *ans << std::endl;
        return 0;
    }
    else
    {
        std::cout << __LOGSTR__ << "Error. Search unsuccessful." << std::endl;
        return 1;
    }
}

int solve(context& ctxt)
{
    std::mt19937 rndm_dev;
    if (ctxt.random_seed)
    {
        std::cerr << __LOGSTR__ << "Warning. Deterministic execution enabled." << std::endl;
        rndm_dev = std::mt19937(*ctxt.random_seed);
    }
    else
    {
        std::random_device seed;
        rndm_dev = std::mt19937(seed());
    }

    ctxt.mutation_limit = ctxt.mutation_limit.get_value_or(context::default_mutation_limit);
    ctxt.samples = ctxt.samples.get_value_or(context::default_samples);
    ctxt.beta = ctxt.beta.get_value_or(context::default_beta);
    ctxt.move_probability = ctxt.move_probability.get_value_or(context::default_move_probability);

    if (!ctxt.synth_fun)
    {
        std::cerr << __LOGSTR__ << "Error. No synthesis function specified." << std::endl;
        return 1;
    }

    if (!ctxt.spec)
    {
        std::cerr << __LOGSTR__ << "Warning. No constraints specified." << std::endl;
        ctxt.spec = bfexpr_p(new fcb(true));
    }

    switch (std::get <2> (*ctxt.synth_fun).sc)
    {
    case sort_class::Integer:
    {
        return solve(ctxt, rndm_dev, z_class(0));
    }
    case sort_class::Boolean:
    {
        return solve(ctxt, rndm_dev, true);
    }
    case sort_class::BV:
    {
        return solve(ctxt, rndm_dev, bv());
    }
    default:
    {
        assert (false);
    }
    }
}

} // namespace context
} // namespace stoch

#endif // __CONTEXT_INFR_H_
