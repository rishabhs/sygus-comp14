#ifndef __CONTEXT_INFR_FTERM_H_
#define __CONTEXT_INFR_FTERM_H_

#include <memory>
#include <utility>

#include <boost/variant.hpp>

#include "context_infr.h"

namespace stoch
{
namespace context
{

typedef boost::variant <afexpr_p, bfexpr_p, bvfexpr_p> fterm;

std::pair <fterm, sort> interpret_fterm(context& ctxt,
                                        const sl2p::Term *t);

std::pair <fterm, sort> interpret_fterm_func(context& ctxt,
        const sl2p::Term *t)
{
    std::vector <std::pair <fterm, sort>> args(t -> Children.size());
    std::vector <sort> arg_types(t -> Children.size());

    std::vector <afexpr_p> achildren;
    std::vector <bfexpr_p> bchildren;
    std::vector <bvfexpr_p> bvchildren;

    for (size_t i = 0; i < t -> Children.size(); i++)
    {
        args[i] = interpret_fterm(ctxt, t -> Children[i]);
        arg_types[i] = args[i].second;

        switch(arg_types[i].sc)
        {
        case sort_class::Integer:
        {
            achildren.push_back(boost::get <afexpr_p> (args[i].first));
            break;
        }
        case sort_class::Boolean:
        {
            bchildren.push_back(boost::get <bfexpr_p> (args[i].first));
            break;
        }
        case sort_class::BV:
        {
            bvchildren.push_back(boost::get <bvfexpr_p> (args[i].first));
            break;
        }
        default:
        {
            assert(false);
        }
        }
    }

    std::string signature = to_string(arg_types);
    auto asubst = idfunc(achildren, false);
    auto bsubst = idfunc(bchildren, false);
    auto bvsubst = idfunc(bvchildren, false);

    if (ctxt.symbol_table_zfun[signature].find(t -> Symbol)
            != ctxt.symbol_table_zfun[signature].end())
    {
        auto& ste = ctxt.symbol_table_zfun[signature].at(t -> Symbol);
        auto ans = ste.first -> f_lift() -> fsubst(asubst, bsubst, bvsubst);
        return std::make_pair(ans, ste.second);
    }
    else if (ctxt.symbol_table_bfun[signature].find(t -> Symbol)
             != ctxt.symbol_table_bfun[signature].end())
    {
        auto& ste = ctxt.symbol_table_bfun[signature].at(t -> Symbol);
        auto ans = ste.first -> f_lift() -> fsubst(asubst, bsubst, bvsubst);
        return std::make_pair(ans, ste.second);
    }
    else if (ctxt.symbol_table_bvfun[signature].find(t -> Symbol)
             != ctxt.symbol_table_bvfun[signature].end())
    {
        auto& ste = ctxt.symbol_table_bvfun[signature].at(t -> Symbol);
        auto ans = ste.first -> f_lift() -> fsubst(asubst, bsubst, bvsubst);
        return std::make_pair(ans, ste.second);
    }
    else if (ctxt.synth_fun
             && std::get <0> (*ctxt.synth_fun) == t -> Symbol
             && std::get <1> (*ctxt.synth_fun) == signature)
    {
        sort s_ans = std::get <2> (*ctxt.synth_fun);
        switch (s_ans.sc)
        {
        case sort_class::Integer:
        {
            afexpr_p ans(new fzcall(0, achildren, bchildren, bvchildren));
            return std::make_pair(ans, s_ans);
        }
        case sort_class::Boolean:
        {
            bfexpr_p ans(new fbcall(0, achildren, bchildren, bvchildren));
            return std::make_pair(ans, s_ans);
        }
        case sort_class::BV:
        {
            bvfexpr_p ans(new fbvcall(0, achildren, bchildren, bvchildren));
            return std::make_pair(ans, s_ans);
        }
        default:
        {
        	assert(false);
        }
        }
    }
    else
    {
        std::cerr << __LOGSTR__ << parse_loc(t)
                  << "Error. Symbol " << t -> Symbol
                  << " undefined. Exiting." << std::endl;
        exit(EXIT_FAILURE);
    }
}

std::pair <fterm, sort> interpret_fterm_lit(const sl2p::Literal *lit)
{
    switch (lit -> LType)
    {
    case sl2p::LiteralType::LITERALTYPE_INT:
    {
        afexpr_p fe(new fcz(lit -> IntValue));
        return std::pair <fterm, sort> (fe, sort_class::Integer);
    }
    case sl2p::LiteralType::LITERALTYPE_BOOL:
    {
        bfexpr_p fe(new fcb(lit -> BoolValue));
        return std::pair <fterm, sort> (fe, sort_class::Boolean);
    }
    case sl2p::LiteralType::LITERALTYPE_ENUM:
    {
        std::cerr << __LOGSTR__ << parse_loc(lit)
                  << " Error. Enumeration types unsupported. Exiting." << std::endl;
        exit(EXIT_FAILURE);
    }
    case sl2p::LiteralType::LITERALTYPE_BV:
    {
        bv v(lit -> LiteralString);
        bvfexpr_p fe(new fcbv(v));
        return std::pair <fterm, sort> (fe, sort(sort_class::BV, v.len));
    }
    default:
    {
        assert(false);
    }
    }
}

std::pair <fterm, sort> interpret_fterm_symbol(context& ctxt,
        const sl2p::Term *t)
{
    if (ctxt.symbol_table_var.find(t -> Symbol)
            != ctxt.symbol_table_var.end())
    {
        auto& var = ctxt.symbol_table_var[t -> Symbol];
        switch (var.second.sc)
        {
        case sort_class::Integer:
        {
            return std::make_pair(afexpr_p(new fzvar(var.first)), var.second);
        }
        case sort_class::Boolean:
        {
            return std::make_pair(bfexpr_p(new fbvar(var.first)), var.second);
        }
        case sort_class::BV:
        {
            return std::make_pair(bvfexpr_p(new fbvvar(var.first, var.second.len)), var.second);
        }
        default:
        {
            assert(false);
        }
        }
    }

    if (ctxt.symbol_table_zfun[""].find(t -> Symbol)
            != ctxt.symbol_table_zfun[""].end())
    {
        auto& ste = ctxt.symbol_table_zfun[""].at(t -> Symbol);
        return std::make_pair(ste.first -> f_lift(), ste.second);
    }
    else if (ctxt.symbol_table_bfun[""].find(t -> Symbol)
             != ctxt.symbol_table_bfun[""].end())
    {
        auto& ste = ctxt.symbol_table_bfun[""].at(t -> Symbol);
        return std::make_pair(ste.first -> f_lift(), ste.second);
    }
    else if (ctxt.symbol_table_bvfun[""].find(t -> Symbol)
             != ctxt.symbol_table_bvfun[""].end())
    {
        auto& ste = ctxt.symbol_table_bvfun[""].at(t -> Symbol);
        return std::make_pair(ste.first -> f_lift(), ste.second);
    }
    else
    {
        std::cerr << __LOGSTR__ << parse_loc(t)
                  << "Error. Symbol " << t -> Symbol
                  << " undefined. Exiting." << std::endl;
        exit(EXIT_FAILURE);
    }
}

std::pair <fterm, sort> interpret_fterm(context& ctxt,
                                        const sl2p::Term *t)
{
    switch (t -> TType)
    {
    case sl2p::TermType::TERMTYPE_FUNC:
    {
        return interpret_fterm_func(ctxt, t);
    }
    case sl2p::TermType::TERMTYPE_LITERAL:
    {
        return interpret_fterm_lit(t -> TheLiteral);
    }
    case sl2p::TermType::TERMTYPE_SYMBOL:
    {
        return interpret_fterm_symbol(ctxt, t);
    }
    default:
    {
        assert(false);
    }
    }
}

int add_constraint(context& ctxt, const sl2p::ConstraintCmd *cmd)
{
    auto t = interpret_fterm(ctxt, cmd -> TheTerm);
    if (t.second != sort_class::Boolean)
    {
        std::cerr << __LOGSTR__ << parse_loc(cmd)
                  << "Error. Constraint expression not of boolean type. Exiting." << std::endl;
        exit(EXIT_FAILURE);
    }

    if (!ctxt.spec)
    {
        ctxt.spec = boost::get <bfexpr_p> (t.first);
    }
    else
    {
        ctxt.spec = (*ctxt.spec && boost::get <bfexpr_p> (t.first));
    }

    return 0;
}

} // namespace context
} // namespace stoch

#endif // __CONTEXT_INFR_TERM_H_
