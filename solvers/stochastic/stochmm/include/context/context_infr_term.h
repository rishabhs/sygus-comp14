#ifndef __CONTEXT_INFR_TERM_H_
#define __CONTEXT_INFR_TERM_H_

#include <memory>
#include <utility>

#include <boost/variant.hpp>

#include "context_infr.h"

namespace stoch
{
namespace context
{

typedef boost::variant <aexpr_p, bexpr_p, bvexpr_p> term;

std::pair <term, sort> interpret_term(context& ctxt,
                                      const std::map <std::string, std::pair <id, sort>>& env,
                                      const sl2p::Term *t);

std::pair <term, sort> interpret_term_func(context& ctxt,
                                      const std::map <std::string, std::pair <id, sort>>& env,
                                      const sl2p::Term *t)
{
    assert(t -> TType == sl2p::TermType::TERMTYPE_FUNC);
    std::vector <std::pair <term, sort>> args(t -> Children.size());
    std::vector <sort> arg_types(t -> Children.size());

    std::vector <aexpr_p> achildren;
    std::vector <bexpr_p> bchildren;
    std::vector <bvexpr_p> bvchildren;

    for (size_t i = 0; i < t -> Children.size(); i++)
    {
        args[i] = interpret_term(ctxt, env, t -> Children[i]);
        arg_types[i] = args[i].second;

        switch(arg_types[i].sc)
        {
        case sort_class::Integer:
        {
            achildren.push_back(boost::get <aexpr_p> (args[i].first));
            break;
        }
        case sort_class::Boolean:
        {
            bchildren.push_back(boost::get <bexpr_p> (args[i].first));
            break;
        }
        case sort_class::BV:
        {
            bvchildren.push_back(boost::get <bvexpr_p> (args[i].first));
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
        auto ans = ste.first -> subst(asubst, bsubst, bvsubst);
        return std::make_pair(ans, ste.second);
    }
    else if (ctxt.symbol_table_bfun[signature].find(t -> Symbol)
             != ctxt.symbol_table_bfun[signature].end())
    {
        auto& ste = ctxt.symbol_table_bfun[signature].at(t -> Symbol);
        auto ans = ste.first -> subst(asubst, bsubst, bvsubst);
        return std::make_pair(ans, ste.second);
    }
    else if (ctxt.symbol_table_bvfun[signature].find(t -> Symbol)
             != ctxt.symbol_table_bvfun[signature].end())
    {
        auto& ste = ctxt.symbol_table_bvfun[signature].at(t -> Symbol);
        auto ans = ste.first -> subst(asubst, bsubst, bvsubst);
        return std::make_pair(ans, ste.second);
    }
    else
    {
        std::cerr << __LOGSTR__ << parse_loc(t)
                  << "Error. Symbol " << t -> Symbol
                  << " undefined. Exiting." << std::endl;
        exit(EXIT_FAILURE);
    }
}

std::pair <term, sort> interpret_term_lit(const sl2p::Literal *lit)
{
    switch (lit -> LType)
    {
    case sl2p::LiteralType::LITERALTYPE_INT:
    {
        aexpr_p e(new cz(lit -> IntValue));
        return std::pair <term, sort> (e, sort_class::Integer);
    }
    case sl2p::LiteralType::LITERALTYPE_BOOL:
    {
        bexpr_p e(new cb(lit -> BoolValue));
        return std::pair <term, sort> (e, sort_class::Boolean);
    }
    case sl2p::LiteralType::LITERALTYPE_ENUM:
    {
        std::cerr << __LOGSTR__ << parse_loc(lit)
                  << "Error. Enumeration types unsupported. Exiting." << std::endl;
        exit(EXIT_FAILURE);
    }
    case sl2p::LiteralType::LITERALTYPE_BV:
    {
        bv v(lit -> LiteralString);
        bvexpr_p e(new cbv(v));
        return std::pair <term, sort> (e, sort(sort_class::BV, v.len));
    }
    default:
    {
        assert(false);
    }
    }
}

std::pair <term, sort> interpret_term_symbol(context& ctxt,
                                             const std::map <std::string, std::pair <id, sort>>& env,
                                             const sl2p::Term *t)
{
    if (env.find(t -> Symbol) != env.end())
    {
        auto& env_e = env.at(t -> Symbol);
        switch (env_e.second.sc)
        {
        case sort_class::Integer:
        {
            aexpr_p zans(new zvar(env_e.first));
            return make_pair(zans, env_e.second);
        }
        case sort_class::Boolean:
        {
            bexpr_p bans(new bvar(env_e.first));
            return make_pair(bans, env_e.second);
        }
        case sort_class::BV:
        {
            bvexpr_p bvans(new bvvar(env_e.first, env_e.second.len));
            return make_pair(bvans, env_e.second);
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
        return std::make_pair(ste.first, ste.second);
    }
    else if (ctxt.symbol_table_bfun[""].find(t -> Symbol)
            != ctxt.symbol_table_bfun[""].end())
    {
        auto& ste = ctxt.symbol_table_bfun[""].at(t -> Symbol);
        return std::make_pair(ste.first, ste.second);
    }
    else if (ctxt.symbol_table_bvfun[""].find(t -> Symbol)
            != ctxt.symbol_table_bvfun[""].end())
    {
        auto& ste = ctxt.symbol_table_bvfun[""].at(t -> Symbol);
        return std::make_pair(ste.first, ste.second);
    }
    else
    {
        std::cerr << __LOGSTR__ << parse_loc(t)
                    << "Error. Symbol " << t -> Symbol
                    << " undefined. Exiting." << std::endl;
        exit(EXIT_FAILURE);
    }
}

std::pair <term, sort> interpret_term(context& ctxt,
                                      const std::map <std::string, std::pair <id, sort>>& env,
                                      const sl2p::Term *t)
{
    switch (t -> TType)
    {
    case sl2p::TermType::TERMTYPE_FUNC:
    {
        return interpret_term_func(ctxt, env, t);
    }
    case sl2p::TermType::TERMTYPE_LITERAL:
    {
        return interpret_term_lit(t -> TheLiteral);
    }
    case sl2p::TermType::TERMTYPE_SYMBOL:
    {
        return interpret_term_symbol(ctxt, env, t);
    }
    default:
    {
        assert(false);
    }
    }
}

bool fun_defined(context& ctxt, const std::vector <sort>& arg_types,
                 const std::string& symbol)
{
    std::string signature = to_string(arg_types);
    return ctxt.symbol_table_zfun[signature].find(symbol) != ctxt.symbol_table_zfun[signature].end()
           || ctxt.symbol_table_bfun[signature].find(symbol) != ctxt.symbol_table_bfun[signature].end()
           || ctxt.symbol_table_bvfun[signature].find(symbol) != ctxt.symbol_table_bvfun[signature].end();
}

int define_fun(context& ctxt, const sl2p::FunDefCmd *cmd)
{
    size_t nz(0), nb(0), nbv(0);
    std::map <std::string, std::pair <id, sort>> env;
    std::vector <sort> arg_types(cmd -> Arguments.size());

    for (size_t i = 0; i < cmd -> Arguments.size(); i++)
    {
        auto& arg = cmd -> Arguments[i];
        auto& name = arg.first;
        auto s = eval_sort(ctxt, arg.second);
        arg_types[i] = s;

        if (env.find(name) != env.end())
        {
            std::cerr << __LOGSTR__ << parse_loc(cmd)
                      << "Error. Attempting to redefine formal parameter "
                      << name << ". Exiting." << std::endl;
            exit(EXIT_FAILURE);
        }

        switch (s.sc)
        {
        case sort_class::Integer:
        {
            env[name] = std::make_pair(id(nz), s);
            nz++;
            break;
        }
        case sort_class::Boolean:
        {
            env[name] = std::make_pair(id(nb), s);
            nb++;
            break;
        }
        case sort_class::BV:
        {
            env[name] = std::make_pair(id(nbv), s);
            nbv++;
            break;
        }
        default:
        {
            assert(false);
        }
        }
    }

    auto t = interpret_term(ctxt, env, cmd -> Def);
    if (eval_sort(ctxt, cmd -> Type) != t.second)
    {
        std::cerr << __LOGSTR__ << parse_loc(cmd)
                  << "Error. Type mismatch in definition of function "
                  << cmd -> Symbol << ". Exiting." << std::endl;
        exit(EXIT_FAILURE);
    }

    if (fun_defined(ctxt, arg_types, cmd -> Symbol))
    {
        std::cerr << __LOGSTR__ << parse_loc(cmd)
                  << "Error. Attempting to redefine function symbol "
                  << cmd -> Symbol << ". Exiting." << std::endl;
        exit(EXIT_FAILURE);
    }

    switch (t.second.sc)
    {
    case sort_class::Integer:
    {
        auto& symbol_table = ctxt.symbol_table_zfun[to_string(arg_types)];
        symbol_table[cmd -> Symbol] = std::make_pair(boost::get <aexpr_p> (t.first), t.second);
        break;
    }
    case sort_class::Boolean:
    {
        auto& symbol_table = ctxt.symbol_table_bfun[to_string(arg_types)];
        symbol_table[cmd -> Symbol] = std::make_pair(boost::get <bexpr_p> (t.first), t.second);
        break;
    }
    case sort_class::BV:
    {
        auto& symbol_table = ctxt.symbol_table_bvfun[to_string(arg_types)];
        symbol_table[cmd -> Symbol] = std::make_pair(boost::get <bvexpr_p> (t.first), t.second);
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

#endif // __CONTEXT_INFR_TERM_H_
