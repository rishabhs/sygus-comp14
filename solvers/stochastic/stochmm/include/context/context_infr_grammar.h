#ifndef __CONTEXT_INFR_GRAMMAR_H_
#define __CONTEXT_INFR_GRAMMAR_H_

#include <boost/variant.hpp>

#include "context_infr.h"

namespace stoch
{
namespace context
{

typedef boost::variant <aprod_rule, bprod_rule, bvprod_rule> prod_rule_poly;
typedef std::map <std::string, std::pair <id, sort>> synth_fun_env;

std::pair <prod_rule_poly, sort> interpret_gterm(context& ctxt,
        std::map <agsymb_t, grammar::aprod_rule_v>& arules,
        std::map <bgsymb_t, grammar::bprod_rule_v>& brules,
        std::map <bvgsymb_t, grammar::bvprod_rule_v>& bvrules,
        const synth_fun_env& env,
        std::map <std::string, std::pair <id, sort>>& grammar_symbols,
        size_t& nz, size_t& nb, size_t& nbv, const std::string& symbol,
        const sl2p::GTerm *gterm)
{
    switch (gterm -> GTType)
    {
    case sl2p::GTermType::GTERMTYPE_SYMBOL:
    {
        auto& symbol_table_zfun = ctxt.symbol_table_zfun.at("");
        auto& symbol_table_bfun = ctxt.symbol_table_bfun.at("");
        auto& symbol_table_bvfun = ctxt.symbol_table_bvfun.at("");

        if (env.find(gterm -> Symbol) != env.end())
        {
            switch (env.at(gterm -> Symbol).second.sc)
            {
            case sort_class::Integer:
            {
                id x(env.at(gterm -> Symbol).first);
                typename aprod_rule::expand_t ex([=](const typename aprod_rule::aexpr_p_v& achildren,
                                                     const typename bprod_rule::bexpr_p_v& bchildren,
                                                     const typename bvprod_rule::bvexpr_p_v& bvchildren)
                {
                    return aexpr_p(new zvar(x));
                });
                return std::pair <prod_rule_poly, sort> (aprod_rule(ex), env.at(gterm -> Symbol).second);
            }
            case sort_class::Boolean:
            {
                id x(env.at(gterm -> Symbol).first);
                typename bprod_rule::expand_t ex([=](const typename aprod_rule::aexpr_p_v& achildren,
                                                     const typename bprod_rule::bexpr_p_v& bchildren,
                                                     const typename bvprod_rule::bvexpr_p_v& bvchildren)
                {
                    return bexpr_p(new bvar(x));
                });
                return std::pair <prod_rule_poly, sort> (bprod_rule(ex), env.at(gterm -> Symbol).second);
            }
            case sort_class::BV:
            {
                id x(env.at(gterm -> Symbol).first);
                size_t len = env.at(gterm -> Symbol).second.len;
                typename bvprod_rule::expand_t ex([=](const typename aprod_rule::aexpr_p_v& achildren,
                                                      const typename bprod_rule::bexpr_p_v& bchildren,
                                                      const typename bvprod_rule::bvexpr_p_v& bvchildren)
                {
                    return bvexpr_p(new bvvar(x, len));
                });
                return std::pair <prod_rule_poly, sort> (bvprod_rule(ex), env.at(gterm -> Symbol).second);
            }
            default:
            {
                assert(false);
            }
            }
        }
        else if (symbol_table_zfun.find(gterm -> Symbol) != symbol_table_zfun.end())
        {
            aexpr_p e = symbol_table_zfun.at(gterm -> Symbol).first;
            sort e_s = symbol_table_zfun.at(gterm -> Symbol).second;
            typename aprod_rule::expand_t ex([=](const typename aprod_rule::aexpr_p_v& achildren,
                                                 const typename bprod_rule::bexpr_p_v& bchildren,
                                                 const typename bvprod_rule::bvexpr_p_v& bvchildren)
            {
                return e;
            });
            return std::pair <prod_rule_poly, sort> (aprod_rule(ex), e_s);
        }
        else if (symbol_table_bfun.find(gterm -> Symbol) != symbol_table_bfun.end())
        {
            bexpr_p e = symbol_table_bfun.at(gterm -> Symbol).first;
            sort e_s = symbol_table_bfun.at(gterm -> Symbol).second;
            typename bprod_rule::expand_t ex([=](const typename aprod_rule::aexpr_p_v& achildren,
                                                 const typename bprod_rule::bexpr_p_v& bchildren,
                                                 const typename bvprod_rule::bvexpr_p_v& bvchildren)
            {
                return e;
            });
            return std::pair <prod_rule_poly, sort> (bprod_rule(ex), e_s);
        }
        else if (symbol_table_bvfun.find(gterm -> Symbol) != symbol_table_bvfun.end())
        {
            bvexpr_p e = symbol_table_bvfun.at(gterm -> Symbol).first;
            sort e_s = symbol_table_bvfun.at(gterm -> Symbol).second;
            typename bvprod_rule::expand_t ex([=](const typename aprod_rule::aexpr_p_v& achildren,
                                                  const typename bprod_rule::bexpr_p_v& bchildren,
                                                  const typename bvprod_rule::bvexpr_p_v& bvchildren)
            {
                return e;
            });
            return std::pair <prod_rule_poly, sort> (bvprod_rule(ex), e_s);
        }
        else if (grammar_symbols.find(gterm -> Symbol) != grammar_symbols.end())
        {
            std::pair <id, sort>& gss = grammar_symbols.at(gterm -> Symbol);
            switch (gss.second.sc)
            {
            case sort_class::Integer:
            {
                typename aprod_rule::expand_t ex([=](const typename aprod_rule::aexpr_p_v& achildren,
                                                     const typename bprod_rule::bexpr_p_v& bchildren,
                                                     const typename bvprod_rule::bvexpr_p_v& bvchildren)
                {
                    return achildren[0];
                });
                aprod_rule rule(ex);
                return std::pair <prod_rule_poly, sort> (rule << agsymb_t(gss.first), gss.second);
            }
            case sort_class::Boolean:
            {
                typename bprod_rule::expand_t ex([=](const typename aprod_rule::aexpr_p_v& achildren,
                                                     const typename bprod_rule::bexpr_p_v& bchildren,
                                                     const typename bvprod_rule::bvexpr_p_v& bvchildren)
                {
                    return bchildren[0];
                });
                bprod_rule rule(ex);
                return std::pair <prod_rule_poly, sort> (rule << bgsymb_t(gss.first), gss.second);
            }
            case sort_class::BV:
            {
                typename bvprod_rule::expand_t ex([=](const typename aprod_rule::aexpr_p_v& achildren,
                                                      const typename bprod_rule::bexpr_p_v& bchildren,
                                                      const typename bvprod_rule::bvexpr_p_v& bvchildren)
                {
                    return bvchildren[0];
                });
                bvprod_rule rule(ex);
                return std::pair <prod_rule_poly, sort> (rule << bvgsymb_t(gss.first), gss.second);
            }
            default:
            {
                assert(false);
            }
            }
        }
        else
        {
            std::cerr << __LOGSTR__ << parse_loc(gterm)
                      << "Error. Symbol " << gterm -> Symbol << " undefined. Exiting." << std::endl;
            exit(EXIT_FAILURE);
        }
    }
    case sl2p::GTermType::GTERMTYPE_LITERAL:
    {
        auto& lit = gterm -> TheLiteral;
        switch (lit -> LType)
        {
        case sl2p::LiteralType::LITERALTYPE_INT:
        {
            aexpr_p e(new cz(lit -> IntValue));
            typename aprod_rule::expand_t ex([=](const typename aprod_rule::aexpr_p_v& achildren,
                                                 const typename bprod_rule::bexpr_p_v& bchildren,
                                                 const typename bvprod_rule::bvexpr_p_v& bvchildren)
            {
                return e;
            });
            return std::pair <prod_rule_poly, sort> (aprod_rule(ex), sort_class::Integer);
        }
        case sl2p::LiteralType::LITERALTYPE_BOOL:
        {
            bexpr_p e(new cb(lit -> BoolValue));
            typename bprod_rule::expand_t ex([=](const typename aprod_rule::aexpr_p_v& achildren,
                                                 const typename bprod_rule::bexpr_p_v& bchildren,
                                                 const typename bvprod_rule::bvexpr_p_v& bvchildren)
            {
                return e;
            });
            return std::pair <prod_rule_poly, sort> (bprod_rule(ex), sort_class::Boolean);
        }
        case sl2p::LiteralType::LITERALTYPE_ENUM:
        {
            std::cerr << __LOGSTR__ << parse_loc(lit)
                      << " Error. Enumerated types unsupported. Exiting." << std::endl;
            exit(EXIT_FAILURE);
        }
        case sl2p::LiteralType::LITERALTYPE_BV:
        {
            bv v(lit -> LiteralString);
            typename bvprod_rule::expand_t ex([=](const typename aprod_rule::aexpr_p_v& achildren,
                                                  const typename bprod_rule::bexpr_p_v& bchildren,
                                                  const typename bvprod_rule::bvexpr_p_v& bvchildren)
            {
                return bvexpr_p(new cbv(v));;
            });
            return std::pair <prod_rule_poly, sort> (bvprod_rule(ex), sort(sort_class::BV, v.len));
        }
        default:
        {
            assert(false);
        }
        }
    }
    case sl2p::GTermType::GTERMTYPE_FUNC:
    {
        std::vector <agsymb_t> achildren;
        std::vector <bgsymb_t> bchildren;
        std::vector <bvgsymb_t> bvchildren;
        std::vector <sort> arg_types;

        for (size_t i = 0; i < gterm -> Children.size(); i++)
        {
            switch (gterm -> Children[i] -> GTType)
            {
            case sl2p::GTermType::GTERMTYPE_SYMBOL:
            {
                std::string symbol = gterm -> Children[i] -> Symbol;
                if (grammar_symbols.find(symbol) != grammar_symbols.end())
                {
                    switch (grammar_symbols[symbol].second.sc)
                    {
                    case sort_class::Integer:
                    {
                        achildren.push_back(grammar_symbols[symbol].first);
                        arg_types.push_back(grammar_symbols[symbol].second);
                        break;
                    }
                    case sort_class::Boolean:
                    {
                        bchildren.push_back(grammar_symbols[symbol].first);
                        arg_types.push_back(grammar_symbols[symbol].second);
                        break;
                    }
                    case sort_class::BV:
                    {
                        bvchildren.push_back(grammar_symbols[symbol].first);
                        arg_types.push_back(grammar_symbols[symbol].second);
                        break;
                    }
                    default:
                    {
                        assert (false);
                    }
                    }
                    break;
                }
                else /* Fall through switch. */ {}
            } case sl2p::GTermType::GTERMTYPE_LITERAL:
            case sl2p::GTermType::GTERMTYPE_FUNC:
            case sl2p::GTermType::GTERMTYPE_CONSTANT:
            case sl2p::GTermType::GTERMTYPE_VARIABLE:
            {
                // For [else] case of GTERMTYPE_SYMBOL,
                // and all cases of GTERMTYPE_LITERAL, GTERMTYPE_FUNC,
                // GTERMTYPE_CONSTANT, GTERMTYPE_VARIABLE.

                std::string child_name = symbol + "@" + boost::lexical_cast <std::string> (i);
                auto p = interpret_gterm(ctxt, arules, brules, bvrules,
                                         env, grammar_symbols, nz, nb, nbv,
                                         child_name, gterm -> Children[i]);
                switch (p.second.sc)
                {
                case sort_class::Integer:
                {
                    agsymb_t child(nz);
                    grammar_symbols[child_name] =
                        std::pair <id, sort> (nz, p.second);
                    nz++;
                    achildren.push_back(child);
                    arg_types.push_back(p.second);
                }
                case sort_class::Boolean:
                {
                    bgsymb_t child(nb);
                    grammar_symbols[child_name] =
                        std::pair <id, sort> (nz, p.second);
                    nb++;
                    bchildren.push_back(child);
                    arg_types.push_back(p.second);
                }
                case sort_class::BV:
                {
                    bgsymb_t child(nbv);
                    grammar_symbols[child_name] =
                        std::pair <id, sort> (nz, p.second);
                    nbv++;
                    bvchildren.push_back(child);
                    arg_types.push_back(p.second);
                }
                default:
                {
                    assert(false);
                }
                }
            }
            default:
            {
                assert (false);
            }
            }
        }

        auto& symbol_table_zfun = ctxt.symbol_table_zfun[to_string(arg_types)];
        auto& symbol_table_bfun = ctxt.symbol_table_bfun[to_string(arg_types)];
        auto& symbol_table_bvfun = ctxt.symbol_table_bvfun[to_string(arg_types)];

        if (symbol_table_zfun.find(gterm -> Symbol) != symbol_table_zfun.end())
        {
            aexpr_p e = symbol_table_zfun[gterm -> Symbol].first;
            sort e_s = symbol_table_zfun[gterm -> Symbol].second;
            typename aprod_rule::expand_t ex([=](const typename aprod_rule::aexpr_p_v& achildren,
                                                 const typename aprod_rule::bexpr_p_v& bchildren,
                                                 const typename aprod_rule::bvexpr_p_v& bvchildren)
            {
                auto asubst = idfunc(achildren);
                auto bsubst = idfunc(bchildren);
                auto bvsubst = idfunc(bvchildren);
                return e -> subst(asubst, bsubst, bvsubst);
            });
            aprod_rule rule(achildren, bchildren, bvchildren, ex);
            return std::pair <prod_rule_poly, sort> (rule, e_s);
        }
        else if (symbol_table_bfun.find(gterm -> Symbol) != symbol_table_bfun.end())
        {
            bexpr_p e = symbol_table_bfun[gterm -> Symbol].first;
            sort e_s = symbol_table_bfun[gterm -> Symbol].second;
            typename bprod_rule::expand_t ex([=](const typename bprod_rule::aexpr_p_v& achildren,
                                                 const typename bprod_rule::bexpr_p_v& bchildren,
                                                 const typename bprod_rule::bvexpr_p_v& bvchildren)
            {
                auto asubst = idfunc(achildren);
                auto bsubst = idfunc(bchildren);
                auto bvsubst = idfunc(bvchildren);
                return e -> subst(asubst, bsubst, bvsubst);
            });
            bprod_rule rule(achildren, bchildren, bvchildren, ex);
            return std::pair <prod_rule_poly, sort> (rule, e_s);
        }
        else if (symbol_table_bvfun.find(gterm -> Symbol) != symbol_table_bvfun.end())
        {
            bvexpr_p e = symbol_table_bvfun[gterm -> Symbol].first;
            sort e_s = symbol_table_bvfun[gterm -> Symbol].second;
            typename bvprod_rule::expand_t ex([=](const typename bprod_rule::aexpr_p_v& achildren,
                                                  const typename bprod_rule::bexpr_p_v& bchildren,
                                                  const typename bprod_rule::bvexpr_p_v& bvchildren)
            {
                auto asubst = idfunc(achildren);
                auto bsubst = idfunc(bchildren);
                auto bvsubst = idfunc(bvchildren);
                return e -> subst(asubst, bsubst, bvsubst);
            });
            bvprod_rule rule(achildren, bchildren, bvchildren, ex);
            return std::pair <prod_rule_poly, sort> (rule, e_s);
        }
        else
        {
            std::cerr << __LOGSTR__ << parse_loc(gterm)
                      << "Error. Function symbol " << gterm -> Symbol << " undefined. Exiting." << std::endl;
            exit(EXIT_FAILURE);
        }
    }
    case sl2p::GTermType::GTERMTYPE_CONSTANT:
    {
        sort s = eval_sort(ctxt, gterm -> TermSort);
        switch (s.sc)
        {
        case sort_class::Integer:
        {
            agsymb_t symb(nz);
            std::string child_name = symbol + "@C";
            nz++;
            typename aprod_rule::expand_t ex0([](const typename aprod_rule::aexpr_p_v& achildren,
                                                 const typename aprod_rule::bexpr_p_v& bchildren,
                                                 const typename aprod_rule::bvexpr_p_v& bvchildren)
            {
                return aexpr_p(new cz(0));
            });
            typename aprod_rule::expand_t ex1([](const typename aprod_rule::aexpr_p_v& achildren,
                                                 const typename aprod_rule::bexpr_p_v& bchildren,
                                                 const typename aprod_rule::bvexpr_p_v& bvchildren)
            {
                return aexpr_p(new cz(1));
            });
            grammar_symbols[child_name] = std::pair <id, sort> (id(symb.v), sort_class::Integer);
            arules[symb].push_back(aprod_rule(ex0));
            arules[symb].push_back(aprod_rule(ex1));

            typename aprod_rule::expand_t ex([](const typename aprod_rule::aexpr_p_v& achildren,
                                                const typename aprod_rule::bexpr_p_v& bchildren,
                                                const typename aprod_rule::bvexpr_p_v& bvchildren)
            {
                return achildren[0];
            });
            aprod_rule rule(ex);
            return std::pair <prod_rule_poly, sort> (rule << symb, s);
        }
        case sort_class::Boolean:
        {
            bgsymb_t symb(nb);
            std::string child_name = symbol + "@C";
            nb++;
            typename bprod_rule::expand_t ext([](const typename aprod_rule::aexpr_p_v& achildren,
                                                 const typename aprod_rule::bexpr_p_v& bchildren,
                                                 const typename aprod_rule::bvexpr_p_v& bvchildren)
            {
                return bexpr_p(new cb(true));
            });
            typename bprod_rule::expand_t exf([](const typename aprod_rule::aexpr_p_v& achildren,
                                                 const typename aprod_rule::bexpr_p_v& bchildren,
                                                 const typename aprod_rule::bvexpr_p_v& bvchildren)
            {
                return bexpr_p(new cb(false));
            });
            grammar_symbols[child_name] = std::pair <id, sort> (id(symb.v), sort_class::Boolean);
            brules[symb].push_back(bprod_rule(ext));
            brules[symb].push_back(bprod_rule(exf));

            typename bprod_rule::expand_t ex([](const typename aprod_rule::aexpr_p_v& achildren,
                                                const typename aprod_rule::bexpr_p_v& bchildren,
                                                const typename aprod_rule::bvexpr_p_v& bvchildren)
            {
                return bchildren[0];
            });
            bprod_rule rule(ex);
            return std::pair <prod_rule_poly, sort> (rule << symb, s);
        }
        case sort_class::BV:
        {
            bvgsymb_t symb(nb);
            std::string child_name = symbol + "@C";
            nbv++;
            typename bvprod_rule::expand_t ex0([=](const typename aprod_rule::aexpr_p_v& achildren,
                                                   const typename aprod_rule::bexpr_p_v& bchildren,
                                                   const typename aprod_rule::bvexpr_p_v& bvchildren)
            {
                return bvexpr_p(new cbv(bv(s.len, 0)));
            });
            typename bvprod_rule::expand_t ex1([=](const typename aprod_rule::aexpr_p_v& achildren,
                                                   const typename aprod_rule::bexpr_p_v& bchildren,
                                                   const typename aprod_rule::bvexpr_p_v& bvchildren)
            {
                return bvexpr_p(new cbv(bv(s.len, 1)));
            });
            grammar_symbols[child_name] = std::pair <id, sort> (id(symb.v), sort_class::BV);
            bvrules[symb].push_back(bvprod_rule(ex0));
            bvrules[symb].push_back(bvprod_rule(ex1));

            typename bvprod_rule::expand_t ex([](const typename aprod_rule::aexpr_p_v& achildren,
                                                 const typename aprod_rule::bexpr_p_v& bchildren,
                                                 const typename aprod_rule::bvexpr_p_v& bvchildren)
            {
                return bvchildren[0];
            });
            bvprod_rule rule(ex);
            return std::pair <prod_rule_poly, sort> (rule << symb, s);
        }
        default:
        {
            assert(false);
        }
        }
    }
    case sl2p::GTermType::GTERMTYPE_VARIABLE:
    {
        sort s = eval_sort(ctxt, gterm -> TermSort);
        std::vector <id> relevant_vars;
        for (auto& kv_env : env)
        {
            if (kv_env.second.second == s)
            {
                relevant_vars.push_back(kv_env.second.first);
            }
        }

        switch (s.sc)
        {
        case sort_class::Integer:
        {
            agsymb_t symb(nz);
            std::string child_name = symbol + "@V";
            nz++;

            for (id& x : relevant_vars)
            {
                typename aprod_rule::expand_t exv([=](const typename aprod_rule::aexpr_p_v& achildren,
                                                 const typename aprod_rule::bexpr_p_v& bchildren,
                                                 const typename aprod_rule::bvexpr_p_v& bvchildren)
                {
                    return aexpr_p(new zvar(x));
                });
                arules[symb].push_back(aprod_rule(exv));
            }

            typename aprod_rule::expand_t ex([=](const typename aprod_rule::aexpr_p_v& achildren,
                                                 const typename aprod_rule::bexpr_p_v& bchildren,
                                                 const typename aprod_rule::bvexpr_p_v& bvchildren)
            {
                return achildren[0];
            });
            aprod_rule rule(ex);
            return std::pair <prod_rule_poly, sort> (rule << symb, s);
        }
        case sort_class::Boolean:
        {
            bgsymb_t symb(nb);
            std::string child_name = symbol + "@V";
            nb++;

            for (id& x : relevant_vars)
            {
                typename bprod_rule::expand_t exv([=](const typename bprod_rule::aexpr_p_v& achildren,
                                                 const typename bprod_rule::bexpr_p_v& bchildren,
                                                 const typename bprod_rule::bvexpr_p_v& bvchildren)
                {
                    return bexpr_p(new bvar(x));
                });
                brules[symb].push_back(bprod_rule(exv));
            }

            typename bprod_rule::expand_t ex([=](const typename bprod_rule::aexpr_p_v& achildren,
                                                 const typename bprod_rule::bexpr_p_v& bchildren,
                                                 const typename bprod_rule::bvexpr_p_v& bvchildren)
            {
                return bchildren[0];
            });
            bprod_rule rule(ex);
            return std::pair <prod_rule_poly, sort> (rule << symb, s);
        }
        case sort_class::BV:
        {
            bvgsymb_t symb(nbv);
            std::string child_name = symbol + "@V";
            nbv++;

            for (id& x : relevant_vars)
            {
                typename bvprod_rule::expand_t exv([=](const typename bvprod_rule::aexpr_p_v& achildren,
                                                  const typename bvprod_rule::bexpr_p_v& bchildren,
                                                  const typename bvprod_rule::bvexpr_p_v& bvchildren)
                {
                    return bvexpr_p(new bvvar(x));
                });
                bvrules[symb].push_back(bvprod_rule(exv));
            }

            typename bvprod_rule::expand_t ex([=](const typename bvprod_rule::aexpr_p_v& achildren,
                                                  const typename bvprod_rule::bexpr_p_v& bchildren,
                                                  const typename bvprod_rule::bvexpr_p_v& bvchildren)
            {
                return bvchildren[0];
            });
            bvprod_rule rule(ex);
            return std::pair <prod_rule_poly, sort> (rule << symb, s);
        }
        default:
        {
            assert(false);
        }
        }
    } default:
    {
        std::cerr << __LOGSTR__ << parse_loc(gterm)
                  << "Assertion failure!" << std::endl;
        assert(false);
    }
    }
}

void populate_synth_fun_env(context& ctxt, const sl2p::SynthFunCmd *cmd,
                            synth_fun_env& env, std::vector <sort>& arg_types,
                            size_t& nz, size_t& nb, size_t& nbv)
{
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
}

int declare_synth_fun(context& ctxt, const sl2p::SynthFunCmd *cmd)
{
    if (ctxt.synth_fun)
    {
        std::cerr << __LOGSTR__ << parse_loc(cmd)
                  << "Error. Multi-function synthesis unsupported. Exiting." << std::endl;
        exit(EXIT_FAILURE);
    }

    synth_fun_env env;
    std::vector <sort> arg_types(cmd -> Arguments.size());
    size_t nz(0), nb(0), nbv(0);
    populate_synth_fun_env(ctxt, cmd, env, arg_types, nz, nb, nbv);

    if (fun_defined(ctxt, arg_types, cmd -> SynthFunName))
    {
        std::cerr << __LOGSTR__ << parse_loc(cmd)
                  << "Error. Attempting to synthesize already defined function "
                  << cmd -> SynthFunName << ". Exiting." << std::endl;
        exit(EXIT_FAILURE);
    }

    ctxt.synth_fun = std::make_tuple(cmd -> SynthFunName, to_string(arg_types), eval_sort(ctxt, cmd -> FunType));
    auto& symbol_table_zconst = ctxt.symbol_table_zfun[""];
    auto& symbol_table_bconst = ctxt.symbol_table_bfun[""];
    auto& symbol_table_bvconst = ctxt.symbol_table_bvfun[""];

    size_t ngz(0), ngb(0), ngbv(0);
    std::map <std::string, std::pair <id, sort>> grammar_symbols;
    for (auto& grule : cmd -> GrammarRules)
    {
        sort grule_s = eval_sort(ctxt, grule -> Sort);
        size_t x(0);
        switch (grule_s.sc)
        {
        case sort_class::Integer:
        {
            x = ngz;
            ngz++;
            break;
        }
        case sort_class::Boolean:
        {
            x = ngb;
            ngb++;
            break;
        }
        case sort_class::BV:
        {
            x = ngbv;
            ngbv++;
            break;
        }
        default:
        {
            assert(false);
        }
        }

        if (grammar_symbols.find(grule -> Symbol) != grammar_symbols.end()
                && grammar_symbols[grule -> Symbol].second != grule_s)
        {
            std::cerr << __LOGSTR__ << parse_loc(grule)
                      << "Error. Cannot redefine grammar symbol "
                      << grule -> Symbol << ". Exiting." << std::endl;
            exit(EXIT_FAILURE);
        }

        if (env.find(grule -> Symbol) != env.end()
                || symbol_table_zconst.find(grule -> Symbol) != symbol_table_zconst.end()
                || symbol_table_bconst.find(grule -> Symbol) != symbol_table_bconst.end()
                || symbol_table_bvconst.find(grule -> Symbol) != symbol_table_bvconst.end())
        {
            std::cerr << __LOGSTR__ << parse_loc(grule)
                      << "Error. Cannot redefine grammar symbol "
                      << grule -> Symbol << ". Exiting." << std::endl;
            exit(EXIT_FAILURE);
        }

        grammar_symbols[grule -> Symbol] = std::make_pair(id(x), grule_s);
    }

    std::map <agsymb_t, grammar::aprod_rule_v> arules;
    std::map <bgsymb_t, grammar::bprod_rule_v> brules;
    std::map <bvgsymb_t, grammar::bvprod_rule_v> bvrules;

    for (auto& grule : cmd -> GrammarRules)
    {
        size_t rule_no = 0;
        for (auto& prod : grule -> Expansions)
        {
            std::string symbol_prefix = grule -> Symbol + boost::lexical_cast <std::string> (rule_no++);
            std::pair <prod_rule_poly, sort> rule = interpret_gterm(ctxt, arules, brules, bvrules,
                                                    env, grammar_symbols, ngz, ngb, ngbv, symbol_prefix, prod);
            if (rule.second != eval_sort(ctxt, grule -> Sort))
            {
                std::cerr << __LOGSTR__ << parse_loc(prod)
                          << "Error. Type mismatch in production rule. Exiting." << std::endl;
                exit(EXIT_FAILURE);
            }

            id symb = grammar_symbols.at(grule -> Symbol).first;

            switch(rule.second.sc)
            {
            case sort_class::Integer:
            {
                arules[symb].push_back(boost::get <aprod_rule> (rule.first));
                break;
            }
            case sort_class::Boolean:
            {
                brules[symb].push_back(boost::get <bprod_rule> (rule.first));
                break;
            }
            case sort_class::BV:
            {
                bvrules[symb].push_back(boost::get <bvprod_rule> (rule.first));
                break;
            }
            default:
            {
                assert(false);
            }
            }
        }
    }

    if (grammar_symbols.find("Start") == grammar_symbols.end())
    {
        std::cerr << __LOGSTR__ << parse_loc(cmd)
                  << "Error. Unable to find grammar symbol Start. Exiting." << std::endl;
        exit(EXIT_FAILURE);
    }
    else if (grammar_symbols["Start"].second != eval_sort(ctxt, cmd -> FunType))
    {
        std::cerr << __LOGSTR__ << parse_loc(cmd)
                  << "Error. Sort of Start symbol incompatible with sort of synthesis function. Exiting." << std::endl;
        exit(EXIT_FAILURE);
    }

    ctxt.g = grammar(gsymbfunc(arules, true), gsymbfunc(brules, true), gsymbfunc(bvrules, true));
    switch (grammar_symbols["Start"].second.sc)
    {
    case sort_class::Integer:
    {
        ctxt.start_symbol = agsymb_t(grammar_symbols["Start"].first);
        break;
    }
    case sort_class::Boolean:
    {
        ctxt.start_symbol = bgsymb_t(grammar_symbols["Start"].first);
        break;
    }
    case sort_class::BV:
    {
        ctxt.start_symbol = bvgsymb_t(grammar_symbols["Start"].first);
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

#endif // __CONTEXT_INFR_GRAMMAR_H_

