#ifndef __PARSER_IFACE_SYNTH_FUN_CMD_HPP_
#define __PARSER_IFACE_SYNTH_FUN_CMD_HPP_

#include "parser_iface.hpp"

namespace stoch {
namespace parser {

void visitor_t::VisitSynthFunCmd(const SynthFunCmd* Cmd)
{
    map <string, dyn_fexpr> arg_map;
    vector <sort> arg_sign;
    var_set arg_set;

    size_t nzargs(0), nbargs(0), nbvargs(0);
    for (auto& arg_sort_pair : Cmd -> GetArgs()) {
        sort s = get_sort(arg_sort_pair -> GetSort());
        arg_sign.push_back(s);

        switch (s.type) {
            case sort::type_t::INT: {
                arg_map[arg_sort_pair -> GetName()] = dyn_fexpr(s, afexpr_p(new fzvar(nzargs)));
                std::get <0> (arg_set).insert(nzargs);
                nzargs++;
                break;
            } case sort::type_t::BOOL: {
                arg_map[arg_sort_pair -> GetName()] = dyn_fexpr(s, bfexpr_p(new fbvar(nbargs)));
                std::get <1> (arg_set).insert(nbargs);
                nbargs++;
                break;
            } case sort::type_t::BV: {
                arg_map[arg_sort_pair -> GetName()] = dyn_fexpr(s, bvfexpr_p(new fbvvar(nbvargs, s.len)));
                std::get <2> (arg_set).insert(nbvargs);
                nbvargs++;
                break;
            } default: {
                assert (false);
            }
        }
    }

    arg_map = grammar_symbol_map(Cmd, arg_map);

    map <string, tuple <sort, variant <agsymb_t, bgsymb_t, bvgsymb_t>>> nonterm_map;
    for (const NTDef* nonterm : Cmd -> GetGrammarRules()) {
        tuple <vector <sort>, string> macros_index(vector <sort> (), nonterm -> GetName());
        if (this -> macros.find(macros_index) != this -> macros.end()) {
            *streams.err << __LOGSTR__ << location(nonterm)
                << "Name of non-terminal clashes with previously defined 0-arity macro." << endl;
            exit(1);
        }

        if (nonterm_map.find(nonterm -> GetName()) != nonterm_map.end()) {
            *streams.err << __LOGSTR__ << location(nonterm)
                << "Error. Attempting to redefine non-terminal " << nonterm -> GetName()
                << "." << endl;
            exit(1);
        }

        if (arg_map.find(nonterm -> GetName()) != arg_map.end()) {
            *streams.err << __LOGSTR__ << location(nonterm)
                << "Error. Nonterminal " << nonterm -> GetName() << " "
                << "has name clash with previously declared function argument "
                << "or let-bound variable." << endl;
            exit(1);
        }

        sort nonterm_sort = get_sort(nonterm -> GetSort());
        id nonterm_id(nonterm_map.size());
        switch (nonterm_sort.type) {
            case sort::type_t::INT: {
                nonterm_map[nonterm -> GetName()] = make_tuple(nonterm_sort, agsymb_t(nonterm_id));
                break;
            } case sort::type_t::BOOL: {
                nonterm_map[nonterm -> GetName()] = make_tuple(nonterm_sort, bgsymb_t(nonterm_id));
                break;
            } case sort::type_t::BV: {
                nonterm_map[nonterm -> GetName()] = make_tuple(nonterm_sort, bvgsymb_t(nonterm_id, nonterm_sort.len));
                break;
            } default: {
                assert (false);
            }
        }
    }

    map <agsymb_t, vector <aprod_rule_p>> arules;
    map <bgsymb_t, vector <bprod_rule_p>> brules;
    map <bvgsymb_t, vector <bvprod_rule_p>> bvrules;

    for (const NTDef* nonterm : Cmd -> GetGrammarRules()) {
        for (const GTerm* expansion : nonterm -> GetExpansions()) {
            grammar_rule_args gra(arg_map, nonterm_map);
            auto dfe = grammar_rule(expansion, gra);

            if (get_sort(nonterm -> GetSort()) != dfe.s) {
                *streams.err << __LOGSTR__ << location(expansion)
                    << "Type mismatch while parsing expansion." << endl;
                exit(1);
            }

            switch (dfe.s.type) {
                case sort::type_t::INT: {
                    auto symb = boost::get <agsymb_t> (std::get <1> (nonterm_map[nonterm -> GetName()]));
                    auto dfep = boost::get <afexpr_p> (dfe.e);
                    aprod_rule_p rule(new aprod_rule(gra.achild_v, gra.bchild_v, gra.bvchild_v, dfep));
                    arules[symb].push_back(rule);
                    break;
                } case sort::type_t::BOOL: {
                    auto symb = boost::get <bgsymb_t> (std::get <1> (nonterm_map[nonterm -> GetName()]));
                    auto dfep = boost::get <bfexpr_p> (dfe.e);
                    bprod_rule_p rule(new bprod_rule(gra.achild_v, gra.bchild_v, gra.bvchild_v, dfep));
                    brules[symb].push_back(rule);
                    break;
                } case sort::type_t::BV: {
                    auto symb = boost::get <bvgsymb_t> (std::get <1> (nonterm_map[nonterm -> GetName()]));
                    auto dfep = boost::get <bvfexpr_p> (dfe.e);
                    bvprod_rule_p rule(new bvprod_rule(gra.achild_v, gra.bchild_v, gra.bvchild_v, dfep));
                    bvrules[symb].push_back(rule);
                    break;
                } default: {
                    assert (false);
                }
            }
        }
    }

    sort fun_sort = get_sort(Cmd -> GetSort());
    if (nonterm_map.find("Start") == nonterm_map.end() ||
        std::get <0> (nonterm_map["Start"]) != fun_sort) {
        *streams.err << __LOGSTR__ << location(Cmd)
            << "Missing or incorrectly typed non-terminal Start." << endl;
        exit(1);
    }

    grammar g(arules, brules, bvrules, std::get <1> (nonterm_map["Start"]));
    g = unroll(g, arg_set);
    dyn_grammar dg(fun_sort, g);
    tuple <vector <sort>, string> synth_index(arg_sign, Cmd -> GetFunName());
    if (synth.find(synth_index) != synth.end() ||
        macros.find(synth_index) != macros.end() ||
        (arg_sign.empty() && uq_var.find(Cmd -> GetFunName()) != uq_var.end())) {
        *streams.err << __LOGSTR__ << location(Cmd)
            << "Naming conflict with previously defined synthesis function, "
            << "macro or universally quantified variable." << endl;
        exit(1);
    }

    g.print(*streams.log << __LOGSTR__ << location(Cmd) << "Grammar unrolled." << endl);

    id f(synth.size());
    synth[synth_index] = make_tuple(f, dg);

    switch (fun_sort.type) {
        case sort::type_t::INT: {
            afuns[f] = make_tuple(dg.g, boost::get <agsymb_t> (dg.g.start));
            break;
        } case sort::type_t::BOOL: {
            bfuns[f] = make_tuple(dg.g, boost::get <bgsymb_t> (dg.g.start));
            break;
        } case sort::type_t::BV: {
            // bvfuns[f] = make_tuple(dg.g, boost::get <bvgsymb_t> (dg.g.start));
            bvfuns.insert(pair <id, tuple <grammar, bvgsymb_t>> (f,
                make_tuple(dg.g, boost::get <bvgsymb_t> (dg.g.start))));
            break;
        } default: {
            assert (false);
        }
    }
}

map <string, dyn_fexpr> visitor_t::grammar_symbol_map(const SynthFunCmd* Cmd,
    const map <string, dyn_fexpr>& arg_map) const
{
    map <string, dyn_fexpr> ans(arg_map);

    for (const NTDef* nonterm : Cmd -> GetGrammarRules()) {
        for (const GTerm* expansion : nonterm -> GetExpansions()) {
            ans = grammar_symbol_map(expansion, ans);
        }
    }

    return ans;
}

map <string, dyn_fexpr> visitor_t::grammar_symbol_map(const GTerm* gterm,
    const map <string, dyn_fexpr>& arg_map) const
{
    map <string, dyn_fexpr> ans(arg_map);

    if (dynamic_cast <const SymbolGTerm*> (gterm)) {
    } else if (auto gtermp = dynamic_cast <const FunGTerm*> (gterm)) {
        for (const GTerm* arg : gtermp -> GetArgs()) {
            ans = grammar_symbol_map(arg, ans);
        }
    } else if (dynamic_cast <const LiteralGTerm*> (gterm)) {
    } else if (dynamic_cast <const ConstantGTerm*> (gterm)) {
        *streams.err << __LOGSTR__ << location(gterm)
            << "Construct (Constant ...) unsupported." << endl;
        exit(1);
    } else if (dynamic_cast <const VariableGTerm*> (gterm)) {
        *streams.err << __LOGSTR__ << location(gterm)
            << "Construct (Variable ...) unsupported." << endl;
        exit(1);
    } else if (auto gtermp = dynamic_cast <const LetGTerm*> (gterm)) {
        for (const LetBindingGTerm* binding : gtermp -> GetBindings()) {
            ans = grammar_symbol_map(binding, ans);
        }
        ans = grammar_symbol_map(gtermp -> GetBoundInTerm(), ans);
    } else {
        *streams.err << __LOGSTR__ << "Could not deduce type of GTerm at " << location(gterm) << endl;
        assert (false);
    }

    return ans;
}

map <string, dyn_fexpr> visitor_t::grammar_symbol_map(const LetBindingGTerm* gterm,
    const map <string, dyn_fexpr>& arg_map) const
{
    map <string, dyn_fexpr> ans(arg_map);

    tuple <vector <sort>, string> macros_index(vector <sort> (), gterm -> GetVarName());
    if (this -> macros.find(macros_index) != this -> macros.end()) {
        *streams.err << __LOGSTR__ << location(gterm)
            << "Name of let-bound variable clashes with previously defined 0-arity macro." << endl;
        exit(1);
    }
    if (ans.find(gterm -> GetVarName()) != ans.end()) {
        if (ans[gterm -> GetVarName()].s != get_sort(gterm -> GetVarSort())) {
            *streams.err << __LOGSTR__ << location(gterm)
                << "Type mismatch." << endl;
            exit(1);
        }
    } else {
        auto var_sort = get_sort(gterm -> GetVarSort());
        id var_id(ans.size());
        switch (var_sort.type) {
            case sort::type_t::INT: {
                ans[gterm -> GetVarName()] = dyn_fexpr(var_sort, afexpr_p(new fzvar(var_id)));
                break;
            } case sort::type_t::BOOL: {
                ans[gterm -> GetVarName()] = dyn_fexpr(var_sort, bfexpr_p(new fbvar(var_id)));
                break;
            } case sort::type_t::BV: {
                ans[gterm -> GetVarName()] = dyn_fexpr(var_sort, bvfexpr_p(new fbvvar(var_id, var_sort.len)));
                break;
            } default: {
                assert (false);
            }
        }
    }

    ans = grammar_symbol_map(gterm -> GetBoundToTerm(), ans);
    return ans;
}

dyn_fexpr visitor_t::grammar_rule(const GTerm *t, grammar_rule_args& args) const
{
    if (auto tp = dynamic_cast <const FunGTerm *> (t)) {
        return grammar_rule_int(tp, args);
    } else if (auto tp = dynamic_cast <const LiteralGTerm *> (t)) {
        return dyn_fexpr(get_lit(tp -> GetLiteral()));
    } else if (auto tp = dynamic_cast <const SymbolGTerm *> (t)) {
        return grammar_rule_int(tp, args);
    } else if (auto tp = dynamic_cast <const LetGTerm *> (t)) {
        return grammar_rule_int(tp, args);
    } else if (dynamic_cast <const ConstantGTerm *> (t)) {
        *streams.err << __LOGSTR__ << location(t)
            << "Construct (Constant ...) unimplemented." << endl;
        assert (false);
    } else if (dynamic_cast <const VariableGTerm *> (t)) {
        *streams.err << __LOGSTR__ << location(t)
            << "Constructs (Variable ...) and (InputVariable ...) unimplemented."
            << endl;
        assert (false);
    } else {
        assert (false);
    }
}

dyn_fexpr visitor_t::grammar_rule_int(const FunGTerm *tp, grammar_rule_args& args) const
{
    vector <sort> arg_sign;
    fsubst_t fsubst;

    for (size_t i = 0; i < tp -> GetArgs().size(); i++) {
        dyn_fexpr arg_i = grammar_rule(tp -> GetArgs()[i], args);
        switch (arg_i.s.type) {
            case sort::type_t::INT: {
                std::get <0> (fsubst)[arg_sign.size()] = boost::get <afexpr_p> (arg_i.e);
                break;
            } case sort::type_t::BOOL: {
                std::get <1> (fsubst)[arg_sign.size()] = boost::get <bfexpr_p> (arg_i.e);
                break;
            } case sort::type_t::BV: {
                std::get <2> (fsubst)[arg_sign.size()] = boost::get <bvfexpr_p> (arg_i.e);
                break;
            } default: {
                assert (false);
            }
        }
        arg_sign.push_back(arg_i.s);
    }

    const string& fun_name = tp -> GetName();

    if (macros.find(make_tuple(arg_sign, fun_name)) != macros.end()) {
        dyn_fexpr fmacro(macros.at(make_tuple(arg_sign, fun_name)));
        return fmacro.subst(fsubst);
    } else {
        *streams.err << __LOGSTR__ << location(tp) << "Couldn't resolve symbol "
            << tp -> GetName() << endl;
        exit(1);
    }
}

dyn_fexpr visitor_t::grammar_rule_int(const SymbolGTerm *tp, grammar_rule_args& args) const
{
    vector <sort> vs;

    if (macros.find(make_tuple(vs, tp -> GetSymbol())) != macros.end()) {
        return dyn_fexpr(macros.at(make_tuple(vs, tp -> GetSymbol())));
    } else if (args.arg_map.find(tp -> GetSymbol()) != args.arg_map.end()) {
        return args.arg_map.at(tp -> GetSymbol());
    } else if (args.nonterm_map.find(tp -> GetSymbol()) != args.nonterm_map.end()) {
        auto nt = args.nonterm_map.at(tp -> GetSymbol());
        switch (std::get <0> (nt).type) {
            case sort::type_t::INT: {
                afexpr_p ans(new fzcall(args.achild_v.size()));
                args.achild_v.push_back(boost::get <agsymb_t> (std::get <1> (nt)));
                return dyn_fexpr(std::get <0> (nt), ans);
            } case sort::type_t::BOOL: {
                bfexpr_p ans(new fbcall(args.bchild_v.size()));
                args.bchild_v.push_back(boost::get <bgsymb_t> (std::get <1> (nt)));
                return dyn_fexpr(std::get <0> (nt), ans);
            } case sort::type_t::BV: {
                bvfexpr_p ans(new fbvcall(args.bvchild_v.size(), std::get <0> (nt).len));
                args.bvchild_v.push_back(boost::get <bvgsymb_t> (std::get <1> (nt)));
                return dyn_fexpr(std::get <0> (nt), ans);
            } default: {
                assert (false);
            }
        }
    } else {
        *streams.err << __LOGSTR__ << location(tp) << "Unable to resolve symbol " << tp -> GetSymbol() << "." << endl;
        exit(1);
    }
}

dyn_fexpr visitor_t::grammar_rule_int(const LetGTerm *tp, grammar_rule_args& args) const
{
    fsubst_t fsubst;

    // *streams.err << __LOGSTR__ << location(tp) << "Beginning parse let." << endl;

    for (auto& arg : tp -> GetBindings()) {
        auto& arg_name = arg -> GetVarName();
        auto arg_fexpr = grammar_rule(arg -> GetBoundToTerm(), args);

        if (get_sort(arg -> GetVarSort()) != arg_fexpr.s) {
            *streams.err << __LOGSTR__ << location(arg) << "Type mismatch." << endl;
            exit(1);
        } else if (args.arg_map.find(arg_name) == args.arg_map.end() ||
            args.arg_map.at(arg_name).s == arg_fexpr.s) {
            switch (arg_fexpr.s.type) {
                case sort::type_t::INT: {
                    afexpr_p fe(boost::get <afexpr_p> (args.arg_map.at(arg_name).e));
                    id x(dynamic_pointer_cast <const fzvar> (fe) -> x);
                    std::get <0> (fsubst)[x.v] = boost::get <afexpr_p> (arg_fexpr.e);
                    break;
                } case sort::type_t::BOOL: {
                    bfexpr_p fe(boost::get <bfexpr_p> (args.arg_map.at(arg_name).e));
                    id x(dynamic_pointer_cast <const fbvar> (fe) -> x);
                    std::get <1> (fsubst)[x.v] = boost::get <bfexpr_p> (arg_fexpr.e);
                    break;
                } case sort::type_t::BV: {
                    bvfexpr_p fe(boost::get <bvfexpr_p> (args.arg_map.at(arg_name).e));
                    id x(dynamic_pointer_cast <const fbvvar> (fe) -> x);
                    std::get <2> (fsubst)[x.v] = boost::get <bvfexpr_p> (arg_fexpr.e);
                    break;
                } default: {
                    assert (false);
                }
            }
        } else {
            *streams.err << __LOGSTR__ << location(arg) << "Type mismatch." << endl;
            exit(1);
        }
    }

    auto ans = grammar_rule(tp -> GetBoundInTerm(), args).bind(fsubst);
    // *streams.err << __LOGSTR__ << location(tp) << "Ending parse let: " << ans << endl;

    return ans;
}

} // namespace parser
} // namespace stoch

#endif // __PARSER_IFACE_SYNTH_FUN_CMD_HPP_

