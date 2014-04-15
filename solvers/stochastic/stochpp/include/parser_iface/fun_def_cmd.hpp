#ifndef __PARSER_IFACE_FUN_DEF_CMD_HPP_
#define __PARSER_IFACE_FUN_DEF_CMD_HPP_

#include "parser_iface.hpp"

namespace stoch {
namespace parser {

void visitor_t::VisitFunDefCmd(const FunDefCmd* Cmd)
{
    map <string, dyn_expr> args;
    vector <sort> arg_sign;
    subst_t macro_args;

    for (auto& arg_sort_pair : Cmd -> GetArgs()) {
        sort s = get_sort(arg_sort_pair -> GetSort());
        arg_sign.push_back(s);
        id arg_id = args.size();

        switch (s.type) {
            case sort::type_t::INT: {
                args[arg_sort_pair -> GetName()] = dyn_expr(s, aexpr_p(new zvar(arg_id)));
                std::get <0> (macro_args)[arg_id] = aexpr_p(new zvar(arg_id));
                break;
            } case sort::type_t::BOOL: {
                args[arg_sort_pair -> GetName()] = dyn_expr(s, bexpr_p(new bvar(arg_id)));
                std::get <1> (macro_args)[arg_id] = bexpr_p(new bvar(arg_id));
                break;
            } case sort::type_t::BV: {
                args[arg_sort_pair -> GetName()] = dyn_expr(s, bvexpr_p(new bvvar(arg_id, s.len)));
                std::get <2> (macro_args)[arg_id] = bvexpr_p(new bvvar(arg_id, s.len));
                break;
            } default: {
                assert (false);
            }
        }
    }

    sort fun_sort = get_sort(Cmd -> GetSort());
    dyn_expr macro = get_macro(Cmd -> GetTerm(), args);

    if (macro.s != fun_sort) {
        *streams.err << __LOGSTR__ << location(Cmd) << "Type mismatch." << endl;
        exit(1);
    }

    macros[make_tuple(arg_sign, Cmd -> GetFunName())] = macro.make_macro(Cmd -> GetFunName(), macro_args);

    *streams.log << __LOGSTR__ << location(Cmd) << "Defined macro "
        << (Cmd -> GetFunName()) << ": " << macro << endl;
}

dyn_expr visitor_t::get_macro(const Term *t, const map <string, dyn_expr>& args) const
{
    if (auto tp = dynamic_cast <const FunTerm *> (t)) {
        return get_macro_int(tp, args);
    } else if (auto tp = dynamic_cast <const LiteralTerm *> (t)) {
        return get_lit(tp -> GetLiteral());
    } else if (auto tp = dynamic_cast <const SymbolTerm *> (t)) {
        return get_macro_int(tp, args);
    } else if (auto tp = dynamic_cast <const LetTerm *> (t)) {
        return get_macro_int(tp, args);
    } else {
        assert (false);
    }
}

dyn_expr visitor_t::get_lit(const Literal *lit) const
{
    const string& lit_str = lit -> GetLiteralString();

    if (boost::regex_match(lit_str, boost::regex("-?\\d+"))) {
        aexpr_p e(new cz(lexical_cast <z_class> (lit_str)));
        return dyn_expr(sort::type_t::INT, e);
    } else if (boost::regex_match(lit_str, boost::regex("(true)|(false)"))) {
        bexpr_p e(new cb(lit_str == "true"));
        return dyn_expr(sort::type_t::BOOL, e);
    } else if (boost::regex_match(lit_str, boost::regex("(#b[01]+)|(#x([0-9]|[a-f]|[A-F])+)"))) {
        bv v(lit_str);
        bvexpr_p e(new cbv(v));
        return dyn_expr(sort(sort::type_t::BV, v.len), e);
    } else {
        *streams.err << __LOGSTR__ << location(lit) << "Unsupported / ill-formed literal detected." << endl;
        exit(1);
    }
}

dyn_expr visitor_t::get_macro_int(const FunTerm *tp, const map <string, dyn_expr>& args) const
{
    vector <sort> arg_sign;
    subst_t subst;

    for (size_t i = 0; i < tp -> GetArgs().size(); i++) {
        dyn_expr arg_i = get_macro(tp -> GetArgs()[i], args);
        switch (arg_i.s.type) {
            case sort::type_t::INT: {
                std::get <0> (subst)[arg_sign.size()] = boost::get <aexpr_p> (arg_i.e);
                break;
            } case sort::type_t::BOOL: {
                std::get <1> (subst)[arg_sign.size()] = boost::get <bexpr_p> (arg_i.e);
                break;
            } case sort::type_t::BV: {
                std::get <2> (subst)[arg_sign.size()] = boost::get <bvexpr_p> (arg_i.e);
                break;
            } default: {
                assert (false);
            }
        }
        arg_sign.push_back(arg_i.s);
    }

    const string& fun_name = tp -> GetFunName();

    if (macros.find(make_tuple(arg_sign, fun_name)) != macros.end()) {
        dyn_expr macro = macros.at(make_tuple(arg_sign, fun_name));
        return macro.subst(subst);
    } else {
        *streams.err << __LOGSTR__ << location(tp) << "Couldn't resolve symbol "
            << tp -> GetFunName() << endl;
        exit(1);
    }
}

dyn_expr visitor_t::get_macro_int(const SymbolTerm *tp, const map <string, dyn_expr>& args) const
{
    vector <sort> ve;
    if (args.find(tp -> GetSymbol()) != args.end()) {
        return args.at(tp -> GetSymbol());
    } else if (macros.find(make_tuple(ve, tp -> GetSymbol())) != macros.end()) {
        return macros.at(make_tuple(ve, tp -> GetSymbol()));
    } else {
        *streams.err << __LOGSTR__ << location(tp) << "Couldn't resolve symbol "
            << tp -> GetSymbol() << endl;
        exit(1);
    }
}

dyn_expr visitor_t::get_macro_int(const LetTerm *tp, const map <string, dyn_expr>& args) const
{
    subst_t subst;
    map <string, dyn_expr> argsp(args);

    // *streams.err << __LOGSTR__ << location(tp) << "Beginning parse let." << endl;

    for (auto& arg : tp -> GetBindings()) {
        auto& arg_name = arg -> GetVarName();
        auto arg_expr = get_macro(arg -> GetBoundToTerm(), args);

        if (get_sort(arg -> GetVarSort()) != arg_expr.s) {
            *streams.err << __LOGSTR__ << location(arg) << "Type mismatch." << endl;
            exit(1);
        } else if (args.find(arg_name) == args.end() ||
            args.at(arg_name).s == arg_expr.s) {
            id x = argsp.size();
            switch (arg_expr.s.type) {
                case sort::type_t::INT: {
                    argsp[arg_name] = dyn_expr(arg_expr.s, aexpr_p(new zvar(x)));
                    std::get <0> (subst)[x.v] = boost::get <aexpr_p> (arg_expr.e);
                    break;
                } case sort::type_t::BOOL: {
                    argsp[arg_name] = dyn_expr(arg_expr.s, bexpr_p(new bvar(x)));
                    std::get <1> (subst)[x.v] = boost::get <bexpr_p> (arg_expr.e);
                    break;
                } case sort::type_t::BV: {
                    argsp[arg_name] = dyn_expr(arg_expr.s, bvexpr_p(new bvvar(x, arg_expr.s.len)));
                    std::get <2> (subst)[x.v] = boost::get <bvexpr_p> (arg_expr.e);
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

    auto ans = get_macro(tp -> GetBoundInTerm(), argsp).bind(subst);
    // *streams.err << __LOGSTR__ << location(tp) << "Ending parse let: " << ans << endl;

    return ans;
}

} // namespace parser
} // namespace stoch

#endif // __PARSER_IFACE_FUN_DEF_CMD_HPP_

