#ifndef __PARSER_IFACE_CONSTRAINT_CMD_HPP_
#define __PARSER_IFACE_CONSTRAINT_CMD_HPP_

#include "parser_iface.hpp"

namespace stoch {
namespace parser {

void visitor_t::VisitConstraintCmd(const ConstraintCmd *cmd)
{
    map <string, dyn_fexpr> args;

    dyn_fexpr new_constr = get_constraint(cmd -> GetTerm(), args);
    if (new_constr.s.type != sort::type_t::BOOL) {
        *streams.err << __LOGSTR__ << location(cmd) << "Constraints should be boolean." << endl;
        exit(1);
    }

    *streams.log << __LOGSTR__ << location(cmd) << "Adding constraint: "
        << *boost::get <bfexpr_p> (new_constr.e) << endl;
    this -> constraint = this -> constraint && boost::get <bfexpr_p> (new_constr.e);
}

dyn_fexpr visitor_t::get_constraint(const Term *t, const map <string, dyn_fexpr>& args) const
{
    if (auto tp = dynamic_cast <const FunTerm *> (t)) {
        return get_constraint_int(tp, args);
    } else if (auto tp = dynamic_cast <const LiteralTerm *> (t)) {
        return dyn_fexpr(get_lit(tp -> GetLiteral()));
    } else if (auto tp = dynamic_cast <const SymbolTerm *> (t)) {
        return get_constraint_int(tp, args);
    } else if (auto tp = dynamic_cast <const LetTerm *> (t)) {
        return get_constraint_int(tp, args);
    } else {
        assert (false);
    }
}

dyn_fexpr visitor_t::get_constraint_int(const FunTerm *tp, const map <string, dyn_fexpr>& args) const
{
    vector <sort> arg_sign;
    fsubst_t fsubst;
    vector <afexpr_p> zargs;
    vector <bfexpr_p> bargs;
    vector <bvfexpr_p> bvargs;

    for (size_t i = 0; i < tp -> GetArgs().size(); i++) {
        dyn_fexpr arg_i = get_constraint(tp -> GetArgs()[i], args);
        switch (arg_i.s.type) {
            case sort::type_t::INT: {
                std::get <0> (fsubst)[arg_sign.size()] = boost::get <afexpr_p> (arg_i.e);
                zargs.push_back(boost::get <afexpr_p> (arg_i.e));
                break;
            } case sort::type_t::BOOL: {
                std::get <1> (fsubst)[arg_sign.size()] = boost::get <bfexpr_p> (arg_i.e);
                bargs.push_back(boost::get <bfexpr_p> (arg_i.e));
                break;
            } case sort::type_t::BV: {
                std::get <2> (fsubst)[arg_sign.size()] = boost::get <bvfexpr_p> (arg_i.e);
                bvargs.push_back(boost::get <bvfexpr_p> (arg_i.e));
                break;
            } default: {
                assert (false);
            }
        }
        arg_sign.push_back(arg_i.s);
    }

    const string& fun_name = tp -> GetFunName();

    if (macros.find(make_tuple(arg_sign, fun_name)) != macros.end()) {
        dyn_fexpr macro(macros.at(make_tuple(arg_sign, fun_name)));
        return macro.subst(fsubst);
    } else if (synth.find(make_tuple(arg_sign, fun_name)) != synth.end()) {
        auto fr = synth.at(make_tuple(arg_sign, fun_name));
        sort s(std::get <1> (fr).s);
        id f = std::get <0> (fr);
        return get_fcall(s, f, zargs, bargs, bvargs);
    } else {
        *streams.err << __LOGSTR__ << location(tp) << "Couldn't resolve symbol "
            << tp -> GetFunName() << endl;
        exit(1);
    }

    return dyn_fexpr();
}

dyn_fexpr visitor_t::get_constraint_int(const SymbolTerm *tp, const map <string, dyn_fexpr>& args) const
{
    vector <sort> ve;
    if (args.find(tp -> GetSymbol()) != args.end()) {
        return args.at(tp -> GetSymbol());
    } else if (uq_var.find(tp -> GetSymbol()) != uq_var.end()) {
        return dyn_fexpr(uq_var.at(tp -> GetSymbol()));
    } else if (macros.find(make_tuple(ve, tp -> GetSymbol())) != macros.end()) {
        return dyn_fexpr(macros.at(make_tuple(ve, tp -> GetSymbol())));
    } else if (synth.find(make_tuple(ve, tp -> GetSymbol())) != synth.end()) {
        auto fr = synth.at(make_tuple(ve, tp -> GetSymbol()));
        sort s(std::get <1> (fr).s);
        id f = std::get <0> (fr);
        vector <afexpr_p> zargs;
        vector <bfexpr_p> bargs;
        vector <bvfexpr_p> bvargs;
        return get_fcall(s, f, zargs, bargs, bvargs);
    } else {
        *streams.err << __LOGSTR__ << location(tp) << "Couldn't resolve symbol "
            << tp -> GetSymbol() << endl;
        exit(1);
    }
}

dyn_fexpr visitor_t::get_constraint_int(const LetTerm *tp, const map <string, dyn_fexpr>& args) const
{
    fsubst_t fsubst;
    map <string, dyn_fexpr> argsp(args);

    for (auto& arg : tp -> GetBindings()) {
        auto& arg_name = arg -> GetVarName();
        auto arg_fexpr = get_constraint(arg -> GetBoundToTerm(), args);

        if (get_sort(arg -> GetVarSort()) != arg_fexpr.s) {
            *streams.err << __LOGSTR__ << location(arg) << "Type mismatch." << endl;
            exit(1);
        } else if (args.find(arg_name) == args.end() ||
            args.at(arg_name).s == arg_fexpr.s) {
            id x = argsp.size();
            switch (arg_fexpr.s.type) {
                case sort::type_t::INT: {
                    argsp[arg_name] = dyn_expr(arg_fexpr.s, aexpr_p(new zvar(x)));
                    std::get <0> (fsubst)[x.v] = boost::get <afexpr_p> (arg_fexpr.e);
                    break;
                } case sort::type_t::BOOL: {
                    argsp[arg_name] = dyn_expr(arg_fexpr.s, bexpr_p(new bvar(x)));
                    std::get <1> (fsubst)[x.v] = boost::get <bfexpr_p> (arg_fexpr.e);
                    break;
                } case sort::type_t::BV: {
                    argsp[arg_name] = dyn_expr(arg_fexpr.s, bvexpr_p(new bvvar(x, arg_fexpr.s.len)));
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

    return get_constraint(tp -> GetBoundInTerm(), argsp).bind(fsubst);
}

dyn_fexpr visitor_t::get_fcall(const sort& s, const id& f,
    const vector <afexpr_p>& zargs, const vector <bfexpr_p>& bargs,
    const vector <bvfexpr_p>& bvargs) const
{
    switch (s.type) {
        case sort::type_t::INT: {
            afexpr_p fe(new fzcall(f, zargs, bargs, bvargs));
            return dyn_fexpr(s, fe);
        } case sort::type_t::BOOL: {
            bfexpr_p fe(new fbcall(f, zargs, bargs, bvargs));
            return dyn_fexpr(s, fe);
        } case sort::type_t::BV: {
            bvfexpr_p fe(new fbvcall(f, zargs, bargs, bvargs, s.len));
            return dyn_fexpr(s, fe);
        } default: {
            assert (false);
        }
    }
}

} // namespace parser
} // namespace stoch

#endif // __PARSER_IFACE_CONSTRAINT_CMD_HPP_

