#ifndef __PARSER_IFACE_VAR_DECL_CMD_HPP_
#define __PARSER_IFACE_VAR_DECL_CMD_HPP_

#include "parser_iface.hpp"

namespace stoch {
namespace parser {

void visitor_t::VisitVarDeclCmd(const VarDeclCmd* Cmd)
{
    string var_name = Cmd -> GetName();
    vector <sort> vs_empty;
    if (uq_var.find(var_name) != uq_var.end() ||
        macros.find(make_tuple(vs_empty, var_name)) != macros.end() ||
        synth.find(make_tuple(vs_empty, var_name)) != synth.end()) {
        *streams.err << __LOGSTR__ << location(Cmd)
            << "Attempting to redefine variable " << var_name << endl;
        exit(1);
    } else {
        sort sort_val = get_sort(Cmd -> GetSort());
        id x = uq_var.size();
        switch (sort_val.type) {
            case sort::type_t::INT: {
                uq_var[var_name] = dyn_expr(sort_val, aexpr_p(new zvar(x)));
                zfree.insert(x);
                break;
            } case sort::type_t::BOOL: {
                uq_var[var_name] = dyn_expr(sort_val, bexpr_p(new bvar(x)));
                bfree.insert(x);
                break;
            } case sort::type_t::BV: {
                uq_var[var_name] = dyn_expr(sort_val, bvexpr_p(new bvvar(x, sort_val.len)));
                bvfree.insert(make_tuple(x, sort_val.len));
                break;
            } default: {
                assert (false);
            }
        }
        *streams.log << __LOGSTR__ << location(Cmd) << "Variable " << var_name
            << " assigned identifier " << x.v << endl;
    }
}

} // namespace parser
} // namespace stoch

#endif // __PARSER_IFACE_VAR_DECL_CMD_HPP_

