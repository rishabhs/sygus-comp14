#ifndef __PARSER_IFACE_FUN_DECL_CMD_HPP_
#define __PARSER_IFACE_FUN_DECL_CMD_HPP_

#include "parser_iface.hpp"

namespace stoch {
namespace parser {

void visitor_t::VisitFunDeclCmd(const FunDeclCmd* Cmd)
{
    *streams.err << __LOGSTR__ << location(Cmd)
        << "Uninterpreted functions unsupported" << endl;
    assert (false);
}

} // namespace parser
} // namespace stoch

#endif // __PARSER_IFACE_FUN_DECL_CMD_HPP_

