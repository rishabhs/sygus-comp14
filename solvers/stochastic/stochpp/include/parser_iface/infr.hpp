#ifndef __PARSER_IFACE_INFR_HPP_
#define __PARSER_IFACE_INFR_HPP_

#include "parser_iface.hpp"

namespace stoch {
namespace parser {

string location(const ASTBase *token)
{
    auto& loc = token -> GetLocation();
    return std::string("At line ") + boost::lexical_cast <string> (loc.GetLineNum())
        + ", column " + boost::lexical_cast <string> (loc.GetColNum()) + ". ";
}

} // namespace parser
} // namespace stoch

#include "parser_iface/sort.hpp"
#include "parser_iface/dyn.hpp"

#include "parser_iface/set_logic_cmd.hpp"
#include "parser_iface/sort_def_cmd.hpp"
#include "parser_iface/var_decl_cmd.hpp"
#include "parser_iface/fun_decl_cmd.hpp"
#include "parser_iface/fun_def_cmd.hpp"
#include "parser_iface/synth_fun_cmd.hpp"
#include "parser_iface/constraint_cmd.hpp"
#include "parser_iface/check_synth_cmd.hpp"
#include "parser_iface/set_opts_cmd.hpp"

#endif // __PARSER_IFACE_INFR_HPP_

