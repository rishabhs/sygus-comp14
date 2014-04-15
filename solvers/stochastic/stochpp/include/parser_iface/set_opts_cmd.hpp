#ifndef __PARSER_IFACE_SET_OPTS_CMD_HPP_
#define __PARSER_IFACE_SET_OPTS_CMD_HPP_

#include "parser_iface.hpp"

namespace stoch {
namespace parser {

void visitor_t::VisitSetOptsCmd(const SetOptsCmd* cmd)
{
    for (const auto& opt : cmd -> GetOpts()) {
        if (opt.first == "random-seed") {
            seed = lexical_cast <size_t> (opt.second);
        } else if (opt.first == "expr-size") {
            expr_size = lexical_cast <size_t> (opt.second);
        } else if (opt.first == "samples") {
            samples = lexical_cast <size_t> (opt.second);
        } else if (opt.first == "mutation-limit") {
            mutation_limit = lexical_cast <size_t> (opt.second);
        } else if (opt.first == "beta") {
            beta = lexical_cast <double> (opt.second);
        } else if (opt.first == "move-probability") {
            move_probability = lexical_cast <double> (opt.second);
        } else {
            *streams.log << __LOGSTR__ << location(cmd) << "Ignoring unrecognized option, ("
                << opt.first << " " << opt.second << ")." << endl;
        }
    }
}

} // namespace parser
} // namespace stoch

#endif // __PARSER_IFACE_SET_OPTS_CMD_HPP_

