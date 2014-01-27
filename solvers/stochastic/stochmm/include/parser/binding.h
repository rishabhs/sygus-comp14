#ifndef __PARSER_BINDING_H_
#define __PARSER_BINDING_H_

#include "context.h"
#include "parser/iface.h"

namespace stoch { namespace context {

int parse(const std::string& fname) {
	sl2p::SynthLib2Parser parser;
	context ctxt;

	parser.AddSetLogicCallback([&](const sl2p::SetLogicCmd *cmd) -> int {
			return set_logic(ctxt, cmd);
		});
	parser.AddFunDefCallback([&](const sl2p::FunDefCmd *cmd) -> int {
			return define_fun(ctxt, cmd);
		});
	parser.AddVarDeclCallback([&](const sl2p::VarDeclCmd *cmd) -> int {
			return declare_var(ctxt, cmd);
		});
	parser.AddSynthFunCallback([&](const sl2p::SynthFunCmd *cmd) -> int {
			return declare_synth_fun(ctxt, cmd);
		});
	parser.AddConstraintCallback([&](const sl2p::ConstraintCmd *cmd) -> int {
			return add_constraint(ctxt, cmd);
		});
	parser.AddCheckSynthCallback([&]() -> int {
			return solve(ctxt);
		});
	parser.AddSortDefCallback([&](const sl2p::SortDefCmd *cmd) -> int {
			return define_sort(ctxt, cmd);
		});
	parser.AddSetOptsCallback([&](const sl2p::SetOptsCmd *cmd) -> int {
			return set_options(ctxt, cmd);
		});

	return parser(fname);
}

}}

#endif // __PARSER_BINDING_H_

