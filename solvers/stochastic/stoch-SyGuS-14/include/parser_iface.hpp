#ifndef __PARSER_IFACE_HPP_
#define __PARSER_IFACE_HPP_

#include "nonstd.hpp"
#include "base.hpp"

#include "SynthLib2ParserIFace.hpp"

namespace stoch {
namespace parser {

namespace sl2p = SynthLib2Parser;
using namespace sl2p;

struct sort;
struct dyn_expr;
struct dyn_fexpr;
struct dyn_grammar;

struct visitor_t : public ASTVisitorBase
{
    visitor_t() : ASTVisitorBase("stoch::parser::visitor_t"), constraint(new fcb(true)),
        seed(random_device()()), expr_size(0), samples(100), mutation_limit(-1),
        beta(0.5), move_probability(0.01)
    {}

    virtual void VisitSetLogicCmd(const SetLogicCmd* Cmd);

    virtual void VisitSortDefCmd(const SortDefCmd* Cmd);
    sort get_sort(const SortExpr *expr) const;

    virtual void VisitVarDeclCmd(const VarDeclCmd* Cmd);
    virtual void VisitFunDeclCmd(const FunDeclCmd* Cmd);

    virtual void VisitFunDefCmd(const FunDefCmd* Cmd);
    dyn_expr get_macro(const Term *t, const map <string, dyn_expr>& args) const;
    dyn_expr get_lit(const Literal *lit) const;
    dyn_expr get_macro_int(const FunTerm *tp, const map <string, dyn_expr>& args) const;
    dyn_expr get_macro_int(const SymbolTerm *tp, const map <string, dyn_expr>& args) const;
    dyn_expr get_macro_int(const LetTerm *tp, const map <string, dyn_expr>& args) const;

    virtual void VisitSynthFunCmd(const SynthFunCmd *cmd);

    map <string, dyn_fexpr> grammar_symbol_map(const SynthFunCmd* Cmd,
        const map <string, dyn_fexpr>& args) const;
    map <string, dyn_fexpr> grammar_symbol_map(const GTerm* gterm,
        const map <string, dyn_fexpr>& args) const;
    map <string, dyn_fexpr> grammar_symbol_map(const LetBindingGTerm* gterm,
        const map <string, dyn_fexpr>& args) const;

    struct grammar_rule_args {
        grammar_rule_args(const map <string, dyn_fexpr>& arg_map,
            const map <string, tuple <sort, variant <agsymb_t, bgsymb_t, bvgsymb_t>>>& nonterm_map)
            : arg_map(arg_map), nonterm_map(nonterm_map)
        {}

        const map <string, dyn_fexpr> arg_map;
        const map <string, tuple <sort, variant <agsymb_t, bgsymb_t, bvgsymb_t>>> nonterm_map;

        vector <agsymb_t> achild_v;
        vector <bgsymb_t> bchild_v;
        vector <bvgsymb_t> bvchild_v;
    };

    dyn_fexpr grammar_rule(const GTerm *t, grammar_rule_args& args) const;
    dyn_fexpr grammar_rule_int(const FunGTerm *tp, grammar_rule_args& args) const;
    dyn_fexpr grammar_rule_int(const SymbolGTerm *tp, grammar_rule_args& args) const;
    dyn_fexpr grammar_rule_int(const LetGTerm *tp, grammar_rule_args& args) const;

    virtual void VisitConstraintCmd(const ConstraintCmd *cmd);
    dyn_fexpr get_constraint(const Term *t, const map <string, dyn_fexpr>& args) const;
    dyn_fexpr get_constraint_int(const FunTerm *tp, const map <string, dyn_fexpr>& args) const;
    dyn_fexpr get_constraint_int(const SymbolTerm *tp, const map <string, dyn_fexpr>& args) const;
    dyn_fexpr get_constraint_int(const LetTerm *tp, const map <string, dyn_fexpr>& args) const;
    dyn_fexpr get_fcall(const sort& s, const id& f, const vector <afexpr_p>& zargs,
        const vector <bfexpr_p>& bargs, const vector <bvfexpr_p>& bvargs) const;

    virtual void VisitSetOptsCmd(const SetOptsCmd *cmd);
    virtual void VisitCheckSynthCmd(const CheckSynthCmd *cmd);

    map <string, sort> sort_table;
    map <string, dyn_expr> uq_var;
    map <tuple <vector <sort>, string>, dyn_expr> macros;
    map <tuple <vector <sort>, string>, tuple <id, dyn_grammar>> synth;
    bfexpr_p constraint;

    size_t seed, expr_size, samples, mutation_limit;
    double beta, move_probability;

    map <id, tuple <grammar, agsymb_t>> afuns;
    map <id, tuple <grammar, bgsymb_t>> bfuns;
    map <id, tuple <grammar, bvgsymb_t>> bvfuns;

    set <id> zfree, bfree;
    set <tuple <id, size_t>> bvfree;
};

void parse(const string& fname)
{
    sl2p::SynthLib2Parser parser;
    parser(fname);
    visitor_t visitor;
    parser.GetProgram() -> Accept(&visitor);
}

} // namespace parser
} // namespace stoch

#include "parser_iface/infr.hpp"

#endif // __PARSER_IFACE_HPP_

