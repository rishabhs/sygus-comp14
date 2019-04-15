#include "include/SymbolTableBuilder.hpp"
#include "include/TheoryManager.hpp"
#include "include/Sygus2ParserExceptions.hpp"

namespace Sygus2Parser {

SymbolTableBuilder::SymbolTableBuilder()
    : ASTVisitorBase("SymbolTableBuilder")
{
    symbol_table = new SymbolTable();
    // push the root scope
    symbol_table->push_scope();
}

SymbolTableBuilder::~SymbolTableBuilder()
{
    symbol_table = nullptr;
}

void SymbolTableBuilder::visit_index(const Index* index)
{

}

void SymbolTableBuilder::visit_identifier(const Identifier* identifier)
{

}

void SymbolTableBuilder::visit_sort_expr(const SortExpr* sort_expr)
{
}

void SymbolTableBuilder::visit_sort_name_and_arity(const SortNameAndArity* sort_name_and_arity)
{

}

void SymbolTableBuilder::visit_datatype_constructor(const DatatypeConstructor* datatype_constructor)
{

}

void SymbolTableBuilder::visit_datatype_constructor_list(const DatatypeConstructorList* datatype_constructor_list)
{

}

void SymbolTableBuilder::visit_literal(const Literal* literal)
{

}

void SymbolTableBuilder::visit_literal_term(const LiteralTerm* literal_term)
{

}

void SymbolTableBuilder::visit_identifier_term(const IdentifierTerm* identifier_term)
{

}

void SymbolTableBuilder::visit_function_application_term(const FunctionApplicationTerm* function_application_term)
{

}

void SymbolTableBuilder::visit_sorted_symbol(const SortedSymbol* sorted_symbol)
{

}

void SymbolTableBuilder::visit_quantified_term(const QuantifiedTerm* quantified_term)
{

}

void SymbolTableBuilder::visit_variable_binding(const VariableBinding* variable_binding)
{

}

void SymbolTableBuilder::visit_let_term(const LetTerm* let_term)
{

}

void SymbolTableBuilder::visit_check_synth_command(const CheckSynthCommand* check_synth_command)
{
    ASTVisitorBase::visit_check_synth_command(check_synth_command);
}

void SymbolTableBuilder::visit_constraint_command(const ConstraintCommand* constraint_command)
{
    ASTVisitorBase::visit_constraint_command(constraint_command);
}

void SymbolTableBuilder::visit_declare_var_command(const DeclareVarCommand* declare_var_command)
{
}

void SymbolTableBuilder::visit_inv_constraint_command(const InvConstraintCommand* inv_constraint_command)
{
    ASTVisitorBase::visit_inv_constraint_command(inv_constraint_command);
    // check that the pre, trans, post are boolean sorted user-defined functions,
    // and that the invariant to be synthesized is a boolean sorted function

    auto const& pre_symbol = inv_constraint_command->get_precondition_symbol();
    auto const& post_symbol = inv_constraint_command->get_postcondition_symbol();
    auto const& trans_symbol = inv_constraint_command->get_transition_relation_symbol();
    auto const& inv_fun_symbol = inv_constraint_command->get_inv_fun_symbol();

    auto pre_fd = symbol_table->lookup_function(pre_symbol);
    if (pre_fd.is_null()) {
        throw new SymbolTableException("Could not resolve symbol: " + pre_symbol,
                                       inv_constraint_command->get_location());
    }

    auto trans_fd = symbol_table->lookup_function(trans_symbol);
    if (trans_fd.is_null()) {
        throw new SymbolTableException("Could not resolve symbol: " + trans_symbol,
                                       inv_constraint_command->get_location());
    }

    auto post_fd = symbol_table->lookup_function(post_symbol);
    if (post_fd.is_null()) {
        throw new SymbolTableException("Could not resolve symbol: " + post_symbol,
                                       inv_constraint_command->get_location());
    }

    auto inv_fd = symbol_table->lookup_function(inv_fun_symbol);
    if (inv_fd.is_null()) {
        throw new SymbolTableException("Could not resolve symbol: " + inv_fun_symbol,
                                       inv_constraint_command->get_location());
    }

    auto bool_sort = SymbolTable::get_boolean_sort();
    if (*(pre_fd->get_range_sort()) != *bool_sort) {
        throw new SymbolTableException("Pre, Post, Trans must be Boolean valued functions",
                                       inv_constraint_command->get_location());
    }

    if (*(post_fd->get_range_sort()) != *bool_sort) {
        throw new SymbolTableException("Pre, Post, Trans must be Boolean valued functions",
                                       inv_constraint_command->get_location());
    }

    if (*(trans_fd->get_range_sort()) != *bool_sort) {
        throw new SymbolTableException("Pre, Post, Trans must be Boolean valued functions",
                                       inv_constraint_command->get_location());
    }

    if (*(trans_fd->get_range_sort()) != *bool_sort) {
        throw new SymbolTableException("The invariant to be synthesized must be a Boolean valued function",
                                       inv_constraint_command->get_location());
    }
}

void SymbolTableBuilder::visit_set_feature_command(const SetFeatureCommand* set_feature_command)
{
    ASTVisitorBase::visit_set_feature_command(set_feature_command);
    auto const& feature_name = set_feature_command->get_feature_name();
    if (feature_name != "grammars" && feature_name != "fwd-decls" && feature_name != "recursion") {
        throw new SymbolTableException("Unsupported feature. Only \"grammars\", \"fwd-decls\" and "
                                       "\"recursion\" are supported features",
                                       set_feature_command->get_location());
    }
    if (set_feature_command->get_value()) {
        symbol_table->enable_feature(feature_name);
    } else {
        symbol_table->disable_feature(feature_name);
    }
}

void SymbolTableBuilder::visit_synth_fun_command(const SynthFunCommand* synth_fun_command)
{
    ASTVisitorBase::visit_synth_fun_command(synth_fun_command);
}

void SymbolTableBuilder::visit_synth_inv_command(const SynthInvCommand* synth_inv_command)
{
    // first determine the sorts of the arguments
    vector<SortDescriptorCSPtr> argument_sorts;
    auto const& parameters = synth_inv_command->get_function_parameters();

    symbol_table->push_scope();

    for(auto const& param : parameters) {
        auto const& symbol = param->get_symbol();
        auto sort_expr = param->get_sort_expr();

    }
}

void SymbolTableBuilder::visit_declare_sort_command(const DeclareSortCommand* declare_sort_command)
{
}

void SymbolTableBuilder::visit_define_fun_command(const DefineFunCommand* define_fun_command)
{

}

void SymbolTableBuilder::visit_define_sort_command(const DefineSortCommand* define_sort_command)
{

}

void SymbolTableBuilder::visit_declare_datatypes_command(const DeclareDatatypesCommand* declare_datatypes_command)
{

}

void SymbolTableBuilder::visit_declare_datatype_command(const DeclareDatatypeCommand* declare_datatype_command)
{

}

void SymbolTableBuilder::visit_set_logic_command(const SetLogicCommand* set_logic_command)
{

}

void SymbolTableBuilder::visit_set_option_command(const SetOptionCommand* set_option_command)
{

}

void SymbolTableBuilder::visit_constant_grammar_term(const ConstantGrammarTerm* constant_grammar_term)
{

}

void SymbolTableBuilder::visit_variable_grammar_term(const VariableGrammarTerm* variable_grammar_term)
{

}

void SymbolTableBuilder::visit_binder_free_grammar_term(const BinderFreeGrammarTerm* binder_free_grammar_term)
{

}

void SymbolTableBuilder::visit_grouped_rule_list(const GroupedRuleList* grouped_rule_list)
{

}

void SymbolTableBuilder::visit_grammar(const Grammar* grammar)
{

}

void SymbolTableBuilder::visit_program(const Program* program)
{
    ASTVisitorBase::visit_program(program);
}

SymbolTableSPtr SymbolTableBuilder::get_symbol_table() const
{
    return symbol_table;
}

SymbolTableSPtr SymbolTableBuilder::run(const Program* program)
{
    SymbolTableBuilder builder;
    program->accept(&builder);
    return builder.symbol_table;
}

} /* end namespace Sygus2Parser */
