#if !defined __SYGUS2_PARSER_SYMBOL_TABLE_BUILDER_HPP
#define __SYGUS2_PARSER_SYMBOL_TABLE_BUILDER_HPP

#include "Sygus2ParserIFace.hpp"
#include "SymbolTable.hpp"

namespace Sygus2Parser {

class SymbolTableBuilder : public ASTVisitorBase
{
private:
    SymbolTableSPtr symbol_table;
    vector<SortDescriptorCSPtr> sort_stack;

public:
    SymbolTableBuilder();
    virtual ~SymbolTableBuilder();

    virtual void visit_index(const Index* index) override;
    virtual void visit_identifier(const Identifier* identifier) override;
    virtual void visit_sort_expr(const SortExpr* sort_expr) override;
    virtual void visit_sort_name_and_arity(const SortNameAndArity* sort_name_and_arity) override;
    virtual void visit_datatype_constructor(const DatatypeConstructor* datatype_constructor) override;
    virtual void visit_datatype_constructor_list(const DatatypeConstructorList* datatype_constructor_list) override;
    virtual void visit_literal(const Literal* literal) override;
    virtual void visit_literal_term(const LiteralTerm* literal_term) override;
    virtual void visit_identifier_term(const IdentifierTerm* identifier_term) override;
    virtual void visit_function_application_term(const FunctionApplicationTerm* function_application_term) override;
    virtual void visit_sorted_symbol(const SortedSymbol* sorted_symbol) override;
    virtual void visit_quantified_term(const QuantifiedTerm* quantified_term) override;
    virtual void visit_variable_binding(const VariableBinding* variable_binding) override;
    virtual void visit_let_term(const LetTerm* let_term) override;

    virtual void visit_check_synth_command(const CheckSynthCommand* check_synth_command) override;
    virtual void visit_constraint_command(const ConstraintCommand* constraint_command) override;
    virtual void visit_declare_var_command(const DeclareVarCommand* declare_var_command) override;
    virtual void visit_inv_constraint_command(const InvConstraintCommand* inv_constraint_command) override;
    virtual void visit_set_feature_command(const SetFeatureCommand* set_feature_command) override;
    virtual void visit_synth_fun_command(const SynthFunCommand* synth_fun_command) override;
    virtual void visit_synth_inv_command(const SynthInvCommand* synth_inv_command) override;
    virtual void visit_declare_sort_command(const DeclareSortCommand* declare_sort_command) override;
    virtual void visit_define_fun_command(const DefineFunCommand* define_fun_command) override;
    virtual void visit_define_sort_command(const DefineSortCommand* define_sort_command) override;
    virtual void visit_declare_datatypes_command(const DeclareDatatypesCommand* declare_datatypes_command) override;
    virtual void visit_declare_datatype_command(const DeclareDatatypeCommand* declare_datatype_command) override;
    virtual void visit_set_logic_command(const SetLogicCommand* set_logic_command) override;
    virtual void visit_set_option_command(const SetOptionCommand* set_option_command) override;
    virtual void visit_constant_grammar_term(const ConstantGrammarTerm* constant_grammar_term) override;
    virtual void visit_variable_grammar_term(const VariableGrammarTerm* variable_grammar_term) override;
    virtual void visit_binder_free_grammar_term(const BinderFreeGrammarTerm* binder_free_grammar_term) override;
    virtual void visit_grouped_rule_list(const GroupedRuleList* grouped_rule_list) override;
    virtual void visit_grammar(const Grammar* grammar) override;

    virtual void visit_program(const Program* program) override;

    SymbolTableSPtr get_symbol_table() const;

    static SymbolTableSPtr run(const Program* program);
};

} /* end namespace Sygus2Parser */

#endif /* __SYGUS2_PARSER_SYMBOL_TABLE_BUILDER_HPP */
