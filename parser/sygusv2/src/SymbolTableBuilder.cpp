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
    // Drop the reference, but don't delete the
    // symbol table: it's ref-counted, will be
    // deleted when no one owns it anymore.
    symbol_table = nullptr;
}

void SymbolTableBuilder::visit_index(const Index* index)
{
    ASTVisitorBase::visit_index(index);
}

void SymbolTableBuilder::visit_identifier(const Identifier* identifier)
{
    ASTVisitorBase::visit_identifier(identifier);
}

void SymbolTableBuilder::visit_sort_expr(const SortExpr* sort_expr)
{
    auto const& identifier = *(sort_expr->get_identifier());
    auto const& param_sorts = sort_expr->get_param_sorts();
    auto sort_desc = symbol_table->lookup_or_resolve_sort(identifier);

    auto const& parameter_placeholders = sort_desc->get_placeholder_parameters();

    if (parameter_placeholders.size() != param_sorts.size()) {
        ostringstream sstr;
        sstr << "Sort \"" << identifier.to_string() << "\" was instantiated with "
             << "the wrong number of sort arguments. Expected " << parameter_placeholders.size()
             << " sort arguments, but received " << param_sorts.size() << " arguments.";
        throw Sygus2ParserException(sstr.str(), sort_expr->get_location());
    }

    // recurse on the parameter sorts
    SortInstantiationVector instantiation_vector;
    for(size_t i = 0; i < parameter_placeholders.size(); ++i) {
        param_sorts[i]->accept(this);
        instantiation_vector.push_back(make_pair(parameter_placeholders[i], sort_stack.back()));
        sort_stack.pop_back();
    }

    // We have the sort descriptors for the parameters.
    // Instantiate the sort and push it onto the stack.
    auto resolved_sort = sort_desc->instantiate_sort(instantiation_vector);
    sort_stack.push_back(resolved_sort);
}

void SymbolTableBuilder::visit_sort_name_and_arity(const SortNameAndArity* sort_name_and_arity)
{
    // should never get here
    throw UnsupportedFeatureException("datatypes", sort_name_and_arity->get_location());
}

void SymbolTableBuilder::visit_datatype_constructor(const DatatypeConstructor* datatype_constructor)
{
    // should never get here
    throw UnsupportedFeatureException("datatypes", datatype_constructor->get_location());
}

void SymbolTableBuilder::visit_datatype_constructor_list(const DatatypeConstructorList* datatype_constructor_list)
{
    // should never get here
    throw UnsupportedFeatureException("datatypes", datatype_constructor_list->get_location());
}

void SymbolTableBuilder::visit_literal(const Literal* literal)
{
    ASTVisitorBase::visit_literal(literal);
}

void SymbolTableBuilder::visit_literal_term(const LiteralTerm* literal_term)
{
    auto literal = literal_term->get_literal();
    auto const& literal_string = literal->get_literal_string();

    switch (literal->get_literal_kind()) {
    case LiteralKind::Numeral:
        literal_term->set_sort(symbol_table->get_integer_sort());
        break;
    case LiteralKind::Decimal:
        literal_term->set_sort(symbol_table->get_real_sort());
        break;
    case LiteralKind::Boolean:
        literal_term->set_sort(symbol_table->get_boolean_sort());
        break;
    case LiteralKind::Binary: {
        auto length = literal_string.length() - 2;
        literal_term->set_sort(symbol_table->get_bitvector_sort(length));
        break;
    }
    case LiteralKind::Hexadecimal: {
        auto length = literal_string.length() - 2;
        literal_term->set_sort(symbol_table->get_bitvector_sort(length * 4));
        break;
    }

    case LiteralKind::String:
        literal_term->set_sort(symbol_table->get_string_sort());
        break;
    }
}

void SymbolTableBuilder::visit_identifier_term(const IdentifierTerm* identifier_term)
{
    auto const& identifier = *(identifier_term->get_identifier());
    auto var_desc = symbol_table->lookup_variable(identifier);
    if (var_desc.is_null()) {
        throw SymbolTableException("Could not resolve identifier: " + identifier.to_string(),
                                   identifier_term->get_location());
    }

    identifier_term->set_sort(var_desc->get_sort_descriptor());
}

void SymbolTableBuilder::visit_function_application_term(const FunctionApplicationTerm* function_application_term)
{
    auto const& identifer = *(function_application_term->get_identifier());
    // recurse on the parameters
    vector<SortDescriptorCSPtr> arg_sorts;
    for (auto arg : function_application_term->get_application_arguments()) {
        arg->accept(this);
        arg_sorts.push_back(arg->get_sort());
    }

    auto func_desc = symbol_table->lookup_function(identifer, arg_sorts);
    if (func_desc.is_null()) {
        throw SymbolTableException("Could not resolve identifer: " + identifer.to_string(),
                                   identifer.get_location());
    }

    function_application_term->set_sort(func_desc->get_range_sort());
}

void SymbolTableBuilder::visit_sorted_symbol(const SortedSymbol* sorted_symbol)
{
    // Should never get here
    throw Sygus2ParserException("Unreachable code was hit!");
}

void SymbolTableBuilder::visit_quantified_term(const QuantifiedTerm* quantified_term)
{
    symbol_table->push_scope();
    auto scope = symbol_table->pop_scope();

    for (auto sorted_symbol : quantified_term->get_quantified_symbols()) {
        auto const& name = sorted_symbol->get_symbol();

        sorted_symbol->get_sort_expr()->accept(this);
        auto sort = sort_stack.back();
        sort_stack.pop_back();

        symbol_table->push_scope();
        auto var_desc = new VariableDescriptor(name, VariableKind::Quantified, sort);
        symbol_table->add_variable(var_desc);
        scope = symbol_table->pop_scope();
    }

    quantified_term->set_symbol_table_scope(scope);
    symbol_table->push_scope(scope);
    // recurse on the term itself
    quantified_term->get_quantified_term()->accept(this);
    if (*(quantified_term->get_sort()) != *(symbol_table->get_boolean_sort())) {
        throw new Sygus2ParserException("Expected a boolean sorted quantified expression.",
                                        quantified_term->get_quantified_term()->get_location());
    }
}

void SymbolTableBuilder::visit_variable_binding(const VariableBinding* variable_binding)
{
    // Should never get here
    throw Sygus2ParserException("Unreachable code was hit!");
}

void SymbolTableBuilder::visit_let_term(const LetTerm* let_term)
{
    symbol_table->push_scope();
    auto scope = symbol_table->pop_scope();

    for (auto binding : let_term->get_bindings()) {
        auto const& name = binding->get_symbol();
        binding->get_binding()->accept(this);

        symbol_table->push_scope();
        auto var_desc = new VariableDescriptor(name, VariableKind::Quantified,
                                               binding->get_binding()->get_sort());
        symbol_table->add_variable(var_desc);
        scope = symbol_table->pop_scope();
    }

    let_term->set_symbol_table_scope(scope);
    symbol_table->push_scope(scope);
    // recurse on the let body
    let_term->get_let_body()->accept(this);
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
    auto const& var_name = declare_var_command->get_symbol();
    declare_var_command->get_sort_expr()->accept(this);
    auto sort_desc = sort_stack.back();
    sort_stack.pop_back();
    auto var_desc = new VariableDescriptor(var_name, VariableKind::Universal, sort_desc);
    symbol_table->add_variable(var_desc);
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

void SymbolTableBuilder::add_params_to_symtab(const vector<SortedSymbolCSPtr>& param_list,
                                              SymbolTableSPtr symbol_table,
                                              vector<SortDescriptorCSPtr>& argument_sorts,
                                              vector<string>& argument_names)
{
    argument_sorts.clear();
    argument_names.clear();

    auto top_scope = symbol_table->pop_scope();
    for(auto const& param : param_list) {
        auto const& param_name = param->get_symbol();
        argument_names.push_back(param_name);

        param->get_sort_expr()->accept(this);
        auto param_sort = sort_stack.back();
        sort_stack.pop_back();

        argument_sorts.push_back(param_sort);
        auto var_desc = new VariableDescriptor(param_name, VariableKind::Parameter, param_sort);

        // push the new scope only when needed
        symbol_table->push_scope(top_scope);
        symbol_table->add_variable(var_desc);
        top_scope = symbol_table->pop_scope();
    }
}

void SymbolTableBuilder::visit_synth_fun_command(const SynthFunCommand* synth_fun_command)
{
    vector<SortDescriptorCSPtr> argument_sorts;
    vector<string> argument_names;

    auto const& parameters = synth_fun_command->get_function_parameters();
    symbol_table->push_scope();
    add_params_to_symtab(parameters, symbol_table, argument_sorts, argument_names);
    auto scope = symbol_table->pop_scope();

    synth_fun_command->set_symbol_table_scope(scope);
    auto synthesis_grammar = synth_fun_command->get_synthesis_grammar();
    if (synthesis_grammar != nullptr) {
        synthesis_grammar->set_symbol_table_scope(scope);
    }


    SortDescriptorCSPtr range_sort_desc;
    FunctionDescriptorCSPtr func_desc;
    if (synth_fun_command->is<SynthInvCommand>()) {
        func_desc = new FunctionDescriptor(synth_fun_command->get_function_symbol(),
                                           argument_sorts, argument_names,
                                           synthesis_grammar,
                                           synth_fun_command->static_as<SynthInvCommand>());
    } else {
        synth_fun_command->get_function_range_sort()->accept(this);
        range_sort_desc = sort_stack.back();
        sort_stack.pop_back();
        func_desc = new FunctionDescriptor(synth_fun_command->get_function_symbol(),
                                           argument_sorts, argument_names,
                                           range_sort_desc,
                                           synthesis_grammar,
                                           synth_fun_command);
    }

    symbol_table->add_function(func_desc);
}

void SymbolTableBuilder::visit_synth_inv_command(const SynthInvCommand* synth_inv_command)
{
    visit_synth_fun_command(synth_inv_command);
}

void SymbolTableBuilder::visit_declare_sort_command(const DeclareSortCommand* declare_sort_command)
{
    throw UnsupportedFeatureException("declare-sort is not (yet) supported.",
                                      declare_sort_command->get_location());
}

void SymbolTableBuilder::visit_define_fun_command(const DefineFunCommand* define_fun_command)
{
    vector<SortDescriptorCSPtr> argument_sorts;
    vector<string> argument_names;

    auto const& parameters = define_fun_command->get_function_parameters();
    symbol_table->push_scope();
    add_params_to_symtab(parameters, symbol_table, argument_sorts, argument_names);
    auto scope = symbol_table->pop_scope();

    define_fun_command->get_function_range_sort()->accept(this);
    auto range_sort = sort_stack.back();
    sort_stack.pop_back();

    symbol_table->push_scope(scope);
    define_fun_command->get_function_body()->accept(this);
    scope = symbol_table->pop_scope();

    define_fun_command->get_function_body()->set_symbol_table_scope(scope);
    auto func_desc = new FunctionDescriptor(define_fun_command->get_function_symbol(),
                                            argument_sorts, argument_names,
                                            range_sort, define_fun_command->get_function_body());
    symbol_table->add_function(func_desc);
}

void SymbolTableBuilder::visit_define_sort_command(const DefineSortCommand* define_sort_command)
{
    auto const& sort_alias = define_sort_command->get_sort_name();
    auto const& parameters = define_sort_command->get_sort_parameters();

    symbol_table->push_scope();
    vector<SortDescriptorCSPtr> parameter_placeholders;
    for (auto const& parameter : parameters) {
        auto sort_desc = SortDescriptor::create_sort_parameter_placeholder(parameter);
        parameter_placeholders.push_back(sort_desc);
        symbol_table->add_sort(sort_desc);
    }

    // Now recurse on the alias target
    define_sort_command->get_sort_expr()->accept(this);
    auto alias_target = sort_stack.back();
    sort_stack.pop_back();

    symbol_table->pop_scope();

    auto alias_sort = SortDescriptor::create_sort_alias(sort_alias, parameter_placeholders, alias_target);
    symbol_table->add_sort(alias_sort);
}

void SymbolTableBuilder::visit_declare_datatypes_command(const DeclareDatatypesCommand* declare_datatypes_command)
{
    throw UnsupportedFeatureException("declare-datatypes is not (yet) supported.",
                                      declare_datatypes_command->get_location());
}

void SymbolTableBuilder::visit_declare_datatype_command(const DeclareDatatypeCommand* declare_datatype_command)
{
    // We accept a very specific kind of declare-datatype command:
    // 1. The constructor list cannot be parametric on a sort,
    // 2. All the constructors in the constructor list must define
    //    constant functions
    auto const& name = declare_datatype_command->get_datatype_name();
    auto constructor_list = declare_datatype_command->get_datatype_constructor_list();
    if (constructor_list->get_sort_parameter_names().size() != 0) {
        throw UnsupportedFeatureException("declare-datatype can only be used with no sort parameters.",
                                          constructor_list->get_location());
    }

    for (auto constructor : constructor_list->get_datatype_constructors()) {
        if (constructor->get_constructor_parameters().size() != 0) {
            throw UnsupportedFeatureException("All constructors in a declare-datatype command must be "
                                              "constant functions", constructor->get_location());
        }
    }

    // This is a supported declare-datatypes command
    auto sort_desc = SortDescriptor::create_primitive_sort(name);
    symbol_table->add_sort(sort_desc);

    // add the constructors
    vector<string> argument_names;
    vector<SortDescriptorCSPtr> argument_sorts;

    vector<SortDescriptorCSPtr> tester_args;
    tester_args.push_back(sort_desc);
    auto bool_sort = symbol_table->get_boolean_sort();
    for (auto constructor : constructor_list->get_datatype_constructors()) {
        auto const& constructor_name = constructor->get_constructor_name();
        auto func_desc = new FunctionDescriptor(constructor_name, sort_desc);
        symbol_table->add_function(func_desc);

        vector<IndexSPtr> indices;
        indices.push_back(new Index(SourceLocation::none, constructor_name));
        Identifier tester_identifier(SourceLocation::none, "is", indices);

        auto tester_desc = new FunctionDescriptor(tester_identifier,
                                                  tester_args,
                                                  bool_sort,
                                                  FunctionKind::Theory);
        symbol_table->add_function(tester_desc);
    }
}

void SymbolTableBuilder::visit_set_logic_command(const SetLogicCommand* set_logic_command)
{
    symbol_table->set_logic(set_logic_command->get_logic_name());
}

void SymbolTableBuilder::visit_set_option_command(const SetOptionCommand* set_option_command)
{
    symbol_table->set_option(set_option_command->get_option_name(),
                             set_option_command->get_option_value());
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
