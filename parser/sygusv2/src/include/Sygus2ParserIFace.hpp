/*
  Copyright (c) 2013,
  Abhishek Udupa,
  Mukund Raghothaman,
  The University of Pennsylvania

  All rights reserved.

  Redistribution and use in source and binary forms, with or without
  modification, are permitted provided that the following conditions are
  met:

  1. Redistributions of source code must retain the above copyright
  notice, this list of conditions and the following disclaimer.

  2. Redistributions in binary form must reproduce the above copyright
  notice, this list of conditions and the following disclaimer in the
  documentation and/or other materials provided with the distribution.

  3. Neither the name of the copyright holder nor the names of its
  contributors may be used to endorse or promote products derived from
  this software without specific prior written permission.

  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
  A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
  HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/

#if !defined __SYGUS2_PARSER_IFACE_H
#define __SYGUS2_PARSER_IFACE_H

#include <string>
#include <utility>
#include <vector>
#include <functional>
#include "Sygus2ParserCommon.hpp"
#include "Sygus2ParserFwd.hpp"

namespace Sygus2Parser {

class SourceLocation
{
private:
    i32 line;
    i32 column;

public:
    SourceLocation(i32 line, i32 column);
    SourceLocation(const SourceLocation& other);
    SourceLocation(SourceLocation&& other);

    ~SourceLocation();

    bool operator == (const SourceLocation& other) const;
    bool operator != (const SourceLocation& other) const;

    SourceLocation& operator = (const SourceLocation& Other);
    SourceLocation& operator = (SourceLocation&& other);
    i64 get_hash_code() const;

    i32 get_line() const;
    i32 get_column() const;

    string to_string() const;
    static SourceLocation none;
};

class ASTBase
{
protected:
    SourceLocation location;

public:
    ASTBase(const SourceLocation& location);
    virtual ~ASTBase();

    // Accessors
    const SourceLocation& get_location() const;

    // Abstract methods
    virtual void accept(ASTVisitorBase* visitor) const = 0;
    virtual ASTBase* clone() const = 0;
};

class Index : public ASTBase
{
private:
    string symbol;
    i32 numeral;
    bool is_symbolic;

public:
    Index(const SourceLocation& location, const string& symbol);
    Index(const SourceLocation& location, i32 numeral);
    Index(const Index& other);
    Index(Index&& other);

    virtual ~Index();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    bool operator == (const Index& other) const;
    bool operator != (const Index& other) const;
    i64 get_hash_code() const;

    Index& operator = (const Index& other);
    Index& operator = (Index&& other);

    // accessors
    bool is_symbol() const;
    bool is_numeral() const;
    const string& get_symbol() const;
    i32 get_numeral() const;
};

class Identifier : public ASTBase
{
private:
    string symbol;
    vector<Index*> indices;
    vector<const Index*> const_indices;

public:
    Identifier(const SourceLocation& location, const string& symbol);
    Identifier(const SourceLocation& location, const string& symbol, const vector<Index*>& indices);
    Identifier(const Identifier& other);
    Identifier(Identifier&& other);

    virtual ~Identifier();

    bool operator == (const Identifier& other) const;
    bool operator != (const Identifier& other) const;
    i64 get_hash_code() const;

    Identifier& operator = (const Identifier& other);
    Identifier& operator = (Identifier&& other);

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    bool is_indexed() const;

    // accessors
    const string& get_symbol() const;
    const vector<const Index*> get_indices() const;
};


class SortExpr : public ASTBase
{
private:
    Identifier* identifier;
    vector<SortExpr*> param_sorts;
    vector<const SortExpr*> const_param_sorts;

public:
    SortExpr(const SourceLocation& location, Identifier* identifier);
    SortExpr(const SourceLocation& location, Identifier* identifier,
             const vector<SortExpr*>& param_sorts);
    virtual ~SortExpr();

    bool operator == (const SortExpr& other) const;
    bool operator != (const SortExpr& other) const;

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    const Identifier* get_identifier() const;
    const vector<const SortExpr*>& get_param_sorts() const;
};

class SortNameAndArity : public ASTBase
{
private:
    string sort_name;
    u32 sort_arity;

public:
    SortNameAndArity(const SourceLocation& location,
                     const string& sort_name, u32 sort_arity);
    virtual ~SortNameAndArity();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    const string& get_sort_name() const;
    u32 get_sort_arity() const;
};

class DatatypeConstructor : public ASTBase
{
private:
    string constructor_name;
    vector<SortedSymbol*> constructor_parameters;
    vector<const SortedSymbol*> const_constructor_parameters;

public:
    DatatypeConstructor(const SourceLocation& location,
                        const string& constructor_name,
                        const vector<SortedSymbol*>& constructor_parameters);
    virtual ~DatatypeConstructor();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    const string& get_constructor_name() const;
    const vector<const SortedSymbol*>& get_constructor_parameters() const;
};

class DatatypeConstructorList : public ASTBase
{
private:
    vector<string> sort_parameter_names;
    vector<DatatypeConstructor*> datatype_constructors;
    vector<const DatatypeConstructor*> const_datatype_constructors;

public:
    DatatypeConstructorList(const SourceLocation& location,
                            const vector<string>& sort_parameter_names,
                            const vector<DatatypeConstructor*>& datatype_constructors);
    virtual ~DatatypeConstructorList();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    const vector<string>& get_sort_parameter_names() const;
    const vector<const DatatypeConstructor*>& get_datatype_constructors() const;
};

enum class LiteralKind
    {
     Numeral,
     Decimal,
     Boolean,
     Hexadecimal,
     Binary,
     String
    };

class Literal : public ASTBase
{
private:
    string literal_string;
    LiteralKind literal_kind;

public:
    Literal(const SourceLocation& location, const string& literal_string,
            LiteralKind literal_kind);
    virtual ~Literal();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    const string& get_literal_string() const;
    LiteralKind get_literal_kind() const;
};

class Term : public ASTBase
{
protected:
    mutable SortExpr* sort;
    Term(const SourceLocation& location);

public:
    virtual ~Term();
    void set_sort(SortExpr* sort) const;
    const SortExpr* get_sort() const;
};

class IdentifierTerm : public Term
{
private:
    Identifier* identifier;

public:
    IdentifierTerm(const SourceLocation& location, Identifier* identifier);
    virtual ~IdentifierTerm();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    const Identifier* get_identifier() const;
};

class LiteralTerm : public Term
{
private:
    Literal* literal;

public:
    LiteralTerm(const SourceLocation& location, Literal* literal);
    virtual ~LiteralTerm();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    const Literal* get_literal() const;
};

class FunctionApplicationTerm : public Term
{
protected:
    Identifier* identifier;
    vector<Term*> application_arguments;
    vector<const Term*> const_application_arguments;

public:
    FunctionApplicationTerm(const SourceLocation& location,
                            Identifier* identifier,
                            const vector<Term*>& application_arguments);
    virtual ~FunctionApplicationTerm();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    const Identifier* get_identifier() const;
    const vector<const Term*>& get_application_arguments() const;
};

enum class QuantifierKind
    {
     Forall,
     Exists
    };

class SortedSymbol : public ASTBase
{
private:
    string symbol;
    SortExpr* sort_expr;

public:
    SortedSymbol(const SourceLocation& location, const string& symbol,
                 SortExpr* sort_expr);
    virtual ~SortedSymbol();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    const string& get_symbol() const;
    const SortExpr* get_sort_expr() const;
};

class QuantifiedTerm : public Term
{
private:
    QuantifierKind quantifier_kind;
    vector<SortedSymbol*> quantified_symbols;
    vector<const SortedSymbol*> const_quantified_symbols;
    Term* quantified_term;

public:
    QuantifiedTerm(const SourceLocation& location,
                   QuantifierKind quantifier_kind,
                   const vector<SortedSymbol*> quantified_symbols,
                   Term* quantified_term);
    virtual ~QuantifiedTerm();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    QuantifierKind get_quantifier_kind() const;
    const vector<const SortedSymbol*>& get_quantified_symbols() const;
    const Term* get_quantified_term() const;
};

class VariableBinding : public ASTBase
{
private:
    const string& symbol;
    Term* binding;

public:
    VariableBinding(const SourceLocation& location,
                    const string& symbol,
                    Term* binding);
    virtual ~VariableBinding();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    const string& get_symbol() const;
    const Term* get_binding() const;
};

class LetTerm : public Term
{
private:
    vector<VariableBinding*> bindings;
    vector<const VariableBinding*> const_bindings;
    Term* let_body;

public:
    LetTerm(const SourceLocation& location, const vector<VariableBinding*>& bindings,
            Term* let_body);
    virtual ~LetTerm();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    const vector<const VariableBinding*>& get_bindings() const;
    const Term* get_let_body() const;
};

class Command : public ASTBase
{
private:
    Command() = delete;
    Command(const Command&) = delete;
    Command(Command&&) = delete;

    Command& operator = (const Command&) = delete;
    Command& operator = (Command&&) = delete;

protected:
    Command(const SourceLocation& location);
};

class CheckSynthCommand : public Command
{
public:
    CheckSynthCommand(const SourceLocation& location);
    virtual ~CheckSynthCommand();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;
};

class ConstraintCommand : public Command
{
private:
    Term* constraint_term;

public:
    ConstraintCommand(const SourceLocation& location,
                      Term* constraint_term);
    virtual ~ConstraintCommand();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    const Term* get_constraint_term() const;
};

class DeclareVarCommand : public Command
{
private:
    string symbol;
    SortExpr* sort_expr;

public:
    DeclareVarCommand(const SourceLocation& location,
                      const string& symbol,
                      SortExpr* sort_expr);
    virtual ~DeclareVarCommand();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    const string& get_symbol() const;
    const SortExpr* get_sort_expr() const;
};

class InvConstraintCommand : public Command
{
private:
    string inv_fun_symbol;
    string precondition_symbol;
    string transition_relation_symbol;
    string postcondition_symbol;

public:
    InvConstraintCommand(const SourceLocation& location,
                         const string& inv_fun_symbol,
                         const string& precondition_symbol,
                         const string& transition_relation_symbol,
                         const string& postcondition_symbol);

    virtual ~InvConstraintCommand();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    const string& get_inv_fun_symbol() const;
    const string& get_precondition_symbol() const;
    const string& get_transition_relation_symbol() const;
    const string& get_postcondition_symbol() const;
};

class SetFeatureCommand : public Command
{
private:
    string feature_name;
    bool value;

public:
    SetFeatureCommand(const SourceLocation& location,
                      const string& feature_name,
                      bool value);

    virtual ~SetFeatureCommand();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    const string& get_feature_name() const;
    bool get_value() const;
};

class SynthFunCommand : public Command
{
private:
    const string& function_symbol;
    vector<SortedSymbol*> function_parameters;
    SortExpr* function_range_sort;
    Grammar* synthesis_grammar;

    vector<const SortedSymbol*> const_function_parameters;

public:
    SynthFunCommand(const SourceLocation& location,
                    const string& function_symbol,
                    const vector<SortedSymbol*>& function_parameters,
                    SortExpr* function_range_sort,
                    Grammar* synthesis_grammar);
    virtual ~SynthFunCommand();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    const string& get_function_symbol() const;
    const vector<const SortedSymbol*>& get_function_parameters() const;
    const SortExpr* get_function_range_sort() const;
    const Grammar* get_synthesis_grammar() const;
};

class SynthInvCommand : public SynthFunCommand
{
public:
    SynthInvCommand(const SourceLocation& location,
                    const string& function_symbol,
                    const vector<SortedSymbol*>& function_parameters,
                    Grammar* synthesis_grammar);
    virtual ~SynthInvCommand();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;
};

class DeclareSortCommand : public Command
{
private:
    string sort_name;
    u32 sort_arity;

public:
    DeclareSortCommand(const SourceLocation& location,
                       const string& sort_name,
                       u32 sort_arity);
    virtual ~DeclareSortCommand();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    const string& get_sort_name() const;
    u32 get_sort_arity() const;
};

class DefineFunCommand : public Command
{
private:
    string function_symbol;
    vector<SortedSymbol*> function_parameters;
    SortExpr* function_range_sort;
    Term* function_body;

    vector<const SortedSymbol*> const_function_parameters;

public:
    DefineFunCommand(const SourceLocation& location,
                     const string& function_symbol,
                     const vector<SortedSymbol*>& function_parameters,
                     SortExpr* function_range_sort,
                     Term* function_body);
    virtual ~DefineFunCommand();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    const string& get_function_symbol() const;
    const vector<const SortedSymbol*>& get_function_parameters() const;
    const SortExpr* get_function_range_sort() const;
    const Term* get_function_body() const;
};

class DefineSortCommand : public Command
{
private:
    string sort_name;
    vector<string> sort_parameters;
    SortExpr* sort_expr;

public:
    DefineSortCommand(const SourceLocation& location,
                      const string& sort_name,
                      const vector<string>& sort_parameters,
                      SortExpr* sort_expr);
    virtual ~DefineSortCommand();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    const string& get_sort_name() const;
    const SortExpr* get_sort_expr() const;
    const vector<string>& get_sort_parameters() const;
};

class DeclareDatatypesCommand : public Command
{
private:
    vector<SortNameAndArity*> sort_names_and_arities;
    vector<DatatypeConstructorList*> datatype_constructor_lists;

    vector<const SortNameAndArity*> const_sort_names_and_arities;
    vector<const DatatypeConstructorList*> const_datatype_constructor_lists;

public:
    DeclareDatatypesCommand(const SourceLocation& location,
                            const vector<SortNameAndArity*>& sort_names_and_arities,
                            const vector<DatatypeConstructorList*>& constructor_lists);
    virtual ~DeclareDatatypesCommand();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    const vector<const SortNameAndArity*>& get_sort_names_and_arities() const;
    const vector<const DatatypeConstructorList*>& get_datatype_constructor_lists() const;
};

class DeclareDatatypeCommand : public Command
{
private:
    string datatype_name;
    DatatypeConstructorList* datatype_constructor_list;

public:
    DeclareDatatypeCommand(const SourceLocation& location,
                           const string& datatype_sort_name,
                           DatatypeConstructorList* datatype_constructor_list);
    virtual ~DeclareDatatypeCommand();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    const string& get_datatype_name() const;
    const DatatypeConstructorList* get_datatype_constructor_list() const;
};

class SetLogicCommand : public Command
{
private:
    string logic_name;

public:
    SetLogicCommand(const SourceLocation& location, const string& logic_name);
    virtual ~SetLogicCommand();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    const string& get_logic_name() const;
};

class SetOptionCommand : public Command
{
private:
    string option_name;
    Literal* option_value;

public:
    SetOptionCommand(const SourceLocation& location,
                     const string& option_name,
                     Literal* option_value);
    virtual ~SetOptionCommand();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    const string& get_option_name() const;
    const Literal* get_option_value() const;
};

class GrammarTerm : public Term
{
private:
    GrammarTerm() = delete;
    GrammarTerm(const GrammarTerm& other) = delete;
    GrammarTerm(GrammarTerm&& other) = delete;

    GrammarTerm& operator = (const GrammarTerm& other) = delete;
    GrammarTerm& operator = (GrammarTerm&& other) = delete;

protected:
    GrammarTerm(const SourceLocation& location);

public:
    virtual ~GrammarTerm();
};

class ConstantGrammarTerm : public GrammarTerm
{
private:
    SortExpr* sort_expr;

public:
    ConstantGrammarTerm(const SourceLocation& location, SortExpr* sort_expr);
    virtual ~ConstantGrammarTerm();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    const SortExpr* get_sort_expr() const;
};

class VariableGrammarTerm : public GrammarTerm
{
private:
    SortExpr* sort_expr;

public:
    VariableGrammarTerm(const SourceLocation& location, SortExpr* sort_expr);
    virtual ~VariableGrammarTerm();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    const SortExpr* get_sort_expr() const;
};

class BinderFreeGrammarTerm : public GrammarTerm
{
private:
    Term* binder_free_term;

public:
    BinderFreeGrammarTerm(const SourceLocation& location, Term* binder_free_term);
    virtual ~BinderFreeGrammarTerm();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    const Term* get_binder_free_term() const;
};

class GroupedRuleList : public ASTBase
{
private:
    string head_symbol;
    SortExpr* head_symbol_sort;
    vector<GrammarTerm*> expansion_rules;
    vector<const GrammarTerm*> const_expansion_rules;

public:
    GroupedRuleList(const SourceLocation& location,
                    const string& head_symbol,
                    SortExpr* head_symbol_sort,
                    const vector<GrammarTerm*>& expansion_rules);
    virtual ~GroupedRuleList();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    const string& get_head_symbol() const;
    const SortExpr* get_head_symbol_sort() const;
    const vector<const GrammarTerm*>& get_expansion_rules() const;
};

class Grammar : public ASTBase
{
private:
    vector<SortedSymbol*> grammar_nonterminals;
    vector<const SortedSymbol*> const_grammar_nonterminals;
    unordered_map<string, GroupedRuleList*> grouped_rule_lists;
    unordered_map<string, const GroupedRuleList*> const_grouped_rule_lists;

public:
    Grammar(const SourceLocation& location,
            const vector<SortedSymbol*>& grammar_nonterminals,
            const vector<GroupedRuleList*>& grouped_rule_lists);
    virtual ~Grammar();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    const vector<const SortedSymbol*>& get_nonterminals() const;
    const unordered_map<string, const GroupedRuleList*>& get_grouped_rule_lists() const;
};

class Program : public ASTBase
{
private:
    vector<Command*> program_commands;
    vector<const Command*> const_program_commands;

public:
    Program(const SourceLocation& location,
            const vector<Command*>& commands);
    virtual ~Program();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    const vector<const Command*>& get_commands() const;
};

// Class definition for the sygus 2.0 parser
class Sygus2Parser
{
private:
    Program* TheProgram;
    SymbolTable* TheSymbolTable;

    // type-state variable :-(
    bool ParseComplete;

public:
    Sygus2Parser();
    ~Sygus2Parser();

    // The main parse action
    Program* parse(const string& file_name);

    // Accessors
    Program* GetProgram() const;
    SymbolTable* GetSymbolTable() const;
};

class ASTVisitorBase
{
private:
    string Name;
public:
    ASTVisitorBase(const string& Name);
    virtual ~ASTVisitorBase();

    const string& GetName() const;

    virtual void visit_index(const Index* index);
    virtual void visit_identifier(const Identifier* identifier);
    virtual void visit_sort_expr(const SortExpr* sort_expr);
    virtual void visit_sort_name_and_arity(const SortNameAndArity* sort_name_and_arity);
    virtual void visit_datatype_constructor(const DatatypeConstructor* datatype_constructor);
    virtual void visit_datatype_constructor_list(const DatatypeConstructorList* datatype_constructor_list);
    virtual void visit_literal(const Literal* literal);
    virtual void visit_literal_term(const LiteralTerm* literal_term);
    virtual void visit_identifier_term(const IdentifierTerm* identifier_term);
    virtual void visit_function_application_term(const FunctionApplicationTerm* function_application_term);
    virtual void visit_quantified_term(const QuantifiedTerm* quantified_term);
    virtual void visit_variable_binding(const VariableBinding* variable_binding);
    virtual void visit_let_term(const LetTerm* let_term);

    virtual void visit_check_synth_command(const CheckSynthCommand* check_synth_command);
    virtual void visit_constraint_command(const ConstraintCommand* constraint_command);
    virtual void visit_declare_var_command(const DeclareVarCommand* declare_var_command);
    virtual void visit_inv_constraint_command(const InvConstraintCommand* inv_constraint_command);
    virtual void visit_set_feature_command(const SetFeatureCommand* set_feature_command);
    virtual void visit_synth_fun_command(const SynthFunCommand* synth_fun_command);
    virtual void visit_synth_inv_command(const SynthInvCommand* synth_inv_command);
    virtual void visit_declare_sort_command(const DeclareSortCommand* declare_sort_command);
    virtual void visit_define_fun_command(const DefineFunCommand* define_fun_command);
    virtual void visit_define_sort_command(const DefineSortCommand* define_sort_command);
    virtual void visit_declare_datatypes_command(const DeclareDatatypesCommand* declare_datatypes_command);
    virtual void visit_declare_datatype_command(const DeclareDatatypeCommand* declare_datatype_command);
    virtual void visit_set_logic_command(const SetLogicCommand* set_logic_command);
    virtual void visit_set_option_command(const SetOptionCommand* set_option_command);
    virtual void visit_constant_grammar_term(const ConstantGrammarTerm* constant_grammar_term);
    virtual void visit_variable_grammar_term(const VariableGrammarTerm* variable_grammar_term);
    virtual void visit_binder_free_grammar_term(const BinderFreeGrammarTerm* binder_free_grammar_term);
    virtual void visit_grouped_rule_list(const GroupedRuleList* grouped_rule_list);
    virtual void visit_grammar(const Grammar* grammar);

    virtual void visit_program(const Program* program);
};


// // Class definition for the synthlib2 parser
// class SynthLib2Parser
// {
// private:
//     Program* TheProgram;
//     SymbolTable* TheSymbolTable;

//     // type-state variable :-(
//     bool ParseComplete;

// public:
//     SynthLib2Parser();
//     ~SynthLib2Parser();

//     // The main parse action
//     void operator () (const string& Filename, bool Pedantic = false);
//     void operator () (FILE* Handle, bool Pedantic = false);

//     // Accessors
//     Program* GetProgram() const;
//     SymbolTable* GetSymbolTable() const;
// };

// // General vector of AST cloner
// template<typename T>
// static inline vector<T> CloneVector(const vector<T>& Vec)
// {
//     const u32 NumElems = Vec.size();
//     vector<T> Retval(NumElems);

//     for(u32 i = 0; i < NumElems; ++i) {
//         Retval[i] = static_cast<T>(Vec[i]->Clone());
//     }
//     return Retval;
// }


} /* End namespace */

#endif /* __SYNTH_LIB2_PARSER_IFACE_H */
