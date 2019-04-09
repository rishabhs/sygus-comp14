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

    static SortExpr* create_bool_sort_expr(const SourceLocation& location = SourceLocation::none);
    static SortExpr* create_int_sort_expr(const SourceLocation& location = SourceLocation::none);
    static SortExpr* create_real_sort_expr(const SourceLocation& location = SourceLocation::none);
    static SortExpr* create_bv_sort_expr(u32 bv_size,
                                         const SourceLocation& location = SourceLocation::none);
    static SortExpr* create_string_sort_expr(const SourceLocation& location = SourceLocation::none);
    static SortExpr* create_array_sort_expr(SortExpr* key_sort, SortExpr* value_sort,
                                            const SourceLocation& location = SourceLocation::none);
    static SortExpr* create_datatype_sort_expr(const string& sort_name,
                                               const vector<string>& sort_constructors,
                                               const SourceLocation& location = SourceLocation::none);
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
    vector<string>& sort_parameter_names;
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
    const vector<const DatatypeConstructor*> get_datatype_constructors() const;
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
    mutable SortExpr* computed_sort;
    Term(const SourceLocation& location);
    virtual ~Term();

public:
    virtual void compute_sort(SymbolTable* symbol_table) const = 0;
    const SortExpr* get_computed_sort() const;
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

    virtual void compute_sort(SymbolTable* symbol_table) const override;

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

    virtual void compute_sort(SymbolTable* symbol_table) const override;

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

    virtual void compute_sort(SymbolTable* symbol_table) const override;

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
    virtual void compute_sort(SymbolTable* symbol_table) const override;

    QuantifierKind get_quantifier_kind() const;
    const vector<const SortedSymbol*> get_quantified_symbols() const;
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
    LetTerm(const SourceLocation& location, const vector<VariableBinding*> bindings,
            Term* let_body);
    virtual ~LetTerm();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;
    virtual void compute_sort(SymbolTable* symbol_table) const override;

    const vector<const VariableBinding*> get_bindings() const;
    const Term* get_let_body() const;
};

class Command : public ASTBase
{
private:
    Command();
    Command(const Command&);
    Command(Command&&);

    Command& operator = (const Command&);
    Command& operator = (Command&&);

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
    vector<SortExpr*> function_parameter_sorts;
    vector<string> function_parameter_symbols;
    vector<const SortExpr*> const_function_parameter_sorts;

public:
    SynthFunCommand(const SourceLocation& location,
                    const string& function_symbol,
                    const vector<SortedSymbol*> function_parameters,
                    SortExpr* function_range_sort,
                    Grammar* synthesis_grammar);
    virtual ~SynthFunCommand();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;

    const string& get_function_symbol() const;
    const vector<const SortedSymbol*> get_function_parameters() const;
    const vector<string>& get_function_parameter_symbols() const;
    const vector<const SortExpr*>& get_function_parameter_sorts() const;
    const SortExpr* get_function_range_sort() const;
    const Grammar* get_synthesis_grammar() const;
};

class SynthInvCommand : public SynthFunCommand
{
public:
    SynthInvCommand(const SourceLocation& location,
                    const string& function_symbol,
                    const vector<SortedSymbol*> function_parameters,
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
    const vector<const SortExpr*>& get_function_parameters() const;
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

public:
    DeclareDatatypesCommand(const SourceLocation& location,
                            const vector<SortNameAndArity*>& sort_names_and_arities,
                            const vector<DatatypeConstructorList*>& constructor_lists);
    virtual ~DeclareDatatypesCommand();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;
};

class DeclareDatatypeCommand : public Command
{
private:
    string datatype_sort_name;
    DatatypeConstructorList* datatype_constructor_list;

public:
    DeclareDatatypeCommand(const SourceLocation& location,
                           const string& datatype_sort_name,
                           DatatypeConstructorList* datatype_constructor_list);
    virtual ~DeclareDatatypeCommand();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBase* clone() const override;
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

class GrammarTerm : public ASTBase
{
public:
    virtual void resolve_types(SymbolTable* symbol_table) const = 0;
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

    virtual void resolve_types(SymbolTable* symbol_table) const override;

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

    virtual void resolve_types(SymbolTable* symbol_table) const override;

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

    virtual void resolve_types(SymbolTable* symbol_table) const override;

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
    const vector<const GrammarTerm*>& get_expansion_rules();
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
    unordered_map<string, const GroupedRuleList*>& get_grouped_rule_lists() const;
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


// class ArgSortPair : public ASTBase
// {
// private:
//     string Name;
//     const SortExpr* Sort;

// public:
//     ArgSortPair(const SourceLocation& Location,
//                 const string& Name,
//                 const SortExpr* Sort);
//     virtual ~ArgSortPair();

//     void Accept(ASTVisitorBase* Visitor) const override;
//     ASTBase* Clone() const override;

//     // Accessors
//     const string& GetName() const;
//     const SortExpr* GetSort() const;
// };

// // Commands
// class ASTCmd : public ASTBase
// {
// protected:
//     ASTCmdKind CmdKind;

// public:
//     ASTCmd(const SourceLocation& Location, ASTCmdKind CmdKind);
//     virtual ~ASTCmd();

//     // Accessors
//     ASTCmdKind GetKind() const;
// };

// class CheckSynthCmd : public ASTCmd
// {
// public:
//     CheckSynthCmd(const SourceLocation& Location);
//     virtual ~CheckSynthCmd();

//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;
// };

// class SetLogicCmd : public ASTCmd
// {
// private:
//     string LogicName;

// public:
//     SetLogicCmd(const SourceLocation& Location,
//                 const string& LogicName);
//     virtual ~SetLogicCmd();

//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;

//     // accessors
//     const string& GetLogicName() const;
// };

// class FunDefCmd : public ASTCmd
// {
// private:
//     string Symbol;
//     ArgList Arguments;
//     const SortExpr* Type;
//     Term* Def;
//     mutable SymbolTableScope* Scope;

// public:
//     FunDefCmd(const SourceLocation& Location,
//               const string& FunSymbol,
//               const ArgList& FunArgs,
//               const SortExpr* FunType,
//               Term* FunDef,
//               SymbolTableScope* Scope);

//     virtual ~FunDefCmd();
//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;

//     // Accessors
//     const string& GetFunName() const;
//     const ArgList& GetArgs() const;
//     const SortExpr* GetSort() const;
//     Term* GetTerm() const;

//     SymbolTableScope* GetScope() const;
//     void SetScope(SymbolTableScope* Scope) const;
// };

// class FunDeclCmd : public ASTCmd
// {
// private:
//     string Symbol;
//     vector<const SortExpr*> ArgTypes;
//     const SortExpr* Type;

// public:
//     FunDeclCmd(const SourceLocation& Location,
//                const string& FunSymbol,
//                const vector<const SortExpr*>& ArgSorts,
//                const SortExpr* Sort);
//     virtual ~FunDeclCmd();

//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;

//     const string& GetFunName() const;
//     const vector<const SortExpr*>& GetArgSorts() const;
//     const SortExpr* GetSort() const;
// };

// class SynthFunCmd : public ASTCmd
// {
// private:
//     string SynthFunName;
//     ArgList Arguments;
//     const SortExpr* FunType;
//     vector<NTDef*> GrammarRules;
//     mutable SymbolTableScope* Scope;

// public:
//     SynthFunCmd(const SourceLocation& Location,
//                 const string& Name,
//                 const ArgList& Args,
//                 const SortExpr* FunType,
//                 const vector<NTDef*> GrammarRules,
//                 SymbolTableScope* Scope);
//     virtual ~SynthFunCmd();

//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;

//     // accessors
//     const string& GetFunName() const;
//     const ArgList& GetArgs() const;
//     const SortExpr* GetSort() const;
//     const vector<NTDef*>& GetGrammarRules() const;
//     void SetScope(SymbolTableScope* Scope) const;
//     SymbolTableScope* GetScope() const;
// };

// class SynthInvCmd : public SynthFunCmd
// {
// public:
//     SynthInvCmd(const SourceLocation& Location,
//                 const string& Name,
//                 const ArgList& Args,
//                 const vector<NTDef*> GrammarRules,
//                 SymbolTableScope* Scope);

//     virtual ~SynthInvCmd();
//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;
// };

// class ConstraintCmd : public ASTCmd
// {
// private:
//     Term* TheTerm;

// public:
//     ConstraintCmd(const SourceLocation& Location,
//                   Term* TheTerm);
//     virtual ~ConstraintCmd();

//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;

//     // accessors
//     Term* GetTerm() const;
// };

// class InvConstraintCmd : public ASTCmd
// {
// private:
//     string FunctionToSynthesize;
//     string Precondition;
//     string TransitionRelation;
//     string PostCondition;

// public:
//     InvConstraintCmd(const SourceLocation& Location,
//                      const string& FunctionToSynthesize,
//                      const string& Precondition,
//                      const string& TransitionRelation,
//                      const string& PostCondition);
//     virtual ~InvConstraintCmd();

//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;

//     // accessors
//     const string& GetFunctionName() const;
//     const string& GetPreconditionName() const;
//     const string& GetTransitionRelationName() const;
//     const string& GetPostConditionName() const;
// };

// class SortDefCmd : public ASTCmd
// {
// private:
//     string Symbol;
//     const SortExpr* Expr;

// public:
//     SortDefCmd(const SourceLocation& Location,
//                const string& Symbol,
//                const SortExpr* TheSortExpr);
//     virtual ~SortDefCmd();

//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;

//     // accessors
//     const string& GetName() const;
//     const SortExpr* GetSortExpr() const;
// };

// class SetOptionCmd : public ASTCmd
// {
// private:
//     string Key;
//     const Literal* Value;

// public:
//     SetOptionCmd(const SourceLocation& Location,
//                  const string& key, const Literal* value);
//     virtual ~SetOptionCmd();

//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;

//     // accessors
//     const string& GetKey() const;
//     const Literal* GetValue() const;
// };

// class SetFeatureCmd : public ASTCmd
// {
// private:
//     string Key;
//     string Value;

// public:
//     SetFeatureCmd(const SourceLocation& Location,
//                   const string& Key, const string& Value);
//     virtual ~SetFeatureCmd();

//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;

//     const string& GetKey() const;
//     const string& GetValue() const;
// };

// class VarDeclCmd : public ASTCmd
// {
// private:
//     string VarName;
//     const SortExpr* VarType;

// public:
//     VarDeclCmd(const SourceLocation& Location,
//                const string& VarName,
//                const SortExpr* VarType);
//     virtual ~VarDeclCmd();

//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;

//     // accessors
//     const string& GetName() const;
//     const SortExpr* GetSort() const;
// };

// class SortExpr : public ASTBase
// {
// private:
//     SortKind Kind;

// public:
//     SortExpr(const SourceLocation& Location,
//              SortKind Kind);

//     virtual ~SortExpr();
//     SortKind GetKind() const;

//     virtual bool Equals(const SortExpr& Other) const = 0;
//     virtual string ToMangleString() const = 0;
//     virtual u32 Hash() const = 0;
// };

// class IntSortExpr : public SortExpr
// {
// public:
//     IntSortExpr(const SourceLocation& Location);
//     IntSortExpr();
//     virtual ~IntSortExpr();

//     virtual bool Equals(const SortExpr& Other) const override;
//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;
//     virtual string ToMangleString() const override;
//     virtual u32 Hash() const override;
// };

// class BVSortExpr : public SortExpr
// {
// private:
//     u32 Size;
// public:
//     BVSortExpr(const SourceLocation& Location,
//                u32 Size);
//     BVSortExpr(u32 Size);
//     virtual ~BVSortExpr();

//     virtual bool Equals(const SortExpr& Other) const override;
//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;
//     virtual string ToMangleString() const override;
//     virtual u32 Hash() const override;
//     // accessors
//     u32 GetSize() const;
// };

// class NamedSortExpr : public SortExpr
// {
// private:
//     string Name;

// public:
//     NamedSortExpr(const SourceLocation& Location,
//                   const string& Name);
//     NamedSortExpr(const string& Name);
//     virtual ~NamedSortExpr();
//     virtual bool Equals(const SortExpr& Other) const override;
//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;
//     virtual string ToMangleString() const override;
//     const string& GetName() const;
//     virtual u32 Hash() const override;
// };

// class ArraySortExpr : public SortExpr
// {
// private:
//     const SortExpr* DomainSort;
//     const SortExpr* RangeSort;

// public:
//     ArraySortExpr(const SourceLocation& Location,
//                   const SortExpr* DomainSort,
//                   const SortExpr* RangeSort);
//     ArraySortExpr(const SortExpr* DomainSort, const SortExpr* RangeSort);
//     virtual ~ArraySortExpr();

//     virtual bool Equals(const SortExpr& Other) const override;
//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;
//     virtual string ToMangleString() const override;

//     // accessors
//     const SortExpr* GetDomainSort() const;
//     const SortExpr* GetRangeSort() const;
//     virtual u32 Hash() const override;
// };

// class RealSortExpr : public SortExpr
// {
// public:
//     RealSortExpr(const SourceLocation& Location);
//     RealSortExpr();
//     virtual ~RealSortExpr();

//     virtual bool Equals(const SortExpr& Other) const override;
//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;
//     virtual string ToMangleString() const override;
//     virtual u32 Hash() const override;
// };

// class FunSortExpr : public SortExpr
// {
// private:
//     vector<const SortExpr*> ArgSorts;
//     const SortExpr* RetSort;

// public:
//     FunSortExpr(const SourceLocation& Location,
//                 const vector<const SortExpr*>& ArgSorts,
//                 const SortExpr* RetSort);
//     FunSortExpr(const vector<const SortExpr*>& ArgSorts,
//                 const SortExpr* RetSort);

//     virtual ~FunSortExpr();

//     virtual bool Equals(const SortExpr& Other) const override;
//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;
//     virtual string ToMangleString() const override;

//     // Accessors
//     const vector<const SortExpr*>& GetArgSorts() const;
//     const SortExpr* GetRetSort() const;
//     virtual u32 Hash() const override;
// };

// class BoolSortExpr : public SortExpr
// {
// public:
//     BoolSortExpr(const SourceLocation& Location);
//     BoolSortExpr();
//     virtual ~BoolSortExpr();

//     virtual bool Equals(const SortExpr& Other) const override;
//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;
//     virtual string ToMangleString() const override;
//     virtual u32 Hash() const override;
// };

// class EnumSortExpr : public SortExpr
// {
// private:
//     mutable string EnumSortName;
//     const vector<string> EnumSortConstructorVec;
//     const set<string> EnumSortConstructorSet;

// public:
//     EnumSortExpr(const SourceLocation& Location,
//                  const string& EnumSortName,
//                  const vector<string>& EnumConstructors);
//     EnumSortExpr(const SourceLocation& Location,
//                  const vector<string>& EnumConstructors);
//     virtual ~EnumSortExpr();

//     virtual bool Equals(const SortExpr& Other) const override;
//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;
//     virtual string ToMangleString() const override;
//     virtual u32 Hash() const override;

//     // accessors
//     const vector<string>& GetConstructors() const;
//     const string& GetEnumSortName() const;
//     void SetEnumSortName(const string& Name) const;
//     bool IsConstructorValid(const string& ConstructorName) const;
// };

// class Literal : public ASTBase
// {
// private:
//     string LiteralString;
//     SortExpr* LiteralSort;

// public:
//     Literal(const SourceLocation& Location,
//             const string& Constructor,
//             SortExpr* Sort);

//     virtual ~Literal();

//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;

//     const SortExpr* GetSort(SymbolTable* SymTab) const;
//     const string& GetLiteralString() const;
// };

// class Term : public ASTBase
// {
// private:
//     TermKind Kind;

// public:
//     Term(const SourceLocation& Location, TermKind Kind);

//     virtual ~Term();

//     TermKind GetKind() const;
//     virtual const SortExpr* GetTermSort(SymbolTable* SymTab) const = 0;
// };

// class FunTerm : public Term
// {
// private:
//     string FunName;
//     vector<Term*> Args;

// public:
//     FunTerm(const SourceLocation& Location,
//             const string& FunName,
//             const vector<Term*>& Args);
//     virtual ~FunTerm();

//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;
//     virtual const SortExpr* GetTermSort(SymbolTable* SymTab) const override;

//     // accessors
//     const string& GetFunName() const;
//     const vector<Term*>& GetArgs() const;
// };

// class LiteralTerm : public Term
// {
// private:
//     Literal* TheLiteral;

// public:
//     LiteralTerm(const SourceLocation& Location,
//                 Literal* TheLiteral);
//     virtual ~LiteralTerm();

//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;
//     virtual const SortExpr* GetTermSort(SymbolTable* SymTab) const override;

//     // accessors
//     Literal* GetLiteral() const;
// };

// class SymbolTerm : public Term
// {
// private:
//     string TheSymbol;

// public:
//     SymbolTerm(const SourceLocation& Location,
//                const string& TheSymbol);
//     virtual ~SymbolTerm();

//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;
//     virtual const SortExpr* GetTermSort(SymbolTable* SymTab) const override;

//     const string& GetSymbol() const;
// };

// class LetBindingTerm : public ASTBase
// {
// private:
//     const string VarName;
//     const SortExpr* VarSort;
//     Term* BoundToTerm;

// public:
//     LetBindingTerm(const SourceLocation& Location,
//                    const string& VarName,
//                    const SortExpr* VarSort,
//                    Term* BoundToTerm);
//     virtual ~LetBindingTerm();

//     void Accept(ASTVisitorBase* Visitor) const override;
//     ASTBase* Clone() const override;

//     // Accessors
//     const string& GetVarName() const;
//     const SortExpr* GetVarSort() const;
//     Term* GetBoundToTerm() const;
// };

// class LetTerm : public Term
// {
// private:
//     vector<LetBindingTerm*> Bindings;
//     Term* BoundInTerm;
//     mutable SymbolTableScope* Scope;

// public:
//     LetTerm(const SourceLocation& Location,
//             const vector<LetBindingTerm*>& Bindings,
//             Term* BoundInTerm,
//             SymbolTableScope* Scope);
//     virtual ~LetTerm();

//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;
//     virtual const SortExpr* GetTermSort(SymbolTable* SymTab) const override;

//     // Accessors
//     const vector<LetBindingTerm*>& GetBindings() const;
//     Term* GetBoundInTerm() const;
//     void SetScope(SymbolTableScope* Scope) const;
//     SymbolTableScope* GetScope() const;
// };

// // TODO: uggh, this code is similar to Term, consider refactoring
// class GTerm : public ASTBase
// {
// private:
//     GTermKind Kind;

// public:
//     GTerm(const SourceLocation& Location,
//           GTermKind Kind);
//     virtual ~GTerm();

//     GTermKind GetKind() const;
//     virtual const SortExpr* GetTermSort(SymbolTable* SymTab) const = 0;
// };

// class SymbolGTerm : public GTerm
// {
// private:
//     string TheSymbol;

// public:
//     SymbolGTerm(const SourceLocation& Location,
//                 const string& TheSymbol);
//     virtual ~SymbolGTerm();

//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;
//     virtual const SortExpr* GetTermSort(SymbolTable* SymTab) const override;

//     // Accessors
//     const string& GetSymbol() const;
// };

// class FunGTerm : public GTerm
// {
// private:
//     string FunName;
//     vector<GTerm*> Args;

// public:
//     FunGTerm(const SourceLocation& Location,
//              const string& FunName,
//              const vector<GTerm*>& Args);
//     virtual ~FunGTerm();

//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;
//     virtual const SortExpr* GetTermSort(SymbolTable* SymTab) const override;

//     // Accessors
//     const string& GetName() const;
//     const vector<GTerm*>& GetArgs() const;
// };

// class LiteralGTerm : public GTerm
// {
// private:
//     Literal* TheLiteral;

// public:
//     LiteralGTerm(const SourceLocation& Location,
//                  Literal* TheLiteral);
//     virtual ~LiteralGTerm();

//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;
//     virtual const SortExpr* GetTermSort(SymbolTable* SymTab) const override;

//     Literal* GetLiteral() const;
// };

// class ConstantGTerm : public GTerm
// {
// private:
//     const SortExpr* ConstantSort;

// public:
//     ConstantGTerm(const SourceLocation& Location,
//                   const SortExpr* Sort);
//     virtual ~ConstantGTerm();

//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;
//     virtual const SortExpr* GetTermSort(SymbolTable* SymTab) const override;

//     // accessor
//     const SortExpr* GetSort() const;
// };

// class VariableGTerm : public GTerm
// {
// private:
//     const SortExpr* VariableSort;
//     VariableKind Kind;

// public:
//     VariableGTerm(const SourceLocation& Location,
//                   const SortExpr* VariableSort,
//                   VariableKind Kind);
//     virtual ~VariableGTerm();

//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;
//     virtual const SortExpr* GetTermSort(SymbolTable* SymTab) const override;

//     // accessors
//     const SortExpr* GetSort() const;
//     VariableKind GetKind() const;
// };

// class LetBindingGTerm : public ASTBase
// {
// private:
//     string VarName;
//     const SortExpr* VarSort;
//     GTerm* BoundToTerm;

// public:
//     LetBindingGTerm(const SourceLocation& Location,
//                     const string& VarName,
//                     const SortExpr* VarSort,
//                     GTerm* BoundToTerm);
//     virtual ~LetBindingGTerm();

//     void Accept(ASTVisitorBase* Visitor) const override;
//     ASTBase* Clone() const override;

//     const string& GetVarName() const;
//     GTerm* GetBoundToTerm() const;
//     const SortExpr* GetVarSort() const;
// };

// class LetGTerm : public GTerm
// {
// private:
//     vector<LetBindingGTerm*> Bindings;
//     GTerm* BoundInTerm;
//     mutable SymbolTableScope* Scope;

// public:
//     LetGTerm(const SourceLocation& Location,
//              const vector<LetBindingGTerm*>& Bindings,
//              GTerm* BoundInTerm,
//              SymbolTableScope* Scope);

//     virtual ~LetGTerm();

//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;
//     virtual const SortExpr* GetTermSort(SymbolTable* SymTab) const override;

//     // accessors
//     const vector<LetBindingGTerm*>& GetBindings() const;
//     GTerm* GetBoundInTerm() const;
//     void SetScope(SymbolTableScope* Scope) const;
//     SymbolTableScope* GetScope() const;
// };

// class NTDef : public ASTBase
// {
// private:
//     string Symbol;
//     const SortExpr* Sort;
//     vector<GTerm*> Expansions;

// public:
//     NTDef(const SourceLocation& Location,
//           const string& Symbol,
//           const SortExpr* Sort,
//           const vector<GTerm*>& Expansions);
//     virtual ~NTDef();

//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;

//     // accessors
//     const string& GetName() const;
//     const SortExpr* GetSort() const;
//     const vector<GTerm*>& GetExpansions() const;
// };

// class Program : public ASTBase
// {
// private:
//     vector<ASTCmd*> Cmds;

// public:
//     Program(const vector<ASTCmd*>& Cmds);
//     virtual ~Program();

//     virtual void Accept(ASTVisitorBase* Visitor) const override;
//     virtual ASTBase* Clone() const override;

//     // accessors
//     const vector<ASTCmd*>& GetCmds() const;
// };

class ASTVisitorBase
{
private:
    string Name;
public:
    ASTVisitorBase(const string& Name);
    virtual ~ASTVisitorBase();

    // Visit methods
    // virtual void VisitProgram(const Program* Prog);

    // virtual void VisitFunDefCmd(const FunDefCmd* Cmd);
    // virtual void VisitFunDeclCmd(const FunDeclCmd* Cmd);
    // virtual void VisitSynthFunCmd(const SynthFunCmd* Cmd);
    // virtual void VisitSortDefCmd(const SortDefCmd* Cmd);
    // virtual void VisitSetOptionCmd(const SetOptionCmd* Cmd);
    // virtual void VisitSetFeatureCmd(const SetFeatureCmd* Cmd);
    // virtual void VisitVarDeclCmd(const VarDeclCmd* Cmd);
    // virtual void VisitConstraintCmd(const ConstraintCmd* Cmd);
    // virtual void VisitSetLogicCmd(const SetLogicCmd* Cmd);
    // virtual void VisitCheckSynthCmd(const CheckSynthCmd* Cmd);
    // virtual void VisitArgSortPair(const ArgSortPair* ASPair);

    // virtual void VisitIntSortExpr(const IntSortExpr* Sort);
    // virtual void VisitBVSortExpr(const BVSortExpr* Sort);
    // virtual void VisitNamedSortExpr(const NamedSortExpr* Sort);
    // virtual void VisitArraySortExpr(const ArraySortExpr* Sort);
    // virtual void VisitRealSortExpr(const RealSortExpr* Sort);
    // virtual void VisitFunSortExpr(const FunSortExpr* Sort);
    // virtual void VisitBoolSortExpr(const BoolSortExpr* Sort);
    // virtual void VisitEnumSortExpr(const EnumSortExpr* Sort);

    // virtual void VisitLetBindingTerm(const LetBindingTerm* Binding);

    // virtual void VisitFunTerm(const FunTerm* TheTerm);
    // virtual void VisitLiteralTerm(const LiteralTerm* TheTerm);
    // virtual void VisitSymbolTerm(const SymbolTerm* TheTerm);
    // virtual void VisitLetTerm(const LetTerm* TheTerm);

    // virtual void VisitLetBindingGTerm(const LetBindingGTerm* Binding);

    // virtual void VisitFunGTerm(const FunGTerm* TheTerm);
    // virtual void VisitLiteralGTerm(const LiteralGTerm* TheTerm);
    // virtual void VisitSymbolGTerm(const SymbolGTerm* TheTerm);
    // virtual void VisitLetGTerm(const LetGTerm* TheTerm);
    // virtual void VisitConstantGTerm(const ConstantGTerm* TheTerm);
    // virtual void VisitVariableGTerm(const VariableGTerm* TheTerm);

    // virtual void VisitNTDef(const NTDef* Def);
    // virtual void VisitLiteral(const Literal* TheLiteral);

    const string& GetName() const;

    virtual void visit_index(const Index* index);
    virtual void visit_identifier(const Identifier* identifier);
    virtual void visit_sort_expr(const SortExpr* sort_expr);
    virtual void visit_literal(const Literal* literal);
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
