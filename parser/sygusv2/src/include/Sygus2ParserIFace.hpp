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
#include <unordered_map>

#include "Sygus2ParserCommon.hpp"
#include "BaseTypes.hpp"
#include "RefCountable.hpp"
#include "ManagedPointer.hpp"
#include "SourceLocation.hpp"

namespace Sygus2Parser {

using namespace std;

class ASTBase;
class ASTVisitorBase;
typedef ManagedPointer<ASTBase> ASTBaseSPtr;
typedef ManagedConstPointer<ASTBase> ASTBaseCSPtr;

class SymbolTable;
typedef ManagedPointer<SymbolTable> SymbolTableSPtr;

class SymbolTableScope;
typedef ManagedPointer<SymbolTableScope> SymbolTableScopeSPtr;

class ASTBase : public RefCountable<ASTBase>, public Downcastable<ASTBase>
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
    virtual ASTBaseSPtr clone() const = 0;
};


class Index : public ASTBase, public Equatable<Index>, public Hashable<Index>
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
    virtual ASTBaseSPtr clone() const override;

    bool equals_(const Index& other) const;
    u64 compute_hash_() const;

    Index& operator = (const Index& other);
    Index& operator = (Index&& other);

    // accessors
    bool is_symbol() const;
    bool is_numeral() const;
    const string& get_symbol() const;
    i32 get_numeral() const;
    string to_string() const;
};

typedef ManagedPointer<Index> IndexSPtr;
typedef ManagedConstPointer<Index> IndexCSPtr;

class Identifier : public ASTBase, public Equatable<Identifier>, public Hashable<Identifier>
{
private:
    string symbol;
    vector<IndexSPtr> indices;
    vector<IndexCSPtr> const_indices;

public:
    Identifier(const string& symbol);
    Identifier(const SourceLocation& location, const string& symbol);
    Identifier(const SourceLocation& location, const string& symbol, const vector<IndexSPtr>& indices);
    Identifier(const Identifier& other);
    Identifier(Identifier&& other);

    virtual ~Identifier();

    bool equals_(const Identifier& other) const;
    u64 compute_hash_() const;

    Identifier& operator = (const Identifier& other);
    Identifier& operator = (Identifier&& other);

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBaseSPtr clone() const override;

    bool is_indexed() const;

    // accessors
    const string& get_symbol() const;
    const vector<IndexCSPtr> get_indices() const;
    string to_string() const;
};

typedef ManagedPointer<Identifier> IdentifierSPtr;
typedef ManagedConstPointer<Identifier> IdentifierCSPtr;

class SortExpr;
typedef ManagedPointer<SortExpr> SortExprSPtr;
typedef ManagedConstPointer<SortExpr> SortExprCSPtr;

class SortExpr : public ASTBase,
                 public Equatable<SortExpr>,
                 public Hashable<SortExpr>
{
private:
    IdentifierSPtr identifier;
    vector<SortExprSPtr> param_sorts;
    vector<SortExprCSPtr> const_param_sorts;

public:
    SortExpr(const SourceLocation& location, IdentifierSPtr identifier);
    SortExpr(const SourceLocation& location, IdentifierSPtr identifier,
             const vector<SortExprSPtr>& param_sorts);
    virtual ~SortExpr();

    bool equals_(const SortExpr& other) const;
    u64 compute_hash_() const;
    string to_string() const;

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBaseSPtr clone() const override;

    IdentifierCSPtr get_identifier() const;
    const vector<SortExprCSPtr>& get_param_sorts() const;
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
    virtual ASTBaseSPtr clone() const override;

    const string& get_sort_name() const;
    u32 get_sort_arity() const;
};

typedef ManagedPointer<SortNameAndArity> SortNameAndAritySPtr;
typedef ManagedConstPointer<SortNameAndArity> SortNameAndArityCSPtr;

class SortedSymbol : public ASTBase
{
private:
    string symbol;
    SortExprSPtr sort_expr;

public:
    SortedSymbol(const SourceLocation& location, const string& symbol,
                 SortExprSPtr sort_expr);
    virtual ~SortedSymbol();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBaseSPtr clone() const override;

    const string& get_symbol() const;
    SortExprCSPtr get_sort_expr() const;
};

typedef ManagedPointer<SortedSymbol> SortedSymbolSPtr;
typedef ManagedConstPointer<SortedSymbol> SortedSymbolCSPtr;

class DatatypeConstructor : public ASTBase
{
private:
    string constructor_name;
    vector<SortedSymbolSPtr> constructor_parameters;
    vector<SortedSymbolCSPtr> const_constructor_parameters;

public:
    DatatypeConstructor(const SourceLocation& location,
                        const string& constructor_name,
                        const vector<SortedSymbolSPtr>& constructor_parameters);
    virtual ~DatatypeConstructor();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBaseSPtr clone() const override;

    const string& get_constructor_name() const;
    const vector<SortedSymbolCSPtr>& get_constructor_parameters() const;
};

typedef ManagedPointer<DatatypeConstructor> DatatypeConstructorSPtr;
typedef ManagedConstPointer<DatatypeConstructor> DatatypeConstructorCSPtr;

class DatatypeConstructorList : public ASTBase
{
private:
    vector<string> sort_parameter_names;
    vector<DatatypeConstructorSPtr> datatype_constructors;
    vector<DatatypeConstructorCSPtr> const_datatype_constructors;

public:
    DatatypeConstructorList(const SourceLocation& location,
                            const vector<string>& sort_parameter_names,
                            const vector<DatatypeConstructorSPtr>& datatype_constructors);
    virtual ~DatatypeConstructorList();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBaseSPtr clone() const override;

    const vector<string>& get_sort_parameter_names() const;
    const vector<DatatypeConstructorCSPtr>& get_datatype_constructors() const;
};

typedef ManagedPointer<DatatypeConstructorList> DatatypeConstructorListSPtr;
typedef ManagedConstPointer<DatatypeConstructorList> DatatypeConstructorListCSPtr;

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
    virtual ASTBaseSPtr clone() const override;

    const string& get_literal_string() const;
    LiteralKind get_literal_kind() const;
};

typedef ManagedPointer<Literal> LiteralSPtr;
typedef ManagedConstPointer<Literal> LiteralCSPtr;

class Term : public ASTBase
{
protected:
    mutable SortExprCSPtr sort;
    mutable SymbolTableScopeSPtr symbol_table_scope;
    Term(const SourceLocation& location);

public:
    virtual ~Term();
    void set_sort(SortExprCSPtr sort) const;
    SortExprCSPtr get_sort() const;

    void set_symbol_table_scope(SymbolTableScopeSPtr symbol_table_scope) const;
    SymbolTableScopeSPtr get_symbol_table_scope() const;

    bool push_symbol_table_scope(SymbolTableSPtr symbol_table) const;
};

typedef ManagedPointer<Term> TermSPtr;
typedef ManagedConstPointer<Term> TermCSPtr;

class IdentifierTerm : public Term
{
private:
    IdentifierSPtr identifier;

public:
    IdentifierTerm(const SourceLocation& location, IdentifierSPtr identifier);
    virtual ~IdentifierTerm();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBaseSPtr clone() const override;

    IdentifierCSPtr get_identifier() const;
};

typedef ManagedPointer<IdentifierTerm> IdentifierTermSPtr;
typedef ManagedConstPointer<IdentifierTerm> IdentifierTermCSPtr;

class LiteralTerm : public Term
{
private:
    LiteralSPtr literal;

public:
    LiteralTerm(const SourceLocation& location, LiteralSPtr literal);
    virtual ~LiteralTerm();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBaseSPtr clone() const override;

    LiteralCSPtr get_literal() const;
};

typedef ManagedPointer<LiteralTerm> LiteralTermSPtr;
typedef ManagedConstPointer<LiteralTerm> LiteralTermCSPtr;

class FunctionApplicationTerm : public Term
{
protected:
    IdentifierSPtr identifier;
    vector<TermSPtr> application_arguments;
    vector<TermCSPtr> const_application_arguments;

public:
    FunctionApplicationTerm(const SourceLocation& location,
                            IdentifierSPtr identifier,
                            const vector<TermSPtr>& application_arguments);
    virtual ~FunctionApplicationTerm();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBaseSPtr clone() const override;

    IdentifierCSPtr get_identifier() const;
    const vector<TermCSPtr>& get_application_arguments() const;
};

typedef ManagedPointer<FunctionApplicationTerm> FunctionApplicationTermSPtr;
typedef ManagedConstPointer<FunctionApplicationTerm> FunctionApplicationTermCSPtr;

enum class QuantifierKind
    {
     Forall,
     Exists
    };

class QuantifiedTerm : public Term
{
private:
    QuantifierKind quantifier_kind;
    vector<SortedSymbolSPtr> quantified_symbols;
    vector<SortedSymbolCSPtr> const_quantified_symbols;
    TermSPtr quantified_term;

public:
    QuantifiedTerm(const SourceLocation& location,
                   QuantifierKind quantifier_kind,
                   const vector<SortedSymbolSPtr> quantified_symbols,
                   TermSPtr quantified_term);
    virtual ~QuantifiedTerm();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBaseSPtr clone() const override;

    QuantifierKind get_quantifier_kind() const;
    const vector<SortedSymbolCSPtr>& get_quantified_symbols() const;
    TermCSPtr get_quantified_term() const;
};

typedef ManagedPointer<QuantifiedTerm> QuantifiedTermSPtr;
typedef ManagedConstPointer<QuantifiedTerm> QuantifiedTermCSPtr;

class VariableBinding : public ASTBase
{
private:
    string symbol;
    TermSPtr binding;

public:
    VariableBinding(const SourceLocation& location,
                    const string& symbol,
                    TermSPtr binding);
    virtual ~VariableBinding();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBaseSPtr clone() const override;

    const string& get_symbol() const;
    TermCSPtr get_binding() const;
};

typedef ManagedPointer<VariableBinding> VariableBindingSPtr;
typedef ManagedConstPointer<VariableBinding> VariableBindingCSPtr;

class LetTerm : public Term
{
private:
    vector<VariableBindingSPtr> bindings;
    vector<VariableBindingCSPtr> const_bindings;
    TermSPtr let_body;

public:
    LetTerm(const SourceLocation& location,
            const vector<VariableBindingSPtr>& bindings,
            TermSPtr let_body);
    virtual ~LetTerm();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBaseSPtr clone() const override;

    const vector<VariableBindingCSPtr>& get_bindings() const;
    TermCSPtr get_let_body() const;
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

typedef ManagedPointer<Command> CommandSPtr;
typedef ManagedConstPointer<Command> CommandCSPtr;

class CheckSynthCommand : public Command
{
public:
    CheckSynthCommand(const SourceLocation& location);
    virtual ~CheckSynthCommand();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBaseSPtr clone() const override;
};

typedef ManagedPointer<CheckSynthCommand> CheckSynthCommandSPtr;
typedef ManagedConstPointer<CheckSynthCommand> CheckSynthCommandCSPtr;

class ConstraintCommand : public Command
{
private:
    TermSPtr constraint_term;

public:
    ConstraintCommand(const SourceLocation& location,
                      TermSPtr constraint_term);
    virtual ~ConstraintCommand();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBaseSPtr clone() const override;

    TermCSPtr get_constraint_term() const;
};

typedef ManagedPointer<ConstraintCommand> ConstraintCommandSPtr;
typedef ManagedConstPointer<ConstraintCommand> ConstraintCommandCSPtr;

class DeclareVarCommand : public Command
{
private:
    string symbol;
    SortExprSPtr sort_expr;

public:
    DeclareVarCommand(const SourceLocation& location,
                      const string& symbol,
                      SortExprSPtr sort_expr);
    virtual ~DeclareVarCommand();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBaseSPtr clone() const override;

    const string& get_symbol() const;
    SortExprCSPtr get_sort_expr() const;
};

typedef ManagedPointer<DeclareVarCommand> DeclareVarCommandSPtr;
typedef ManagedConstPointer<DeclareVarCommand> DeclareVarCommandCSPtr;

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
    virtual ASTBaseSPtr clone() const override;

    const string& get_inv_fun_symbol() const;
    const string& get_precondition_symbol() const;
    const string& get_transition_relation_symbol() const;
    const string& get_postcondition_symbol() const;
};

typedef ManagedPointer<InvConstraintCommand> InvConstraintCommandSPtr;
typedef ManagedConstPointer<InvConstraintCommand> InvConstraintCommandCSPtr;

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
    virtual ASTBaseSPtr clone() const override;

    const string& get_feature_name() const;
    bool get_value() const;
};

typedef ManagedPointer<SetFeatureCommand> SetFeatureCommandSPtr;
typedef ManagedConstPointer<SetFeatureCommand> SetFeatureCommandCSPtr;

class Grammar;
typedef ManagedPointer<Grammar> GrammarSPtr;
typedef ManagedConstPointer<Grammar> GrammarCSPtr;

class SynthFunCommand : public Command
{
private:
    string function_symbol;
    vector<SortedSymbolSPtr> function_parameters;
    SortExprSPtr function_range_sort;
    GrammarSPtr synthesis_grammar;

    vector<SortedSymbolCSPtr> const_function_parameters;
    mutable SymbolTableScopeSPtr symbol_table_scope;

public:
    SynthFunCommand(const SourceLocation& location,
                    const string& function_symbol,
                    const vector<SortedSymbolSPtr>& function_parameters,
                    SortExprSPtr function_range_sort,
                    GrammarSPtr synthesis_grammar);
    virtual ~SynthFunCommand();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBaseSPtr clone() const override;

    const string& get_function_symbol() const;
    const vector<SortedSymbolCSPtr>& get_function_parameters() const;
    SortExprCSPtr get_function_range_sort() const;
    GrammarCSPtr get_synthesis_grammar() const;

    void set_symbol_table_scope(SymbolTableScopeSPtr scope) const;
    SymbolTableScopeSPtr get_symbol_table_scope() const;
};

typedef ManagedPointer<SynthFunCommand> SynthFunCommandSPtr;
typedef ManagedConstPointer<SynthFunCommand> SynthFunCommandCSPtr;

class SynthInvCommand : public SynthFunCommand
{
public:
    SynthInvCommand(const SourceLocation& location,
                    const string& function_symbol,
                    const vector<SortedSymbolSPtr>& function_parameters,
                    GrammarSPtr synthesis_grammar);
    virtual ~SynthInvCommand();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBaseSPtr clone() const override;
};

typedef ManagedPointer<SynthInvCommand> SynthInvCommandSPtr;
typedef ManagedConstPointer<SynthInvCommand> SynthInvCommandCSPtr;

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
    virtual ASTBaseSPtr clone() const override;

    const string& get_sort_name() const;
    u32 get_sort_arity() const;
};

typedef ManagedPointer<DeclareSortCommand> DeclareSortCommandSPtr;
typedef ManagedConstPointer<DeclareSortCommand> DeclareSortCommandCSPtr;

class DefineFunCommand : public Command
{
private:
    string function_symbol;
    vector<SortedSymbolSPtr> function_parameters;
    SortExprSPtr function_range_sort;
    TermSPtr function_body;

    vector<SortedSymbolCSPtr> const_function_parameters;

public:
    DefineFunCommand(const SourceLocation& location,
                     const string& function_symbol,
                     const vector<SortedSymbolSPtr>& function_parameters,
                     SortExprSPtr function_range_sort,
                     TermSPtr function_body);
    virtual ~DefineFunCommand();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBaseSPtr clone() const override;

    const string& get_function_symbol() const;
    const vector<SortedSymbolCSPtr>& get_function_parameters() const;
    SortExprCSPtr get_function_range_sort() const;
    TermCSPtr get_function_body() const;
};

typedef ManagedPointer<DefineFunCommand> DefineFunCommandSPtr;
typedef ManagedConstPointer<DefineFunCommand> DefineFunCommandCSPtr;

class DefineSortCommand : public Command
{
private:
    string sort_name;
    vector<string> sort_parameters;
    SortExprSPtr sort_expr;

public:
    DefineSortCommand(const SourceLocation& location,
                      const string& sort_name,
                      const vector<string>& sort_parameters,
                      SortExprSPtr sort_expr);
    virtual ~DefineSortCommand();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBaseSPtr clone() const override;

    const string& get_sort_name() const;
    SortExprCSPtr get_sort_expr() const;
    const vector<string>& get_sort_parameters() const;
};

typedef ManagedPointer<DefineSortCommand> DefineSortCommandSPtr;
typedef ManagedConstPointer<DefineSortCommand> DefineSortCommandCSPtr;

class DeclareDatatypesCommand : public Command
{
private:
    vector<SortNameAndAritySPtr> sort_names_and_arities;
    vector<DatatypeConstructorListSPtr> datatype_constructor_lists;

    vector<SortNameAndArityCSPtr> const_sort_names_and_arities;
    vector<DatatypeConstructorListCSPtr> const_datatype_constructor_lists;

public:
    DeclareDatatypesCommand(const SourceLocation& location,
                            const vector<SortNameAndAritySPtr>& sort_names_and_arities,
                            const vector<DatatypeConstructorListSPtr>& constructor_lists);
    virtual ~DeclareDatatypesCommand();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBaseSPtr clone() const override;

    const vector<SortNameAndArityCSPtr>& get_sort_names_and_arities() const;
    const vector<DatatypeConstructorListCSPtr>& get_datatype_constructor_lists() const;
};

typedef ManagedPointer<DeclareDatatypesCommand> DeclareDatatypesCommandSPtr;
typedef ManagedConstPointer<DeclareDatatypesCommand> DeclareDatatypesCommandCSPtr;

class DeclareDatatypeCommand : public Command
{
private:
    string datatype_name;
    DatatypeConstructorListSPtr datatype_constructor_list;

public:
    DeclareDatatypeCommand(const SourceLocation& location,
                           const string& datatype_sort_name,
                           DatatypeConstructorListSPtr datatype_constructor_list);
    virtual ~DeclareDatatypeCommand();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBaseSPtr clone() const override;

    const string& get_datatype_name() const;
    DatatypeConstructorListCSPtr get_datatype_constructor_list() const;
};

typedef ManagedPointer<DeclareDatatypeCommand> DeclareDatatypeCommandSPtr;
typedef ManagedConstPointer<DeclareDatatypeCommand> DeclareDatatypeCommandCSPtr;

class SetLogicCommand : public Command
{
private:
    string logic_name;

public:
    SetLogicCommand(const SourceLocation& location, const string& logic_name);
    virtual ~SetLogicCommand();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBaseSPtr clone() const override;

    const string& get_logic_name() const;
};

typedef ManagedPointer<SetLogicCommand> SetLogicCommandSPtr;
typedef ManagedConstPointer<SetLogicCommand> SetLogicCommandCSPtr;

class SetOptionCommand : public Command
{
private:
    string option_name;
    LiteralSPtr option_value;

public:
    SetOptionCommand(const SourceLocation& location,
                     const string& option_name,
                     LiteralSPtr option_value);
    virtual ~SetOptionCommand();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBaseSPtr clone() const override;

    const string& get_option_name() const;
    LiteralCSPtr get_option_value() const;
};

typedef ManagedPointer<SetOptionCommand> SetOptionCommandSPtr;
typedef ManagedConstPointer<SetOptionCommand> SetOptionCommandCSPtr;

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

typedef ManagedPointer<GrammarTerm> GrammarTermSPtr;
typedef ManagedConstPointer<GrammarTerm> GrammarTermCSPtr;

class ConstantGrammarTerm : public GrammarTerm
{
private:
    SortExprSPtr sort_expr;

public:
    ConstantGrammarTerm(const SourceLocation& location, SortExprSPtr sort_expr);
    virtual ~ConstantGrammarTerm();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBaseSPtr clone() const override;

    SortExprCSPtr get_sort_expr() const;
};

typedef ManagedPointer<ConstantGrammarTerm> ConstantGrammarTermSPtr;
typedef ManagedConstPointer<ConstantGrammarTerm> ConstantGrammarTermCSPtr;

class VariableGrammarTerm : public GrammarTerm
{
private:
    SortExprSPtr sort_expr;

public:
    VariableGrammarTerm(const SourceLocation& location, SortExprSPtr sort_expr);
    virtual ~VariableGrammarTerm();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBaseSPtr clone() const override;

    SortExprCSPtr get_sort_expr() const;
};

typedef ManagedPointer<VariableGrammarTerm> VariableGrammarTermSPtr;
typedef ManagedConstPointer<VariableGrammarTerm> VariableGrammarTermCSPtr;

class BinderFreeGrammarTerm : public GrammarTerm
{
private:
    TermSPtr binder_free_term;

public:
    BinderFreeGrammarTerm(const SourceLocation& location, TermSPtr binder_free_term);
    virtual ~BinderFreeGrammarTerm();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBaseSPtr clone() const override;

    TermCSPtr get_binder_free_term() const;
};

typedef ManagedPointer<BinderFreeGrammarTerm> BinderFreeGrammarTermSPtr;
typedef ManagedConstPointer<BinderFreeGrammarTerm> BinderFreeGrammarTermCSPtr;

class GroupedRuleList : public ASTBase
{
private:
    string head_symbol;
    SortExprSPtr head_symbol_sort;
    vector<GrammarTermSPtr> expansion_rules;
    vector<GrammarTermCSPtr> const_expansion_rules;

public:
    GroupedRuleList(const SourceLocation& location,
                    const string& head_symbol,
                    SortExprSPtr head_symbol_sort,
                    const vector<GrammarTermSPtr>& expansion_rules);
    virtual ~GroupedRuleList();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBaseSPtr clone() const override;

    const string& get_head_symbol() const;
    SortExprCSPtr get_head_symbol_sort() const;
    const vector<GrammarTermCSPtr>& get_expansion_rules() const;
};

typedef ManagedPointer<GroupedRuleList> GroupedRuleListSPtr;
typedef ManagedConstPointer<GroupedRuleList> GroupedRuleListCSPtr;

class Grammar : public ASTBase
{
private:
    vector<SortedSymbolSPtr> grammar_nonterminals;
    vector<SortedSymbolCSPtr> const_grammar_nonterminals;
    unordered_map<string, GroupedRuleListSPtr> grouped_rule_lists;
    unordered_map<string, GroupedRuleListCSPtr> const_grouped_rule_lists;
    mutable SymbolTableScopeSPtr symbol_table_scope;

public:
    Grammar(const SourceLocation& location,
            const vector<SortedSymbolSPtr>& grammar_nonterminals,
            const vector<GroupedRuleListSPtr>& grouped_rule_lists);
    virtual ~Grammar();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBaseSPtr clone() const override;

    const vector<SortedSymbolCSPtr>& get_nonterminals() const;
    const unordered_map<string, GroupedRuleListCSPtr>& get_grouped_rule_lists() const;

    SymbolTableScopeSPtr get_symbol_table_scope() const;
    void set_symbol_table_scope(SymbolTableScopeSPtr scope) const;

    bool push_symbol_table_scope(SymbolTableSPtr symbol_table) const;
};

typedef ManagedPointer<Grammar> GrammarSPtr;
typedef ManagedConstPointer<Grammar> GrammarCSPtr;

class Program : public ASTBase
{
private:
    vector<CommandSPtr> program_commands;
    vector<CommandCSPtr> const_program_commands;

public:
    Program(const SourceLocation& location,
            const vector<CommandSPtr>& commands);
    virtual ~Program();

    virtual void accept(ASTVisitorBase* visitor) const override;
    virtual ASTBaseSPtr clone() const override;

    const vector<CommandCSPtr>& get_commands() const;
};

typedef ManagedPointer<Program> ProgramSPtr;
typedef ManagedConstPointer<Program> ProgramCSPtr;

// Class definition for the sygus 2.0 parser
class Sygus2Parser
{
public:
    Sygus2Parser() = delete;
    Sygus2Parser(const Sygus2Parser& other) = delete;
    Sygus2Parser(Sygus2Parser&& other) = delete;
    Sygus2Parser& operator = (const Sygus2Parser& other) = delete;
    Sygus2Parser& operator = (Sygus2Parser&& other) = delete;

    // The main parse action
    static ProgramSPtr parse(const string& file_name);
    static ProgramSPtr parse(istream& input_stream);
    static ProgramSPtr parse(FILE* handle);
    static ProgramSPtr parse_string(const string& input_string);
    static ProgramSPtr parse(char* buffer);
};

class ASTVisitorBase
{
private:
    string name;
public:
    ASTVisitorBase(const string& name);
    virtual ~ASTVisitorBase();

    const string& get_name() const;

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
    virtual void visit_sorted_symbol(const SortedSymbol* sorted_symbol);
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
} /* End namespace */

#endif /* __SYNTH_LIB2_PARSER_IFACE_H */
