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

#include <algorithm>
#include <boost/functional/hash.hpp>
#include <boost/algorithm/string/split.hpp>
#include <boost/algorithm/string/classification.hpp>

#include "include/Sygus2ParserIFace.hpp"
#include "include/Sygus2ParserExceptions.hpp"
#include "include/SymbolTable.hpp"

namespace Sygus2Bison {
extern Sygus2Parser::Program* the_program;
}

typedef struct yy_buffer_state * YY_BUFFER_STATE;
extern FILE* yyin;
extern int yyparse();
extern YY_BUFFER_STATE yy_scan_string(char* str);
extern void yy_delete_buffer(YY_BUFFER_STATE buffer);

namespace Sygus2Parser {

// helper functions to clone vectors
template<typename T>
static inline void copy_vector(const vector<ManagedPointer<T>>& source,
                               vector<ManagedConstPointer<T>>& destination)
{
    destination.clear();
    destination.insert(destination.end(), source.begin(), source.end());
}

template<typename T>
static inline bool compare_ptr_vectors(const vector<ManagedPointer<T>>& v1,
                                       const vector<ManagedPointer<T>>& v2)
{
    if (v1.size() != v2.size()) {
        return false;
    }

    for(size_t i = 0; i < v1.size(); ++i) {
        if (*(v1[i]) != *(v2[i])) {
            return false;
        }
    }
    return true;
}

template<typename T>
static inline bool compare_ptr_vectors(const vector<ManagedConstPointer<T>>& v1,
                                       const vector<ManagedConstPointer<T>>& v2)
{
    if (v1.size() != v2.size()) {
        return false;
    }

    for(size_t i = 0; i < v1.size(); ++i) {
        if (*(v1[i]) != *(v2[i])) {
            return false;
        }
    }
    return true;
}

template<typename T>
static inline void clone_vector(const vector<ManagedPointer<T>>& source,
                                vector<ManagedPointer<T>>& destination)
{
    destination.clear();
    for(auto const& source_ptr : source) {
        destination.push_back(source_ptr->clone()->template static_as<T>());
    }
}

template<typename T>
static inline void clone_vector(const vector<ManagedConstPointer<T>>& source,
                                vector<ManagedPointer<T>>& destination)
{
    destination.clear();
    for(auto const& source_ptr : source) {
        destination.push_back(source_ptr->clone()->template static_as<T>());
    }
}

// Implementation of SourceLocation
SourceLocation SourceLocation::none(-1, -1);

SourceLocation::SourceLocation(i32 line, i32 column)
    : line(line), column(column)
{
    // Nothing here
}

SourceLocation::SourceLocation(const SourceLocation& other)
    : line(other.line), column(other.column)
{
    // Nothing here
}

SourceLocation::SourceLocation(SourceLocation&& other)
    : line(std::move(other.line)),
      column(std::move(other.column))
{
    // Nothing here
}

SourceLocation::~SourceLocation()
{
    // Nothing here
}

bool SourceLocation::equals_(const SourceLocation& other) const
{
    return line == other.line && column == other.column;
}

u64 SourceLocation::compute_hash_() const
{
    return (((u64)line * 317) ^ column);
}

SourceLocation& SourceLocation::operator = (const SourceLocation& other)
{
    if (&other == this) {
        return *this;
    }
    line = other.line;
    column = other.column;
    return *this;
}

SourceLocation& SourceLocation::operator = (SourceLocation&& other)
{
    if (&other == this) {
        return *this;
    }

    line = other.line;
    column = other.column;
    return *this;
}

i32 SourceLocation::get_line() const
{
    return line;
}

i32 SourceLocation::get_column() const
{
    return column;
}

string SourceLocation::to_string() const
{
    ostringstream sstr;
    sstr << line << ":" << column;
    return sstr.str();
}

// Implementation of ASTBase
ASTBase::ASTBase(const SourceLocation& location)
    : location(location)
{
    // Nothing here
}

ASTBase::~ASTBase()
{
    // Nothing here
}

const SourceLocation& ASTBase::get_location() const
{
    return location;
}

// Implementation of Index
Index::Index(const SourceLocation& location, const string& symbol)
    : ASTBase(location), symbol(symbol), numeral(-1), is_symbolic(true)
{
    // Nothing here
}

Index::Index(const SourceLocation& location, i32 numeral)
    : ASTBase(location), symbol(""), numeral(numeral), is_symbolic(false)
{
    // Nothing here
}

Index::Index(const Index& other)
    : ASTBase(other.location), symbol(other.symbol), numeral(other.numeral),
      is_symbolic(other.is_symbolic)
{
    // Nothing here
}

Index::Index(Index&& other)
    : ASTBase(std::move(other.location)),
      symbol(std::move(other.symbol)),
      numeral(std::move(other.numeral)),
      is_symbolic(std::move(other.is_symbolic))
{
    // Nothing here
}

Index::~Index()
{
    // Nothing here
}

bool Index::equals_(const Index& other) const
{
    if (is_symbolic != other.is_symbolic) {
        return false;
    }

    return is_symbolic ? symbol == other.symbol : numeral == other.numeral;
}

u64 Index::compute_hash_() const
{
    std::hash<string> string_hasher;
    if (is_symbolic) {
        auto hash = string_hasher(symbol);
        return hash << 16 ^ hash ^ hash << 23;
    } else {
        auto hash = numeral * 317;
        return hash << 16 ^ hash ^ hash << 23;
    }
}

Index& Index::operator = (const Index& other)
{
    if (&other == this) {
        return *this;
    }

    location = other.location;
    symbol = other.symbol;
    numeral = other.numeral;
    is_symbolic = other.is_symbolic;
    return *this;
}

Index& Index::operator = (Index&& other)
{
    if (&other == this) {
        return *this;
    }

    location = std::move(other.location);
    symbol = std::move(other.symbol);
    numeral = std::move(other.numeral);
    is_symbolic = std::move(other.is_symbolic);
    return *this;
}

void Index::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_index(this);
}

ASTBaseSPtr Index::clone() const
{
    if (is_symbolic) {
        return new Index(location, symbol);
    } else {
        return new Index(location, numeral);
    }
}

bool Index::is_symbol() const
{
    return is_symbolic;
}

bool Index::is_numeral() const
{
    return !is_symbolic;
}

const string& Index::get_symbol() const
{
    return symbol;
}

i32 Index::get_numeral() const
{
    return numeral;
}

string Index::to_string() const
{
    return is_symbolic ? symbol : std::to_string(numeral);
}

// Implementation of Identifier
Identifier::Identifier(const string& symbol)
    : ASTBase(SourceLocation::none), symbol(symbol)
{
    // Nothing here
}

Identifier::Identifier(const SourceLocation& location, const string& symbol)
    : ASTBase(location), symbol(symbol)
{
    // Nothing here
}

Identifier::Identifier(const SourceLocation& location, const string& symbol, const vector<IndexSPtr>& indices)
    : ASTBase(location), symbol(symbol), indices(indices)
{
    copy_vector(indices, const_indices);
}

Identifier::~Identifier()
{
    // Nothing here
}

bool Identifier::equals_(const Identifier& other) const
{
    if (symbol != other.symbol) {
        return false;
    }

    return compare_ptr_vectors(indices, other.indices);
}

u64 Identifier::compute_hash_() const
{
    std::hash<string> string_hasher;
    auto hash = string_hasher(symbol);

    for(auto const& index : indices) {
        hash = (hash * 317) ^ index->get_hash();
    }
    return hash;
}

void Identifier::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_identifier(this);
}

ASTBaseSPtr Identifier::clone() const
{
    vector<IndexSPtr> cloned_indices;
    clone_vector(indices, cloned_indices);
    return new Identifier(location, symbol, cloned_indices);
}

const string& Identifier::get_symbol() const
{
    return symbol;
}

const vector<IndexCSPtr> Identifier::get_indices() const
{
    return const_indices;
}

string Identifier::to_string() const
{
    if (indices.size() == 0) {
        return symbol;
    }

    ostringstream sstr;
    sstr << "(_ " << symbol;
    for (auto const& index : indices) {
        sstr << " " << index->to_string();
    }

    sstr << ")";
    return sstr.str();
}


// Implementation of SortExpr
SortExpr::SortExpr(const SourceLocation& location, IdentifierSPtr identifier)
    : ASTBase(location), identifier(identifier)
{
    // Nothing here
}

SortExpr::SortExpr(const SourceLocation& location, IdentifierSPtr identifier,
                   const vector<SortExprSPtr>& param_sorts)
    : ASTBase(location), identifier(identifier), param_sorts(param_sorts)
{
    copy_vector(param_sorts, const_param_sorts);
}

SortExpr::~SortExpr()
{
    // Nothing here
}

bool SortExpr::equals_(const SortExpr& other) const
{
    if (&other == this) {
        return true;
    }

    if(*identifier != *(other.identifier)) {
        return false;
    }

    return compare_ptr_vectors(param_sorts, other.param_sorts);
}

u64 SortExpr::compute_hash_() const
{
    Hasher<Identifier> identifier_hasher;
    u64 result = identifier_hasher(*identifier);

    for (auto const& param_sort : param_sorts) {
        result = (result * 1001933) ^ param_sort->get_hash();
    }

    return result;
}

string SortExpr::to_string() const
{
    ostringstream sstr;
    sstr << identifier->to_string();

    if (param_sorts.size() != 0) {
        sstr << "(";
        bool first = true;
        for(auto const& param_sort : param_sorts) {
            if (!first) {
                sstr << " ";
            }
            first = false;
            sstr << param_sort->to_string();
        }
        sstr << ")";
    }

    return sstr.str();
}

void SortExpr::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_sort_expr(this);
}

ASTBaseSPtr SortExpr::clone() const
{
    vector<SortExprSPtr> cloned_params;
    clone_vector(param_sorts, cloned_params);

    return new SortExpr(location, identifier->clone()->static_as<Identifier>(), cloned_params);
}

IdentifierCSPtr SortExpr::get_identifier() const
{
    return identifier;
}

const vector<SortExprCSPtr>& SortExpr::get_param_sorts() const
{
    return const_param_sorts;
}

// Implementation of SortNameAndArity
SortNameAndArity::SortNameAndArity(const SourceLocation& location,
                                   const string& sort_name, u32 sort_arity)
    : ASTBase(location), sort_name(sort_name), sort_arity(sort_arity)
{
    // Nothing here
}

SortNameAndArity::~SortNameAndArity()
{
    // Nothing here
}

void SortNameAndArity::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_sort_name_and_arity(this);
}

ASTBaseSPtr SortNameAndArity::clone() const
{
    return new SortNameAndArity(location, sort_name, sort_arity);
}

const string& SortNameAndArity::get_sort_name() const
{
    return sort_name;
}

u32 SortNameAndArity::get_sort_arity() const
{
    return sort_arity;
}

// Implementation of DatatypeConstructor
DatatypeConstructor::DatatypeConstructor(const SourceLocation& location,
                                         const string& constructor_name,
                                         const vector<SortedSymbolSPtr>& constructor_parameters)
    : ASTBase(location), constructor_name(constructor_name),
      constructor_parameters(constructor_parameters)
{
    copy_vector(constructor_parameters, const_constructor_parameters);
}

DatatypeConstructor::~DatatypeConstructor()
{
    // Nothing here
}

void DatatypeConstructor::accept(ASTVisitorBase* visitor) const
{
    return visitor->visit_datatype_constructor(this);
}

ASTBaseSPtr DatatypeConstructor::clone() const
{
    vector<SortedSymbolSPtr> cloned_params;
    clone_vector(constructor_parameters, cloned_params);
    return new DatatypeConstructor(location, constructor_name, cloned_params);
}

const string& DatatypeConstructor::get_constructor_name() const
{
    return constructor_name;
}

const vector<SortedSymbolCSPtr>& DatatypeConstructor::get_constructor_parameters() const
{
    return const_constructor_parameters;
}

// Implementation of DatatypeConstructorList
DatatypeConstructorList::DatatypeConstructorList(const SourceLocation& location,
                                                 const vector<string>& sort_parameter_names,
                                                 const vector<DatatypeConstructorSPtr>& datatype_constructors)
    : ASTBase(location), sort_parameter_names(sort_parameter_names),
      datatype_constructors(datatype_constructors)
{
    copy_vector(datatype_constructors, const_datatype_constructors);
}

DatatypeConstructorList::~DatatypeConstructorList()
{
    // Nothing here
}

void DatatypeConstructorList::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_datatype_constructor_list(this);
}

ASTBaseSPtr DatatypeConstructorList::clone() const
{
    vector<DatatypeConstructorSPtr> cloned_constructors;
    clone_vector(datatype_constructors, cloned_constructors);
    return new DatatypeConstructorList(location, sort_parameter_names, cloned_constructors);
}

const vector<string>& DatatypeConstructorList::get_sort_parameter_names() const
{
    return sort_parameter_names;
}

const vector<DatatypeConstructorCSPtr>& DatatypeConstructorList::get_datatype_constructors() const
{
    return const_datatype_constructors;
}


// Implementation of Literal
Literal::Literal(const SourceLocation& location, const string& literal_string,
                 LiteralKind literal_kind)
    : ASTBase(location), literal_string(literal_string), literal_kind(literal_kind)
{
    // Nothing here
}

Literal::~Literal()
{
    // Nothing here
}

void Literal::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_literal(this);
}

ASTBaseSPtr Literal::clone() const
{
    return new Literal(location, literal_string, literal_kind);
}

const string& Literal::get_literal_string() const
{
    return literal_string;
}

LiteralKind Literal::get_literal_kind() const
{
    return literal_kind;
}

// Implementation of Term
Term::Term(const SourceLocation& location)
    : ASTBase(location), sort(nullptr)
{
    // Nothing here
}

Term::~Term()
{
    // Nothing here
}

SortExprCSPtr Term::get_sort() const
{
    return sort;
}

void Term::set_sort(SortExprCSPtr sort) const
{
    this->sort = sort;
}

void Term::set_symbol_table_scope(SymbolTableScopeSPtr scope) const
{
    symbol_table_scope = scope;
}

SymbolTableScopeSPtr Term::get_symbol_table_scope() const
{
    return symbol_table_scope;
}

bool Term::push_symbol_table_scope(SymbolTableSPtr symbol_table) const
{
    if (symbol_table_scope.is_null()) {
        return false;
    }

    symbol_table->push_scope(symbol_table_scope);
    return true;
}

IdentifierTerm::IdentifierTerm(const SourceLocation& location, IdentifierSPtr identifier)
    : Term(location), identifier(identifier)
{
    // Nothing here
}

IdentifierTerm::~IdentifierTerm()
{
    // Nothing here
}

void IdentifierTerm::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_identifier_term(this);
}

ASTBaseSPtr IdentifierTerm::clone() const
{
    return new IdentifierTerm(location, identifier->clone()->static_as<Identifier>());
}

IdentifierCSPtr IdentifierTerm::get_identifier() const
{
    return identifier;
}

// Implementation of LiteralTerm
LiteralTerm::LiteralTerm(const SourceLocation& location, LiteralSPtr literal)
    : Term(location), literal(literal)
{
    // Nothing here
}

LiteralTerm::~LiteralTerm()
{
    delete literal;
}

void LiteralTerm::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_literal_term(this);
}

ASTBaseSPtr LiteralTerm::clone() const
{
    return new LiteralTerm(location, literal->clone()->static_as<Literal>());
}

LiteralCSPtr LiteralTerm::get_literal() const
{
    return literal;
}

// Implementation of FunctionApplicationTerm
FunctionApplicationTerm::FunctionApplicationTerm(const SourceLocation& location,
                                                 IdentifierSPtr identifier,
                                                 const vector<TermSPtr>& application_arguments)
    : Term(location), identifier(identifier), application_arguments(application_arguments)
{
    copy_vector(application_arguments, const_application_arguments);
}

FunctionApplicationTerm::~FunctionApplicationTerm()
{
    // Nothing here
}

void FunctionApplicationTerm::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_function_application_term(this);
}

ASTBaseSPtr FunctionApplicationTerm::clone() const
{
    vector<TermSPtr> cloned_args;
    clone_vector(application_arguments, cloned_args);
    return new FunctionApplicationTerm(location, identifier->clone()->static_as<Identifier>(), cloned_args);
}

IdentifierCSPtr FunctionApplicationTerm::get_identifier() const
{
    return identifier;
}

const vector<TermCSPtr>& FunctionApplicationTerm::get_application_arguments() const
{
    return const_application_arguments;
}

// Implementation of SortedSymbol
SortedSymbol::SortedSymbol(const SourceLocation& location, const string& symbol,
                           SortExprSPtr sort_expr)
    : ASTBase(location), symbol(symbol), sort_expr(sort_expr)
{
    // Nothing here
}

SortedSymbol::~SortedSymbol()
{
    // Nothing here
}

void SortedSymbol::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_sorted_symbol(this);
}

ASTBaseSPtr SortedSymbol::clone() const
{
    return new SortedSymbol(location, symbol, sort_expr->clone()->static_as<SortExpr>());
}

const string& SortedSymbol::get_symbol() const
{
    return symbol;
}

SortExprCSPtr SortedSymbol::get_sort_expr() const
{
    return sort_expr;
}

// Implementation of QuantifiedTerm
QuantifiedTerm::QuantifiedTerm(const SourceLocation& location,
                               QuantifierKind quantifier_kind,
                               const vector<SortedSymbolSPtr> quantified_symbols,
                               TermSPtr quantified_term)
    : Term(location), quantifier_kind(quantifier_kind),
      quantified_symbols(quantified_symbols), quantified_term(quantified_term)
{
    copy_vector(quantified_symbols, const_quantified_symbols);
}

QuantifiedTerm::~QuantifiedTerm()
{
    // Nothing here
}

void QuantifiedTerm::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_quantified_term(this);
}

ASTBaseSPtr QuantifiedTerm::clone() const
{
    vector<SortedSymbolSPtr> cloned_quantified_symbols;
    clone_vector(quantified_symbols, cloned_quantified_symbols);
    return new QuantifiedTerm(location, quantifier_kind, cloned_quantified_symbols,
                              quantified_term->clone()->static_as<Term>());
}

QuantifierKind QuantifiedTerm::get_quantifier_kind() const
{
    return quantifier_kind;
}

const vector<SortedSymbolCSPtr>& QuantifiedTerm::get_quantified_symbols() const
{
    return const_quantified_symbols;
}

TermCSPtr QuantifiedTerm::get_quantified_term() const
{
    return quantified_term;
}

// Implementation of VariableBinding
VariableBinding::VariableBinding(const SourceLocation& location,
                                 const string& symbol, TermSPtr binding)
    : ASTBase(location), symbol(symbol), binding(binding)
{
    // Nothing here
}

VariableBinding::~VariableBinding()
{
    // Nothing here
}

void VariableBinding::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_variable_binding(this);
}

ASTBaseSPtr VariableBinding::clone() const
{
    return new VariableBinding(location, symbol, binding->clone()->static_as<Term>());
}

const string& VariableBinding::get_symbol() const
{
    return symbol;
}

TermCSPtr VariableBinding::get_binding() const
{
    return binding;
}

// Implementation of LetTerm
LetTerm::LetTerm(const SourceLocation& location,
                 const vector<VariableBindingSPtr>& bindings,
                 TermSPtr let_body)
    : Term(location), bindings(bindings), let_body(let_body)
{
    copy_vector(bindings, const_bindings);
}

LetTerm::~LetTerm()
{
    // Nothing here
}

void LetTerm::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_let_term(this);
}

ASTBaseSPtr LetTerm::clone() const
{
    vector<VariableBindingSPtr> cloned_bindings;
    clone_vector(bindings, cloned_bindings);
    return new LetTerm(location, cloned_bindings, let_body->clone()->static_as<Term>());
}

const vector<VariableBindingCSPtr>& LetTerm::get_bindings() const
{
    return const_bindings;
}

TermCSPtr LetTerm::get_let_body() const
{
    return let_body;
}

// Implementation of Command
Command::Command(const SourceLocation& location)
    : ASTBase(location)
{
    // Nothing here
}

// Implementation of CheckSynthCommand
CheckSynthCommand::CheckSynthCommand(const SourceLocation& location)
    : Command(location)
{
    // Nothing here
}

CheckSynthCommand::~CheckSynthCommand()
{
    // Nothing here
}

void CheckSynthCommand::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_check_synth_command(this);
}

ASTBaseSPtr CheckSynthCommand::clone() const
{
    return new CheckSynthCommand(location);
}

// Implementation of ConstraintCommand
ConstraintCommand::ConstraintCommand(const SourceLocation& location,
                                     TermSPtr constraint_term)
    : Command(location), constraint_term(constraint_term)
{
    // Nothing here
}

ConstraintCommand::~ConstraintCommand()
{
    // Nothing here
}

void ConstraintCommand::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_constraint_command(this);
}

ASTBaseSPtr ConstraintCommand::clone() const
{
    return new ConstraintCommand(location, constraint_term->clone()->static_as<Term>());
}

TermCSPtr ConstraintCommand::get_constraint_term() const
{
    return constraint_term;
}

// Implementation of DeclareVarCommand
DeclareVarCommand::DeclareVarCommand(const SourceLocation& location, const string& symbol,
                                     SortExprSPtr sort_expr)
    : Command(location), symbol(symbol), sort_expr(sort_expr)
{
    // Nothing here
}

DeclareVarCommand::~DeclareVarCommand()
{
    // Nothing here
}

void DeclareVarCommand::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_declare_var_command(this);
}

ASTBaseSPtr DeclareVarCommand::clone() const
{
    return new DeclareVarCommand(location, symbol, sort_expr->clone()->static_as<SortExpr>());
}

const string& DeclareVarCommand::get_symbol() const
{
    return symbol;
}

SortExprCSPtr DeclareVarCommand::get_sort_expr() const
{
    return sort_expr;
}


// Implementation of InvConstraintCommand
InvConstraintCommand::InvConstraintCommand(const SourceLocation& location,
                                           const string& inv_fun_symbol,
                                           const string& precondition_symbol,
                                           const string& transition_relation_symbol,
                                           const string& postcondition_symbol)
    : Command(location), inv_fun_symbol(inv_fun_symbol),
      precondition_symbol(precondition_symbol),
      transition_relation_symbol(transition_relation_symbol),
      postcondition_symbol(postcondition_symbol)
{
    // Nothing here
}

InvConstraintCommand::~InvConstraintCommand()
{
    // Nothing here
}

void InvConstraintCommand::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_inv_constraint_command(this);
}

ASTBaseSPtr InvConstraintCommand::clone() const
{
    return new InvConstraintCommand(location, inv_fun_symbol, precondition_symbol,
                                    transition_relation_symbol, postcondition_symbol);
}

const string& InvConstraintCommand::get_inv_fun_symbol() const
{
    return inv_fun_symbol;
}

const string& InvConstraintCommand::get_precondition_symbol() const
{
    return precondition_symbol;
}

const string& InvConstraintCommand::get_transition_relation_symbol() const
{
    return transition_relation_symbol;
}

const string& InvConstraintCommand::get_postcondition_symbol() const
{
    return postcondition_symbol;
}

// Implementation of SetFeatureCommand
SetFeatureCommand::SetFeatureCommand(const SourceLocation& location,
                                     const string& feature_name,
                                     bool value)
    : Command(location), feature_name(feature_name), value(value)
{
    // Nothing here
}

SetFeatureCommand::~SetFeatureCommand()
{
    // Nothing here
}

void SetFeatureCommand::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_set_feature_command(this);
}

ASTBaseSPtr SetFeatureCommand::clone() const
{
    return new SetFeatureCommand(location, feature_name, value);
}

const string& SetFeatureCommand::get_feature_name() const
{
    return feature_name;
}

bool SetFeatureCommand::get_value() const
{
    return value;
}

// Implementation of SynthFunCommand
SynthFunCommand::SynthFunCommand(const SourceLocation& location, const string& function_symbol,
                                 const vector<SortedSymbolSPtr>& function_parameters,
                                 SortExprSPtr function_range_sort,
                                 GrammarSPtr synthesis_grammar)
    : Command(location), function_symbol(function_symbol),
      function_parameters(function_parameters), function_range_sort(function_range_sort),
      synthesis_grammar(synthesis_grammar)
{
    copy_vector(function_parameters, const_function_parameters);
}

SynthFunCommand::~SynthFunCommand()
{
    // Nothing here
}

void SynthFunCommand::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_synth_fun_command(this);
}

ASTBaseSPtr SynthFunCommand::clone() const
{
    vector<SortedSymbolSPtr> cloned_params;
    clone_vector(function_parameters, cloned_params);
    return new SynthFunCommand(location, function_symbol, cloned_params,
                               function_range_sort->clone()->static_as<SortExpr>(),
                               synthesis_grammar->clone()->static_as<Grammar>());
}

const string& SynthFunCommand::get_function_symbol() const
{
    return function_symbol;
}

const vector<SortedSymbolCSPtr>& SynthFunCommand::get_function_parameters() const
{
    return const_function_parameters;
}

SortExprCSPtr SynthFunCommand::get_function_range_sort() const
{
    return function_range_sort;
}

GrammarCSPtr SynthFunCommand::get_synthesis_grammar() const
{
    return synthesis_grammar;
}

void SynthFunCommand::set_symbol_table_scope(SymbolTableScopeSPtr scope) const
{
    symbol_table_scope = scope;
}

SymbolTableScopeSPtr SynthFunCommand::get_symbol_table_scope() const
{
    return symbol_table_scope;
}

// Implementation of SynthInvCommand
SynthInvCommand::SynthInvCommand(const SourceLocation& location,
                                 const string& function_symbol,
                                 const vector<SortedSymbolSPtr>& function_parameters,
                                 GrammarSPtr synthesis_grammar)
    : SynthFunCommand(location, function_symbol, function_parameters,
                      new SortExpr(location, new Identifier(location, "Bool")),
                      synthesis_grammar)
{
    // Nothing here
}

SynthInvCommand::~SynthInvCommand()
{
    // Nothing here
}

void SynthInvCommand::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_synth_inv_command(this);
}

ASTBaseSPtr SynthInvCommand::clone() const
{
    vector<SortedSymbolSPtr> cloned_params;
    clone_vector(get_function_parameters(), cloned_params);
    return new SynthInvCommand(location, get_function_symbol(), cloned_params,
                               get_synthesis_grammar()->clone()->static_as<Grammar>());
}


// Implementation of DeclareSortCommand
DeclareSortCommand::DeclareSortCommand(const SourceLocation& location,
                                       const string& sort_name,
                                       u32 sort_arity)
    : Command(location), sort_name(sort_name), sort_arity(sort_arity)
{
    // Nothing here
}

DeclareSortCommand::~DeclareSortCommand()
{
    // Nothing here
}

void DeclareSortCommand::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_declare_sort_command(this);
}

ASTBaseSPtr DeclareSortCommand::clone() const
{
    return new DeclareSortCommand(location, sort_name, sort_arity);
}

const string& DeclareSortCommand::get_sort_name() const
{
    return sort_name;
}

u32 DeclareSortCommand::get_sort_arity() const
{
    return sort_arity;
}

// Implementation of DefineFunCommand
DefineFunCommand::DefineFunCommand(const SourceLocation& location,
                                   const string& function_symbol,
                                   const vector<SortedSymbolSPtr>& function_parameters,
                                   SortExprSPtr function_range_sort,
                                   TermSPtr function_body)
    : Command(location), function_symbol(function_symbol),
      function_parameters(function_parameters), function_range_sort(function_range_sort),
      function_body(function_body)
{
    copy_vector(function_parameters, const_function_parameters);
}

DefineFunCommand::~DefineFunCommand()
{
    // Nothing here
}

void DefineFunCommand::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_define_fun_command(this);
}

ASTBaseSPtr DefineFunCommand::clone() const
{
    vector<SortedSymbolSPtr> cloned_params;
    clone_vector(function_parameters, cloned_params);
    return new DefineFunCommand(location, function_symbol,cloned_params,
                                function_range_sort->clone()->static_as<SortExpr>(),
                                function_body->clone()->static_as<Term>());
}

const string& DefineFunCommand::get_function_symbol() const
{
    return function_symbol;
}

const vector<SortedSymbolCSPtr>& DefineFunCommand::get_function_parameters() const
{
    return const_function_parameters;
}

SortExprCSPtr DefineFunCommand::get_function_range_sort() const
{
    return function_range_sort;
}

TermCSPtr DefineFunCommand::get_function_body() const
{
    return function_body;
}

// Implementation of DefineSortCommand
DefineSortCommand::DefineSortCommand(const SourceLocation& location,
                                     const string& sort_name,
                                     const vector<string>& sort_parameters,
                                     SortExprSPtr sort_expr)
    : Command(location), sort_name(sort_name), sort_parameters(sort_parameters),
      sort_expr(sort_expr)
{
    // Nothing here
}

DefineSortCommand::~DefineSortCommand()
{
    // Nothing here
}

void DefineSortCommand::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_define_sort_command(this);
}

ASTBaseSPtr DefineSortCommand::clone() const
{
    return new DefineSortCommand(location, sort_name, sort_parameters,
                                 sort_expr->clone()->static_as<SortExpr>());
}

const string& DefineSortCommand::get_sort_name() const
{
    return sort_name;
}

SortExprCSPtr DefineSortCommand::get_sort_expr() const
{
    return sort_expr;
}

const vector<string>& DefineSortCommand::get_sort_parameters() const
{
    return sort_parameters;
}

// Implementation of DeclareDatatypesCommand
DeclareDatatypesCommand::DeclareDatatypesCommand(const SourceLocation& location,
                                                 const vector<SortNameAndAritySPtr>& sort_names_and_arities,
                                                 const vector<DatatypeConstructorListSPtr>& constructor_lists)
    : Command(location), sort_names_and_arities(sort_names_and_arities),
      datatype_constructor_lists(constructor_lists)
{
    copy_vector(sort_names_and_arities, const_sort_names_and_arities);
    copy_vector(datatype_constructor_lists, const_datatype_constructor_lists);
}

DeclareDatatypesCommand::~DeclareDatatypesCommand()
{
    // Nothing here
}

void DeclareDatatypesCommand::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_declare_datatypes_command(this);
}

ASTBaseSPtr DeclareDatatypesCommand::clone() const
{
    vector<SortNameAndAritySPtr> cloned_sort_names_and_arities;
    vector<DatatypeConstructorListSPtr> cloned_constructors;

    clone_vector(sort_names_and_arities, cloned_sort_names_and_arities);
    clone_vector(datatype_constructor_lists, cloned_constructors);

    return new DeclareDatatypesCommand(location, cloned_sort_names_and_arities,
                                       cloned_constructors);
}

const vector<SortNameAndArityCSPtr>& DeclareDatatypesCommand::get_sort_names_and_arities() const
{
    return const_sort_names_and_arities;
}

const vector<DatatypeConstructorListCSPtr>& DeclareDatatypesCommand::get_datatype_constructor_lists() const
{
    return const_datatype_constructor_lists;
}

// Implementation of DeclareDatatypeCommand
DeclareDatatypeCommand::DeclareDatatypeCommand(const SourceLocation& location,
                                               const string& datatype_name,
                                               DatatypeConstructorListSPtr constructor_list)
    : Command(location), datatype_name(datatype_name),
      datatype_constructor_list(constructor_list)
{
    // Nothing here
}

DeclareDatatypeCommand::~DeclareDatatypeCommand()
{
    // Nothing here
}

void DeclareDatatypeCommand::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_declare_datatype_command(this);
}

ASTBaseSPtr DeclareDatatypeCommand::clone() const
{
    return new DeclareDatatypeCommand(location, datatype_name,
                                      datatype_constructor_list->clone()->static_as<DatatypeConstructorList>());
}

DatatypeConstructorListCSPtr DeclareDatatypeCommand::get_datatype_constructor_list() const
{
    return datatype_constructor_list;
}

// Implementation of SetLogicCommand
SetLogicCommand::SetLogicCommand(const SourceLocation& location, const string& logic_name)
    : Command(location), logic_name(logic_name)
{
    // Nothing here
}

SetLogicCommand::~SetLogicCommand()
{
    // Nothing here
}

void SetLogicCommand::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_set_logic_command(this);
}

ASTBaseSPtr SetLogicCommand::clone() const
{
    return new SetLogicCommand(location, logic_name);
}

const string& SetLogicCommand::get_logic_name() const
{
    return logic_name;
}

// Implementation of SetOptionCommand
SetOptionCommand::SetOptionCommand(const SourceLocation& location,
                                   const string& option_name,
                                   LiteralSPtr option_value)
    : Command(location), option_name(option_name), option_value(option_value)
{
    // Nothing here
}

SetOptionCommand::~SetOptionCommand()
{
    delete option_value;
}

void SetOptionCommand::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_set_option_command(this);
}

ASTBaseSPtr SetOptionCommand::clone() const
{
    return new SetOptionCommand(location, option_name,
                                option_value->clone()->static_as<Literal>());
}

const string& SetOptionCommand::get_option_name() const
{
    return option_name;
}

LiteralCSPtr SetOptionCommand::get_option_value() const
{
    return option_value;
}

// Implementation of GrammarTerm
GrammarTerm::GrammarTerm(const SourceLocation& location)
    : Term(location)
{
    // Nothing here
}

GrammarTerm::~GrammarTerm()
{
    // Nothing here
}

// Implementation of ConstantGrammarTerm
ConstantGrammarTerm::ConstantGrammarTerm(const SourceLocation& location,
                                         SortExprSPtr sort_expr)
    : GrammarTerm(location), sort_expr(sort_expr)
{
    // Nothing here
}

ConstantGrammarTerm::~ConstantGrammarTerm()
{
    // Nothing here
}

void ConstantGrammarTerm::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_constant_grammar_term(this);
}

ASTBaseSPtr ConstantGrammarTerm::clone() const
{
    return new ConstantGrammarTerm(location, sort_expr->clone()->static_as<SortExpr>());
}

SortExprCSPtr ConstantGrammarTerm::get_sort_expr() const
{
    return sort_expr;
}


// Implementation of VariableGrammarTerm
VariableGrammarTerm::VariableGrammarTerm(const SourceLocation& location,
                                         SortExprSPtr sort_expr)
    : GrammarTerm(location), sort_expr(sort_expr)
{
    // Nothing here
}

VariableGrammarTerm::~VariableGrammarTerm()
{
    // Nothing here
}

void VariableGrammarTerm::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_variable_grammar_term(this);
}

ASTBaseSPtr VariableGrammarTerm::clone() const
{
    return new VariableGrammarTerm(location, sort_expr->clone()->static_as<SortExpr>());
}

SortExprCSPtr VariableGrammarTerm::get_sort_expr() const
{
    return sort_expr;
}

// Implementation of BinderFreeGrammarTerm
BinderFreeGrammarTerm::BinderFreeGrammarTerm(const SourceLocation& location,
                                             TermSPtr binder_free_term)
    : GrammarTerm(location), binder_free_term(binder_free_term)
{
    // Nothing here
}

BinderFreeGrammarTerm::~BinderFreeGrammarTerm()
{
    // Nothing here
}

void BinderFreeGrammarTerm::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_binder_free_grammar_term(this);
}

ASTBaseSPtr BinderFreeGrammarTerm::clone() const
{
    return new BinderFreeGrammarTerm(location, binder_free_term->clone()->static_as<Term>());
}

TermCSPtr BinderFreeGrammarTerm::get_binder_free_term() const
{
    return binder_free_term;
}

// Implementation of GroupedRuleList
GroupedRuleList::GroupedRuleList(const SourceLocation& location,
                                 const string& head_symbol,
                                 SortExprSPtr head_symbol_sort,
                                 const vector<GrammarTermSPtr>& expansion_rules)
    : ASTBase(location), head_symbol(head_symbol), head_symbol_sort(head_symbol_sort),
      expansion_rules(expansion_rules)
{
    copy_vector(expansion_rules, const_expansion_rules);
}

GroupedRuleList::~GroupedRuleList()
{
    // Nothing here
}

void GroupedRuleList::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_grouped_rule_list(this);
}

ASTBaseSPtr GroupedRuleList::clone() const
{
    vector<GrammarTermSPtr> cloned_expansion_rules;
    clone_vector(expansion_rules, cloned_expansion_rules);
    return new GroupedRuleList(location, head_symbol,
                               head_symbol_sort->clone()->static_as<SortExpr>(),
                               cloned_expansion_rules);
}

const string& GroupedRuleList::get_head_symbol() const
{
    return head_symbol;
}

SortExprCSPtr GroupedRuleList::get_head_symbol_sort() const
{
    return head_symbol_sort;
}

const vector<GrammarTermCSPtr>& GroupedRuleList::get_expansion_rules() const
{
    return const_expansion_rules;
}


// Implementation of Grammar
Grammar::Grammar(const SourceLocation& location,
                 const vector<SortedSymbolSPtr>& grammar_nonterminals,
                 const vector<GroupedRuleListSPtr>& grouped_rule_lists)
    : ASTBase(location), grammar_nonterminals(grammar_nonterminals)
{
    copy_vector(grammar_nonterminals, const_grammar_nonterminals);

    for(auto const& rule_list : grouped_rule_lists) {
        const string& head_symbol = rule_list->get_head_symbol();
        if (this->grouped_rule_lists.find(head_symbol) != this->grouped_rule_lists.end()) {
            ostringstream sstr;
            sstr << "Head Symbol \"" + head_symbol + "\" is associated with more than one "
                 << "rule list. At location: " << location.to_string() << endl;
            throw Sygus2ParserException(sstr.str());
        }
        this->grouped_rule_lists[head_symbol] = rule_list;
        this->const_grouped_rule_lists[head_symbol] = rule_list;
    }
}

Grammar::~Grammar()
{
    // Nothing here
}

void Grammar::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_grammar(this);
}

ASTBaseSPtr Grammar::clone() const
{
    vector<SortedSymbolSPtr> cloned_nonterminals;
    vector<GroupedRuleListSPtr> cloned_rule_lists;

    clone_vector(grammar_nonterminals, cloned_nonterminals);
    for(auto it = grouped_rule_lists.begin(); it != grouped_rule_lists.end(); ++it) {
        cloned_rule_lists.push_back(it->second->clone()->static_as<GroupedRuleList>());
    }

    return new Grammar(location, cloned_nonterminals, cloned_rule_lists);
}

const vector<SortedSymbolCSPtr>& Grammar::get_nonterminals() const
{
    return const_grammar_nonterminals;
}

const unordered_map<string, GroupedRuleListCSPtr>& Grammar::get_grouped_rule_lists() const
{
    return const_grouped_rule_lists;
}

SymbolTableScopeSPtr Grammar::get_symbol_table_scope() const
{
    return symbol_table_scope;
}

void Grammar::set_symbol_table_scope(SymbolTableScopeSPtr scope) const
{
    symbol_table_scope = scope;
}

bool Grammar::push_symbol_table_scope(SymbolTableSPtr symbol_table) const
{
    if (symbol_table_scope.is_null()) {
        return false;
    }

    symbol_table->push_scope(symbol_table_scope);
    return true;
}

// Implementation of Program
Program::Program(const SourceLocation& location,
                 const vector<CommandSPtr>& commands)
    : ASTBase(location), program_commands(commands)
{
    copy_vector(program_commands, const_program_commands);
}

Program::~Program()
{
    // Nothing here
}

void Program::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_program(this);
}

ASTBaseSPtr Program::clone() const
{
    vector<CommandSPtr> cloned_commands;
    clone_vector(program_commands, cloned_commands);
    return new Program(location, cloned_commands);
}

const vector<CommandCSPtr>& Program::get_commands() const
{
    return const_program_commands;
}

// Implementation of Sygus2Parser
static inline void do_parse()
{
    if(yyparse() != 0) {
        fclose(yyin);
        throw Sygus2ParserException("Error parsing input file.");
    }
}

ProgramSPtr Sygus2Parser::parse(const string& file_name)
{
    Sygus2Bison::the_program = nullptr;

    yyin = fopen(file_name.c_str(), "r");
    if (yyin == NULL) {
        throw Sygus2ParserException("Could not open input file \"" + file_name + "\"");
    }
    do_parse();
    fclose(yyin);
    return Sygus2Bison::the_program;
}

ProgramSPtr Sygus2Parser::parse(istream& input_stream)
{
    Sygus2Bison::the_program = nullptr;
    ostringstream contents;
    contents << input_stream.rdbuf();
    return parse(contents.str());
}

ProgramSPtr Sygus2Parser::parse(FILE* handle)
{
    Sygus2Bison::the_program = nullptr;
    yyin = handle;
    do_parse();
    return Sygus2Bison::the_program;
}

ProgramSPtr Sygus2Parser::parse_string(const string& input_string)
{
    Sygus2Bison::the_program = nullptr;
    auto buffer_handle = yy_scan_string(const_cast<char*>(input_string.c_str()));
    if(yyparse() != 0) {
        yy_delete_buffer(buffer_handle);
        throw Sygus2ParserException("Error parsing string input.");
    }
    yy_delete_buffer(buffer_handle);
    return Sygus2Bison::the_program;
}

ProgramSPtr Sygus2Parser::parse(char* buffer)
{
    Sygus2Bison::the_program = nullptr;
    auto buffer_handle = yy_scan_string(buffer);
    if(yyparse() != 0) {
        yy_delete_buffer(buffer_handle);
        throw Sygus2ParserException("Error parsing input buffer");
    }
    yy_delete_buffer(buffer_handle);
    return Sygus2Bison::the_program;
}

// Implementation of ASTVisitorBase
ASTVisitorBase::ASTVisitorBase(const string& name)
    : name(name)
{
    // Nothing here
}

ASTVisitorBase::~ASTVisitorBase()
{
    // Nothing here
}

const string& ASTVisitorBase::get_name() const
{
    return name;
}

void ASTVisitorBase::visit_index(const Index* index)
{
    // Nothing here
}

void ASTVisitorBase::visit_identifier(const Identifier* identifier)
{
    for (auto const& index : identifier->get_indices()) {
        index->accept(this);
    }
}

void ASTVisitorBase::visit_sort_expr(const SortExpr* sort_expr)
{
    sort_expr->get_identifier()->accept(this);
    for(auto const& param_sort : sort_expr->get_param_sorts()) {
        param_sort->accept(this);
    }
}

void ASTVisitorBase::visit_sort_name_and_arity(const SortNameAndArity* sort_name_and_arity)
{
    // Nothing here
}

void ASTVisitorBase::visit_datatype_constructor(const DatatypeConstructor* datatype_constructor)
{
    for(auto const& constructor_parameter : datatype_constructor->get_constructor_parameters()) {
        constructor_parameter->accept(this);
    }
}

void ASTVisitorBase::visit_datatype_constructor_list(const DatatypeConstructorList* datatype_constructor_list)
{
    for(auto const& datatype_constructor : datatype_constructor_list->get_datatype_constructors()) {
        datatype_constructor->accept(this);
    }
}

void ASTVisitorBase::visit_literal(const Literal* literal)
{
    // Nothing here
}

void ASTVisitorBase::visit_literal_term(const LiteralTerm* literal_term)
{
    literal_term->get_literal()->accept(this);
}

void ASTVisitorBase::visit_identifier_term(const IdentifierTerm* identifier_term)
{
    identifier_term->get_identifier()->accept(this);
}

void ASTVisitorBase::visit_function_application_term(const FunctionApplicationTerm* function_application_term)
{
    function_application_term->get_identifier()->accept(this);
    for(auto const& arg_term : function_application_term->get_application_arguments()) {
        arg_term->accept(this);
    }
}

void ASTVisitorBase::visit_sorted_symbol(const SortedSymbol* sorted_symbol)
{
    sorted_symbol->get_sort_expr()->accept(this);
}

void ASTVisitorBase::visit_quantified_term(const QuantifiedTerm* quantified_term)
{
    for(auto const& quantified_symbol : quantified_term->get_quantified_symbols()) {
        quantified_symbol->accept(this);
    }

    quantified_term->get_quantified_term()->accept(this);
}

void ASTVisitorBase::visit_variable_binding(const VariableBinding* variable_binding)
{
    variable_binding->get_binding()->accept(this);
}

void ASTVisitorBase::visit_let_term(const LetTerm* let_term)
{
    for(auto const& binding : let_term->get_bindings()) {
        binding->accept(this);
    }

    let_term->get_let_body()->accept(this);
}

void ASTVisitorBase::visit_check_synth_command(const CheckSynthCommand* check_synth_command)
{
    // Nothing here
}

void ASTVisitorBase::visit_constraint_command(const ConstraintCommand* constraint_command)
{
    constraint_command->get_constraint_term()->accept(this);
}

void ASTVisitorBase::visit_declare_var_command(const DeclareVarCommand* declare_var_command)
{
    declare_var_command->get_sort_expr()->accept(this);
}

void ASTVisitorBase::visit_inv_constraint_command(const InvConstraintCommand* inv_constraint_command)
{
    // Nothing here
}

void ASTVisitorBase::visit_set_feature_command(const SetFeatureCommand* set_feature_command)
{
    // Nothing here
}

void ASTVisitorBase::visit_synth_fun_command(const SynthFunCommand* synth_fun_command)
{
    for(auto const& param : synth_fun_command->get_function_parameters()) {
        param->accept(this);
    }

    synth_fun_command->get_function_range_sort()->accept(this);

    auto grammar = synth_fun_command->get_synthesis_grammar();
    if (grammar != nullptr) {
        synth_fun_command->get_synthesis_grammar()->accept(this);
    }
}

void ASTVisitorBase::visit_synth_inv_command(const SynthInvCommand* synth_inv_command)
{
    for(auto const& param : synth_inv_command->get_function_parameters()) {
        param->accept(this);
    }

    auto grammar = synth_inv_command->get_synthesis_grammar();
    if (grammar != nullptr) {
        synth_inv_command->get_synthesis_grammar()->accept(this);
    }
}

void ASTVisitorBase::visit_declare_sort_command(const DeclareSortCommand* declare_sort_command)
{
    // Nothing here
}

void ASTVisitorBase::visit_define_fun_command(const DefineFunCommand* define_fun_command)
{
    for(auto const& param : define_fun_command->get_function_parameters()) {
        param->accept(this);
    }
    define_fun_command->get_function_range_sort()->accept(this);
    define_fun_command->get_function_body()->accept(this);
}

void ASTVisitorBase::visit_define_sort_command(const DefineSortCommand* define_sort_command)
{
    define_sort_command->get_sort_expr()->accept(this);
}

void ASTVisitorBase::visit_declare_datatypes_command(const DeclareDatatypesCommand* declare_datatypes_command)
{
    for(auto const& sort_name_and_arity : declare_datatypes_command->get_sort_names_and_arities()) {
        sort_name_and_arity->accept(this);
    }

    for(auto const& datatype_constructor_list : declare_datatypes_command->get_datatype_constructor_lists()) {
        datatype_constructor_list->accept(this);
    }
}

void ASTVisitorBase::visit_declare_datatype_command(const DeclareDatatypeCommand* declare_datatype_command)
{
    declare_datatype_command->get_datatype_constructor_list()->accept(this);
}

void ASTVisitorBase::visit_set_logic_command(const SetLogicCommand* set_logic_command)
{
    // Nothing here
}

void ASTVisitorBase::visit_set_option_command(const SetOptionCommand* set_option_command)
{
    set_option_command->get_option_value()->accept(this);
}

void ASTVisitorBase::visit_constant_grammar_term(const ConstantGrammarTerm* constant_grammar_term)
{
    constant_grammar_term->get_sort_expr()->accept(this);
}

void ASTVisitorBase::visit_variable_grammar_term(const VariableGrammarTerm* variable_grammar_term)
{
    variable_grammar_term->get_sort_expr()->accept(this);
}

void ASTVisitorBase::visit_binder_free_grammar_term(const BinderFreeGrammarTerm* binder_free_term)
{
    binder_free_term->get_binder_free_term()->accept(this);
}

void ASTVisitorBase::visit_grouped_rule_list(const GroupedRuleList* grouped_rule_list)
{
    grouped_rule_list->get_head_symbol_sort()->accept(this);
    for (auto const& expansion : grouped_rule_list->get_expansion_rules()) {
        expansion->accept(this);
    }
}

void ASTVisitorBase::visit_grammar(const Grammar* grammar)
{
    for(auto const& nonterminal : grammar->get_nonterminals()) {
        nonterminal->accept(this);
    }

    auto const start = grammar->get_grouped_rule_lists().begin();
    auto const end = grammar->get_grouped_rule_lists().end();

    for(auto it = start; it != end; ++it) {
        it->second->accept(this);
    }
}

void ASTVisitorBase::visit_program(const Program* program)
{
    for(auto const& command : program->get_commands()) {
        command->accept(this);
    }
}

} /* end namespace */
