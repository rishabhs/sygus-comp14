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

#include "include/Sygus2ParserIFace.hpp"
#include "include/Sygus2ParserExceptions.hpp"
 // #include "include/SymbolTable.hpp"
 // #include "include/LogicSymbols.hpp"
 // #include "include/SymtabBuilder.hpp"
#include <algorithm>
#include <boost/functional/hash.hpp>
#include <boost/algorithm/string/split.hpp>
#include <boost/algorithm/string/classification.hpp>

namespace Sygus2Bison {
extern Sygus2Parser::Program* the_program;
extern string* file_name;
}

extern FILE* yyin;
extern int yyparse();

namespace Sygus2Parser {

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

bool SourceLocation::operator == (const SourceLocation& other) const
{
    if (&other == this) {
        return true;
    }

    return line == other.line && column == other.column;
}

bool SourceLocation::operator != (const SourceLocation& other) const
{
    return !(*this == other);
}

i64 SourceLocation::get_hash_code() const
{
    return (((i64)line * 317) ^ column);
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

bool Index::operator == (const Index& other) const
{
    if (&other == this) {
        return true;
    }

    if (is_symbolic != other.is_symbolic) {
        return false;
    }

    return is_symbolic ? symbol == other.symbol : numeral == other.numeral;
}

bool Index::operator != (const Index& other) const
{
    return !(*this == other);
}

i64 Index::get_hash_code() const
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

ASTBase* Index::clone() const
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

// Implementation of Identifier
Identifier::Identifier(const SourceLocation& location, const string& symbol)
    : ASTBase(location), symbol(symbol)
{
    // Nothing here
}

Identifier::Identifier(const SourceLocation& location, const string& symbol, const vector<Index*>& indices)
    : ASTBase(location), symbol(symbol), indices(indices)
{
    const_indices.insert(const_indices.end(), indices.begin(), indices.end());
}

Identifier::~Identifier()
{
    for(auto const& index : indices) {
        delete index;
    }
}

bool Identifier::operator == (const Identifier& other) const
{
    if (&other == this) {
        return true;
    }

    if (symbol != other.symbol) {
        return false;
    }

    if (indices.size() != other.indices.size()) {
        return false;
    }

    for(size_t i = 0; i < indices.size(); ++i) {
        if (*indices[i] != *other.indices[i]) {
            return false;
        }
    }

    return true;
}

bool Identifier::operator != (const Identifier& other) const
{
    return !(*this == other);
}

i64 Identifier::get_hash_code() const
{
    std::hash<string> string_hasher;
    auto hash = string_hasher(symbol);

    for(auto const& index : indices) {
        hash = (hash * 317) ^ index->get_hash_code();
    }
    return hash;
}

void Identifier::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_identifier(this);
}

ASTBase* Identifier::clone() const
{
    vector<Index*> cloned_indices;

    for(auto const& index : indices) {
        cloned_indices.push_back(static_cast<Index*>(index->clone()));
    }

    return new Identifier(location, symbol, cloned_indices);
}

const string& Identifier::get_symbol() const
{
    return symbol;
}

const vector<const Index*> Identifier::get_indices() const
{
    return const_indices;
}


// Implementation of SortExpr
SortExpr::SortExpr(const SourceLocation& location, Identifier* identifier)
    : ASTBase(location), identifier(identifier)
{
    // Nothing here
}

SortExpr::SortExpr(const SourceLocation& location, Identifier* identifier,
                   const vector<SortExpr*>& param_sorts)
    : ASTBase(location), identifier(identifier), param_sorts(param_sorts)
{
    const_param_sorts.insert(const_param_sorts.end(),
                             param_sorts.begin(), param_sorts.end());
}

SortExpr::~SortExpr()
{
    // Nothing here
}

bool SortExpr::operator == (const SortExpr& other) const
{
    if (&other == this) {
        return true;
    }

    if(*identifier != *(other.identifier)) {
        return false;
    }

    if (param_sorts.size() != other.param_sorts.size()) {
        return false;
    }

    for(size_t i = 0; i < param_sorts.size(); ++i) {
        if (*(param_sorts[i]) != *(other.param_sorts[i])) {
            return false;
        }
    }

    return true;
}

bool SortExpr::operator != (const SortExpr& other) const
{
    return !(*this == other);
}

void SortExpr::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_sort_expr(this);
}

ASTBase* SortExpr::clone() const
{
    vector<SortExpr*> cloned_params;

    for(auto const& param : param_sorts) {
        cloned_params.push_back(static_cast<SortExpr*>(param->clone()));
    }

    return new SortExpr(location, static_cast<Identifier*>(identifier->clone()), cloned_params);
}

const Identifier* SortExpr::get_identifier() const
{
    return identifier;
}

const vector<const SortExpr*>& SortExpr::get_param_sorts() const
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

ASTBase* SortNameAndArity::clone() const
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
                                         const vector<SortedSymbol*>& constructor_parameters)
    : ASTBase(location), constructor_name(constructor_name),
      constructor_parameters(constructor_parameters)
{
    const_constructor_parameters.insert(const_constructor_parameters.end(),
                                        constructor_parameters.begin(),
                                        constructor_parameters.end());
}

DatatypeConstructor::~DatatypeConstructor()
{
    for(auto const& param : constructor_parameters) {
        delete param;
    }
}

void DatatypeConstructor::accept(ASTVisitorBase* visitor) const
{
    return visitor->visit_datatype_constructor(this);
}

ASTBase* DatatypeConstructor::clone() const
{
    vector<SortedSymbol*> cloned_params;
    for(auto const& param : constructor_parameters) {
        cloned_params.push_back(static_cast<SortedSymbol*>(param->clone()));
    }
    return new DatatypeConstructor(location, constructor_name, cloned_params);
}

const string& DatatypeConstructor::get_constructor_name() const
{
    return constructor_name;
}

const vector<const SortedSymbol*>& DatatypeConstructor::get_constructor_parameters() const
{
    return const_constructor_parameters;
}

// Implementation of DatatypeConstructorList
DatatypeConstructorList::DatatypeConstructorList(const SourceLocation& location,
                                                 const vector<string>& sort_parameter_names,
                                                 const vector<DatatypeConstructor*>& datatype_constructors)
    : ASTBase(location), sort_parameter_names(sort_parameter_names),
      datatype_constructors(datatype_constructors)
{
    const_datatype_constructors.insert(const_datatype_constructors.end(),
                                       datatype_constructors.begin(),
                                       datatype_constructors.end());
}

DatatypeConstructorList::~DatatypeConstructorList()
{
    for(auto const& constructor : datatype_constructors) {
        delete constructor;
    }
}

void DatatypeConstructorList::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_datatype_constructor_list(this);
}

ASTBase* DatatypeConstructorList::clone() const
{
    vector<DatatypeConstructor*> cloned_constructors;
    for(auto const& constructor : datatype_constructors) {
        cloned_constructors.push_back(static_cast<DatatypeConstructor*>(constructor->clone()));
    }

    return new DatatypeConstructorList(location, sort_parameter_names, cloned_constructors);
}

const vector<string>& DatatypeConstructorList::get_sort_parameter_names() const
{
    return sort_parameter_names;
}

const vector<const DatatypeConstructor*>& DatatypeConstructorList::get_datatype_constructors() const
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

ASTBase* Literal::clone() const
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

const SortExpr* Term::get_sort() const
{
    return sort;
}

void Term::set_sort(SortExpr* sort) const
{
    this->sort = sort;
}

IdentifierTerm::IdentifierTerm(const SourceLocation& location, Identifier* identifier)
    : Term(location), identifier(identifier)
{
    // Nothing here
}

IdentifierTerm::~IdentifierTerm()
{
    delete identifier;
}

void IdentifierTerm::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_identifier_term(this);
}

ASTBase* IdentifierTerm::clone() const
{
    return new IdentifierTerm(location, static_cast<Identifier*>(identifier->clone()));
}

const Identifier* IdentifierTerm::get_identifier() const
{
    return identifier;
}

// Implementation of LiteralTerm
LiteralTerm::LiteralTerm(const SourceLocation& location, Literal* literal)
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

ASTBase* LiteralTerm::clone() const
{
    return new LiteralTerm(location, static_cast<Literal*>(literal->clone()));
}

const Literal* LiteralTerm::get_literal() const
{
    return literal;
}

// Implementation of FunctionApplicationTerm
FunctionApplicationTerm::FunctionApplicationTerm(const SourceLocation& location,
                                                 Identifier* identifier,
                                                 const vector<Term*>& application_arguments)
    : Term(location), identifier(identifier), application_arguments(application_arguments)
{
    const_application_arguments.insert(const_application_arguments.end(),
                                       application_arguments.begin(),
                                       application_arguments.end());
}

FunctionApplicationTerm::~FunctionApplicationTerm()
{
    for(auto const& arg : application_arguments) {
        delete arg;
    }
}

void FunctionApplicationTerm::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_function_application_term(this);
}

ASTBase* FunctionApplicationTerm::clone() const
{
    vector<Term*> cloned_args;
    for(auto const& arg : application_arguments) {
        cloned_args.push_back(static_cast<Term*>(arg->clone()));
    }

    return new FunctionApplicationTerm(location, static_cast<Identifier*>(identifier->clone()),
                                       cloned_args);
}

const Identifier* FunctionApplicationTerm::get_identifier() const
{
    return identifier;
}

const vector<const Term*>& FunctionApplicationTerm::get_application_arguments() const
{
    return const_application_arguments;
}

// Implementation of QuantifiedTerm
QuantifiedTerm::QuantifiedTerm(const SourceLocation& location,
                               QuantifierKind quantifier_kind,
                               const vector<SortedSymbol*> quantified_symbols,
                               Term* quantified_term)
    : Term(location), quantifier_kind(quantifier_kind),
      quantified_symbols(quantified_symbols), quantified_term(quantified_term)
{
    const_quantified_symbols.insert(const_quantified_symbols.end(),
                                    quantified_symbols.begin(),
                                    quantified_symbols.end());
}

QuantifiedTerm::~QuantifiedTerm()
{
    for(auto const& sorted_sym : quantified_symbols) {
        delete sorted_sym;
    }

    delete quantified_term;
}

void QuantifiedTerm::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_quantified_term(this);
}

ASTBase* QuantifiedTerm::clone() const
{
    vector<SortedSymbol*> cloned_quantified_symbols;
    for(auto const& sorted_sym : quantified_symbols) {
        cloned_quantified_symbols.push_back(static_cast<SortedSymbol*>(sorted_sym->clone()));
    }

    return new QuantifiedTerm(location, quantifier_kind, cloned_quantified_symbols,
                              static_cast<Term*>(quantified_term->clone()));
}

QuantifierKind QuantifiedTerm::get_quantifier_kind() const
{
    return quantifier_kind;
}

const vector<const SortedSymbol*>& QuantifiedTerm::get_quantified_symbols() const
{
    return const_quantified_symbols;
}

const Term* QuantifiedTerm::get_quantified_term() const
{
    return quantified_term;
}

// Implementation of VariableBinding
VariableBinding::VariableBinding(const SourceLocation& location,
                                 const string& symbol, Term* binding)
    : ASTBase(location), symbol(symbol), binding(binding)
{
    // Nothing here
}

VariableBinding::~VariableBinding()
{
    delete binding;
}

void VariableBinding::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_variable_binding(this);
}

ASTBase* VariableBinding::clone() const
{
    return new VariableBinding(location, symbol, static_cast<Term*>(binding->clone()));
}

const string& VariableBinding::get_symbol() const
{
    return symbol;
}

const Term* VariableBinding::get_binding() const
{
    return binding;
}

// Implementation of LetTerm
LetTerm::LetTerm(const SourceLocation& location,
                 const vector<VariableBinding*>& bindings,
                 Term* let_body)
    : Term(location), bindings(bindings), let_body(let_body)
{
    const_bindings.insert(const_bindings.end(), bindings.begin(), bindings.end());
}

LetTerm::~LetTerm()
{
    for(auto const& binding : bindings) {
        delete binding;
    }

    delete let_body;
}

void LetTerm::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_let_term(this);
}

ASTBase* LetTerm::clone() const
{
    vector<VariableBinding*> cloned_bindings;
    for(auto const& binding : bindings) {
        cloned_bindings.push_back(static_cast<VariableBinding*>(binding->clone()));
    }

    return new LetTerm(location, cloned_bindings, static_cast<Term*>(let_body->clone()));
}

const vector<const VariableBinding*>& LetTerm::get_bindings() const
{
    return const_bindings;
}

const Term* LetTerm::get_let_body() const
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

ASTBase* CheckSynthCommand::clone() const
{
    return new CheckSynthCommand(location);
}

// Implementation of ConstraintCommand
ConstraintCommand::ConstraintCommand(const SourceLocation& location,
                                     Term* constraint_term)
    : Command(location), constraint_term(constraint_term)
{
    // Nothing here
}

ConstraintCommand::~ConstraintCommand()
{
    delete constraint_term;
}

void ConstraintCommand::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_constraint_command(this);
}

ASTBase* ConstraintCommand::clone() const
{
    return new ConstraintCommand(location, static_cast<Term*>(constraint_term->clone()));
}

const Term* ConstraintCommand::get_constraint_term() const
{
    return constraint_term;
}

// Implementation of DeclareVarCommand
DeclareVarCommand::DeclareVarCommand(const SourceLocation& location, const string& symbol,
                                     SortExpr* sort_expr)
    : Command(location), symbol(symbol), sort_expr(sort_expr)
{
    // Nothing here
}

DeclareVarCommand::~DeclareVarCommand()
{
    delete sort_expr;
}

void DeclareVarCommand::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_declare_var_command(this);
}

ASTBase* DeclareVarCommand::clone() const
{
    return new DeclareVarCommand(location, symbol, static_cast<SortExpr*>(sort_expr->clone()));
}

const string& DeclareVarCommand::get_symbol() const
{
    return symbol;
}

const SortExpr* DeclareVarCommand::get_sort_expr() const
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

ASTBase* InvConstraintCommand::clone() const
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

ASTBase* SetFeatureCommand::clone() const
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
                                 const vector<SortedSymbol*>& function_parameters,
                                 SortExpr* function_range_sort,
                                 Grammar* synthesis_grammar)
    : Command(location), function_symbol(function_symbol),
      function_parameters(function_parameters), function_range_sort(function_range_sort),
      synthesis_grammar(synthesis_grammar)
{
    const_function_parameters.insert(const_function_parameters.end(),
                                     function_parameters.begin(),
                                     function_parameters.end());
}

SynthFunCommand::~SynthFunCommand()
{
    for(auto const& param : function_parameters) {
        delete param;
    }
    delete function_range_sort;
    delete synthesis_grammar;
}

void SynthFunCommand::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_synth_fun_command(this);
}

ASTBase* SynthFunCommand::clone() const
{
    vector<SortedSymbol*> cloned_params;
    for(auto const& param : function_parameters) {
        cloned_params.push_back(static_cast<SortedSymbol*>(param->clone()));
    }

    return new SynthFunCommand(location, function_symbol, cloned_params,
                               static_cast<SortExpr*>(function_range_sort->clone()),
                               static_cast<Grammar*>(synthesis_grammar->clone()));
}

const string& SynthFunCommand::get_function_symbol() const
{
    return function_symbol;
}

const vector<const SortedSymbol*>& SynthFunCommand::get_function_parameters() const
{
    return const_function_parameters;
}

const SortExpr* SynthFunCommand::get_function_range_sort() const
{
    return function_range_sort;
}

const Grammar* SynthFunCommand::get_synthesis_grammar() const
{
    return synthesis_grammar;
}

// Implementation of SynthInvCommand
SynthInvCommand::SynthInvCommand(const SourceLocation& location,
                                 const string& function_symbol,
                                 const vector<SortedSymbol*>& function_parameters,
                                 Grammar* synthesis_grammar)
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

ASTBase* SynthInvCommand::clone() const
{
    vector<SortedSymbol*> cloned_params;

    for(auto const& param : get_function_parameters()) {
        cloned_params.push_back(static_cast<SortedSymbol*>(param->clone()));
    }

    return new SynthInvCommand(location, get_function_symbol(), cloned_params,
                               static_cast<Grammar*>(get_synthesis_grammar()->clone()));
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

ASTBase* DeclareSortCommand::clone() const
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
                                   const vector<SortedSymbol*>& function_parameters,
                                   SortExpr* function_range_sort,
                                   Term* function_body)
    : Command(location), function_symbol(function_symbol),
      function_parameters(function_parameters), function_range_sort(function_range_sort),
      function_body(function_body)
{
    const_function_parameters.insert(const_function_parameters.end(),
                                     function_parameters.begin(),
                                     function_parameters.end());
}

DefineFunCommand::~DefineFunCommand()
{
    for(auto const& param : function_parameters) {
        delete param;
    }

    delete function_body;
}

void DefineFunCommand::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_define_fun_command(this);
}

ASTBase* DefineFunCommand::clone() const
{
    vector<SortedSymbol*> cloned_params;
    for(auto const& param : function_parameters) {
        cloned_params.push_back(static_cast<SortedSymbol*>(param->clone()));
    }

    return new DefineFunCommand(location, function_symbol,cloned_params,
                                static_cast<SortExpr*>(function_range_sort->clone()),
                                static_cast<Term*>(function_body->clone()));
}

const string& DefineFunCommand::get_function_symbol() const
{
    return function_symbol;
}

const vector<const SortedSymbol*>& DefineFunCommand::get_function_parameters() const
{
    return const_function_parameters;
}

const SortExpr* DefineFunCommand::get_function_range_sort() const
{
    return function_range_sort;
}

const Term* DefineFunCommand::get_function_body() const
{
    return function_body;
}

// Implementation of DefineSortCommand
DefineSortCommand::DefineSortCommand(const SourceLocation& location,
                                     const string& sort_name,
                                     const vector<string>& sort_parameters,
                                     SortExpr* sort_expr)
    : Command(location), sort_name(sort_name), sort_parameters(sort_parameters),
      sort_expr(sort_expr)
{
    // Nothing here
}

DefineSortCommand::~DefineSortCommand()
{
    delete sort_expr;
}

void DefineSortCommand::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_define_sort_command(this);
}

ASTBase* DefineSortCommand::clone() const
{
    return new DefineSortCommand(location, sort_name, sort_parameters,
                                 static_cast<SortExpr*>(sort_expr->clone()));
}

const string& DefineSortCommand::get_sort_name() const
{
    return sort_name;
}

const SortExpr* DefineSortCommand::get_sort_expr() const
{
    return sort_expr;
}

const vector<string>& DefineSortCommand::get_sort_parameters() const
{
    return sort_parameters;
}

// Implementation of DeclareDatatypesCommand
DeclareDatatypesCommand::DeclareDatatypesCommand(const SourceLocation& location,
                                                 const vector<SortNameAndArity*>& sort_names_and_arities,
                                                 const vector<DatatypeConstructorList*>& constructor_lists)
    : Command(location), sort_names_and_arities(sort_names_and_arities),
      datatype_constructor_lists(constructor_lists)
{
    const_sort_names_and_arities.insert(const_sort_names_and_arities.end(),
                                        sort_names_and_arities.begin(),
                                        sort_names_and_arities.end());
    const_datatype_constructor_lists.insert(const_datatype_constructor_lists.end(),
                                            datatype_constructor_lists.begin(),
                                            datatype_constructor_lists.end());
}

DeclareDatatypesCommand::~DeclareDatatypesCommand()
{
    for(auto const& sort_name_and_arity : sort_names_and_arities) {
        delete sort_name_and_arity;
    }

    for(auto const& constructor_list : datatype_constructor_lists) {
        delete constructor_list;
    }
}

void DeclareDatatypesCommand::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_declare_datatypes_command(this);
}

ASTBase* DeclareDatatypesCommand::clone() const
{
    vector<SortNameAndArity*> cloned_sort_names_and_arities;
    vector<DatatypeConstructorList*> cloned_constructors;

    for(auto const& sort_name_and_arity : sort_names_and_arities) {
        cloned_sort_names_and_arities.push_back(static_cast<SortNameAndArity*>(sort_name_and_arity->clone()));
    }

    for(auto const& constructor_list : datatype_constructor_lists) {
        cloned_constructors.push_back(static_cast<DatatypeConstructorList*>(constructor_list->clone()));
    }

    return new DeclareDatatypesCommand(location, cloned_sort_names_and_arities,
                                       cloned_constructors);
}

const vector<const SortNameAndArity*>& DeclareDatatypesCommand::get_sort_names_and_arities() const
{
    return const_sort_names_and_arities;
}

const vector<const DatatypeConstructorList*>& DeclareDatatypesCommand::get_datatype_constructor_lists() const
{
    return const_datatype_constructor_lists;
}

// Implementation of DeclareDatatypeCommand
DeclareDatatypeCommand::DeclareDatatypeCommand(const SourceLocation& location,
                                               const string& datatype_name,
                                               DatatypeConstructorList* constructor_list)
    : Command(location), datatype_name(datatype_name),
      datatype_constructor_list(constructor_list)
{
    // Nothing here
}

DeclareDatatypeCommand::~DeclareDatatypeCommand()
{
    delete datatype_constructor_list;
}

void DeclareDatatypeCommand::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_declare_datatype_command(this);
}

ASTBase* DeclareDatatypeCommand::clone() const
{
    return new DeclareDatatypeCommand(location, datatype_name,
                                      static_cast<DatatypeConstructorList*>(datatype_constructor_list->clone()));
}

const DatatypeConstructorList* DeclareDatatypeCommand::get_datatype_constructor_list() const
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

ASTBase* SetLogicCommand::clone() const
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
                                   Literal* option_value)
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

ASTBase* SetOptionCommand::clone() const
{
    return new SetOptionCommand(location, option_name,
                                static_cast<Literal*>(option_value->clone()));
}

const string& SetOptionCommand::get_option_name() const
{
    return option_name;
}

const Literal* SetOptionCommand::get_option_value() const
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
                                         SortExpr* sort_expr)
    : GrammarTerm(location), sort_expr(sort_expr)
{
    // Nothing here
}

ConstantGrammarTerm::~ConstantGrammarTerm()
{
    delete sort_expr;
}

void ConstantGrammarTerm::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_constant_grammar_term(this);
}

ASTBase* ConstantGrammarTerm::clone() const
{
    return new ConstantGrammarTerm(location, static_cast<SortExpr*>(sort_expr->clone()));
}

const SortExpr* ConstantGrammarTerm::get_sort_expr() const
{
    return sort_expr;
}


// Implementation of VariableGrammarTerm
VariableGrammarTerm::VariableGrammarTerm(const SourceLocation& location,
                                         SortExpr* sort_expr)
    : GrammarTerm(location), sort_expr(sort_expr)
{
    // Nothing here
}

VariableGrammarTerm::~VariableGrammarTerm()
{
    delete sort_expr;
}

void VariableGrammarTerm::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_variable_grammar_term(this);
}

ASTBase* VariableGrammarTerm::clone() const
{
    return new VariableGrammarTerm(location, static_cast<SortExpr*>(sort_expr->clone()));
}

const SortExpr* VariableGrammarTerm::get_sort_expr() const
{
    return sort_expr;
}

// Implementation of BinderFreeGrammarTerm
BinderFreeGrammarTerm::BinderFreeGrammarTerm(const SourceLocation& location,
                                             Term* binder_free_term)
    : GrammarTerm(location), binder_free_term(binder_free_term)
{
    // Nothing here
}

BinderFreeGrammarTerm::~BinderFreeGrammarTerm()
{
    delete binder_free_term;
}

void BinderFreeGrammarTerm::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_binder_free_grammar_term(this);
}

ASTBase* BinderFreeGrammarTerm::clone() const
{
    return new BinderFreeGrammarTerm(location, static_cast<Term*>(binder_free_term->clone()));
}

const Term* BinderFreeGrammarTerm::get_binder_free_term() const
{
    return binder_free_term;
}

// Implementation of GroupedRuleList
GroupedRuleList::GroupedRuleList(const SourceLocation& location,
                                 const string& head_symbol,
                                 SortExpr* head_symbol_sort,
                                 const vector<GrammarTerm*>& expansion_rules)
    : ASTBase(location), head_symbol(head_symbol), head_symbol_sort(head_symbol_sort),
      expansion_rules(expansion_rules)
{
    const_expansion_rules.insert(const_expansion_rules.end(),
                                 expansion_rules.begin(), expansion_rules.end());
}

GroupedRuleList::~GroupedRuleList()
{
    delete head_symbol_sort;
    for(auto const& expansion_rule : expansion_rules) {
        delete expansion_rule;
    }
}

void GroupedRuleList::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_grouped_rule_list(this);
}

ASTBase* GroupedRuleList::clone() const
{
    vector<GrammarTerm*> cloned_expansion_rules;
    for(auto const& expansion_rule : expansion_rules) {
        cloned_expansion_rules.push_back(static_cast<GrammarTerm*>(expansion_rule->clone()));
    }

    return new GroupedRuleList(location, head_symbol,
                               static_cast<SortExpr*>(head_symbol_sort->clone()),
                               cloned_expansion_rules);
}

const string& GroupedRuleList::get_head_symbol() const
{
    return head_symbol;
}

const SortExpr* GroupedRuleList::get_head_symbol_sort() const
{
    return head_symbol_sort;
}

const vector<const GrammarTerm*>& GroupedRuleList::get_expansion_rules() const
{
    return const_expansion_rules;
}


// Implementation of Grammar
Grammar::Grammar(const SourceLocation& location,
                 const vector<SortedSymbol*>& grammar_nonterminals,
                 const vector<GroupedRuleList*>& grouped_rule_lists)
    : ASTBase(location), grammar_nonterminals(grammar_nonterminals)
{
    const_grammar_nonterminals.insert(const_grammar_nonterminals.end(),
                                      grammar_nonterminals.begin(),
                                      grammar_nonterminals.end());

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
    for(auto const& nonterminal : grammar_nonterminals) {
        delete nonterminal;
    }

    for(auto it = grouped_rule_lists.begin(); it != grouped_rule_lists.end(); ++it) {
        delete it->second;
    }
}

void Grammar::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_grammar(this);
}

ASTBase* Grammar::clone() const
{
    vector<SortedSymbol*> cloned_nonterminals;
    vector<GroupedRuleList*> cloned_rule_lists;

    for(auto const& nonterminal : grammar_nonterminals) {
        cloned_nonterminals.push_back(static_cast<SortedSymbol*>(nonterminal->clone()));
    }

    for(auto it = grouped_rule_lists.begin(); it != grouped_rule_lists.end(); ++it) {
        cloned_rule_lists.push_back(static_cast<GroupedRuleList*>(it->second->clone()));
    }

    return new Grammar(location, cloned_nonterminals, cloned_rule_lists);
}

const vector<const SortedSymbol*>& Grammar::get_nonterminals() const
{
    return const_grammar_nonterminals;
}

const unordered_map<string, const GroupedRuleList*>& Grammar::get_grouped_rule_lists() const
{
    return const_grouped_rule_lists;
}

// Implementation of Program
Program::Program(const SourceLocation& location,
                 const vector<Command*>& commands)
    : ASTBase(location), program_commands(commands)
{
    const_program_commands.insert(const_program_commands.end(),
                                  program_commands.begin(),
                                  program_commands.end());
}

Program::~Program()
{
    for(auto const& command : program_commands) {
        delete command;
    }
}

void Program::accept(ASTVisitorBase* visitor) const
{
    visitor->visit_program(this);
}

ASTBase* Program::clone() const
{
    vector<Command*> cloned_commands;
    for(auto const& command : program_commands) {
        cloned_commands.push_back(static_cast<Command*>(command->clone()));
    }

    return new Program(location, cloned_commands);
}

const vector<const Command*>& Program::get_commands() const
{
    return const_program_commands;
}

} /* end namespace */
