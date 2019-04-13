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

#include "include/SymbolTable.hpp"
#include "include/Sygus2ParserExceptions.hpp"

namespace Sygus2Parser {

SymbolTableKey::SymbolTableKey(const Identifier& identifier)
    : identifier(identifier)
{
    // Nothing here
}

SymbolTableKey::SymbolTableKey(const Identifier& identifier,
                               const vector<SortDescriptorCSPtr>& argument_sorts)
    : identifier(identifier), argument_sorts(argument_sorts)
{
    // Nothing here
}

SymbolTableKey::SymbolTableKey(const SymbolTableKey& other)
    : identifier(other.identifier), argument_sorts(other.argument_sorts)
{
    // Nothing here
}

SymbolTableKey::SymbolTableKey(SymbolTableKey&& other)
    : identifier(std::move(other.identifier)),
      argument_sorts(std::move(other.argument_sorts))
{
    // Nothing here
}

SymbolTableKey::~SymbolTableKey()
{
    // Nothing here
}

SymbolTableKey& SymbolTableKey::operator = (const SymbolTableKey& other)
{
    if (&other == this) {
        return *this;
    }

    identifier = other.identifier;
    argument_sorts = other.argument_sorts;
    return *this;
}

SymbolTableKey& SymbolTableKey::operator = (SymbolTableKey&& other)
{
    if (&other == this) {
        return *this;
    }

    identifier = std::move(other.identifier);
    argument_sorts = std::move(other.argument_sorts);
    return *this;
}

bool SymbolTableKey::equals_(const SymbolTableKey& other) const
{
    if (&other == this) {
        return true;
    }

    if (identifier != other.identifier) {
        return false;
    }

    if (argument_sorts.size() != other.argument_sorts.size()) {
        return false;
    }

    for(size_t i = 0; i < argument_sorts.size(); ++i) {
        if (*(argument_sorts[i]) != *(other.argument_sorts[i])) {
            return false;
        }
    }

    return true;
}

u64 SymbolTableKey::compute_hash_() const
{
    Hasher<Identifier> identifier_hasher;
    u64 result = identifier_hasher(identifier) * 317;

    for(auto const& arg_sort : argument_sorts) {
        result = (result * 101159) ^ arg_sort->get_hash();
    }

    return result;
}

string SymbolTableKey::to_string() const
{
    ostringstream sstr;
    sstr << "Key(Identifier = " << identifier.to_string();
    if (argument_sorts.size() == 0) {
        sstr << ")";
        return sstr.str();
    }

    sstr << ", ArgumentSorts = (";
    bool first = true;

    for (auto const& arg_sort : argument_sorts) {
        if (!first) {
            sstr << ", ";
        }
        first = false;
        sstr << arg_sort->to_string();
    }

    sstr << ")";
    return sstr.str();
}

const Identifier& SymbolTableKey::get_identifier() const
{
    return identifier;
}

const vector<SortDescriptorCSPtr>& SymbolTableKey::get_argument_sorts() const
{
    return argument_sorts;
}

SymbolTableEntry::SymbolTableEntry(SymbolTableEntryKind kind, const Identifier& identifier)
    : entry_kind(kind), identifier(identifier)
{
    // Nothing here
}

SymbolTableEntryKind SymbolTableEntry::get_entry_kind() const
{
    return entry_kind;
}

const Identifier& SymbolTableEntry::get_identifier() const
{
    return identifier;
}

FunctionDescriptor::FunctionDescriptor(const Identifier& identifier,
                                       const vector<SortDescriptorCSPtr>& argument_sorts,
                                       const vector<string>& argument_names,
                                       SortDescriptorCSPtr range_sort,
                                       TermCSPtr function_body,
                                       FunctionKind kind)
    : SymbolTableEntry(SymbolTableEntryKind::Function, identifier),
      kind(kind), argument_sorts(argument_sorts), argument_names(argument_names),
      range_sort(range_sort), function_body(function_body), synthesis_grammar(nullptr)
{
    if (argument_names.size() != argument_sorts.size()) {
        throw Sygus2ParserException("Argument sorts and names must have the same length.");
    }
}

FunctionDescriptor::FunctionDescriptor(const Identifier& identifier,
                                       const vector<SortDescriptorCSPtr>& argument_sorts,
                                       const vector<string>& argument_names,
                                       SortDescriptorCSPtr range_sort,
                                       GrammarCSPtr synthesis_grammar,
                                       FunctionKind kind)
    : SymbolTableEntry(SymbolTableEntryKind::Function, identifier),
      kind(kind), argument_sorts(argument_sorts), argument_names(argument_names),
      range_sort(range_sort), function_body(nullptr), synthesis_grammar(synthesis_grammar)
{
    if (argument_names.size() != argument_sorts.size()) {
        throw Sygus2ParserException("Argument sorts and names must have the same length.");
    }
}

FunctionDescriptor::FunctionDescriptor(const Identifier& identifier,
                                       const vector<SortDescriptorCSPtr>& argument_sorts,
                                       const vector<string>& argument_names,
                                       GrammarCSPtr synthesis_grammar,
                                       FunctionKind kind)
    : SymbolTableEntry(SymbolTableEntryKind::Function, identifier),
      kind(kind), argument_sorts(argument_sorts), argument_names(argument_names),
      range_sort(nullptr), function_body(nullptr), synthesis_grammar(synthesis_grammar)
{
    if (argument_names.size() != argument_sorts.size()) {
        throw Sygus2ParserException("Argument sorts and names must have the same length.");
    }
}

FunctionDescriptor::FunctionDescriptor(const Identifier& identifier,
                                       const vector<SortDescriptorCSPtr>& argument_sorts,
                                       SortDescriptorCSPtr range_sort,
                                       FunctionKind kind)
    : SymbolTableEntry(SymbolTableEntryKind::Function, identifier),
      kind(kind), argument_sorts(argument_sorts), argument_names(),
      range_sort(range_sort), function_body(nullptr), synthesis_grammar(nullptr)

{
    // Nothing here
}

FunctionDescriptor::~FunctionDescriptor()
{
    // Nothing here
}

bool FunctionDescriptor::equals_(const FunctionDescriptor& other) const
{
    if (&other == this) {
        return true;
    }

    // equality of functions is based on identifier and
    // the argument sorts. This is the signature of the
    // function, we can't have two functions with the same
    // signature, ever
    if (identifier != other.identifier) {
        return false;
    }

    if (argument_sorts.size() != other.argument_sorts.size()) {
        return false;
    }

    for(size_t i = 0; i < argument_sorts.size(); ++i) {
        if (*(argument_sorts[i]) != *(other.argument_sorts[i])) {
            return false;
        }
    }

    return true;
}

u64 FunctionDescriptor::compute_hash_() const
{
    u64 result = identifier.get_hash();
    for (auto const& arg_sort : argument_sorts) {
        result = (result * 1299721) ^ arg_sort->get_hash();
    }
    return result;
}

FunctionKind FunctionDescriptor::get_kind() const
{
    return kind;
}

const vector<SortDescriptorCSPtr>& FunctionDescriptor::get_argument_sorts() const
{
    return argument_sorts;
}

const vector<string>& FunctionDescriptor::get_argument_names() const
{
    return argument_names;
}

SortDescriptorCSPtr FunctionDescriptor::get_range_sort() const
{
    return range_sort;
}

TermCSPtr FunctionDescriptor::get_function_body() const
{
    return function_body;
}

GrammarCSPtr FunctionDescriptor::get_synthesis_grammar() const
{
    return synthesis_grammar;
}

u32 FunctionDescriptor::get_arity() const
{
    return (u32)argument_sorts.size();
}

SortDescriptor::SortDescriptor(const Identifier& identifier, SortKind kind)
    : SymbolTableEntry(SymbolTableEntryKind::Sort, identifier), kind(kind)
{
    // Nothing here
}


SortDescriptor::SortDescriptor(const Identifier& identifier, SortKind kind, u32 sort_arity)
    : SymbolTableEntry(SymbolTableEntryKind::Sort, identifier),
      kind(kind), sort_arity(sort_arity)
{
    // Nothing here
}

SortDescriptor::SortDescriptor(const Identifier& identifier, SortKind kind,
                               const vector<SortDescriptorCSPtr>& sort_parameters)
    : SymbolTableEntry(SymbolTableEntryKind::Sort, identifier),
      kind(kind), sort_arity(sort_parameters.size()), sort_parameters(sort_parameters)
{
    // Nothing here
}

SortDescriptor::~SortDescriptor()
{
    // Nothing here
}

bool SortDescriptor::equals_(const SortDescriptor& other) const
{
    if (&other == this) {
        return true;
    }

    // sorts are compared purely based on their identifier
    // and the sort_parameters
    if (identifier != other.identifier) {
        return false;
    }

    if (sort_parameters.size() != other.sort_parameters.size()) {
        return false;
    }

    for(size_t i = 0; i < sort_parameters.size(); ++i) {
        if (*(sort_parameters[i]) != *(other.sort_parameters[i])) {
            return false;
        }
    }

    return true;
}

u64 SortDescriptor::compute_hash_() const
{
    Hasher<Identifier> identifier_hasher;
    auto result = identifier_hasher(identifier);
    for (auto const& sort_parameter : sort_parameters) {
        result = (result * 1301011) ^ sort_parameter->get_hash();
    }

    return result;
}

string SortDescriptor::to_string() const
{
    ostringstream sstr;
    sstr << "SortDescriptor(Identifier = " << identifier.to_string();
    if (sort_parameters.size() == 0) {
        sstr << ")";
        return sstr.str();
    }

    sstr << ", SortParameters = (";
    bool first = true;

    for(auto const& arg_sort : sort_parameters) {
        if (!first) {
            sstr << ", ";
        }
        first = false;
        sstr << arg_sort->to_string();
    }

    sstr << ")";
    return sstr.str();
}

SortKind SortDescriptor::get_kind() const
{
    return kind;
}

u32 SortDescriptor::get_arity() const
{
    return sort_arity;
}

const vector<SortDescriptorCSPtr>& SortDescriptor::get_sort_parameters() const
{
    return sort_parameters;
}

bool SortDescriptor::is_parametric() const
{
    return sort_arity > 0;
}

bool SortDescriptor::is_instantiated() const
{
    return sort_arity == sort_parameters.size();
}

VariableDescriptor::VariableDescriptor(const Identifier& identifier, VariableKind kind,
                                       SortDescriptorCSPtr sort_descriptor)
    : SymbolTableEntry(SymbolTableEntryKind::Variable, identifier),
      kind(kind), sort_descriptor(sort_descriptor)
{
    // Nothing here
}

VariableDescriptor::~VariableDescriptor()
{
    // Nothing here
}

VariableKind VariableDescriptor::get_kind() const
{
    return kind;
}

SortDescriptorCSPtr VariableDescriptor::get_sort_descriptor() const
{
    return sort_descriptor;
}

GrammarSymbolDescriptor::GrammarSymbolDescriptor(const Identifier& identifier,
                                                 SortDescriptorCSPtr sort_descriptor)
    : SymbolTableEntry(SymbolTableEntryKind::Variable, identifier),
      sort_descriptor(sort_descriptor)
{
    // Nothing here
}

GrammarSymbolDescriptor::~GrammarSymbolDescriptor()
{
    // Nothing here
}

SortDescriptorCSPtr GrammarSymbolDescriptor::get_sort_descriptor() const
{
    return sort_descriptor;
}

SymbolTableScope::SymbolTableScope()
{
    // Nothing here
}

SymbolTableScope::SymbolTableScope(const SymbolTableScope& other)
    : mappings(other.mappings)
{
    // Nothing here
}

SymbolTableScope::SymbolTableScope(SymbolTableScope&& other)
    : mappings(std::move(other.mappings))
{
    // Nothing here
}

SymbolTableScope::~SymbolTableScope()
{
    // Nothing here
}

void SymbolTableScope::add_mapping(const SymbolTableKey& key, SymbolTableEntrySPtr entry)
{
    mappings[key] = entry;
}

SymbolTableEntryCSPtr SymbolTableScope::lookup(const SymbolTableKey& key) const
{
    auto it = mappings.find(key);
    if (it == mappings.end()) {
        return SymbolTableEntryCSPtr::null_pointer;
    }
    return it->second;
}

SymbolTable::SymbolTable()
{
    // Nothing here
}

SymbolTable::~SymbolTable()
{
    // Nothing here
}

SymbolTableScopeSPtr SymbolTable::push_scope(SymbolTableScopeSPtr scope_to_push)
{
    if (scope_to_push == SymbolTableScopeSPtr::null_pointer) {
        scope_to_push = new SymbolTableScope();
    }

    scope_stack.push_back(scope_to_push);
    return scope_to_push;
}

SymbolTableScopeSPtr SymbolTable::pop_scope()
{
    auto result = scope_stack.back();
    scope_stack.pop_back();
    return result;
}

SymbolTableEntryCSPtr SymbolTable::lookup(const SymbolTableKey& key,
                                          bool in_current_scope_only) const
{
    const i32 num_scopes = (i32)scope_stack.size();
    for(i32 i = num_scopes - 1; i >= 0; --i) {
        auto const& scope = scope_stack[i];
        auto result = scope->lookup(key);
        if (!result.is_null()) {
            return result;
        }

        if (in_current_scope_only) {
            return SymbolTableEntryCSPtr::null_pointer;
        }
    }

    return SymbolTableEntryCSPtr::null_pointer;
}

SymbolTableEntryCSPtr SymbolTable::lookup(const Identifier& identifier,
                                          bool in_current_scope_only) const
{
    SymbolTableKey key(identifier);
    return lookup(key, in_current_scope_only);
}

SortDescriptorCSPtr SymbolTable::lookup_sort(const Identifier& identifier,
                                             bool in_current_scope_only) const
{
    SymbolTableKey key(identifier);
    auto result = lookup(key, in_current_scope_only);
    if (result->is<SortDescriptor>()) {
        return result->static_as<SortDescriptor>();
    }

    return nullptr;
}

SortDescriptorCSPtr SymbolTable::lookup_sort(SortExprCSPtr sort_expr) const
{
    // TODO: Resolve using the resolver
    throw Sygus2ParserException("Not implemented");
}

VariableDescriptorCSPtr SymbolTable::lookup_variable(const Identifier& identifier,
                                                     bool in_current_scope_only) const
{
    SymbolTableKey key(identifier);
    auto result = lookup(key, in_current_scope_only);
    if (result->is<VariableDescriptor>()) {
        return result->static_as<VariableDescriptor>();
    }

    return nullptr;
}

GrammarSymbolDescriptorCSPtr SymbolTable::lookup_grammar_symbol(const Identifier& identifier,
                                                                bool in_current_scope_only) const
{
    SymbolTableKey key(identifier);
    auto result = lookup(key, in_current_scope_only);
    if (result->is<GrammarSymbolDescriptor>()) {
        return result->static_as<GrammarSymbolDescriptor>();
    }

    return nullptr;
}

FunctionDescriptorCSPtr SymbolTable::lookup_function(const Identifier& identifier,
                                                     bool in_current_scope_only) const
{
    SymbolTableKey key(identifier);
    auto result = lookup(key, in_current_scope_only);
    if (result->is<FunctionDescriptor>()) {
        return result->static_as<FunctionDescriptor>();
    }

    return nullptr;
}

FunctionDescriptorCSPtr SymbolTable::lookup_function(const Identifier& identifier,
                                                     const vector<SortDescriptorCSPtr>& argument_sorts,
                                                     bool in_current_scope_only) const
{
    SymbolTableKey key(identifier, argument_sorts);
    auto result = lookup(key, in_current_scope_only);
    if (result->is<FunctionDescriptor>()) {
        return result->static_as<FunctionDescriptor>();
    }

    return nullptr;
}

void SymbolTable::add_sort(SortDescriptorSPtr sort_descriptor)
{
    SymbolTableKey key(sort_descriptor->get_identifier());
    auto const& scope = scope_stack.back();
    if (scope->lookup(key) != nullptr) {
        throw new SymbolTableException("Duplicate mapping in same scope for key " + key.to_string());
    }

    scope_stack.back()->add_mapping(key, sort_descriptor.get_raw_pointer());
}

void SymbolTable::add_function(FunctionDescriptorSPtr function_descriptor)
{
    SymbolTableKey key(function_descriptor->get_identifier(),
                       function_descriptor->get_argument_sorts());
    auto const& scope = scope_stack.back();
    if (scope->lookup(key) != nullptr) {
        throw new SymbolTableException("Duplicate mapping in same scope for key " + key.to_string());
    }

    scope_stack.back()->add_mapping(key, function_descriptor.get_raw_pointer());
}

void SymbolTable::add_variable(VariableDescriptorSPtr variable_descriptor)
{
    SymbolTableKey key(variable_descriptor->get_identifier());
    auto const& scope = scope_stack.back();
    if (scope->lookup(key) != nullptr) {
        throw new SymbolTableException("Duplicate mapping in same scope for key " + key.to_string());
    }

    scope_stack.back()->add_mapping(key, variable_descriptor.get_raw_pointer());
}

void SymbolTable::add_grammar_symbol(GrammarSymbolDescriptorSPtr grammar_symbol_descriptor)
{
    SymbolTableKey key(grammar_symbol_descriptor->get_identifier());
    auto const& scope = scope_stack.back();
    if (scope->lookup(key) != nullptr) {
        throw new SymbolTableException("Duplicate mapping in same scope for key " + key.to_string());
    }

    scope_stack.back()->add_mapping(key, grammar_symbol_descriptor.get_raw_pointer());
}

} /* end namespace */
