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

#include "include/SymbolTable.hpp"
#include "include/Sygus2ParserExceptions.hpp"
#include "include/TheoryManager.hpp"

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
      range_sort(range_sort), function_body(function_body), synthesis_grammar(nullptr),
      synth_fun_command(nullptr), synth_inv_command(nullptr)
{
    if (argument_names.size() != argument_sorts.size()) {
        throw Sygus2ParserException("Argument sorts and names must have the same length.");
    }
}

FunctionDescriptor::FunctionDescriptor(const Identifier& identifier,
                                       SortDescriptorCSPtr range_sort,
                                       FunctionKind kind)
    : SymbolTableEntry(SymbolTableEntryKind::Function, identifier),
      kind(kind), range_sort(range_sort), function_body(nullptr), synthesis_grammar(nullptr),
      synth_fun_command(nullptr), synth_inv_command(nullptr)
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
                                       SynthFunCommandCSPtr synth_fun_command,
                                       FunctionKind kind)
    : SymbolTableEntry(SymbolTableEntryKind::Function, identifier),
      kind(kind), argument_sorts(argument_sorts), argument_names(argument_names),
      range_sort(range_sort), function_body(nullptr), synthesis_grammar(synthesis_grammar),
      synth_fun_command(synth_fun_command), synth_inv_command(nullptr)
{
    if (argument_names.size() != argument_sorts.size()) {
        throw Sygus2ParserException("Argument sorts and names must have the same length.");
    }
}

FunctionDescriptor::FunctionDescriptor(const Identifier& identifier,
                                       const vector<SortDescriptorCSPtr>& argument_sorts,
                                       const vector<string>& argument_names,
                                       GrammarCSPtr synthesis_grammar,
                                       SynthInvCommandCSPtr synth_inv_command,
                                       FunctionKind kind)
    : SymbolTableEntry(SymbolTableEntryKind::Function, identifier),
      kind(kind), argument_sorts(argument_sorts), argument_names(argument_names),
      range_sort(nullptr), function_body(nullptr), synthesis_grammar(synthesis_grammar),
      synth_fun_command(nullptr), synth_inv_command(synth_inv_command)
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
      range_sort(range_sort), function_body(nullptr), synthesis_grammar(nullptr),
      synth_fun_command(nullptr), synth_inv_command(nullptr)
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

SynthFunCommandCSPtr FunctionDescriptor::get_synth_fun_command() const
{
    return synth_fun_command;
}

SynthInvCommandCSPtr FunctionDescriptor::get_synth_inv_command() const
{
    return synth_inv_command;
}

SortDescriptor::SortDescriptor(const Identifier& identifier)
    : SymbolTableEntry(SymbolTableEntryKind::Sort, identifier)
{
    // Nothing here
}

SortDescriptor::~SortDescriptor()
{
    // Nothing here
}

SortDescriptorCSPtr SortDescriptor::create_primitive_sort(const Identifier& identifier)
{
    auto result = new SortDescriptor(identifier);
    result->kind = SortKind::Primitive;
    result->sort_arity = -1;
    result->alias_target = nullptr;
    return result;
}

SortDescriptorCSPtr SortDescriptor::create_uninterpreted_sort(const Identifier& identifier,
                                                              u32 sort_arity)
{
    auto result = new SortDescriptor(identifier);
    result->kind = SortKind::Uninterpreted;
    result->sort_arity = sort_arity;
    result->alias_target = nullptr;
    return result;
}

bool SortDescriptor::check_unbound_placeholders(const vector<SortDescriptorCSPtr>& allowed_placeholders,
                                                vector<SortDescriptorCSPtr>& unbound_placeholders) const
{
    auto const& placeholders = get_placeholder_parameters();
    for (auto const& placeholder : placeholders) {
        bool found = false;
        for(auto const& allowed_placeholder : allowed_placeholders) {
            if (*placeholder == *allowed_placeholder) {
                found = true;
                break;
            }
        }
        if (!found) {
            unbound_placeholders.push_back(placeholder);
        }
    }

    return unbound_placeholders.size() > 0;
}

SortDescriptorCSPtr SortDescriptor::create_sort_parameter_placeholder(const Identifier& identifier)
{
    auto result = new SortDescriptor(identifier);
    result->kind = SortKind::SortParameterPlaceholder;
    result->sort_arity = -1;
    result->alias_target = nullptr;
    return result;
}

SortDescriptorCSPtr SortDescriptor::create_parametric_sort(const Identifier& identifier,
                                                           const vector<SortDescriptorCSPtr>& parameter_placeholders)
{
    for(auto const& placeholder : parameter_placeholders) {
        if (placeholder->get_kind() != SortKind::SortParameterPlaceholder) {
            throw Sygus2ParserException("Parametric sorts can only be created with parameter placeholders.");
        }
    }

    auto result = new SortDescriptor(identifier);
    result->kind = SortKind::Parametric;
    result->sort_arity = -1;
    result->sort_parameters = parameter_placeholders;
    result->alias_target = nullptr;

    return result;
}

SortDescriptorCSPtr SortDescriptor::create_sort_alias(const Identifier& identifier,
                                                      const vector<SortDescriptorCSPtr>& parameter_placeholders,
                                                      SortDescriptorCSPtr alias_target)
{
    for(auto const& placeholder : parameter_placeholders) {
        if (placeholder->get_kind() != SortKind::SortParameterPlaceholder) {
            throw Sygus2ParserException("Parametric sorts can only be created with parameter placeholders.");
        }
    }

    vector<SortDescriptorCSPtr> unbound_placeholders;
    if (alias_target->check_unbound_placeholders(parameter_placeholders, unbound_placeholders)) {
        ostringstream sstr;
        sstr << "Alias target contains unbound placeholders." << endl;
        sstr << "Alias target: " << alias_target->to_string() << endl;
        sstr << "The following placeholders are unbound:" << endl;
        for (auto const& unbound_placeholder : unbound_placeholders) {
            sstr << unbound_placeholder->to_string() << endl;
        }
        throw Sygus2ParserException(sstr.str());
    }

    auto result = new SortDescriptor(identifier);
    result->kind = SortKind::SortAlias;
    result->sort_arity = alias_target->sort_arity;
    result->sort_parameters = parameter_placeholders;
    result->alias_target = alias_target;
    return result;
}

SortDescriptorCSPtr SortDescriptor::instantiate_sort_impl(const SortInstantiationVector& instantiation_vector) const
{
    if (get_num_placeholder_parameters() == 0) {
        return this;
    }

    auto result = new SortDescriptor(identifier);
    result->kind = kind;
    result->sort_arity = -1;

    vector<SortDescriptorCSPtr> new_sort_parameters(sort_parameters);
    for (auto const& mapping : instantiation_vector) {
        auto target = mapping.first;
        auto replacement = mapping.second;
        bool replaced = false;
        for (size_t i = 0; i < new_sort_parameters.size(); ++i) {
            if (*(new_sort_parameters[i]) == *target) {
                new_sort_parameters[i] = target;
                replaced = true;
                break;
            }
        }

        if (!replaced) {
            delete result;
            throw new Sygus2ParserException("Could not find placeholder parameter: " + target->to_string());
        }
    }

    result->sort_parameters = new_sort_parameters;
    if (alias_target.is_null()) {
        result->alias_target = nullptr;
    } else {
        result->alias_target = alias_target->instantiate_sort_impl(instantiation_vector);
    }

    return result;
}

SortDescriptorCSPtr SortDescriptor::instantiate_sort(const SortInstantiationVector& instantiation_vector) const
{
    if (get_num_placeholder_parameters() == 0) {
        throw Sygus2ParserException("Sort cannot be instantiated: it is either non-parametric, or "
                                    "fully instantiated already");
    }
    return instantiate_sort_impl(instantiation_vector);
}

SortDescriptorCSPtr SortDescriptor::resolve_aliases() const
{
    if (alias_target.is_null()) {
        return this;
    }

    return alias_target->resolve_aliases();
}

bool SortDescriptor::equals_(const SortDescriptor& other) const
{
    if (&other == this) {
        return true;
    }

    // Sorts are equal if their identifiers and parameters are equal
    if (identifier != other.identifier) {
        return false;
    }

    if (sort_parameters.size() != other.sort_parameters.size()) {
        return false;
    }

    for (size_t i = 0; i < sort_parameters.size(); ++i) {
        if (*(sort_parameters[i]) != *(other.sort_parameters[i])) {
            return false;
        }
    }

    return true;
}

u64 SortDescriptor::compute_hash_() const
{
    Hasher<Identifier> identifier_hasher;
    u64 result = identifier_hasher(identifier);
    for (auto const& sort_param : sort_parameters) {
        result = (result * 1300319) ^ sort_param->get_hash();
    }

    return result;
}

string SortDescriptor::to_string() const
{
    ostringstream sstr;
    if (kind == SortKind::SortParameterPlaceholder) {
        sstr << "^" << identifier.to_string();
        return sstr.str();
    }

    sstr << identifier.to_string();
    if (sort_parameters.size() == 0) {
        return sstr.str();
    }

    bool first = true;
    sstr << " (";
    for (auto const& param : sort_parameters) {
        if (!first) {
            sstr << " ";
        }
        first = false;
        sstr << param;
    }

    sstr << ")";
    return sstr.str();
}

SortKind SortDescriptor::get_kind() const
{
    return kind;
}

i32 SortDescriptor::get_sort_arity() const
{
    return sort_arity;
}

SortDescriptorCSPtr SortDescriptor::get_alias_target() const
{
    return alias_target;
}

const vector<SortDescriptorCSPtr>& SortDescriptor::get_sort_parameters() const
{
    return sort_parameters;
}

vector<SortDescriptorCSPtr> SortDescriptor::get_placeholder_parameters() const
{
    vector<SortDescriptorCSPtr> result;
    for (auto const& param : sort_parameters) {
        if (param->kind == SortKind::SortParameterPlaceholder) {
            result.push_back(param);
        } else {
            result.push_back(nullptr);
        }
    }

    return result;
}

vector<SortDescriptorCSPtr> SortDescriptor::get_non_placeholder_parameters() const
{
    vector<SortDescriptorCSPtr> result;
    for (auto const& param : sort_parameters) {
        if (param->kind != SortKind::SortParameterPlaceholder) {
            result.push_back(param);
        } else {
            result.push_back(nullptr);
        }
    }

    return result;
}

u32 SortDescriptor::get_num_parameters() const
{
    return sort_parameters.size();
}

u32 SortDescriptor::get_num_placeholder_parameters() const
{
    u32 result = 0;
    for (auto const& param : sort_parameters) {
        if (param->kind == SortKind::SortParameterPlaceholder) {
            result++;
        }
    }
    return result;
}

u32 SortDescriptor::get_num_non_placeholder_parameters() const
{
    u32 result = 0;
    for (auto const& param : sort_parameters) {
        if (param->kind != SortKind::SortParameterPlaceholder) {
            result++;
        }
    }
    return result;
}

bool SortDescriptor::is_fully_instantiated() const
{
    return get_num_placeholder_parameters() == 0;
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

void SymbolTableScope::add_mapping(const SymbolTableKey& key, SymbolTableEntryCSPtr entry)
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
    enable_feature("grammars");
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

SortDescriptorCSPtr SymbolTable::lookup_or_resolve_sort(const Identifier& identifier)
{
    auto result = lookup_sort(identifier);
    if (!result.is_null()) {
        return result;
    }

    result = TheoryManager::resolve_sort(identifier);
    if (!result.is_null()) {
        add_sort(result);
    }
    return result;
}

FunctionDescriptorCSPtr SymbolTable::lookup_or_resolve_function(const Identifier& identifier,
                                                                const vector<SortDescriptorCSPtr>& argument_sorts)
{
    auto result = lookup_function(identifier, argument_sorts);
    if (!result.is_null()) {
        return result;
    }

    result = TheoryManager::resolve_function(identifier, argument_sorts);
    if (!result.is_null()) {
        add_function(result);
    }
    return result;
}

void SymbolTable::add_sort(SortDescriptorCSPtr sort_descriptor)
{
    SymbolTableKey key(sort_descriptor->get_identifier());
    if (lookup(key, false) != nullptr) {
        throw new SymbolTableException("Redeclaration of identifier " + key.to_string());
    }

    scope_stack.back()->add_mapping(key, sort_descriptor.get_raw_pointer());
}

void SymbolTable::add_function(FunctionDescriptorCSPtr function_descriptor)
{
    SymbolTableKey key(function_descriptor->get_identifier(),
                       function_descriptor->get_argument_sorts());
    auto const& scope = scope_stack.back();
    if (scope->lookup(key) != nullptr) {
        throw new SymbolTableException("Duplicate mapping in same scope for key " + key.to_string());
    }

    scope_stack.back()->add_mapping(key, function_descriptor.get_raw_pointer());
}

void SymbolTable::add_variable(VariableDescriptorCSPtr variable_descriptor)
{
    SymbolTableKey key(variable_descriptor->get_identifier());
    auto const& scope = scope_stack.back();
    if (scope->lookup(key) != nullptr) {
        throw new SymbolTableException("Duplicate mapping in same scope for key " + key.to_string());
    }

    scope_stack.back()->add_mapping(key, variable_descriptor.get_raw_pointer());
}

void SymbolTable::add_grammar_symbol(GrammarSymbolDescriptorCSPtr grammar_symbol_descriptor)
{
    SymbolTableKey key(grammar_symbol_descriptor->get_identifier());
    auto const& scope = scope_stack.back();
    if (scope->lookup(key) != nullptr) {
        throw new SymbolTableException("Duplicate mapping in same scope for key " + key.to_string());
    }

    scope_stack.back()->add_mapping(key, grammar_symbol_descriptor.get_raw_pointer());
}

SortDescriptorCSPtr SymbolTable::get_boolean_sort()
{
    return CoreResolver::get_bool_sort();
}

SortDescriptorCSPtr SymbolTable::get_integer_sort()
{
    return IntegerResolver::get_integer_sort();
}

SortDescriptorCSPtr SymbolTable::get_string_sort()
{
    return StringResolver::get_string_sort();
}

SortDescriptorCSPtr SymbolTable::get_real_sort()
{
    return RealResolver::get_real_sort();
}

bool SymbolTable::is_bitvector_sort(SortDescriptorCSPtr sort_descriptor)
{
    u32 unused;
    return is_bitvector_sort(sort_descriptor, unused);
}

bool SymbolTable::is_bitvector_sort(SortDescriptorCSPtr sort_descriptor, u32& size)
{
    if (sort_descriptor->get_sort_arity() != 0) {
        return false;
    }
    auto const& identifier = sort_descriptor->get_identifier();
    return BitVectorResolver::parse_bitvector_identifier(identifier, size);
}

bool SymbolTable::is_array_sort(SortDescriptorCSPtr sort_descriptor)
{
    SortDescriptorCSPtr key;
    SortDescriptorCSPtr value;
    return is_array_sort(sort_descriptor, key, value);
}

bool SymbolTable::is_array_sort(SortDescriptorCSPtr sort_descriptor,
                                SortDescriptorCSPtr& key_sort,
                                SortDescriptorCSPtr& value_sort)
{
    return ArrayResolver::is_array_sort(sort_descriptor, key_sort, value_sort);
}


} /* end namespace */
