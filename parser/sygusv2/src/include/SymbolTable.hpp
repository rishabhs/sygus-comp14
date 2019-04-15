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

#if !defined __SYGUS2_PARSER_SYMBOL_TABLE_HPP
#define __SYGUS2_PARSER_SYMBOL_TABLE_HPP

#include <unordered_map>

#include "Sygus2ParserCommon.hpp"
#include "BaseTypes.hpp"
#include "Sygus2ParserIFace.hpp"

namespace Sygus2Parser {

using namespace std;

class SortDescriptor;
typedef ManagedPointer<SortDescriptor> SortDescriptorSPtr;
typedef ManagedConstPointer<SortDescriptor> SortDescriptorCSPtr;
typedef vector<pair<SortDescriptorCSPtr, SortDescriptorCSPtr>> SortInstantiationVector;

class SymbolTableKey : public Hashable<SymbolTableKey>, public Equatable<SymbolTableKey>
{
private:
    Identifier identifier;
    vector<SortDescriptorCSPtr> argument_sorts;

public:
    SymbolTableKey(const Identifier& identifier);
    SymbolTableKey(const Identifier& identifier, const vector<SortDescriptorCSPtr>& argument_sorts);

    SymbolTableKey(const SymbolTableKey& other);
    SymbolTableKey(SymbolTableKey&& other);
    ~SymbolTableKey();

    SymbolTableKey& operator = (const SymbolTableKey& other);
    SymbolTableKey& operator = (SymbolTableKey&& other);

    bool equals_(const SymbolTableKey& other) const;
    u64 compute_hash_() const;

    string to_string() const;

    // accessors
    const Identifier& get_identifier() const;
    const vector<SortDescriptorCSPtr>& get_argument_sorts() const;
};

enum class SymbolTableEntryKind
    {
     Variable,
     Function,
     Sort,
     GrammarSymbol,
    };

class SymbolTableEntry : public Downcastable<SymbolTableEntry>, public RefCountable<SymbolTableEntry>
{
protected:
    SymbolTableEntryKind entry_kind;
    Identifier identifier;

    SymbolTableEntry() = delete;
    SymbolTableEntry(const SymbolTableEntry& other) = delete;
    SymbolTableEntry(SymbolTableEntry&& other) = delete;
    SymbolTableEntry& operator = (const SymbolTableEntry& other) = delete;
    SymbolTableEntry& operator = (SymbolTableEntry&& other) = delete;
    SymbolTableEntry(SymbolTableEntryKind kind, const Identifier& identifier);

public:
    SymbolTableEntryKind get_entry_kind() const;
    const Identifier& get_identifier() const;
};

typedef ManagedPointer<SymbolTableEntry> SymbolTableEntrySPtr;
typedef ManagedConstPointer<SymbolTableEntry> SymbolTableEntryCSPtr;

enum class FunctionKind
    {
     SynthFun,
     SynthInv,
     UserDefined,
     Uninterpreted,
     Theory,
    };

class FunctionDescriptor : public SymbolTableEntry,
                           public Equatable<FunctionDescriptor>,
                           public Hashable<FunctionDescriptor>
{
private:
    FunctionKind kind;
    vector<SortDescriptorCSPtr> argument_sorts;
    vector<string> argument_names;
    SortDescriptorCSPtr range_sort;
    TermCSPtr function_body;
    GrammarCSPtr synthesis_grammar;

public:
    // For user defined functions
    FunctionDescriptor(const Identifier& identifier,
                       const vector<SortDescriptorCSPtr>& argument_sorts,
                       const vector<string>& argument_names,
                       SortDescriptorCSPtr range_sort,
                       TermCSPtr function_body,
                       FunctionKind kind = FunctionKind::UserDefined);

    // For functions to be synthesized
    FunctionDescriptor(const Identifier& identifier,
                       const vector<SortDescriptorCSPtr>& argument_sorts,
                       const vector<string>& argument_names,
                       SortDescriptorCSPtr range_sort,
                       GrammarCSPtr synthesis_grammar,
                       FunctionKind kind = FunctionKind::SynthFun);

    // For invariants to be synthesized
    FunctionDescriptor(const Identifier& identifier,
                       const vector<SortDescriptorCSPtr>& argument_sorts,
                       const vector<string>& argument_names,
                       GrammarCSPtr synthesis_grammar,
                       FunctionKind = FunctionKind::SynthInv);

    // For universally quantified (uninterpreted) functions, or theory functions
    FunctionDescriptor(const Identifier& identifier,
                       const vector<SortDescriptorCSPtr>& argument_sorts,
                       SortDescriptorCSPtr range_sort,
                       FunctionKind kind);

    virtual ~FunctionDescriptor();

    bool equals_(const FunctionDescriptor& other) const;
    u64 compute_hash_() const;

    // accessors
    FunctionKind get_kind() const;
    const vector<SortDescriptorCSPtr>& get_argument_sorts() const;
    const vector<string>& get_argument_names() const;
    SortDescriptorCSPtr get_range_sort() const;
    TermCSPtr get_function_body() const;
    GrammarCSPtr get_synthesis_grammar() const;
    u32 get_arity() const;
};

typedef ManagedPointer<FunctionDescriptor> FunctionDescriptorSPtr;
typedef ManagedConstPointer<FunctionDescriptor> FunctionDescriptorCSPtr;

enum class SortKind
    {
     Primitive,
     Uninterpreted,
     Parametric,
     SortParameterPlaceholder,
     SortAlias
    };

class SortDescriptor : public SymbolTableEntry,
                       public Equatable<SortDescriptor>,
                       public Hashable<SortDescriptor>
{
private:
    SortKind kind;
    vector<SortDescriptorCSPtr> sort_parameters;
    i32 sort_arity;
    SortDescriptorCSPtr alias_target;

    SortDescriptor() = delete;
    SortDescriptor(const SortDescriptor&) = delete;
    SortDescriptor(SortDescriptor&&) = delete;
    SortDescriptor& operator = (const SortDescriptor&) = delete;
    SortDescriptor& operator = (SortDescriptor&&) = delete;

    SortDescriptor(const Identifier& identifier);
    virtual ~SortDescriptor();

    bool check_unbound_placeholders(const vector<SortDescriptorCSPtr>& allowed_placeholders,
                                    vector<SortDescriptorCSPtr>& unbound_placeholders) const;

    SortDescriptorCSPtr instantiate_sort_impl(const SortInstantiationVector& instantiation_vector) const;

public:
    static SortDescriptorCSPtr create_primitive_sort(const Identifier& identifier);
    static SortDescriptorCSPtr create_uninterpreted_sort(const Identifier& identifier,
                                                         u32 sort_arity);
    static SortDescriptorCSPtr create_sort_parameter_placeholder(const Identifier& identifier);
    static SortDescriptorCSPtr create_parametric_sort(const Identifier& identifier,
                                                      const vector<SortDescriptorCSPtr>& parameter_placeholders);
    static SortDescriptorCSPtr create_sort_alias(const Identifier& identifier,
                                                 const vector<SortDescriptorCSPtr>& parameter_placeholders,
                                                 SortDescriptorCSPtr alias_target);

    SortDescriptorCSPtr instantiate_sort(const SortInstantiationVector& instantiation_vector) const;
    SortDescriptorCSPtr resolve_aliases() const;

    // equality and hash methods
    bool equals_(const SortDescriptor& other) const;
    u64 compute_hash_() const;
    string to_string() const;

    // accessors
    SortKind get_kind() const;
    i32 get_sort_arity() const;
    SortDescriptorCSPtr get_alias_target() const;
    const vector<SortDescriptorCSPtr>& get_sort_parameters() const;
    vector<SortDescriptorCSPtr> get_placeholder_parameters() const;
    vector<SortDescriptorCSPtr> get_non_placeholder_parameters() const;
    u32 get_num_parameters() const;
    u32 get_num_placeholder_parameters() const;
    u32 get_num_non_placeholder_parameters() const;
    bool is_fully_instantiated() const;

};

enum class VariableKind
    {
     Universal,
     Parameter,
     Quantified,
     LetBound
    };

class VariableDescriptor : public SymbolTableEntry
{
private:
    VariableKind kind;
    SortDescriptorCSPtr sort_descriptor;

public:
    VariableDescriptor(const Identifier& identifier, VariableKind kind,
                       SortDescriptorCSPtr sort_descriptor);
    virtual ~VariableDescriptor();

    // accessors
    VariableKind get_kind() const;
    SortDescriptorCSPtr get_sort_descriptor() const;
};

typedef ManagedPointer<VariableDescriptor> VariableDescriptorSPtr;
typedef ManagedConstPointer<VariableDescriptor> VariableDescriptorCSPtr;

class GrammarSymbolDescriptor : public SymbolTableEntry
{
private:
    SortDescriptorCSPtr sort_descriptor;

public:
    GrammarSymbolDescriptor(const Identifier& identifier, SortDescriptorCSPtr sort_descriptor);
    virtual ~GrammarSymbolDescriptor();

    // accessors
    SortDescriptorCSPtr get_sort_descriptor() const;
};

typedef ManagedPointer<GrammarSymbolDescriptor> GrammarSymbolDescriptorSPtr;
typedef ManagedConstPointer<GrammarSymbolDescriptor> GrammarSymbolDescriptorCSPtr;

class SymbolTable;

class SymbolTableScope : public RefCountable<SymbolTableScope>
{
    friend class SymbolTable;

private:
    unordered_map<SymbolTableKey, SymbolTableEntryCSPtr,
                  Hasher<SymbolTableKey>, Equals<SymbolTableKey>> mappings;

    void add_mapping(const SymbolTableKey& key, SymbolTableEntryCSPtr entry);

public:
    SymbolTableScope();
    SymbolTableScope(const SymbolTableScope& other);
    SymbolTableScope(SymbolTableScope&& other);

    virtual ~SymbolTableScope();

    // For sort names, variable names and grammar symbols
    SymbolTableEntryCSPtr lookup(const SymbolTableKey& key) const;
};

typedef ManagedPointer<SymbolTableScope> SymbolTableScopeSPtr;
typedef ManagedConstPointer<SymbolTableScope> SymbolTableScopeCSPtr;

class SymbolTable : public RefCountable<SymbolTable>
{
private:
    vector<SymbolTableScopeSPtr> scope_stack;
    vector<string> enabled_features;
    unordered_map<string, LiteralCSPtr> options;
    string logic;
    SymbolTableEntryCSPtr lookup(const SymbolTableKey& key, bool in_current_scope_only) const;

public:
    SymbolTable();
    virtual ~SymbolTable();

    SymbolTableScopeSPtr push_scope(SymbolTableScopeSPtr scope_to_push = SymbolTableScopeSPtr::null_pointer);
    SymbolTableScopeSPtr pop_scope();

    SymbolTableEntryCSPtr lookup(const Identifier& identifier,
                                 bool in_current_scope_only = false) const;
    SortDescriptorCSPtr lookup_sort(const Identifier& identifier,
                                    bool in_current_scope_only = false) const;
    VariableDescriptorCSPtr lookup_variable(const Identifier& identifier,
                                            bool in_current_scope_only = false) const;
    GrammarSymbolDescriptorCSPtr lookup_grammar_symbol(const Identifier& identifier,
                                                       bool in_current_scope_only = false) const;
    FunctionDescriptorCSPtr lookup_function(const Identifier& identifier,
                                            bool in_current_scope_only = false) const;
    FunctionDescriptorCSPtr lookup_function(const Identifier& identifier,
                                            const vector<SortDescriptorCSPtr>& argument_sorts,
                                            bool in_current_scope_only = false) const;

    SortDescriptorCSPtr lookup_or_resolve_sort(const Identifier& identifier);
    FunctionDescriptorCSPtr lookup_or_resolve_function(const Identifier& identifier,
                                                       const vector<SortDescriptorCSPtr>& argument_sorts);

    void add_sort(SortDescriptorCSPtr sort_descriptor);
    void add_function(FunctionDescriptorCSPtr function_descriptor);
    void add_variable(VariableDescriptorCSPtr variable_descriptor);
    void add_grammar_symbol(GrammarSymbolDescriptorCSPtr grammar_symbol_descriptor);

    // one off settings for logics, options and features
    void enable_feature(const string& feature_name);
    void disable_feature(const string& feature_name);

    void set_logic(const string& logic_name);

    void set_option(const string& option_name, const LiteralCSPtr literal);

    static SortDescriptorCSPtr get_boolean_sort();
    static SortDescriptorCSPtr get_integer_sort();
    static SortDescriptorCSPtr get_string_sort();
    static SortDescriptorCSPtr get_real_sort();
    static bool is_bitvector_sort(SortDescriptorCSPtr sort_descriptor);
    static bool is_bitvector_sort(SortDescriptorCSPtr sort_descriptor, u32& size);
    static bool is_array_sort(SortDescriptorCSPtr sort_descriptor);
    static bool is_array_sort(SortDescriptorCSPtr sort_descriptor,
                              SortDescriptorCSPtr& key_sort,
                              SortDescriptorCSPtr& value_sort);
};

typedef ManagedPointer<SymbolTable> SymbolTableSPtr;
typedef ManagedConstPointer<SymbolTable> SymbolTableCSPtr;

} /* end namespace */

#endif /* __SYGUS2_PARSER_SYMBOL_TABLE_HPP */
