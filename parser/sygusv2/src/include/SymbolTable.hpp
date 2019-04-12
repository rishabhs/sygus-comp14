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

#include "BaseTypes.hpp"
#include "Sygus2ParserFwd.hpp"
#include <memory>
#include <unordered_map>

namespace Sygus2Parser {

class SymbolTableKey;
class SymbolTableEntry;
class FunctionDescriptor;
class VariableDescriptor;
class SortDescriptor;
class GrammarSymbolDescriptor;

typedef shared_ptr<SymbolTableEntry> SymbolTableEntrySPtr;
typedef shared_ptr<FunctionDescriptor> FunctionDescriptorSPtr;
typedef shared_ptr<VariableDescriptor> VariableDescriptorSPtr;
typedef shared_ptr<SortDescriptor> SortDescriptorSPtr;
typedef shared_ptr<GrammarSymbolDescriptor> GrammarSymbolDescriptorSPtr;

typedef shared_ptr<const SymbolTableEntry> SymbolTableEntryCSPtr;
typedef shared_ptr<const FunctionDescriptor> FunctionDescriptorCSPtr;
typedef shared_ptr<const VariableDescriptor> VariableDescriptorCSPtr;
typedef shared_ptr<const SortDescriptor> SortDescriptorCSPtr;
typedef shared_ptr<const GrammarSymbolDescriptor> GrammarSymbolDescriptorCSPtr;

class SymbolTableKey : public Hashable<SymbolTableKey>, public Equatable<SymbolTableKey>
{
private:
    Identifier identifier;
    vector<const SortDescriptor*> argument_sorts;

public:
    SymbolTableKey(const Identifier& identifier);
    SymbolTableKey(const Identifier& identifier, const vector<const SortDescriptor*>& argument_sorts);

    SymbolTableKey(const SymbolTableKey& other);
    SymbolTableKey(SymbolTableKey&& other);
    ~SymbolTableKey();

    SymbolTableKey& operator = (const SymbolTableKey& other);
    SymbolTableKey& operator = (SymbolTableKey&& other);

    bool equals_(const SymbolTableKey& other) const;
    u64 compute_hash_() const;

    // accessors
    const Identifier& get_identifier() const;
    const vector<const SortDescriptor*>& get_argument_sorts() const;
};

enum class SymbolTableEntryKind
    {
     Variable,
     Function,
     Sort,
     GrammarSymbol,
    };

enum class VariableKind
    {
     Universal,
     Parameter,
     Quantified,
     LetBound
    };

enum class FunctionKind
    {
     SynthFun,
     SynthInv,
     UserDefined
    };

enum class SortKind
    {
     Primitive,
     UserDefined,
     Uninterpreted
    };

class SymbolTableEntry : public Downcastable<SymbolTableEntry>
{
private:
    SymbolTableEntryKind kind;
    Identifier identifier;

    SymbolTableEntry() = delete;
    SymbolTableEntry(const SymbolTableEntry& other) = delete;
    SymbolTableEntry(SymbolTableEntry&& other) = delete;
    SymbolTableEntry& operator = (const SymbolTableEntry& other) = delete;
    SymbolTableEntry& operator = (SymbolTableEntry&& other) = delete;

protected:
    SymbolTableEntry(SymbolTableEntryKind kind, const Identifier& identifier);

public:
    SymbolTableEntryKind get_kind() const;
    const Identifier& get_identifier() const;
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
    Term* function_body;
    Grammar* synthesis_grammar;

public:
    // For user defined functions
    FunctionDescriptor(const Identifier& identifier,
                       const vector<SortDescriptorCSPtr>& argument_sorts,
                       const vector<string>& argument_names,
                       SortDescriptorCSPtr range_sort,
                       Term* function_body,
                       FunctionKind kind = FunctionKind::UserDefined);

    // For functions to be synthesized
    FunctionDescriptor(const Identifier& identifier,
                       const vector<SortDescriptorCSPtr>& argument_sorts,
                       const vector<string>& argument_names,
                       SortDescriptorCSPtr range_sort,
                       Grammar* synthesis_grammar,
                       FunctionKind kind = FunctionKind::SynthFun);

    // For invariants to be synthesized
    FunctionDescriptor(const Identifier& identifier,
                       const vector<SortDescriptorCSPtr>& argument_sorts,
                       const vector<string>& argument_names,
                       Grammar* synthesis_grammar,
                       FunctionKind = FunctionKind::SynthInv);

    virtual ~FunctionDescriptor();

    bool equals_(const FunctionDescriptor& other) const;
    u64 compute_hash_() const;

    // accessors
    FunctionKind get_kind() const;
    const vector<SortDescriptorCSPtr>& get_argument_sorts() const;
    const vector<string>& get_argument_names() const;
    SortDescriptorCSPtr get_range_sort() const;
    const Term* get_function_body() const;
    const Grammar* get_synthesis_grammar() const;
    u32 get_arity() const;
};

class SortDescriptor : public SymbolTableEntry,
                       public Equatable<SortDescriptor>
                       public Hashable<SortDescriptor>
{
private:
    SortKind kind;
    u32 sort_arity;
    vector<SortDescriptorCSPtr> sort_parameters;

public:
    // for non-parametric sorts, user-defined or primitive.
    SortDescriptor(const Identifier& identifier, SortKind kind);
    // for uninterpreted sorts
    SortDescriptor(const Identifier& identifier, SortKind kind, u32 sort_arity);
    // for parametric sorts, user-defined or primitive.
    SortDescriptor(const Identifier& identifier, SortKind kind, const vector<SortDescriptor*>& sort_parameters);

    ~SortDescriptor();

    bool equals_(const SortDescriptor& other) const;
    u64 compute_hash_() const;

    const Identifier& get_identifier() const;
    SortKind get_kind() const;
    u32 get_arity() const;
    const vector<SortDescriptorCSPtr>& get_sort_parameters() const;
    bool is_parametric() const;
};

class VariableDescriptor : public SymbolTableEntry
{
private:
    VariableKind kind;
    SortDescriptorCSPtr sort_descriptor;

public:
    VariableDescriptor(const Identifier& identifier, VariableKind kind,
                       const SortDescriptor* sort_descriptor);
    virtual ~VariableDescriptor();

    // accessors
    VariableKind get_kind() const;
    const SortDescriptor* get_sort_descriptor() const;
};

class GrammarSymbolDescriptor : public SymbolTableEntry
{
private:
    const SortDescriptor* sort_descriptor;

public:
    GrammarSymbolDescriptor(const Identifier& identifier, const SortDescriptor* sort_descriptor);
};

} /* end namespace */

#endif /* __SYGUS2_PARSER_SYMBOL_TABLE_HPP */
