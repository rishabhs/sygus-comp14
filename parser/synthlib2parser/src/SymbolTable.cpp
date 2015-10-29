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

#include <SymbolTable.hpp>

namespace SynthLib2Parser {

    SymbolTableEntry::SymbolTableEntry(SymtabEntryKind STEKind, const SortExpr* STESort)
        : STEKind(STEKind), STESort(STESort), FunDef(NULL), LetBoundTerm(NULL)
    {
        if(STEKind == STENTRY_USER_FUNCTION || STEKind == STENTRY_BVARIABLE) {
            throw SymbolTableException("INTERNAL: Wrong constructor called on SymbolTableEntry");
        }
    }

    SymbolTableEntry::SymbolTableEntry(FunDefCmd* FunDef)
        : STEKind(STENTRY_USER_FUNCTION), FunDef(FunDef), LetBoundTerm(NULL)
    {
        // Create a sort for this function type
        vector<const SortExpr*> ArgSorts;
        auto const& Args = FunDef->GetArgs();
        for(auto const& ASPair : Args) {
            ArgSorts.push_back(static_cast<const SortExpr*>(ASPair->GetSort()->Clone()));
        }

        STESort = new FunSortExpr(SourceLocation::None, ArgSorts,
                                  static_cast<const SortExpr*>(FunDef->GetSort()->Clone()));
    }

    SymbolTableEntry::SymbolTableEntry(Term* LetBoundTerm, const SortExpr* TermSort)
        : STEKind(STENTRY_BVARIABLE), STESort(TermSort),
          FunDef(NULL), LetBoundTerm(LetBoundTerm)
    {
        // Nothing here
    }

    SymbolTableEntry::~SymbolTableEntry()
    {
        if(STESort != NULL) {
            delete STESort;
            STESort = NULL;
        }
        if(FunDef != NULL) {
            delete FunDef;
            FunDef = NULL;
        }
        if(LetBoundTerm != NULL) {
            delete LetBoundTerm;
            LetBoundTerm = NULL;
        }
    }

    SymtabEntryKind SymbolTableEntry::GetKind() const
    {
        return STEKind;
    }

    const SortExpr* SymbolTableEntry::GetSort() const
    {
        return STESort;
    }

    FunDefCmd* SymbolTableEntry::GetFunDef() const
    {
        if(GetKind() != STENTRY_USER_FUNCTION) {
            throw SymbolTableException((string)"INTERNAL: Called SymbolTableEntry::GetFunDef() " +
                                       "on non function STE");
        }
        return FunDef;
    }

    Term* SymbolTableEntry::GetLetBoundTerm() const
    {
        if(GetKind() != STENTRY_BVARIABLE) {
            throw SymbolTableException((string)"INTERNAL: Called " +
                                       "SymbolTableEntry::GetLetBoundTerm() " +
                                       "on non bound var STE");
        }
        return LetBoundTerm;
    }

    SymbolTableEntry* SymbolTableEntry::Clone() const
    {
        switch(STEKind) {
        case STENTRY_QVARIABLE:
        case STENTRY_ARG:
        case STENTRY_SORT:
        case STENTRY_THEORY_FUNCTION:
        case STENTRY_SYNTH_FUNCTION:
        case STENTRY_UNINTERP_FUNCTION:
            return new SymbolTableEntry(STEKind, static_cast<SortExpr*>(STESort->Clone()));

        case STENTRY_USER_FUNCTION:
            return new SymbolTableEntry(static_cast<FunDefCmd*>(FunDef->Clone()));

        case STENTRY_BVARIABLE:
            return new SymbolTableEntry(static_cast<Term*>(LetBoundTerm->Clone()),
                                        static_cast<SortExpr*>(STESort->Clone()));
        }
        // get the compiler to stop complaining.
        // should never reach here
        return NULL;
    }

    // SymtabScope implementation
    SymbolTableScope::SymbolTableScope()
    {
        // Nothing here
    }

    SymbolTableScope::~SymbolTableScope()
    {
        // delete all the entries
        for (auto const& NameSTEPair : Bindings) {
            delete NameSTEPair.second;
        }
        Bindings.clear();
    }

    SymbolTableEntry* SymbolTableScope::Lookup(const string& Identifier) const
    {
        auto it = Bindings.find(Identifier);
        if(it == Bindings.end()) {
            return NULL;
        }
        return it->second;
    }

    void SymbolTableScope::Bind(const string& Identifier, SymbolTableEntry* STE)
    {
        Bindings[Identifier] = STE;
    }

    void SymbolTableScope::CheckedBind(const string& Identifier, SymbolTableEntry* STE)
    {
        if (Lookup(Identifier) != NULL) {
            throw SymbolTableException((string)"Error: Redeclaration of identifier \"" +
                                       Identifier + "\"");
        }
        Bindings[Identifier] = STE;
    }

    SymbolTableScope* SymbolTableScope::Clone() const
    {
        auto Retval = new SymbolTableScope();
        for(auto const& Binding : Bindings) {
            (Retval->Bindings)[Binding.first] = Binding.second->Clone();
        }
        return Retval;
    }

    // Symbol table implementation
    SymbolTable::SymbolTable()
    {
        // Push the global scope
        Scopes.push_back(new SymbolTableScope());
    }

    SymbolTable::~SymbolTable()
    {
        for(auto const& Scope : Scopes) {
            delete Scope;
        }
    }

    // Utility function for name mangling
    inline string SymbolTable::MangleName(const string& Name,
                                          const vector<const SortExpr*>& ArgSorts) const
    {
        string Retval = Name;
        for(auto const& ArgSort : ArgSorts) {
            auto ActualSort = ResolveSort(ArgSort);
            Retval += "_@_" + ActualSort->ToMangleString();
        }
        return Retval;
    }

    inline string SymbolTable::MangleSortName(const string& Name) const
    {
        return Name + "_@S";
    }

    // Sort resolution
    const SortExpr* SymbolTable::ResolveSort(const SortExpr* TheSort) const
    {
        if(TheSort == NULL) {
            // throw SymbolTableException((string)"Interal: SymbolTable::ResolveSort() " +
            //                            "was called with a NULL argument");
            return NULL;
        }
        if(TheSort->GetKind() != SORTKIND_NAMED) {
            return TheSort;
        }
        auto SortAsNamed = dynamic_cast<const NamedSortExpr*>(TheSort);
        auto NamedEntry = LookupSort(SortAsNamed->GetName());
        return ResolveSort(NamedEntry->GetSort());
    }

    void SymbolTable::Push()
    {
        Scopes.push_back(new SymbolTableScope());
    }

    void SymbolTable::Push(SymbolTableScope* Scope)
    {
        Scopes.push_back(Scope);
    }

    SymbolTableScope* SymbolTable::Pop()
    {
        if (Scopes.size() == 1) {
            throw SymbolTableException("Error: SymbolTable::Pop(), tried to pop too many scopes");
        }
        auto Retval = Scopes.back();
        Scopes.pop_back();
        return Retval;
    }

    const SymbolTableEntry* SymbolTable::Lookup(const string& Identifier) const
    {
        SymbolTableEntry* Retval = NULL;
        const u32 NumScopes = Scopes.size();

        for(u32 i = NumScopes; i > 0; --i) {
            if((Retval = Scopes[i-1]->Lookup(Identifier)) != NULL) {
                return Retval;
            }
        }
        return NULL;
    }

    const SymbolTableEntry* SymbolTable::LookupSort(const string& SortName) const
    {
        auto Retval = Lookup(MangleSortName(SortName));
        if(Retval != NULL && Retval->GetKind() == STENTRY_SORT) {
            return Retval;
        }
        return NULL;
    }

    const SymbolTableEntry* SymbolTable::LookupSortRecursive(const string& SortName) const
    {
        auto Retval = LookupSort(SortName);
        if (Retval != nullptr && Retval->GetKind() == STENTRY_SORT &&
            Retval->GetSort()->GetKind() == SORTKIND_NAMED) {
            const NamedSortExpr* RetvalPrime = static_cast<const NamedSortExpr*>(Retval->GetSort());
            return LookupSortRecursive(RetvalPrime->GetName());
        } else {
            return Retval;
        }
    }

    const SymbolTableEntry* SymbolTable::LookupVariable(const string& VarName) const
    {
        auto Retval = Lookup(VarName);
        if(Retval != NULL && (Retval->GetKind() == STENTRY_QVARIABLE ||
                              Retval->GetKind() == STENTRY_BVARIABLE ||
                              Retval->GetKind() == STENTRY_ARG)) {
            return Retval;
        }
        return NULL;
    }

    const SymbolTableEntry* SymbolTable::LookupFun(const string& Name,
                                                   const vector<const SortExpr*>& ArgSorts) const
    {
        auto MangledName = MangleName(Name, ArgSorts);
        auto Retval = Lookup(MangledName);
        if(Retval != NULL && (Retval->GetKind() == STENTRY_USER_FUNCTION ||
                              Retval->GetKind() == STENTRY_SYNTH_FUNCTION ||
                              Retval->GetKind() == STENTRY_THEORY_FUNCTION ||
                              Retval->GetKind() == STENTRY_UNINTERP_FUNCTION)) {
            return Retval;
        }
        return NULL;
    }

    void SymbolTable::BindSort(const string& Name, SortExpr* Sort)
    {
        Scopes[0]->CheckedBind(MangleSortName(Name),
                                   new SymbolTableEntry(STENTRY_SORT, Sort));
    }

    void SymbolTable::BindVariable(const string& Name, SortExpr* Sort)
    {
        Scopes.back()->CheckedBind(Name, new SymbolTableEntry(STENTRY_QVARIABLE, Sort));
    }

    void SymbolTable::BindFormal(const string& Name, const SortExpr* Sort)
    {
        Scopes.back()->CheckedBind(Name, new SymbolTableEntry(STENTRY_ARG, Sort));
    }

    void SymbolTable::BindLetVariable(const string& Name, Term* LetBoundTerm)
    {
        Scopes.back()->
            CheckedBind(Name,
                        new
                        SymbolTableEntry(static_cast<Term*>(LetBoundTerm->Clone()),
                                         static_cast<SortExpr*>
                                         (LetBoundTerm->GetTermSort(this)->Clone())));
    }

    void SymbolTable::BindTheoryFun(const string& Name,
                                    const vector<const SortExpr*>& ArgSorts,
                                    const SortExpr* RetSort)
    {
        auto FunSort = new FunSortExpr(SourceLocation::None, CloneVector(ArgSorts),
                                       static_cast<const SortExpr*>(RetSort->Clone()));
        auto MangledName = MangleName(Name, ArgSorts);

        Scopes[0]->CheckedBind(MangledName, new SymbolTableEntry(STENTRY_THEORY_FUNCTION, FunSort));
    }

    void SymbolTable::BindUserFun(FunDefCmd* FunDef)
    {
        // get the arg sorts
        vector<const SortExpr*> ArgSorts;
        for(auto const& ASPair : FunDef->GetArgs()) {
            ArgSorts.push_back(ASPair->GetSort());
        }
        auto MangledName = MangleName(FunDef->GetFunName(), ArgSorts);
        Scopes.back()->CheckedBind(MangledName, new SymbolTableEntry(FunDef));
    }

    void SymbolTable::BindSynthFun(const string& Name,
                                   const vector<const SortExpr*>& ArgSorts,
                                   const SortExpr* RetSort)
    {
        auto FunSort = new FunSortExpr(SourceLocation::None, CloneVector(ArgSorts),
                                       static_cast<const SortExpr*>(RetSort->Clone()));
        auto MangledName = MangleName(Name, ArgSorts);
        Scopes.back()->CheckedBind(MangledName,
                                   new SymbolTableEntry(STENTRY_SYNTH_FUNCTION, FunSort));
    }

    void SymbolTable::BindUninterpFun(const string& Name,
                                      const vector<const SortExpr*>& ArgSorts,
                                      const SortExpr* RetSort)
    {
        auto FunSort = new FunSortExpr(SourceLocation::None,
                                       CloneVector(ArgSorts),
                                       static_cast<const SortExpr*>(RetSort->Clone()));
        auto MangledName = MangleName(Name, ArgSorts);
        Scopes.back()->CheckedBind(MangledName, new SymbolTableEntry(STENTRY_UNINTERP_FUNCTION,
                                                                     FunSort));
    }

} /* end namespace */
