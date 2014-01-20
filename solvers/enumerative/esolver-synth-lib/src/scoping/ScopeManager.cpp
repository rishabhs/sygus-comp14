// ScopeManager.cpp --- 
// 
// Filename: ScopeManager.cpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:54:46 2014 (-0500)
// 
// 
// Copyright (c) 2013, Abhishek Udupa, University of Pennsylvania
// All rights reserved.
// 
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in the
//    documentation and/or other materials provided with the distribution.
// 3. All advertising materials mentioning features or use of this software
//    must display the following acknowledgement:
//    This product includes software developed by The University of Pennsylvania
// 4. Neither the name of the University of Pennsylvania nor the
//    names of its contributors may be used to endorse or promote products
//    derived from this software without specific prior written permission.
// 
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER ''AS IS'' AND ANY
// EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
// WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
// DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
// DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
// (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
// LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
// ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
// SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
// 
// 

// Code:


#include "ScopeManager.hpp"
#include "ESolverScope.hpp"
#include "../descriptions/Operators.hpp"
#include "../exceptions/ESException.hpp"

namespace ESolver {

    ScopeManager::ScopeManager()
    {
        // Push a default scope
        ScopeStack.push_back(new ESolverScope(true));
    }

    ScopeManager::~ScopeManager()
    {
        while(ScopeStack.size() > 1) {
            PopScope();
        }
        delete ScopeStack.back();
        ScopeStack.pop_back();
        for (auto const& NameScope : ScopeMap) {
            delete NameScope.second;
        }
    }

    void ScopeManager::PushScope(const string& ScopeName)
    {
        auto it = ScopeMap.find(ScopeName);
        if (it != ScopeMap.end()) {
            ScopeStack.push_back(it->second);
        } else {
            auto NewScope = new ESolverScope();
            ScopeMap[ScopeName] = NewScope;
            ScopeStack.push_back(NewScope);
        }
    }

    void ScopeManager::PushScope()
    {
        ScopeStack.push_back(new ESolverScope(true));
    }

    void ScopeManager::ReplaceScope(const string& ScopeName)
    {
        PopScope();
        PushScope(ScopeName);
    }

    void ScopeManager::PopScope()
    {
        if (ScopeStack.size() <= 1) {
            throw ContextException("Popped too many scopes");
        }
        auto PoppedScope = ScopeStack.back();
        ScopeStack.pop_back();
        if (PoppedScope->IsAnonymous()) {
            delete PoppedScope;
        }
    }

    void ScopeManager::DestroyScope(const string& ScopeName)
    {
        auto it = ScopeMap.find(ScopeName);
        if (it == ScopeMap.end()) {
            return;
        }
        delete it->second;
        ScopeMap.erase(it);
    }

    OperatorBase* ScopeManager::LookupOperator(const string& OperatorName) const
    {
        const uint32 NumScopes = ScopeStack.size();
        for (uint32 i = NumScopes; i > 0; --i) {
            auto Retval = ScopeStack[i - 1]->LookupOperator(OperatorName);
            if (Retval != nullptr) {
                return Retval;
            }
        }
        return nullptr;
    }

    FuncOperatorBase* ScopeManager::LookupOperator(const string& OperatorName,
                                                   const vector<const ESFixedTypeBase*>& ArgTypes) const
    {
        auto MangledName = FuncOperatorBase::MangleName(OperatorName, ArgTypes);
        return LookupOperator(MangledName)->As<FuncOperatorBase>();
    }

    void ScopeManager::AddOperator(OperatorBase* Op, bool ToBottom)
    {
        if (ToBottom) {
            ScopeStack[0]->AddOperator(Op);
        } else {
            ScopeStack.back()->AddOperator(Op);
        }
    }

} /* End namespace */


// 
// ScopeManager.cpp ends here
