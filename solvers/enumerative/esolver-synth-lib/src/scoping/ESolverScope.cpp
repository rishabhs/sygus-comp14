// ESolverScope.cpp --- 
// 
// Filename: ESolverScope.cpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:54:43 2014 (-0500)
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


#include "ESolverScope.hpp"
#include "../descriptions/Operators.hpp"

namespace ESolver {

    ESolverScope::ESolverScope(bool Anonymous)
        : Anonymous(Anonymous)
    {
        // Nothing here
    }

    ESolverScope::~ESolverScope()
    {
        // Delete all the added operators
        for (auto const& NameOp : OperatorMap) {
            delete NameOp.second;
        }
    }

    void ESolverScope::AddOperator(OperatorBase* Op)
    {
        OperatorMap[Op->GetMangledName()] = Op;
    }

    OperatorBase* ESolverScope::LookupOperator(const string& OperatorName)
    {
        auto it = OperatorMap.find(OperatorName);
        if (it == OperatorMap.end()) {
            return nullptr;
        }
        return it->second;
    }

    FuncOperatorBase* ESolverScope::LookupOperator(const string& OperatorName,
                                                   const vector<const ESFixedTypeBase*>& ArgTypes)
    {
        auto const& MangledName = FuncOperatorBase::MangleName(OperatorName, ArgTypes);
        return LookupOperator(MangledName)->As<FuncOperatorBase>();
    }

    bool ESolverScope::IsAnonymous() const
    {
        return Anonymous;
    }

} /* End namespace */

// 
// ESolverScope.cpp ends here
