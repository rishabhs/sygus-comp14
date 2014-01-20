// TypeManager.cpp --- 
// 
// Filename: TypeManager.cpp
// Author: Abhishek Udupa
// Created: Wed Jan  1 20:54:39 2014 (-0500)
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
//    This product includes software developed by the University of Pennsylvania.
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

#include "TypeManager.hpp"
#include "../descriptions/ESType.hpp"
#include "../z3interface/TheoremProver.hpp"

namespace ESolver {

    TypeManager::TypeManager(TheoremProver* TP)
        : TP(TP)
    {
        // Nothing here
    }

    TypeManager::~TypeManager()
    {
        for (auto const& Type : TheTypeSet) {
            delete Type;
        }
        TheTypeSet.clear();
        TheTypeMap.clear();
    }

    void TypeManager::BindType(const string& Typename, const ESFixedTypeBase* Type)
    {
        TheTypeMap[Typename] = const_cast<ESFixedTypeBase*>(Type);
    }

    const ESFixedTypeBase* TypeManager::LookupType(const string& TypeName) const
    {
        auto it = TheTypeMap.find(TypeName);
        if (it == TheTypeMap.end()) {
            return nullptr;
        } else {
            return it->second;
        }
    }

} /* end namespace */

// 
// TypeManager.cpp ends here
