// ValueManager.cpp --- 
// 
// Filename: ValueManager.cpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:53:26 2014 (-0500)
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


#include "ValueManager.hpp"
#include "ConcreteValueBase.hpp"

namespace ESolver {

    ValueManager::ValueManager()
    {
        // CVSet.set_empty_key(NULL);
        ValuePool = new boost::pool<>(sizeof(ConcreteValueBase));
    }
    
    ValueManager::~ValueManager()
    {
        delete ValuePool;
    }

    const ConcreteValueBase* ValueManager::GetValue(const ESFixedTypeBase* Type, int64 TheValue)
    {
        ConcreteValueBase ThisValue(Type, TheValue);
        auto CachedIt = CVSet.find(&ThisValue);
        if(CachedIt != CVSet.end()) {
            return *CachedIt;
        } else {
            auto Retval = new (ValuePool->malloc()) ConcreteValueBase(Type, TheValue);
            CVSet.insert(Retval);
            return Retval;
        }
    }

    const ConcreteValueBase* ValueManager::GetValueNT(const ESFixedTypeBase* Type,
                                                      int64 TheValue)
    {
        ConcreteValueBase* ThisValue = new ConcreteValueBase(Type, TheValue);
        return ThisValue;
    }

    void ValueManager::Clear()
    {
        // Deleting the pool will clear all the values
    }

    uint64 ValueManager::GetNumConcreteValues() const
    {
        return CVSet.size();
    }

} /* End namespace */


// 
// ValueManager.cpp ends here
