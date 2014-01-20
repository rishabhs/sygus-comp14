// Signature.cpp --- 
// 
// Filename: Signature.cpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:53:29 2014 (-0500)
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


#include "Signature.hpp"
#include <boost/functional/hash.hpp>
#include "ConcreteValueBase.hpp"
#include "../exceptions/ESException.hpp"
#include "../solverutils/ConcreteEvaluator.hpp"

namespace ESolver {
    
    Signature::Signature(uint32 Size, uint32 ExpTypeID)
        : HashValue(UNDEFINED_HASH_VALUE), Size(Size), ExpTypeID(ExpTypeID)
    {
        if(Size == 0) {
            ValVec = NULL;
        } else {
            ValVec = (ConcreteValueBase const**)ConcreteEvaluator::SigVecPool->malloc();
        }
    }

    Signature::~Signature()
    {
        // Do not free ValVec, it belongs to the pool
        // the pool will take care of it.
    }

    void Signature::ComputeHashValue() const
    {
        HashValue = 0;
        boost::hash_combine(HashValue, ExpTypeID);
        for(uint32 i = 0; i < Size; ++i) {
            boost::hash_combine(HashValue, ValVec[i]->Hash());
        }
    }

    ConcreteValueBase const*& Signature::operator [] (uint32 Index)
    {
        return ValVec[Index];
    }

    ConcreteValueBase const* Signature::operator [] (uint32 Index) const
    {
        return ValVec[Index];
    }
    
    bool Signature::Equals(const Signature& Other) const
    {
        if(Hash() != Other.Hash()) {
            return false;
        }

        return (ExpTypeID == Other.ExpTypeID && 
                memcmp(ValVec, Other.ValVec, sizeof(ConcreteValueBase*) * Size) == 0);
    }

    bool Signature::DeepEquals(const Signature& Other) const
    {
        if (Hash() != Other.Hash()) {
            return false;
        }
        if (ExpTypeID != Other.ExpTypeID) {
            return false;
        }
        for (uint32 i = 0; i < Size; ++i) {
            if (!ValVec[i]->Equals(*(Other.ValVec[i]))) {
                return false;
            }
        }
        return true;
    }

    bool Signature::operator == (const Signature& Other) const
    {
        return this->Equals(Other);
    }

    uint64 Signature::Hash() const
    {
        if(HashValue == UNDEFINED_HASH_VALUE) {
            ComputeHashValue();
        }
        return HashValue;
    }

    uint32 Signature::GetSize() const
    {
        return Size;
    }

    string Signature::ToString() const
    {
        ostringstream sstr;
        sstr << "<";
        for(uint32 i = 0; i < Size; ++i) {
            sstr << ValVec[i]->ToString();
            if(i != Size - 1) {
                sstr << ", ";
            }
        }
        sstr << ">";
        return sstr.str();
    }

    ostream& operator << (ostream& str, const Signature& VVec)
    {
        str << VVec.ToString();
        return str;
    }
    
} /* End namespace */


// 
// Signature.cpp ends here
