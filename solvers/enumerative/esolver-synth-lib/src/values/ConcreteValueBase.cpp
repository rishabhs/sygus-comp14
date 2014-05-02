// ConcreteValueBase.cpp --- 
// 
// Filename: ConcreteValueBase.cpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:53:22 2014 (-0500)
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


#include "ConcreteValueBase.hpp"
#include "../solvers/ESolver.hpp"
#include "../descriptions/ESType.hpp"
#include "../utils/TextUtils.hpp"
#include "../external/spookyhash/SpookyHash.hpp"
#include "../z3interface/TheoremProver.hpp"

namespace ESolver {

    ConcreteValueBase::ConcreteValueBase()
        : TheValue(-1), Type(nullptr), HashValue(UNDEFINED_HASH_VALUE)
    {
        // Nothing here
    }

    ConcreteValueBase::ConcreteValueBase(const ESFixedTypeBase* Type, int64 TheValue)
        : TheValue(TheValue), Type(Type), HashValue((uint32)UNDEFINED_HASH_VALUE)
    {
        // Nothing here
    }

    ConcreteValueBase::ConcreteValueBase(const ConcreteValueBase& Other)
        : TheValue(Other.TheValue), Type(Other.Type), HashValue(Other.HashValue)
    {
        // Nothing here
    }

    ConcreteValueBase::~ConcreteValueBase()
    {
        // Nothing here
    }

    void ConcreteValueBase::ComputeHashValue() const
    {
        HashValue = (uint64)0;
        boost::hash_combine(HashValue, Type->Hash());
        boost::hash_combine(HashValue, TheValue);
        return;
    }

    bool ConcreteValueBase::Equals(const ConcreteValueBase& Other) const
    {
        // Types and values need to match
        return (Other.Type->GetID() == Type->GetID() && 
                Other.TheValue == TheValue);
    }

    inline string ConcreteValueBase::IntToString(bool Simple) const
    {
        ostringstream sstr;
        sstr << TheValue;
        return sstr.str();
    }

    inline string ConcreteValueBase::BoolToString(bool Simple) const
    {
        return (TheValue == 0 ? "false" : "true");
    }

    inline string ConcreteValueBase::BVToString(bool Simple) const
    {
        ostringstream sstr;
        auto Type = static_cast<const ESBVType*>(this->Type);
        auto Size = Type->GetSize();
        if (Size % 4 == 0) {
            sstr << "#x" << setw(Size/4) << setfill('0') << hex << TheValue;
        } else {
            sstr << "#b";
            for (uint32 i = Size; i > 0; --i) {
                uint64 Mask;
                if (i == 1) {
                    Mask = 1;
                } else {
                    Mask = (uint64)1 << (i - 1);
                }
                if ((Mask & TheValue) != 0) {
                    sstr << "1";
                } else {
                    sstr << "0";
                }
            }
        }
        return sstr.str();
    }


    inline string ConcreteValueBase::EnumTypeToString(bool Simple) const
    {
        return static_cast<const ESEnumType*>(Type)->GetEnumValueNameForID((EnumValueID)TheValue);
    }

    string ConcreteValueBase::ToString() const
    {
        ostringstream sstr;
        if(Type == NULL) {
            sstr << "Undefined";
            return sstr.str();
        }
        switch(Type->GetBaseType()) {
        case BaseTypeBool:
            return BoolToString();
        case BaseTypeInt:
            return IntToString();
        case BaseTypeEnum:
            return EnumTypeToString();
        case BaseTypeBitVector:
            return BVToString();
        default:
            return "(Undefined: due to weird type)";
        }
    }

    string ConcreteValueBase::ToSimpleString() const
    {
        ostringstream sstr;
        if(Type == NULL) {
            sstr << "Undefined";
            return sstr.str();
        }
        switch(Type->GetBaseType()) {
        case BaseTypeBool:
            return BoolToString(true);
        case BaseTypeInt:
            return IntToString(true);
        case BaseTypeEnum:
            return EnumTypeToString(true);
        case BaseTypeBitVector:
            return BVToString(true);
        default:
            return "(Undefined: due to weird type)";
        }
    }

    int64 ConcreteValueBase::GetValue() const
    {
        return TheValue;
    }

    inline SMTExpr ConcreteValueBase::IntToSMT(TheoremProver* TP) const
    {
        return TP->CreateIntConstant((int32)TheValue);
    }

    inline SMTExpr ConcreteValueBase::BoolToSMT(TheoremProver* TP) const
    {
        return (TheValue == 0 ? TP->CreateFalseExpr() : TP->CreateTrueExpr());
    }

    inline SMTExpr ConcreteValueBase::EnumTypeToSMT(TheoremProver* TP) const
    {
        const string& EnumValueName = 
            static_cast<const ESEnumType*>(Type)->GetEnumValueNameForID((EnumValueID)TheValue);
        return TP->CreateEnumConstant(EnumValueName);
    }

    inline SMTExpr ConcreteValueBase::BVToSMT(TheoremProver* TP) const
    {
        return TP->CreateBVConstant((uint64)TheValue, static_cast<const ESBVType*>(Type)->GetSize());
    }

    SMTExpr ConcreteValueBase::ToSMT(TheoremProver* TP) const
    {
        switch(Type->GetBaseType()) {
        case BaseTypeBool:
            return BoolToSMT(TP);
        case BaseTypeInt:
            return IntToSMT(TP);
        case BaseTypeEnum:
            return EnumTypeToSMT(TP);
        case BaseTypeBitVector:
            return BVToSMT(TP);
        default:
            assert(false);
        }
    }

    bool ConcreteValueBase::operator == (const ConcreteValueBase& Other) const
    {
        return Equals(Other);
    }

    bool ConcreteValueBase::operator != (const ConcreteValueBase& Other) const
    {
        return !(Equals(Other));
    }

    const ESFixedTypeBase* ConcreteValueBase::GetType() const
    {
        return Type;
    }

    uint64 ConcreteValueBase::Hash() const
    {
        if(UNLIKELY(HashValue == (uint32)UNDEFINED_HASH_VALUE)) {
            ComputeHashValue();
        }
        return HashValue;
    }

    void ConcreteValueBase::Set(const ESFixedTypeBase* Type, int64 TheValue)
    {
        this->Type = Type;
        this->TheValue = TheValue;
    }
    
} /* End namespace */


// 
// ConcreteValueBase.cpp ends here
