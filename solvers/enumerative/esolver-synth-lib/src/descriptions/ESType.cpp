// ESType.cpp --- 
// 
// Filename: ESType.cpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:56:08 2014 (-0500)
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


#include "ESType.hpp"
#include <ctype.h>
#include <boost/functional/hash.hpp>
#include "../z3interface/TheoremProver.hpp"

namespace ESolver {

    UIDGenerator TypeUIDGenerator;
    UIDGenerator EnumValueUIDGenerator;

    ESTypeBase::ESTypeBase(BaseType BType)
        : BType(BType), TypeUID((TypeID)TypeUIDGenerator.GetUID()),
          HashValid(false)
    {
        // Nothng here
    }

    ESTypeBase::~ESTypeBase()
    {
        // Nothing here
    }

    BaseType ESTypeBase::GetBaseType() const
    {
        return BType;
    }

    TypeID ESTypeBase::GetID() const
    {
        return TypeUID;
    }

    uint64 ESTypeBase::Hash() const
    {
        if (!HashValid) {
            ComputeHashValue();
            HashValid = true;
        }
        return HashValue;
    }

    ESFixedTypeBase::ESFixedTypeBase(BaseType BType, SMTType TPType)
        : ESTypeBase(BType), TPType(TPType)
    {
        // Nothing here
    }

    ESFixedTypeBase::~ESFixedTypeBase()
    {
        TPType = SMTType();
    }

    SMTType ESFixedTypeBase::GetSMTType() const
    {
        return TPType;
    }

    ESIntType::ESIntType(TheoremProver* TP)
        : ESFixedTypeBase(BaseTypeInt, TP->CreateIntType())
    {
        // Nothing here
    }

    ESIntType::ESIntType()
        : ESFixedTypeBase(BaseTypeInt, SMTType())
    {
        // Nothing here
    }

    ESIntType::~ESIntType()
    {
        // Nothing here
    }

    bool ESIntType::Equals(const ESTypeBase& Other) const
    {
        return (Other.As<ESIntType>() != nullptr);
    }

    string ESIntType::ToString() const
    {
        return "Int";
    }

    string ESIntType::ToSimpleString() const
    {
        return ToString();
    }

    void ESIntType::ComputeHashValue() const
    {
        HashValid = true;
        HashValue = boost::hash_value(ToString());
    }

    ESBoolType::ESBoolType(TheoremProver* TP)
        : ESFixedTypeBase(BaseTypeBool, TP->CreateBoolType())
    {
        // Nothing here
    }

    ESBoolType::ESBoolType()
        : ESFixedTypeBase(BaseTypeBool, SMTType())
    {
        // Nothing here
    }

    ESBoolType::~ESBoolType()
    {
        // Nothing here
    }

    void ESBoolType::ComputeHashValue() const
    {
        HashValid = true;
        HashValue = boost::hash_value(ToString());
    }

    string ESBoolType::ToString() const
    {
        return "Bool";
    }

    string ESBoolType::ToSimpleString() const
    {
        return ToString();
    }

    bool ESBoolType::Equals(const ESTypeBase& Other) const
    {
        return (Other.As<ESBoolType>() != nullptr);
    }

    ESRealType::ESRealType(TheoremProver* TP)
        : ESFixedTypeBase(BaseTypeReal, TP->CreateRealType())
    {
        // Nothing here
    }

    ESRealType::ESRealType()
        : ESFixedTypeBase(BaseTypeReal, SMTType())
    {
        // Nothing here
    }

    ESRealType::~ESRealType()
    {
        // Nothing here
    }

    void ESRealType::ComputeHashValue() const
    {
        HashValid = true;
        HashValue = boost::hash_value(ToString());
    }

    string ESRealType::ToString() const
    {
        return "Real";
    }

    string ESRealType::ToSimpleString() const
    {
        return ToString();
    }

    bool ESRealType::Equals(const ESTypeBase& Other) const
    {
        return (Other.As<ESRealType>() != nullptr);
    }

    ESEnumType::ESEnumType(const string& EnumTypeName,
                           const vector<string>& EnumConstructors)
        : ESFixedTypeBase(BaseTypeEnum, SMTType()), EnumTypeName(EnumTypeName)
    {
        for (auto const& Constructor : EnumConstructors) {
            EnumTypeConstructorSet.insert(Constructor);
            auto ValUID = (EnumValueID)EnumValueUIDGenerator.GetUID();
            EnumValueIDToNameMap[ValUID] = Constructor;
            EnumNameToValueIDMap[Constructor] = ValUID;
            EnumValueIDSet.insert(ValUID);
            EnumValueIDs.push_back(ValUID);
        }
    }

    ESEnumType::ESEnumType(TheoremProver* TP, const string& EnumTypeName,
                           const vector<string>& EnumConstructors)
        : ESFixedTypeBase(BaseTypeEnum, SMTType()), EnumTypeName(EnumTypeName)
    {
        for (auto const& Constructor : EnumConstructors) {
            EnumTypeConstructorSet.insert(Constructor);
            auto ValUID = (EnumValueID)EnumValueUIDGenerator.GetUID();
            EnumValueIDToNameMap[ValUID] = Constructor;
            EnumNameToValueIDMap[Constructor] = ValUID;
            EnumValueIDSet.insert(ValUID);
            EnumValueIDs.push_back(ValUID);
        }

        TPType = TP->CreateEnumType(EnumTypeName, EnumConstructors);
    }

    ESEnumType::~ESEnumType()
    {
        // Nothing here
    }

    bool ESEnumType::Equals(const ESTypeBase& Other) const
    {
        auto OtherPtr = Other.As<ESEnumType>();
        if (OtherPtr == nullptr) {
            return false;
        }

        if (EnumTypeName != OtherPtr->EnumTypeName) {
            return false;
        }

        if (OtherPtr->EnumTypeConstructorSet.size() != EnumTypeConstructorSet.size()) {
            return false;
        }

        for (auto it = EnumTypeConstructorSet.begin(); it != EnumTypeConstructorSet.end(); ++it) {
            if (OtherPtr->EnumTypeConstructorSet.find(*it) == OtherPtr->EnumTypeConstructorSet.end()) {
                return false;
            }
        }
        return true;
    }

    void ESEnumType::ComputeHashValue() const
    {
        HashValid = true;
        HashValue = (uint64)0;
        boost::hash_combine(HashValue, EnumTypeName);
        for (auto const& Constructor : EnumTypeConstructorSet) {
            boost::hash_combine(HashValue, Constructor);
        }
    }
    
    string ESEnumType::ToString() const
    {
        ostringstream sstr;
        sstr << "(Enum " << EnumTypeName;
        for (auto const& Constructor : EnumTypeConstructorSet) {
            sstr << " " << Constructor;
        }
        sstr << ")" << endl;
        return sstr.str();
    }

    string ESEnumType::ToSimpleString() const
    {
        ostringstream sstr;
        sstr << "(Enum " << EnumTypeName << ")";
        return sstr.str();
    }

    const string& ESEnumType::GetName() const
    {
        return EnumTypeName;
    }

    const vector<EnumValueID> ESEnumType::GetEnumValueIDVec() const
    {
        return EnumValueIDs;
    }

    EnumValueID ESEnumType::GetEnumValueIDForName(const string& Name) const
    {
        map<string, EnumValueID>::const_iterator it;
        if ((it = EnumNameToValueIDMap.find(Name)) == EnumNameToValueIDMap.end()) {
            throw TypeException((string)"Error: Enum constructor \"" + Name + "\" is not a " + 
                                "valid constructor for enum type \"" + EnumTypeName + "\"");
        }
        return it->second;
    }

    const string& ESEnumType::GetEnumValueNameForID(EnumValueID EVID) const
    {
        map<EnumValueID, string>::const_iterator it;
        if ((it = EnumValueIDToNameMap.find(EVID)) == EnumValueIDToNameMap.end()) {
            throw TypeException((string)"Error: Enum value \"" + to_string(EVID) + "\" is not a " + 
                                "valid value for enum type \"" + EnumTypeName + "\"");
        }
        return it->second;
    }

    bool ESEnumType::IsValidEnumConstructor(const string& EnumConstructor) const
    {
        return (EnumTypeConstructorSet.find(EnumConstructor) != EnumTypeConstructorSet.end());
    }

    bool ESEnumType::IsValidEnumID(EnumValueID EVID) const
    {
        return (EnumValueIDSet.find(EVID) != EnumValueIDSet.end());
    }

    ESBVType::ESBVType(TheoremProver* TP, uint32 Size)
        : ESFixedTypeBase(BaseTypeBitVector, TP->CreateBVType(Size)), Size(Size)
    {
        // Nothing here
    }

    ESBVType::ESBVType(uint32 Size)
        : ESFixedTypeBase(BaseTypeBitVector, SMTType()), Size(Size)
    {
        // Nothing here
    }

    ESBVType::~ESBVType()
    {
        // Nothing here
    }

    void ESBVType::ComputeHashValue() const
    {
        HashValid = true;
        HashValue = boost::hash_value("BVType");
        boost::hash_combine(HashValue, Size);
    }

    string ESBVType::ToString() const
    {
        return ((string)"(BitVec " + to_string(Size) + ")");
    }

    string ESBVType::ToSimpleString() const
    {
        return ToString();
    }

    bool ESBVType::Equals(const ESTypeBase& Other) const
    {
        auto OtherPtr = Other.As<ESBVType>();
        if (OtherPtr == nullptr) {
            return false;
        } 
        return (Size == OtherPtr->Size);
    }

    uint32 ESBVType::GetSize() const
    {
        return Size;
    }

    ESArrayType::ESArrayType(TheoremProver* TP,
                             const ESFixedTypeBase* IndexType,
                             const ESFixedTypeBase* ValueType)
        : ESFixedTypeBase(BaseTypeArray, TP->CreateArrayType(IndexType->GetSMTType(),
                                                             ValueType->GetSMTType())),
          IndexType(IndexType), ValueType(ValueType)
    {
        // Nothing here
    }
                
    ESArrayType::ESArrayType(const ESFixedTypeBase* IndexType,
                             const ESFixedTypeBase* ValueType)
        : ESFixedTypeBase(BaseTypeArray, SMTType()),
          IndexType(IndexType), ValueType(ValueType)
    {
        // Nothing here
    }

    ESArrayType::~ESArrayType()
    {
        // Nothing here
    }

    void ESArrayType::ComputeHashValue() const
    {
        HashValid = true;
        HashValue = boost::hash_value("ArrayType");
        boost::hash_combine(HashValue, IndexType->Hash());
        boost::hash_combine(HashValue, ValueType->Hash());
    }

    bool ESArrayType::Equals(const ESTypeBase& Other) const
    {
        auto OtherPtr = Other.As<ESArrayType>();
        if (OtherPtr == nullptr) {
            return false;
        }
        
        return (OtherPtr->IndexType->Equals(*IndexType) &&
                OtherPtr->ValueType->Equals(*ValueType));
    }

    string ESArrayType::ToString() const
    {
        ostringstream sstr;
        sstr << "(Array" << IndexType->ToString() << " "
             << ValueType->ToString() << ")";
        return sstr.str();
    }

    string ESArrayType::ToSimpleString() const
    {
        return "Array";
    }

    const ESFixedTypeBase* ESArrayType::GetIndexType() const
    {
        return IndexType;
    }

    const ESFixedTypeBase* ESArrayType::GetValueType() const
    {
        return ValueType;
    }

    ESSetType::ESSetType(TheoremProver* TP,
                         const ESFixedTypeBase* ElementType)
        : ESFixedTypeBase(BaseTypeSet, TP->CreateSetType(ElementType->GetSMTType())), 
          ElementType(ElementType)
    {
        // Nothing here
    }

    ESSetType::ESSetType(const ESFixedTypeBase* ElementType)
        : ESFixedTypeBase(BaseTypeSet, SMTType()), 
          ElementType(ElementType)
    {
        // Nothing here
    }

    ESSetType::~ESSetType()
    {
        // Nothing here
    }

    bool ESSetType::Equals(const ESTypeBase& Other) const
    {
        auto OtherPtr = Other.As<ESSetType>();
        if (OtherPtr == nullptr) {
            return false;
        }
        return (OtherPtr->ElementType->Equals(*ElementType));
    }

    string ESSetType::ToString() const
    {
        return "(SetType " + ElementType->ToString() + ")";
    }

    string ESSetType::ToSimpleString() const
    {
        return "SetType";
    }

    void ESSetType::ComputeHashValue() const
    {
        HashValid = true;
        HashValue = boost::hash_value("SetType");
        boost::hash_combine(HashValue, ElementType->Hash());
    }
    
    const ESFixedTypeBase* ESSetType::GetElementType() const
    {
        return ElementType;
    }

    ESFunctionType::ESFunctionType(const vector<const ESFixedTypeBase*>& DomainTypes,
                                   const ESFixedTypeBase* RangeType)
        : ESFixedTypeBase(BaseTypeFunction, SMTType()),
          DomainTypes(DomainTypes), RangeType(RangeType)
    {
        // Nothing here
    }

    ESFunctionType::ESFunctionType(TheoremProver* /* TP */,
                                   const vector<const ESFixedTypeBase*>& DomainTypes,
                                   const ESFixedTypeBase* RangeType)
        : ESFixedTypeBase(BaseTypeFunction, SMTType()), DomainTypes(DomainTypes),
          RangeType(RangeType)
    {
        // Nothing here
    }

    ESFunctionType::~ESFunctionType()
    {
        // Nothing here
    }

    void ESFunctionType::ComputeHashValue() const
    {
        HashValid = true;
        HashValue = boost::hash_value("FuncType");
        for (auto const& DomainType : DomainTypes) {
            boost::hash_combine(HashValue, DomainType->Hash());
        }
        boost::hash_combine(HashValue, RangeType->Hash());
    }

    bool ESFunctionType::Equals(const ESTypeBase& Other) const
    {
        auto OtherPtr = Other.As<ESFunctionType>();
        if (OtherPtr == nullptr) {
            return false;
        }
        if (OtherPtr->DomainTypes.size() != DomainTypes.size()) {
            return false;
        }

        const uint32 NumArgs = DomainTypes.size();
        for (uint32 i = 0; i < NumArgs; ++i) {
            if (!OtherPtr->DomainTypes[i]->Equals(*DomainTypes[i])) {
                return false;
            }
        }
        return (OtherPtr->RangeType->Equals(*RangeType));
    }

    string ESFunctionType::ToString() const
    {
        ostringstream sstr;
        sstr << "(FunctionType";
        for (auto const& DomainType : DomainTypes) {
            sstr << " " << DomainType->ToString();
        }
        sstr << " -> " << RangeType->ToString() << ")";
        return sstr.str();
    }

    string ESFunctionType::ToSimpleString() const
    {
        return "FunctionType";
    }
    
    const vector<const ESFixedTypeBase*>& ESFunctionType::GetDomainTypes() const
    {
        return DomainTypes;
    }

    const ESFixedTypeBase* ESFunctionType::GetRangeType() const
    {
        return RangeType;
    }

    string ESFunctionType::GetMangleSuffix() const
    {
        ostringstream sstr;
        for (auto const& DomainType : DomainTypes) {
            sstr << "@" << DomainType->GetID();
        }
        return sstr.str();
    }

    SMTType ESFunctionType::GetSMTType() const
    {
        throw InternalError((string)"Internal Error: ESFunctionType::GetSMTType() must never have been called.\n" + 
                            "At " + __FILE__ + ":" + to_string(__LINE__));
    }

} /* End namespace */


// 
// ESType.cpp ends here
