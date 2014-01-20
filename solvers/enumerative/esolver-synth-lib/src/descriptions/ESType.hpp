// ESType.hpp --- 
// 
// Filename: ESType.hpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:51:59 2014 (-0500)
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


#if !defined __ESOLVER_ES_TYPE_HPP
#define __ESOLVER_ES_TYPE_HPP

#include "../common/ESolverForwardDecls.hpp"
#include "../exceptions/ESException.hpp"
#include "../utils/UIDGenerator.hpp"
#include <map>
#include "../z3interface/Z3TheoremProver.hpp"

namespace ESolver {

    enum BaseType {
        BaseTypeBool,
        BaseTypeInt,
        BaseTypeSet,
        BaseTypeEnum,
        BaseTypeBitVector,
        BaseTypeReal,
        BaseTypeArray,
        BaseTypeFunction,
        // Insert any additional base types
        // before this line
        BaseTypeUndefined = UINT32_MAX
    };

    // forward declarations

    class ESTypeBase
    {
    protected:
        BaseType BType;
        TypeID TypeUID;
        mutable bool HashValid;
        mutable uint64 HashValue;

        virtual void ComputeHashValue() const = 0;
        
    public:
        ESTypeBase(BaseType BType);
        virtual ~ESTypeBase();

        BaseType GetBaseType() const;
        TypeID GetID() const;
        uint64 Hash() const;

        virtual bool Equals(const ESTypeBase& Other) const = 0;
        virtual string ToString() const = 0;
        virtual string ToSimpleString() const = 0;
        

        // Two level API
        template<typename T>
        T* As()
        {
            return dynamic_cast<T*>(this);
        }

        template<typename T>
        const T* As() const
        {
            return dynamic_cast<const T*>(this);
        }
    };

    // Subclass for fixed types, in the event that 
    // support for generic types will be added later
    class ESFixedTypeBase : public ESTypeBase
    {
    protected:
        SMTType TPType;
        
    public:
        ESFixedTypeBase(BaseType BType, SMTType TPType);
        virtual ~ESFixedTypeBase();

        virtual SMTType GetSMTType() const;
    };

    class ESIntType : public ESFixedTypeBase
    {
    protected:
        virtual void ComputeHashValue() const override;

    public:
        ESIntType();
        ESIntType(TheoremProver* TP);
        virtual ~ESIntType();

        virtual bool Equals(const ESTypeBase& Other) const override;
        virtual string ToString() const override;
        virtual string ToSimpleString() const override;
    };
    
    class ESBoolType : public ESFixedTypeBase
    {
    protected:
        virtual void ComputeHashValue() const override;

    public:
        ESBoolType();
        ESBoolType(TheoremProver* TP);
        virtual ~ESBoolType();
        
        virtual bool Equals(const ESTypeBase& Other) const override;
        virtual string ToString() const override;
        virtual string ToSimpleString() const override;
    };

    class ESRealType : public ESFixedTypeBase
    {
    protected:
        virtual void ComputeHashValue() const override;

    public:
        ESRealType();
        ESRealType(TheoremProver* TP);
        virtual ~ESRealType();

        virtual bool Equals(const ESTypeBase& Other) const override;
        virtual string ToString() const override;
        virtual string ToSimpleString() const override;
    };

    class ESEnumType : public ESFixedTypeBase
    {
    protected:
        virtual void ComputeHashValue() const override;

    private:
        map<EnumValueID, string> EnumValueIDToNameMap;
        map<string, EnumValueID> EnumNameToValueIDMap;
        vector<EnumValueID> EnumValueIDs;
        set<string> EnumTypeConstructorSet;
        set<EnumValueID> EnumValueIDSet;
        string EnumTypeName;

    public:
        ESEnumType(const string& EnumTypeName,
                   const vector<string>& EnumConstructors);
        ESEnumType(TheoremProver* TP,
                   const string& EnumTypeName,
                   const vector<string>& EnumConstructors);
        virtual ~ESEnumType();
        
        virtual bool Equals(const ESTypeBase& Other) const override;
        virtual string ToString() const override;
        virtual string ToSimpleString() const override;

        const string& GetName() const;
        const vector<EnumValueID> GetEnumValueIDVec() const;
        EnumValueID GetEnumValueIDForName(const string& Name) const;
        const string& GetEnumValueNameForID(EnumValueID EVID) const;
        bool IsValidEnumConstructor(const string& EnumConstructor) const;
        bool IsValidEnumID(EnumValueID EVID) const;
    };

    class ESBVType : public ESFixedTypeBase
    {
    protected:
        virtual void ComputeHashValue() const override;

    private:
        uint32 Size;

    public:
        ESBVType(uint32 Size);
        ESBVType(TheoremProver* TP, uint32 Size);
        virtual ~ESBVType();

        virtual bool Equals(const ESTypeBase& Other) const override;
        virtual string ToString() const override;
        virtual string ToSimpleString() const override;
        
        uint32 GetSize() const;
    };

    class ESArrayType : public ESFixedTypeBase
    {
    protected:
        virtual void ComputeHashValue() const override;

    private:
        const ESFixedTypeBase* IndexType;
        const ESFixedTypeBase* ValueType;

    public:
        ESArrayType(const ESFixedTypeBase* IndexType,
                    const ESFixedTypeBase* ValueType);
        ESArrayType(TheoremProver* TP, 
                    const ESFixedTypeBase* IndexType, 
                    const ESFixedTypeBase* ValueType);
        virtual ~ESArrayType();
        
        virtual bool Equals(const ESTypeBase& Other) const override;
        virtual string ToString() const override;
        virtual string ToSimpleString() const override;

        const ESFixedTypeBase* GetIndexType() const;
        const ESFixedTypeBase* GetValueType() const;
    };

    class ESSetType : public ESFixedTypeBase
    {
    protected:
        virtual void ComputeHashValue() const override;

    private:
        const ESFixedTypeBase* ElementType;

    public:
        ESSetType(const ESFixedTypeBase* ElementType);
        ESSetType(TheoremProver* TP, const ESFixedTypeBase* ElementType);
        virtual ~ESSetType();

        virtual bool Equals(const ESTypeBase& Other) const override;
        virtual string ToString() const override;
        virtual string ToSimpleString() const override;

        const ESFixedTypeBase* GetElementType() const;
    };

    class ESFunctionType : public ESFixedTypeBase
    {
    protected:
        virtual void ComputeHashValue() const override;

    private:
        vector<const ESFixedTypeBase*> DomainTypes;
        const ESFixedTypeBase* RangeType;

    public:
        ESFunctionType(const vector<const ESFixedTypeBase*>& DomainTypes,
                       const ESFixedTypeBase* RangeType);

        ESFunctionType(TheoremProver* TP,
                       const vector<const ESFixedTypeBase*>& DomainTypes,
                       const ESFixedTypeBase* RangeType);
        virtual ~ESFunctionType();

        virtual SMTType GetSMTType() const override;
        virtual bool Equals(const ESTypeBase& Other) const override;
        virtual string ToString() const override;
        virtual string ToSimpleString() const override;
        
        const vector<const ESFixedTypeBase*>& GetDomainTypes() const;
        const ESFixedTypeBase* GetRangeType() const;
        string GetMangleSuffix() const;
    };

    extern UIDGenerator TypeUIDGenerator;
    extern UIDGenerator EnumValueUIDGenerator;

} /* End namespace */

#endif /* __ESOLVER_ES_TYPE_HPP */


// 
// ESType.hpp ends here
