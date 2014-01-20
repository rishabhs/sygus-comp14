// Operators.cpp --- 
// 
// Filename: Operators.cpp
// Author: Abhishek Udupa
// Created: Wed Jan  1 18:19:48 2014 (-0500)
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

#include "Operators.hpp"
#include "../descriptions/ESType.hpp"
#include "FunctorBase.hpp"
#include <boost/functional/hash.hpp>
#include "../descriptions/Grammar.hpp"

namespace ESolver {

    UIDGenerator OpUIDGenerator;
    UIDGenerator AnonConstUIDGenerator;

    OperatorBase::OperatorBase(const string& Name, const string& MangledName,
                               const ESFixedTypeBase* Type, uint32 Cost)
        : Name(Name), MangledName(MangledName), 
          OpID(OpUIDGenerator.GetUID()), EvalType(Type), 
          HashValue(boost::hash_value(OpID)), Cost(Cost)
    {
        // Nothing here
    }

    OperatorBase::~OperatorBase()
    {
        // Nothing here
    }

    const ESFixedTypeBase* OperatorBase::GetEvalType() const
    {
        return EvalType;
    }

    uint64 OperatorBase::GetID() const
    {
        return OpID;
    }

    uint64 OperatorBase::Hash() const
    {
        return HashValue;
    }

    const string& OperatorBase::GetName() const
    {
        return Name;
    }

    uint32 OperatorBase::GetCost() const
    {
        return Cost;
    }

    const string& OperatorBase::GetMangledName() const
    {
        return MangledName;
    }
    
    // By default, var operators have the same mangled name as the name
    VarOperatorBase::VarOperatorBase(const string& Name, const ESFixedTypeBase* Type, uint32 Cost)
        : OperatorBase(Name, Name, Type, Cost)
    {
        // Nothing here
    }

    VarOperatorBase::VarOperatorBase(const string& Name, const string& MangledName,
                                     const ESFixedTypeBase* Type, uint32 Cost)
        : OperatorBase(Name, MangledName, Type, Cost)
    {
        // Nothing here
    }

    VarOperatorBase::~VarOperatorBase()
    {
        // Nothing here
    }

    uint32 VarOperatorBase::GetArity() const
    {
        return 0;
    }

    uint64 VarOperatorBase::GetPosition() const
    {
        return Position;
    }

    void VarOperatorBase::SetPosition(uint64 NewPosition) const
    {
        Position = NewPosition;
    }

    UQVarOperator::~UQVarOperator()
    {
        // Nothing here
    }
    
    // Let bound var operators are mangled by suffixing with the UID
    // and the word "let"
    LetBoundVarOperator::LetBoundVarOperator(const string& Name, const ESFixedTypeBase* Type,
                                             uint64 LetUID)
        : VarOperatorBase(Name, Name + "_" + to_string(LetUID) + "_let", Type, 1), 
          LetUID(LetUID)
    {
        // Nothing here
    }

    uint64 LetBoundVarOperator::GetLetUID() const
    {
        return LetUID;
    }

    LetBoundVarOperator::~LetBoundVarOperator()
    {
        // Nothing here
    }

    AuxVarOperator::AuxVarOperator(uint64 AuxID, const ESFixedTypeBase* Type)
        : VarOperatorBase((string)"AuxVar_" + to_string(AuxID), Type)
    {
        Position = AuxID;
    }

    AuxVarOperator::~AuxVarOperator()
    {
        // Nothing here
    }

    // Formal param operators are mangled by suffixing with
    // the UID and the word "fp"
    FormalParamOperator::FormalParamOperator(const string& Name, const ESFixedTypeBase* Type,
                                             uint32 Position, uint64 FPUID)
        : VarOperatorBase(Name, Name + "_" + to_string(FPUID) + "_fp", Type, 1),
          FPUID(FPUID)
    {
        this->Position = Position;
    }

    FormalParamOperator::~FormalParamOperator()
    {
        // Nothing here
    }

    uint64 FormalParamOperator::GetFPUID() const
    {
        return FPUID;
    }

    string FuncOperatorBase::MangleName(const string& FuncName, const ESFunctionType* FuncType)
    {
        return MangleName(FuncName, FuncType->GetDomainTypes());
    }

    string FuncOperatorBase::MangleName(const string& FuncName, 
                                        const vector<const ESFixedTypeBase*>& ArgTypes)
    {
        ostringstream sstr;
        sstr << FuncName;
        for (auto const& ArgType : ArgTypes) {
            sstr << "@" << ArgType->GetID();
        }
        return sstr.str();        
    }

    FuncOperatorBase::FuncOperatorBase(const string& Name, const ESFunctionType* FuncType, uint32 Cost)
        : OperatorBase(Name, MangleName(Name, FuncType), FuncType->GetRangeType(), Cost), FuncType(FuncType)
    {
        // Nothing here
    }

    FuncOperatorBase::~FuncOperatorBase()
    {
        // Nothing here
    }

    const ESFunctionType* FuncOperatorBase::GetFuncType() const
    {
        return FuncType;
    }

    uint32 FuncOperatorBase::GetArity() const
    {
        return FuncType->GetDomainTypes().size();
    }

    bool FuncOperatorBase::IsSymmetric() const
    {
        return false;
    }

    ConstOperator::ConstOperator(const string& Name, const ESFunctionType* FuncType,
                                 const ConcreteValueBase* ConstantValue, uint32 Cost)
        : FuncOperatorBase(Name, FuncType, Cost), Anon(false), ConstantValue(ConstantValue)
    {
        // Nothing here
    }

    ConstOperator::ConstOperator(const ESFunctionType* FuncType, 
                                 const ConcreteValueBase* ConstantValue,
                                 uint32 Cost)
        : FuncOperatorBase("AnonConst_" + to_string(AnonConstUIDGenerator.GetUID()), FuncType, Cost), 
          Anon(true), ConstantValue(ConstantValue)
    {
        // Nothing here
    }

    bool ConstOperator::IsAnon() const
    {
        return Anon;
    }

    const ConcreteValueBase* ConstOperator::GetConstantValue() const
    {
        return ConstantValue;
    }

    InterpretedFuncOperator::InterpretedFuncOperator(const string& Name, 
                                                     const ESFunctionType* FuncType,
                                                     ConcFunctorBase* ConcFunctor,
                                                     SymbFunctorBase* SymbFunctor,
                                                     bool Symmetric,
                                                     uint32 Cost)
        : FuncOperatorBase(Name, FuncType, Cost), 
          ConcFunctor(ConcFunctor), SymbFunctor(SymbFunctor), Symmetric(Symmetric)
    {
        // Nothing here
    }

    InterpretedFuncOperator::~InterpretedFuncOperator()
    {
        // We own the functors. Delete them
        if (ConcFunctor != nullptr) {
            delete ConcFunctor;
        }
        if (SymbFunctor != nullptr) {
            delete SymbFunctor;
        }
    }

    ConcFunctorBase* InterpretedFuncOperator::GetConcFunctor() const
    {
        return ConcFunctor;
    }

    SymbFunctorBase* InterpretedFuncOperator::GetSymbFunctor() const
    {
        return SymbFunctor;
    }

    bool InterpretedFuncOperator::IsSymmetric() const
    {
        return Symmetric;
    }

    MacroOperator::MacroOperator(const string& Name, const ESFunctionType* FuncType,
                                 const vector<Expression>& FormalParamExpressions,
                                 const Expression& MacroExpression, bool Symmetric, uint32 Cost)
        : InterpretedFuncOperator(Name, FuncType, 
                                  new MacroConcreteFunctor(Name, MacroExpression),
                                  new MacroSymbolicFunctor(Name, MacroExpression),
                                  Symmetric, Cost), 
                MacroExpression(MacroExpression),
                FormalParamExpressions(FormalParamExpressions), Symmetric(Symmetric)
    {
        // Nothing here
    }

    MacroOperator::~MacroOperator()
    {
        // Nothing here
    }

    const Expression& MacroOperator::GetMacroExpression() const
    {
        return MacroExpression;
    }

    const vector<Expression>& MacroOperator::GetFormalParamExpressions() const
    {
        return FormalParamExpressions;
    }

    bool MacroOperator::IsSymmetric() const
    {
        return Symmetric;
    }

    SynthFuncOperator::SynthFuncOperator(const string& Name, const ESFunctionType* FuncType,
                                         const vector<string>& ParamNames,
                                         const Grammar* SynthGrammar)
        : FuncOperatorBase(Name, FuncType, 0), SynthGrammar(SynthGrammar), ParamNames(ParamNames)
    {
        // Nothing here
    }

    SynthFuncOperator::~SynthFuncOperator()
    {
        delete SynthGrammar;
    }

    uint32 SynthFuncOperator::GetPosition() const
    {
        return Position;
    }

    void SynthFuncOperator::SetPosition(uint32 NewPosition) const
    {
        Position = NewPosition;
    }

    uint32 SynthFuncOperator::GetNumParams() const
    {
        return NumParams;
    }

    void SynthFuncOperator::SetNumParams(uint32 NumParams) const
    {
        this->NumParams = NumParams;
    }

    uint32 SynthFuncOperator::GetNumLetVars() const
    {
        return NumLetVars;
    }

    void SynthFuncOperator::SetNumLetVars(uint32 NumLetVars) const
    {
        this->NumLetVars = NumLetVars;
    }

    const Grammar* SynthFuncOperator::GetSynthGrammar() const
    {
        return SynthGrammar;
    }

    const vector<string>& SynthFuncOperator::GetParamNames() const
    {
        return ParamNames;
    }
    
} /* end namespace */

// 
// Operators.cpp ends here
