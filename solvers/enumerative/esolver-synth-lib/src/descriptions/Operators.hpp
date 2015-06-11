// Operators.hpp ---
//
// Filename: Operators.hpp
// Author: Abhishek Udupa
// Created: Wed Jan  1 17:08:56 2014 (-0500)
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

#if !defined __ESOLVER_OPERATORS_HPP
#define __ESOLVER_OPERATORS_HPP

#include "../common/ESolverForwardDecls.hpp"
#include "../utils/UIDGenerator.hpp"
#include "../containers/ESSmartPtr.hpp"
#include "../expressions/UserExpression.hpp"

namespace ESolver {

    // We define some operator classes which
    // encapsulate operators/variables/constants
    // At it's most basic level an operator is a function
    // We specialize the base class based on the
    // kind of the function (constant/variable/etc)

    extern UIDGenerator OpUIDGenerator;
    extern UIDGenerator AnonConstUIDGenerator;

    // forward declarations

    class OperatorBase
    {
    protected:
        string Name;
        string MangledName;
        // A universal ID common to all operators
        uint64 OpID;
        const ESFixedTypeBase* EvalType;
        mutable uint64 HashValue;
        uint32 Cost;

    public:
        OperatorBase(const string& Name, const string& MangledName,
                     const ESFixedTypeBase* Type, uint32 Cost);
        virtual ~OperatorBase();

        // Accessors
        const ESFixedTypeBase* GetEvalType() const;
        uint64 GetID() const;
        uint64 Hash() const;
        // For printing, etc
        const string& GetName() const;
        // For internal reference
        const string& GetMangledName() const;

        virtual uint32 GetArity() const = 0;

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

        uint32 GetCost() const;
    };

    class VarOperatorBase : public OperatorBase
    {
    protected:
        mutable uint64 Position;

    public:
        VarOperatorBase(const string& Name, const ESFixedTypeBase* Type, uint32 Cost = 1);
        VarOperatorBase(const string& Name, const string& MangledName,
                        const ESFixedTypeBase* Type, uint32 Cost = 1);

        virtual ~VarOperatorBase();

        virtual uint32 GetArity() const override;

        uint64 GetPosition() const;
        void SetPosition(uint64 NewPosition) const;
    };

    class UQVarOperator : public VarOperatorBase
    {
    public:
        using VarOperatorBase::VarOperatorBase;
        virtual ~UQVarOperator();
    };

    class LetBoundVarOperator : public VarOperatorBase
    {
    private:
        uint64 LetUID;

    public:
        LetBoundVarOperator(const string& Name, const ESFixedTypeBase* Type, uint64 LetUID);
        virtual ~LetBoundVarOperator();

        uint64 GetLetUID() const;
    };

    class AuxVarOperator : public VarOperatorBase
    {
    public:
        AuxVarOperator(uint64 AuxID, const ESFixedTypeBase* Type);
        virtual ~AuxVarOperator();
    };

    class FormalParamOperator : public VarOperatorBase
    {
    private:
        uint64 FPUID;

    public:
        FormalParamOperator(const string& Name, const ESFixedTypeBase* Type, uint32 Position, uint64 FPUID);
        virtual ~FormalParamOperator();

        uint64 GetFPUID() const;
    };

    class FuncOperatorBase : public OperatorBase
    {
    protected:
        const ESFunctionType* FuncType;

    public:
        // Helper method
        static string MangleName(const string& FuncName, const ESFunctionType* FuncType);
        static string MangleName(const string& FuncName, const vector<const ESFixedTypeBase*>& ArgTypes);

        FuncOperatorBase(const string& Name, const ESFunctionType* FuncType, uint32 Cost = 1);
        virtual ~FuncOperatorBase();

        const ESFunctionType* GetFuncType() const;
        uint32 GetArity() const override;
        virtual bool IsSymmetric() const;
    };

    class ConstOperator : public FuncOperatorBase
    {
    private:
        bool Anon;
        const ConcreteValueBase* ConstantValue;

    public:
        ConstOperator(const string& Name, const ESFunctionType* FuncType,
                      const ConcreteValueBase* ConstantValue, uint32 Cost = 1);
        ConstOperator(const ESFunctionType* FuncType,
                      const ConcreteValueBase* ConstantValue, uint32 Cost = 1);

        bool IsAnon() const;
        const ConcreteValueBase* GetConstantValue() const;
    };

    class InterpretedFuncOperator : public FuncOperatorBase
    {
    protected:
        ConcFunctorBase* ConcFunctor;
        SymbFunctorBase* SymbFunctor;
        bool Symmetric;

    public:
        InterpretedFuncOperator(const string& Name, const ESFunctionType* FuncType,
                                ConcFunctorBase* ConcFunctor,
                                SymbFunctorBase* SymbFunctor,
                                bool Symmetric = false,
                                uint32 Cost = 1);
        virtual ~InterpretedFuncOperator();

        ConcFunctorBase* GetConcFunctor() const;
        SymbFunctorBase* GetSymbFunctor() const;
        virtual bool IsSymmetric() const;
    };

    class MacroOperator : public InterpretedFuncOperator
    {
    private:
        // In terms of formal params only
        Expression MacroExpression;
        vector<Expression> FormalParamExpressions;
        bool Symmetric;

    public:
        MacroOperator(const string& Name, const ESFunctionType* FuncType,
                      const vector<Expression>& FormalParamExpressions,
                      const Expression& MacroExpression, bool Symmetric = false, uint32 Cost = 1);
        virtual ~MacroOperator();

        const Expression& GetMacroExpression() const;
        const vector<Expression>& GetFormalParamExpressions() const;
        virtual bool IsSymmetric() const override;
    };

    class SynthFuncOperator : public FuncOperatorBase
    {
    private:
        mutable uint32 Position;
        mutable uint32 NumParams;
        mutable uint32 NumLetVars;
        const Grammar* SynthGrammar;
        // purely for pretty printing
        vector<string> ParamNames;

    public:
        SynthFuncOperator(const string& Name, const ESFunctionType* FuncType,
                          const vector<string>& ParamNames, const Grammar* SynthGrammar);

        virtual ~SynthFuncOperator();

        uint32 GetPosition() const;
        void SetPosition(uint32 NewPosition) const;

        uint32 GetNumParams() const;
        void SetNumParams(uint32 NumParams) const;

        uint32 GetNumLetVars() const;
        void SetNumLetVars(uint32 NumLetVars) const;

        const Grammar* GetSynthGrammar() const;
        const vector<string>& GetParamNames() const;
    };


} /* end namespace */

#endif /* __ESOLVER_OPERATORS_HPP */

//
// Operators.hpp ends here
