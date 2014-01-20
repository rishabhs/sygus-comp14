// ESolver.cpp --- 
// 
// Filename: ESolver.cpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:54:39 2014 (-0500)
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


#include "ESolver.hpp"
#include "../descriptions/Builtins.hpp"
#include "../z3interface/Z3TheoremProver.hpp"
#include "../scoping/ScopeManager.hpp"
#include "../values/ValueManager.hpp"
#include "../expressions/ExprManager.hpp"
#include "../solverutils/ConstManager.hpp"
#include "../solverutils/TypeManager.hpp"
#include "../utils/TextUtils.hpp"
#include "../visitors/ExpCheckers.hpp"
#include "../logics/BVLogic.hpp"
#include "../logics/LIALogic.hpp"

namespace ESolver {

    inline void ESolver::CheckOperatorRedeclaration(const string& OperatorName,
                                                    const vector<const ESFixedTypeBase*>& TypeVector) const
    {
        if(LookupOperatorNI(OperatorName, TypeVector) != NULL) {
            throw TypeException("Redeclaration of operator \"" + OperatorName + "\"");
        }
    }

    inline void ESolver::CheckOperatorRedeclaration(const string& OperatorName) const
    {
        if(LookupOperatorNI(OperatorName) != NULL) {
            throw TypeException("Redeclaration of variable or constant \"" + OperatorName + "\".");
        }
    }

    inline void ESolver::RegisterType(const ESFixedTypeBase* Type)
    {
        // Create an equality operator
        vector<const ESFixedTypeBase*> ArgTypes;
        ArgTypes.push_back(Type);
        ArgTypes.push_back(Type);
        CreateFunction("=", ArgTypes, BoolType, new EQSymbolicFunctor(),
                       new EQConcreteFunctor(), true, true);

        // Create an ITE operator
        ArgTypes.clear();
        ArgTypes.push_back(BoolType);
        ArgTypes.push_back(Type);
        ArgTypes.push_back(Type);
        CreateFunction("ite", ArgTypes, Type, new ITESymbolicFunctor(), 
                       new ITEConcreteFunctor(), false, true);
    }

    ESolver::ESolver(const ESolverOpts* Opts)
        : Opts(*Opts), TheLogger(Opts->LogFileName, Opts->StatsLevel)
    {
        CheckOpts(Opts);

        SMTSolverParams Params;
        Params["RANDOM_SEED"] = to_string(Opts->RandomSeed);
        TheLogger.Log1("Using Random Seed: ").Log1(Opts->RandomSeed).Log1("\n");

        TP = new Z3TheoremProver(Params);

        ScopeMgr = new ScopeManager();
        ValMgr = new ValueManager();
        ExpMgr = new ExprManager();
        ConstMgr = new ConstManager();
        TypeMgr = new TypeManager(TP);

        AddBuiltins();

        ResourceLimitManager::SetMemLimit(Opts->MemoryLimit);
        ResourceLimitManager::SetCPULimit(Opts->CPULimit);
        Push();
    }

    ESolver::~ESolver()
    {
        TheLogger.Flush();
        // Unload logics
        for (auto const& LL : LoadedLogics) {
            delete LL;
        }

        delete ScopeMgr;
        delete ValMgr;
        delete ExpMgr;
        delete ConstMgr;
        delete TypeMgr;

        delete TP;
    }

    TheoremProver* ESolver::GetTP() const
    {
        return TP;
    }

    void ESolver::Push()
    {
        ScopeMgr->PushScope();
    }
    
    void ESolver::Push(const string& ScopeName)
    {
        ScopeMgr->PushScope(ScopeName);
    }

    void ESolver::Pop()
    {
        // Good time to GC
        ExpMgr->GC();
        ScopeMgr->PopScope();
    }

    void ESolver::DestroyScope(const string& ScopeName)
    {
        ScopeMgr->DestroyScope(ScopeName);
    }

    void ESolver::ReplaceScope(const string& ScopeName)
    {
        // Good time to GC
        ExpMgr->GC();
        ScopeMgr->ReplaceScope(ScopeName);
    }

    const ESFixedTypeBase* ESolver::LookupType(const string& TypeName) const
    {
        return TypeMgr->LookupType(TypeName);
    }

    const OperatorBase* ESolver::LookupOperator(const string& OpName) const
    {
        return ScopeMgr->LookupOperator(OpName);
    }
    
    const FuncOperatorBase* ESolver::LookupOperator(const string& OpName,
                                                    const vector<const ESFixedTypeBase*>& TypeVector) const
    {
        auto Retval = ScopeMgr->LookupOperator(OpName, TypeVector);
        if (Retval == nullptr) {
            for (auto const& LL : LoadedLogics) {
                if (LL->InstantiateOperator(OpName, TypeVector)) {
                    break;
                }
            }
            return ScopeMgr->LookupOperator(OpName, TypeVector);
        }
        return Retval;
    }


    const OperatorBase* ESolver::LookupOperatorNI(const string& OpName) const
    {
        return ScopeMgr->LookupOperator(OpName);
    }
    
    const FuncOperatorBase* ESolver::LookupOperatorNI(const string& OpName,
                                                      const vector<const ESFixedTypeBase*>& TypeVector) const
    {
        return ScopeMgr->LookupOperator(OpName, TypeVector);
    }

    const ESFixedTypeBase* ESolver::CreateBoolType() const
    {
        return BoolType;
    }

    const ESFixedTypeBase* ESolver::CreateIntType() const
    {
        return IntType;
    }

    const ESFixedTypeBase* ESolver::CreateEnumType(const string& TypeName,
                                                   const vector<string>& EnumConstructors)
    {
        if(TypeMgr->LookupType(TypeName) != NULL) {
            throw TypeException("Redeclaration of Type \"" + TypeName + "\"");
        }

        // Safety check to ensure that enum constructors are not
        // repeated
        set<string> EnumConstructorSet;
        const uint32 NumEnumConstructors = EnumConstructors.size();
        for(uint32 i = 0; i < NumEnumConstructors; ++i) {
            if(EnumConstructorSet.find(EnumConstructors[i]) != EnumConstructorSet.end()) {
                throw TypeException((string)"Duplicate Enum constructor \"" + EnumConstructors[i] + "\"");
            }
            EnumConstructorSet.insert(EnumConstructors[i]);
        }

        auto Retval = TypeMgr->CreateType<ESEnumType>(TypeName, EnumConstructors);
        TypeMgr->BindType(TypeName, Retval);

        RegisterType(Retval);
        
        // Create values and constant operators for each constructor
        // Push a bunch of constant operators into the fray. One for each enum constructor
        for(auto const& EnumConstructor : EnumConstructors) {
            CreateConstant(TypeName + "::" + EnumConstructor,
                           Retval, EnumConstructor);
        }

        return Retval;
    }

    const ESFixedTypeBase* ESolver::CreateBitVectorType(uint32 NumBits)
    {
        if(NumBits > ESOLVER_MAX_BV_SIZE) {
            throw UnimplementedException((string)"Error: ESolver cannot currently handle bit-vectors " +
                                         "larger than " + to_string(ESOLVER_MAX_BV_SIZE) + " bits in length");
        }
        string TypeName = ESOLVER_BITVEC_PREFIX + "_" + to_string(NumBits);
        auto Retval = TypeMgr->LookupType<ESBVType>(TypeName);
        if (Retval == nullptr) {
            Retval = TypeMgr->CreateType<ESBVType>(NumBits);
            TypeMgr->BindType(TypeName, Retval);
            RegisterType(Retval);
        }
        
        return Retval;
    }

    void ESolver::BindType(const string& TypeName, const ESFixedTypeBase* Type)
    {
        if (LookupType(TypeName) != nullptr) {
            throw TypeException((string)"Error: Attempted to rebind previously bound type name \"" + 
                                TypeName + "\"");
        }
        TypeMgr->BindType(TypeName, Type);
    }

    const ConcreteValueBase* ESolver::CreateValue(const ESFixedTypeBase* Type, const string& ValueString)
    {
        switch(Type->GetBaseType()) {
        case BaseTypeBool:
            return CreateValue(Type, ParseBoolString(ValueString));
        case BaseTypeInt:
            return CreateValue(Type, ParseIntString(ValueString));
        case BaseTypeEnum:
            return CreateValue(Type, ParseEnumString(ValueString, Type));
        case BaseTypeBitVector:
            return CreateValue(Type, ParseBVString(ValueString, Type->As<ESBVType>()->GetSize()));
        default:
            throw TypeException("Unhandled type in CreateValue()");
        }
    }

    const ConcreteValueBase* ESolver::CreateValue(const ESFixedTypeBase* Type, int64 TheValue)
    {
        return (ValMgr->GetValue(Type, TheValue));
    }

    const ConcreteValueBase* ESolver::CreateTrueValue()
    {
        return TrueValue;
    }

    const ConcreteValueBase* ESolver::CreateFalseValue()
    {
        return FalseValue;
    }

    const ConstOperator* ESolver::CreateConstant(const string& ConstantName,
                                                 const ESFixedTypeBase* Type,
                                                 const string& ConstantString)
    {
        const ConcreteValueBase* TheValue = CreateValue(Type, ConstantString);
        return CreateConstant(ConstantName, TheValue);
    }

    const ConstOperator* ESolver::CreateConstant(const string& ConstantName,
                                                 const ConcreteValueBase* TheValue)
    {
        CheckOperatorRedeclaration(ConstantName);
        for (auto const& LL : LoadedLogics) {
            if (LL->IsNameReserved(ConstantName)) {
                throw IdentifierException((string)"Identifier \"" + ConstantName + "\" is reserved");
            }
        }

        ConstOperator* Retval;
        auto Type = TheValue->GetType();
        // recover the type for this constant
        vector<const ESFixedTypeBase*> EmptyVec;
        auto FuncType = TypeMgr->CreateType<ESFunctionType>(EmptyVec, Type);
        Retval = new ConstOperator(ConstantName, FuncType, TheValue);
        ScopeMgr->AddOperator(Retval);
        return Retval;
    }

    // Anonymous constants
    const ConstOperator* ESolver::CreateConstant(const ConcreteValueBase* ConstantValue)
    {
        vector<const ESFixedTypeBase*> EmptyVec;
        auto FuncType = TypeMgr->CreateType<ESFunctionType>(EmptyVec, ConstantValue->GetType());
        return ConstMgr->GetOp(ConstantValue, FuncType);
    }

    const InterpretedFuncOperator* ESolver::CreateFunction(const string& FuncName,
                                                           const vector<const ESFixedTypeBase*>& DomainTypes,
                                                           const ESFixedTypeBase* RangeType,
                                                           SymbFunctorBase* SymbFunctor,
                                                           ConcFunctorBase* ConcFunctor,
                                                           bool Symmetric,
                                                           bool Builtin,
                                                           uint32 Cost)
    {
        CheckOperatorRedeclaration(FuncName, DomainTypes);
        if (!Builtin) {
            for (auto const& LL : LoadedLogics) {
                if (LL->IsNameReserved(FuncName)) {
                    throw IdentifierException((string)"Identifier \"" + FuncName + "\" is reserved");
                }
            }
        }
        auto FuncType = TypeMgr->CreateType<ESFunctionType>(DomainTypes, RangeType);
        auto Op = new InterpretedFuncOperator(FuncName, FuncType, ConcFunctor, SymbFunctor, Symmetric, Cost);
        ScopeMgr->AddOperator(Op, Builtin);
        return Op;
    }

    const MacroOperator* ESolver::CreateFunction(const string& FuncName,
                                                 const vector<const ESFixedTypeBase*>& DomainTypes,
                                                 const ESFixedTypeBase* RangeType,
                                                 const Expression& MacroExpression,
                                                 uint32 Cost)
    {
        CheckOperatorRedeclaration(FuncName, DomainTypes);
        for (auto const& LL : LoadedLogics) {
            if (LL->IsNameReserved(FuncName)) {
                throw IdentifierException((string)"Identifier \"" + FuncName + "\" is reserved");
            }
        }

        auto FuncType = TypeMgr->CreateType<ESFunctionType>(DomainTypes, RangeType);
        vector<Expression> FormalParamExps;
        MacroExpChecker::Do(MacroExpression, DomainTypes, RangeType, FormalParamExps);
        auto Op = new MacroOperator(FuncName, FuncType, FormalParamExps, 
                                    MacroExpression, false, Cost);
        ScopeMgr->AddOperator(Op, false);
        return Op;
    }

    const SynthFuncOperator* ESolver::CreateFunction(const string& FuncName,
                                                     const vector<const ESFixedTypeBase*>& DomainTypes,
                                                     const vector<string>& ParamNames,
                                                     const ESFixedTypeBase* RangeType,
                                                     Grammar* SynthGrammar)
    {
        CheckOperatorRedeclaration(FuncName, DomainTypes);
        for (auto const& LL : LoadedLogics) {
            if (LL->IsNameReserved(FuncName)) {
                throw IdentifierException((string)"Identifier \"" + FuncName + "\" is reserved");
            }
        }

        auto SFType = TypeMgr->CreateType<ESFunctionType>(DomainTypes, RangeType);
        auto Op = new SynthFuncOperator(FuncName, SFType, ParamNames, SynthGrammar);
        ScopeMgr->AddOperator(Op);
        return Op;
    }

    const UQVarOperator* ESolver::CreateQuantifiedVariable(const string& VarName,
                                                           const ESFixedTypeBase* Type)
    {
        CheckOperatorRedeclaration(VarName);
        for (auto const& LL : LoadedLogics) {
            if (LL->IsNameReserved(VarName)) {
                throw IdentifierException((string)"Identifier \"" + VarName + "\" is reserved");
            }
        }

        auto Op = new UQVarOperator(VarName, Type);
        ScopeMgr->AddOperator(Op);
        return Op;
    }

    const FormalParamOperator* ESolver::CreateFormalParamOperator(const string& VarName,
                                                                  const ESFixedTypeBase* Type,
                                                                  uint32 Position)
    {
        auto FPUID = FPUIDGenerator.GetUID();
        auto Op = new FormalParamOperator(VarName, Type, Position, FPUID);
        ScopeMgr->AddOperator(Op);
        return Op;
    }

    const LetBoundVarOperator* ESolver::CreateLetBoundVariable(const string& Name, const ESFixedTypeBase* Type)
    {
        auto LetUID = LetUIDGenerator.GetUID();
        auto Op = new LetBoundVarOperator(Name, Type, LetUID);
        ScopeMgr->AddOperator(Op);
        return Op;
    }

    const AuxVarOperator* ESolver::CreateAuxVariable(uint64 AuxID, const ESFixedTypeBase* Type)
    {
        auto Cached = ScopeMgr->LookupOperator("AuxVar_" + to_string(AuxID));
        if (Cached != nullptr) {
            return Cached->As<AuxVarOperator>();
        }
        auto Op = new AuxVarOperator(AuxID, Type);
        ScopeMgr->AddOperator(Op);
        return Op;
    }

    Expression ESolver::CreateFreshLetBoundVarExpression(const string& VarName,
                                                         const ESFixedTypeBase* Type)
    {
        auto Op = CreateLetBoundVariable(VarName, Type);
        return CreateExpression(Op);
    }

    Expression ESolver::CreateFreshFormalParamExpression(const string& ParamName,
                                                         const ESFixedTypeBase* Type,
                                                         uint32 Position)
    {
        auto Op = CreateFormalParamOperator(ParamName, Type, Position);
        return CreateExpression(Op);
    }
    
    Expression ESolver::CreateAuxVarExpression(uint64 AuxID, const ESFixedTypeBase* Type)
    {
        auto Op = CreateAuxVariable(AuxID, Type);
        if (Op->GetEvalType() != Type) {
            throw TypeException((string)"Aux Var with ID " + to_string(AuxID) + " has already " + 
                                "been declared with a different type!");
        }
        return CreateExpression(Op);
    }

    Expression ESolver::CreateLetExpression(const LetExpBindingMap& Bindings,
                                            Expression BoundInExpression)
    {
        // Check that the lhs of each binding is indeed a let bound variable
        for (auto const& KV : Bindings) {
            auto Op = KV.first->GetOp()->As<LetBoundVarOperator>();
            if (Op == nullptr) {
                ostringstream sstr;
                sstr << KV.first;
                throw TypeException((string)"Error: Found a weird expression where a let bound var expression " +
                                    "was expected.\nThe expression that caused the exception: " + sstr.str());
            }
        }
        Expression Retval = new UserLetExpression(Bindings, BoundInExpression);
        return ExpMgr->GetExp(Retval);
    }
    
    Expression ESolver::CreateExpression(const OperatorBase* OpInfo,
                                         const vector<Expression>& Children)
    {
        Expression NewExp;
        // Type checks
        if (Children.size() > 0) {
            auto FuncOp = OpInfo->As<FuncOperatorBase>();
            const uint32 NumChildren = Children.size();
            vector<const ESFixedTypeBase*> ArgTypes(NumChildren);
            for (uint32 i = 0; i < NumChildren; ++i) {
                ArgTypes[i] = Children[i]->GetType();
            }
            // Quick type check using name mangling
            auto const& ExpectedName = FuncOp->GetMangledName();
            auto const&& ActualName = FuncOperatorBase::MangleName(OpInfo->GetName(), ArgTypes);
            if (ExpectedName != ActualName) {
                throw TypeException((string)"Error in application of function \"" + OpInfo->GetName() + "\".\n" + 
                                    "This could be due to mismatched numbers or types of parameters");
            }
            // We're good. Create the expression
            if (OpInfo->As<InterpretedFuncOperator>() != nullptr) {
                NewExp = new UserInterpretedFuncExpression(OpInfo->As<InterpretedFuncOperator>(),
                                                           Children);
            } else {
                NewExp = new UserSynthFuncExpression(OpInfo->As<SynthFuncOperator>(),
                                                     Children);
            }
        } else {
            
            // This could be a constant, a UQVariable, an aux variable, 
            // a formal param or a let bound variable
            if (OpInfo->As<VarOperatorBase>() != nullptr) {
                if (OpInfo->As<UQVarOperator>() != nullptr) {
                    NewExp = new UserUQVarExpression(OpInfo->As<UQVarOperator>());
                } else if (OpInfo->As<FormalParamOperator>() != nullptr) {
                    NewExp = new UserFormalParamExpression(OpInfo->As<FormalParamOperator>());
                } else if (OpInfo->As<AuxVarOperator>() != nullptr) {
                    NewExp = new UserAuxVarExpression(OpInfo->As<AuxVarOperator>());
                } else if (OpInfo->As<LetBoundVarOperator>() != nullptr) {
                    NewExp = new UserLetBoundVarExpression(OpInfo->As<LetBoundVarOperator>());
                } else {
                    throw InternalError((string)"BUG: Unhandled operator type at " + __FILE__ + ":" + 
                                        to_string(__LINE__));
                }
            } else {
                // This can only be a const operator now
                if (OpInfo->As<ConstOperator>() != nullptr) {
                    NewExp = new UserConstExpression(OpInfo->As<ConstOperator>());
                } else {
                    throw TypeException((string)"Error: Could not find a meaningful way to construct " +
                                        "an expression with operator having name \"" + OpInfo->GetName() + 
                                        "\".\nPerhaps you provided arguments where none were expected, " + 
                                        "or this could be a bug");
                }
            }
        }

        ExpMgr->GC();
        return ExpMgr->GetExp(NewExp);
    }

    Expression ESolver::CreateExpression(const string& OperatorName,
                                         const vector<Expression>& Children)
    {
        vector<const ESFixedTypeBase*> ArgTypes;
        for(uint32 i = 0; i < Children.size(); ++i) {
            ArgTypes.push_back(Children[i]->GetType());
        }
        const OperatorBase* OpInfo = LookupOperator(OperatorName, ArgTypes);
        if(OpInfo == NULL) {
            throw TypeException((string)"No overloaded operator found for operator name: \"" +
                                OperatorName + "\"");
        }
        return CreateExpression(OpInfo, Children);
    }

    Expression ESolver::CreateExpression(const string& OperatorName,
                                         const Expression& Exp1)
    {
        vector<Expression> Children(1);
        Children[0] = Exp1;
        return CreateExpression(OperatorName, Children);
    }

    Expression ESolver::CreateExpression(const string& OperatorName,
                                         const Expression& Exp1,
                                         const Expression& Exp2)
    {
        vector<Expression> Children(2);
        Children[0] = Exp1;
        Children[1] = Exp2;
        return CreateExpression(OperatorName, Children);
    }

    Expression ESolver::CreateExpression(const string& OperatorName,
                                         const Expression& Exp1,
                                         const Expression& Exp2,
                                         const Expression& Exp3)
    {
        // special case for bv extract

        if (OperatorName == "bvextract") {
            if (Exp2->As<UserConstExpression>() == nullptr ||
                Exp3->As<UserConstExpression>() == nullptr) {
                throw TypeException((string)"bvextract can only be applied to constant indices");
            }
            if (Exp2->GetType() != IntType ||
                Exp3->GetType() != IntType) {
                throw TypeException((string)"bvextract can only be applied to constant integer indices");
            }

            auto OpName = BVLogic::GetExtractOpName(Exp1->GetType(), 
                                                    Exp2->GetOp()->As<ConstOperator>()->GetConstantValue()->GetValue(), 
                                                    Exp3->GetOp()->As<ConstOperator>()->GetConstantValue()->GetValue());
            // recurse with new name
            auto Op = LookupOperator(OpName);
            if (Op == nullptr) {
                LoadedBVLogic->InstantiateExtractOperator(Exp1->GetType(), 
                                                          Exp2->GetOp()->As<ConstOperator>()->GetConstantValue()->GetValue(), 
                                                          Exp3->GetOp()->As<ConstOperator>()->GetConstantValue()->GetValue());
                Op = LookupOperator(OpName);
            }
            vector<Expression> Children = { Exp1 };
            return CreateExpression(Op, Children);
        }

        vector<Expression> Children(3);
        Children[0] = Exp1;
        Children[1] = Exp2;
        Children[2] = Exp3;
        return CreateExpression(OperatorName, Children);
    }

    Expression ESolver::CreateExpression(const ConcreteValueBase* TheValue)
    {
        // Create an anonymous constant operator for this value
        vector<const ESFixedTypeBase*> EmptyVec;
        auto FuncType = TypeMgr->CreateType<ESFunctionType>(EmptyVec, TheValue->GetType());
        auto Op = ConstMgr->GetOp(TheValue, FuncType);
        return CreateExpression(Op);
    }

    Expression ESolver::CreateExpression(const ESFixedTypeBase* Type,
                                         const string& ConstantString)
    {
        const ConcreteValueBase* TheValue = CreateValue(Type, ConstantString);
        return CreateExpression(TheValue);
    }

    Expression ESolver::CreateTrueExpression()
    {
        return CreateExpression(TrueValue);
    }

    Expression ESolver::CreateFalseExpression()
    {
        return CreateExpression(FalseValue);
    }

    Expression ESolver::CreateExpression(const string& VariableName)
    {
        vector<Expression> Args;
        const OperatorBase* Op = ScopeMgr->LookupOperator(VariableName)->As<VarOperatorBase>();
        if (Op == nullptr) {
            Op = ScopeMgr->LookupOperator(VariableName)->As<ConstOperator>();
        }
        if(Op == NULL) {
            throw UndefinedVarException((string)"Variable or constant \"" + VariableName +
                                        + "\" not found to create expression");
        }
        return CreateExpression(Op, Args);
    }

    Expression ESolver::CreateExpression(const OperatorBase* OpInfo)
    {
        vector<Expression> ArgTypes;
        return CreateExpression(OpInfo, ArgTypes);
    }

    Expression ESolver::CreateAndExpression(const Expression& Exp1,
                                            const Expression& Exp2)
    {
        return CreateExpression("and", Exp1, Exp2);
    }

    Expression ESolver::CreateAndExpression(const vector<Expression>& Conjuncts)
    {
        if(Conjuncts.size() == 0) {
            return Expression::NullObject;
        }
        if(Conjuncts.size() == 1) {
            return Conjuncts[0];
        }

        Expression Current = CreateAndExpression(Conjuncts[0], Conjuncts[1]);
        uint32 NumConjuncts = Conjuncts.size();
        for(uint32 i = 2; i < NumConjuncts; ++i) {
            Current = CreateAndExpression(Current, Conjuncts[i]);
        }
        return CreateExpression("and", Current->GetChildren());
    }

    Expression ESolver::CreateOrExpression(const Expression& Exp1,
                                           const Expression& Exp2)
    {
        return CreateExpression("or", Exp1, Exp2);
    }

    Expression ESolver::CreateOrExpression(const vector<Expression>& Disjuncts)
    {
        if(Disjuncts.size() == 0) {
            return Expression::NullObject;
        }
        if(Disjuncts.size() == 1) {
            return Disjuncts[0];
        }

        Expression Current = CreateOrExpression(Disjuncts[0], Disjuncts[1]);
        uint32 NumDisjuncts = Disjuncts.size();
        for(uint32 i = 2; i < NumDisjuncts; ++i) {
            Current = CreateOrExpression(Current, Disjuncts[i]);
        }
        return CreateExpression("or", Current->GetChildren());
    }

    Expression ESolver::CreateNotExpression(const Expression& Exp)
    {
        return CreateExpression("not", Exp);
    }

    Expression ESolver::CreateImpliesExpression(const Expression& Exp1, 
                                                const Expression& Exp2)
    {
        vector<Expression> Children;
        Children.push_back(CreateNotExpression(Exp1));
        Children.push_back(Exp2);
        return CreateOrExpression(Children);
    }

    Expression ESolver::CreateIffExpression(const Expression& Exp1,
                                            const Expression& Exp2)
    {
        vector<Expression> Children;
        Children.push_back(CreateImpliesExpression(Exp1, Exp2));
        Children.push_back(CreateImpliesExpression(Exp2, Exp1));
        return CreateAndExpression(Children);
    }
    
    void ESolver::SetBudget(uint32 NewBudget)
    {
        Opts.CostBudget = NewBudget;
    }

    void ESolver::CheckResourceLimits()
    {
        if(ResourceLimitManager::CheckTimeOut()) {
            EndSolve();
            SolveEndTime = TimeValue::GetTimeValue();
            SolveEndMemStats = MemStats::GetMemStats();
            throw OutOfTimeException("Query time limit exceeded");
        } else if(ResourceLimitManager::CheckMemOut()) {
            EndSolve();
            SolveEndTime = TimeValue::GetTimeValue();
            SolveEndMemStats = MemStats::GetMemStats();
            throw OutOfMemoryException("Out of memory");
        }
    }


    void ESolver::PreSolve()
    {
        // SolveStartMemStats = MemStats::GetMemStats();
        // SolveStartTime = TimeValue::GetTimeValue();
        
        // Also setup the signal handlers for mem and timeout
        ResourceLimitManager::QueryStart();
    }

    void ESolver::PostSolve()
    {
        // SolveEndMemStats = MemStats::GetMemStats();
        // SolveEndTime = TimeValue::GetTimeValue();

        // Stop the timer
        ResourceLimitManager::QueryEnd();

        // TheLogger.Log1("Solve time: ").Log1(SolveEndTime - SolveStartTime).Log1("\n\n");
        // TheLogger.Log1("Memory used by solve:\n");
        // TheLogger.Log1(SolveEndMemStats - SolveStartMemStats).Log1("\n\n");
    }

    const ESolverOpts& ESolver::GetOpts() const
    {
        return Opts;
    }

    Logger& ESolver::GetLogger() const
    {
        return const_cast<Logger&>(TheLogger);
    }
    

} /* End namespace */


// 
// ESolver.cpp ends here
