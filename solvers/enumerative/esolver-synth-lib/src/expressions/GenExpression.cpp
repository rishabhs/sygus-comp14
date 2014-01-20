// GenExpression.cpp --- 
// 
// Filename: GenExpression.cpp
// Author: Abhishek Udupa
// Created: Fri Jan  3 04:26:56 2014 (-0500)
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

#include "GenExpression.hpp"
#include "../descriptions/FunctorBase.hpp"
#include "../z3interface/TheoremProver.hpp"
#include "../descriptions/ESType.hpp"
#include "../solvers/ESolver.hpp"

namespace ESolver {

    // Static variables for evaluation
    ConcreteValueBase const* const** GenExpressionBase::LetBindingValStack;
    uint32 GenExpressionBase::LetBindingValStackTop;
    vector<map<uint32, SMTExpr>> GenExpressionBase::LetBindingSMTStack;
    ConcreteValueBase** GenExpressionBase::CVPool;
    uint32 GenExpressionBase::CVPoolTop;
    ConcreteValueBase** GenExpressionBase::EvalStack;
    uint32 GenExpressionBase::EvalStackTop;
    uint64 GenExpressionBase::FreshVarID;

    GenExpressionBase::GenExpressionBase()
    {
        // Nothing here
    }

    GenExpressionBase::~GenExpressionBase()
    {
        // Nothing here
    }

    void GenExpressionBase::Initialize()
    {
        // Allocate space for the let binding stack
        LetBindingValStack = (ConcreteValueBase const* const**)malloc(sizeof(ConcreteValueBase const* const*) *
                                                                      ESOLVER_MAX_LET_BINDING_STACK_SIZE);
        for (uint32 i = 0; i < ESOLVER_MAX_LET_BOUND_VARS; ++i) {
            LetBindingValStack[i] = (ConcreteValueBase const* const*)malloc(sizeof(ConcreteValueBase const*) *
                                                                            ESOLVER_MAX_LET_BOUND_VARS);
        }
        LetBindingValStackTop = 0;
        memset((void*)(LetBindingValStack[LetBindingValStackTop]), 0, (sizeof(ConcreteValueBase const*) * 
                                                                       ESOLVER_MAX_LET_BOUND_VARS));

        // Allocate space for the CVPool
        CVPool = (ConcreteValueBase**)malloc(sizeof(ConcreteValueBase*) * ESOLVER_CVPOOL_SIZE);
        for (uint32 i = 0; i < ESOLVER_CVPOOL_SIZE; ++i) {
            CVPool[i] = new ConcreteValueBase();
        }

        CVPoolTop = 0;

        // Allocate space for the evaluation stack
        EvalStack = (ConcreteValueBase**)malloc(sizeof(ConcreteValueBase*) * ESOLVER_GEN_EVAL_STACK_SIZE);
        EvalStackTop = 0;
        FreshVarID = (uint64)0;
    }

    void GenExpressionBase::Finalize()
    {
        for (uint32 i = 0; i < ESOLVER_MAX_LET_BOUND_VARS; ++i) {
            free((void*)LetBindingValStack[i]);
        }
        free((void*)LetBindingValStack);

        for (uint32 i = 0; i < ESOLVER_CVPOOL_SIZE; ++i) {
            delete CVPool[i];
        }
        free(CVPool);
        free(EvalStack);
    }

    ConcreteValueBase* GenExpressionBase::GetCV()
    {
        if (CVPoolTop == ESOLVER_CVPOOL_SIZE) {
            throw InternalError((string)"Internal Error: CVPool exhausted.\n" + 
                                "At " + __FILE__ + ":" + to_string(__LINE__));
        }
        return CVPool[CVPoolTop++];
    }

    void GenExpressionBase::Evaluate(const GenExpressionBase* Exp, VariableMap VarMap,
                                     const uint32* ParamMap, ConcreteValueBase* Result) 
    {
        Exp->Evaluate(ParamMap, VarMap);
        if (!PartialExpression) {
            new (Result) ConcreteValueBase(*EvalStack[EvalStackTop - 1]);
        }
        // Reset the stacks and the pools
        CVPoolTop = 0;
        EvalStackTop = 0;
        LetBindingValStackTop = 0;
        return;
    }

    SMTExpr GenExpressionBase::ToSMT(const GenExpressionBase* Exp, TheoremProver* TP,
                                     const uint32* ParamMap,
                                     const vector<SMTExpr>& BaseExprs, vector<SMTExpr>& Assumptions)
    {
        // Create a default let binding stack entry with nothing bound
        LetBindingSMTStack.push_back(map<uint32, SMTExpr>());
        return Exp->ToSMT(TP, ParamMap, BaseExprs, Assumptions);
        LetBindingSMTStack.pop_back();
    }

    Expression GenExpressionBase::ToUserExpression(const GenExpressionBase* Exp, ESolver* Solver)
    {
        map<uint32, const LetBoundVarOperator*> BoundOps;
        return Exp->ToUserExpression(Solver, BoundOps);
    }

    GenLetVarExpression::GenLetVarExpression(const LetBoundVarOperator* Op)
        : GenExpressionBase(), Op(Op)
    {
        // Nothing here
    }

    GenLetVarExpression::~GenLetVarExpression()
    {
        // Nothing here
    }

    string GenLetVarExpression::ToString() const
    {
        return "LetVar_" + to_string(Op->GetPosition());
    }

    void GenLetVarExpression::Evaluate(const uint32* ParamMap, 
                                       VariableMap VarMap) const

    {
        // Check if we even have a binding
        if (LetBindingValStack[LetBindingValStackTop][Op->GetPosition()] == nullptr) {
            PartialExpression = true;
            return;
        }
        EvalStack[EvalStackTop++] = 
            const_cast<ConcreteValueBase*>(LetBindingValStack[LetBindingValStackTop][Op->GetPosition()]);
    }

    SMTExpr GenLetVarExpression::ToSMT(TheoremProver* TP, const uint32* ParamMap,
                                       const vector<SMTExpr>& BaseExprs,
                                       vector<SMTExpr>& Assumptions) const
    {
        return (LetBindingSMTStack.back())[Op->GetPosition()];
    }

    Expression GenLetVarExpression::ToUserExpression(ESolver* Solver,
                                                     const map<uint32, const LetBoundVarOperator*>& BoundOps) const
    {
        auto it = BoundOps.find(Op->GetPosition());
        if (it == BoundOps.end()) {
            throw InternalError((string)"Internal Error: Unexpected let bound variable encountered!\n" + 
                                "At: " + __FILE__ + ":" + to_string(__LINE__));
        }
        return Solver->CreateExpression(it->second);
    }
    
    const ESFixedTypeBase* GenLetVarExpression::GetType() const
    {
        return LetBindingValStack[LetBindingValStackTop][Op->GetPosition()]->GetType();
    }

    uint32 GenLetVarExpression::GetVarID() const
    {
        return Op->GetPosition();
    }

    void GenLetVarExpression::SetVarID(const uint32 NewVarID) const
    {
        Op->SetPosition(NewVarID);
    }    

    GenFPExpression::GenFPExpression(const FormalParamOperator* Op)
        : GenExpressionBase(), Op(Op)
    {
        // Nothing here
    }

    GenFPExpression::~GenFPExpression()
    {
        // Nothing here
    }

    string GenFPExpression::ToString() const
    {
        return Op->GetName();
    }

    void GenFPExpression::Evaluate(const uint32* ParamMap,
                                   VariableMap VarMap) const
    {
        if (!PartialExpression) {
            EvalStack[EvalStackTop++] = const_cast<ConcreteValueBase*>(VarMap[ParamMap[Op->GetPosition()]]);
        }
    }

    SMTExpr GenFPExpression::ToSMT(TheoremProver* TP, const uint32* ParamMap,
                                   const vector<SMTExpr>& BaseExprs,
                                   vector<SMTExpr>& Assumptions) const
    {
        return BaseExprs[ParamMap[Op->GetPosition()]];
    }

    Expression GenFPExpression::ToUserExpression(ESolver* Solver,
                                                 const map<uint32, const LetBoundVarOperator*>& BoundOps) const
    {
        return Solver->CreateExpression(Op);
    }


    const ESFixedTypeBase* GenFPExpression::GetType() const
    {
        return Op->GetEvalType();
    }

    GenConstExpression::GenConstExpression(const ConstOperator* Op)
        : Op(Op)
    {
        // Nothing here
    }

    GenConstExpression::~GenConstExpression()
    {
        // Nothing here
    }

    string GenConstExpression::ToString() const
    {
        return Op->GetConstantValue()->ToString();
    }

    void GenConstExpression::Evaluate(const uint32* ParamMap,
                                      VariableMap VarMap) const
    {
        if (!PartialExpression) {
            EvalStack[EvalStackTop++] = const_cast<ConcreteValueBase*>(Op->GetConstantValue());
        }
    }

    SMTExpr GenConstExpression::ToSMT(TheoremProver* TP,
                                      const uint32* ParamMap,
                                      const vector<SMTExpr>& BaseExprs,
                                      vector<SMTExpr>& Assumptions) const
    {
        return Op->GetConstantValue()->ToSMT(TP);
    }

    const ESFixedTypeBase* GenConstExpression::GetType() const
    {
        return Op->GetEvalType();
    }

    Expression GenConstExpression::ToUserExpression(ESolver* Solver,
                                                    const map<uint32, const LetBoundVarOperator*>& BoundOps) const
    {
        return Solver->CreateExpression(Op);
    }

    GenFuncExpression::GenFuncExpression(const InterpretedFuncOperator* Op,
                                         GenExpressionBase const* const* Children)
        : Op(Op), Children(Children)
    {
        // Nothing here
    }

    GenFuncExpression::~GenFuncExpression()
    {
        // The children are assumed to come from a pool
        // and thus will not be freed by the class
    }

    string GenFuncExpression::ToString() const
    {
        ostringstream sstr;
        sstr << "(" << Op->GetName();
        for(uint32 i = 0; i < Op->GetArity(); ++i) {
            sstr << " " << Children[i]->ToString();
        }
        sstr << ")";
        return sstr.str();
    }

    void GenFuncExpression::Evaluate(const uint32* ParamMap,
                                     VariableMap VarMap) const
    {
        if (PartialExpression) {
            return;
        }
        const uint32 NumChildren = Op->GetArity();
        for(uint32 i = 0; i < NumChildren; ++i) {
            Children[i]->Evaluate(ParamMap, VarMap);
            if (PartialExpression) {
                return;
            }
        }
        // results of evaluation are on the top of the stack now
        auto Functor = Op->GetConcFunctor();
        auto Result = GetCV();
        (*Functor)(&EvalStack[EvalStackTop - NumChildren], Result);
        EvalStackTop -= NumChildren;
        EvalStack[EvalStackTop++] = Result;
    }

    SMTExpr GenFuncExpression::ToSMT(TheoremProver* TP,
                                     const uint32* ParamMap,
                                     const vector<SMTExpr>& BaseExprs,
                                     vector<SMTExpr>& Assumptions) const
    {
        const uint32 NumChildren = Op->GetArity();
        vector<SMTExpr> ChildSMT(NumChildren);

        for(uint32 i = 0; i < NumChildren; ++i) {
            ChildSMT[i] = Children[i]->ToSMT(TP, ParamMap, BaseExprs, Assumptions);
        }
        auto Functor = Op->GetSymbFunctor();
        return (*Functor)(TP, ChildSMT, Assumptions);
    }

    Expression GenFuncExpression::ToUserExpression(ESolver* Solver,
                                                   const map<uint32, const LetBoundVarOperator*>& BoundOps) const
    {
        const uint32 NumChildren = Op->GetArity();
        vector<Expression> ChildUserExps(NumChildren);
        for (uint32 i = 0; i < NumChildren; ++i) {
            ChildUserExps[i] = Children[i]->ToUserExpression(Solver, BoundOps);
        }

        return Solver->CreateExpression(Op, ChildUserExps);
    }

    const ESFixedTypeBase* GenFuncExpression::GetType() const
    {
        return Op->GetEvalType();
    }

    GenLetExpression::GenLetExpression(GenExpressionBase const* const* Bindings,
                                       GenExpressionBase const* LetBoundExp,
                                       uint32 NumBindings)
        : Bindings(Bindings), LetBoundExp(LetBoundExp), NumBindings(NumBindings)
        
    {
        // Nothing here
    }

    GenLetExpression::~GenLetExpression()
    {
        // The bindings are assumed to come from a pool
        // We don't release/free the bindings in this class
    }

    string GenLetExpression::ToString() const
    {
        ostringstream sstr;
        sstr << "(let (";
        for (uint32 i = 0; i < NumBindings; ++i) {
            if (Bindings[i] != nullptr) {
                sstr << "(LetVar_" + to_string(i) << " " << Bindings[i]->ToString() << ")";
            }
        }
        sstr << ") " << LetBoundExp->ToString() << ")";
        return sstr.str();
    }

    void GenLetExpression::Evaluate(const uint32* ParamMap,
                                    VariableMap VarMap) const
    {
        if (PartialExpression) {
            return;
        }
        // Evaluate all the let bound expressions
        // and place them on a new stack entry
        memcpy((void*)LetBindingValStack[LetBindingValStackTop + 1],
               (void*)LetBindingValStack[LetBindingValStackTop],
               sizeof(ConcreteValueBase const*) * NumBindings);

        LetBindingValStackTop++;
        for (uint32 i = 0; i < NumBindings; ++i) {
            if (Bindings[i] != nullptr) {
                // Evaluate this binding and put it on top of the stack
                Bindings[i]->Evaluate(ParamMap, VarMap);
                if (PartialExpression) {
                    return;
                }

                (const_cast<ConcreteValueBase const**>(LetBindingValStack[LetBindingValStackTop]))[i] = 
                    EvalStack[EvalStackTop - 1];

                EvalStackTop--;
            }
        }
        // Now evaluate the expression itself
        LetBoundExp->Evaluate(ParamMap, VarMap);
        // Pop the let bindings off the stack
        // but reset before
        memset((void*)LetBindingValStack[LetBindingValStackTop - 1], 0,
               sizeof(ConcreteValueBase const*) * NumBindings);
        LetBindingValStackTop--;
    }

    SMTExpr GenLetExpression::ToSMT(TheoremProver* TP, const uint32* ParamMap,
                                    const vector<SMTExpr>& BaseExprs,
                                    vector<SMTExpr>& Assumptions) const
    {
        // Create new bindings, but push them AFTER the current vars have
        // been bound. These bindings should not be visible WHILE 
        // the current bindings are being computed
        map<uint32, SMTExpr> NewBindingSMT(LetBindingSMTStack.back());
        vector<SMTExpr> NewAssumptions;

        for (uint32 i = 0; i < NumBindings; ++i) {
            if (Bindings[i] != nullptr) {
                // Make the assumptions
                auto BindingAsSMT = Bindings[i]->ToSMT(TP, ParamMap, BaseExprs, Assumptions);
                auto CurVar = TP->CreateVarExpr((string)"LetVar_" + to_string(i) + "_" +
                                                to_string(FreshVarID++),
                                                BindingAsSMT.GetSort());
                
                auto CurAssumption = TP->CreateEQExpr(CurVar, BindingAsSMT);
                NewAssumptions.push_back(CurAssumption);
                NewBindingSMT[i] = CurVar;
            }
        }

        // Now push the assumptions and SMTfy the expression itself
        LetBindingSMTStack.push_back(NewBindingSMT);
        Assumptions.insert(Assumptions.end(), NewAssumptions.begin(), NewAssumptions.end());
        auto Retval = LetBoundExp->ToSMT(TP, ParamMap, BaseExprs, Assumptions);
        LetBindingSMTStack.pop_back();
        return Retval;
    }

    Expression GenLetExpression::ToUserExpression(ESolver* Solver, 
                                                  const map<uint32, const LetBoundVarOperator*>& BoundOps) const 
    {
        auto NewMap = BoundOps;

        map<Expression, Expression> UserBindings;
        for (uint32 i = 0; i < NumBindings; ++i) {
            if (Bindings[i] != nullptr) {
                // Create new let bound var operators
                NewMap[i] = Solver->CreateLetBoundVariable((string)"LetVar_" + to_string(i), 
                                                           Bindings[i]->GetType());
                // Recurse on the binding
                UserBindings[Solver->CreateExpression(NewMap[i])] = 
                    Bindings[i]->ToUserExpression(Solver, BoundOps);
            }
        }

        // recurse on the bound in expression
        auto UserBoundInExp = LetBoundExp->ToUserExpression(Solver, NewMap);
        return Solver->CreateLetExpression(UserBindings, UserBoundInExp);
    }

    const ESFixedTypeBase* GenLetExpression::GetType() const
    {
        return LetBoundExp->GetType();
    }

} /* end namespace */

// 
// GenExpression.cpp ends here
