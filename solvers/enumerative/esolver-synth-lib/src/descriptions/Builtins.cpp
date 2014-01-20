// Builtins.cpp --- 
// 
// Filename: Builtins.cpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:56:04 2014 (-0500)
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


#include "Builtins.hpp"
#include "../solvers/ESolver.hpp"
#include "../utils/UIDGenerator.hpp"
#include "../values/ConcreteValueBase.hpp"
#include "../descriptions/ESType.hpp"
#include "../scoping/ESolverScope.hpp"
#include "../descriptions/Operators.hpp"
#include "../z3interface/TheoremProver.hpp"
#include "../scoping/ScopeManager.hpp"
#include "../values/ValueManager.hpp"
#include "../solverutils/TypeManager.hpp"
#include "../logics/LIALogic.hpp"
#include "../logics/BVLogic.hpp"

namespace ESolver {

    /**
       This file contains the implementations of builtin functions
       See Builtins.h for more details
    */

    AndConcreteFunctor::~AndConcreteFunctor()
    {
        // Nothing here
    }

    void AndConcreteFunctor::operator () (EvalMap Args,
                                          ConcreteValueBase* Result)
    {
        int64 TheValue;
        TheValue = ((Args[0]->GetValue() != 0 && Args[1]->GetValue() != 0) ? 1 : 0);
        new (Result) ConcreteValueBase(Args[0]->GetType(), TheValue);
    }
    
    string AndConcreteFunctor::ToString() const
    {
        return "AndConcreteFunctor";
    }

    ConcFunctorBase* AndConcreteFunctor::Clone() const
    {
        return new AndConcreteFunctor(GetID());
    }
    
    OrConcreteFunctor::~OrConcreteFunctor()
    {
        // Nothing here
    }
    
    void OrConcreteFunctor::operator () (EvalMap Args,
                                         ConcreteValueBase* Result)
    {
        int64 TheValue;
        TheValue = ((Args[0]->GetValue() != 0 || Args[1]->GetValue() != 0) ? 1 : 0);
        new (Result) ConcreteValueBase(Args[0]->GetType(), TheValue);
    }

    string OrConcreteFunctor::ToString() const
    {
        return "OrConcreteFunctor";
    }

    ConcFunctorBase* OrConcreteFunctor::Clone() const
    {
        return new OrConcreteFunctor(GetID());
    }

    NegConcreteFunctor::~NegConcreteFunctor()
    {
        // Nothing here
    }

    void NegConcreteFunctor::operator () (EvalMap Args,
                                          ConcreteValueBase* Result)
    {
        int64 TheValue;
        TheValue = ((Args[0]->GetValue() == 0) ? 1 : 0);
        new (Result) ConcreteValueBase(Args[0]->GetType(), TheValue);
    }

    string NegConcreteFunctor::ToString() const
    {
        return "NegConcreteFunctor";
    }

    ConcFunctorBase* NegConcreteFunctor::Clone() const
    {
        return new NegConcreteFunctor(GetID());
    }

    ImpliesConcreteFunctor::~ImpliesConcreteFunctor()
    {
        // Nothing here
    }

    void ImpliesConcreteFunctor::operator () (EvalMap Args,
                                              ConcreteValueBase* Result)
    {
        int64 TheValue;
        TheValue = ((Args[0]->GetValue() == 0 || Args[1]->GetValue() != 0) ? 1 : 0);
        new (Result) ConcreteValueBase(Args[0]->GetType(), TheValue);
    }

    string ImpliesConcreteFunctor::ToString() const
    {
        return "ImpliesConcreteFunctor";
    }

    ConcFunctorBase* ImpliesConcreteFunctor::Clone() const
    {
        return new ImpliesConcreteFunctor(GetID());
    }

    IffConcreteFunctor::~IffConcreteFunctor()
    {
        // Nothing here
    }

    void IffConcreteFunctor::operator () (EvalMap Args,
                                          ConcreteValueBase* Result)
    {
        int64 TheValue;
        TheValue = (((Args[0]->GetValue() == 0 || Args[1]->GetValue() != 0) &&
                     (Args[1]->GetValue() == 0 || Args[0]->GetValue() != 0)) ? 1 : 0);
        new (Result) ConcreteValueBase(Args[0]->GetType(), TheValue);
    }

    string IffConcreteFunctor::ToString() const
    {
        return "IffConcreteFunctor";
    }

    ConcFunctorBase* IffConcreteFunctor::Clone() const
    {
        return new IffConcreteFunctor(GetID());
    }

    EQConcreteFunctor::~EQConcreteFunctor()
    {
        // Nothing here
    }

    void EQConcreteFunctor::operator () (EvalMap Args,
                                         ConcreteValueBase* Result)
    {
        int64 TheValue;
        TheValue = ((Args[0]->GetValue() == Args[1]->GetValue()) ? 1 : 0);
        new (Result) ConcreteValueBase(Args[0]->GetType(), TheValue);
    }

    string EQConcreteFunctor::ToString() const
    {
        return "EQConcreteFunctor";
    }

    ConcFunctorBase* EQConcreteFunctor::Clone() const
    {
        return new EQConcreteFunctor(GetID());
    }

    ITEConcreteFunctor::~ITEConcreteFunctor()
    {
        // Nothing here
    }

    void ITEConcreteFunctor::operator () (EvalMap Args,
                                          ConcreteValueBase* Result)
    {
        int64 TheValue = Args[0]->GetValue() != 0 ? Args[1]->GetValue() : Args[2]->GetValue();
        new (Result) ConcreteValueBase(Args[1]->GetType(), TheValue);
    }

    string ITEConcreteFunctor::ToString() const
    {
        return "ITEConcreteFunctor";
    }

    ConcFunctorBase* ITEConcreteFunctor::Clone() const
    {
        return new ITEConcreteFunctor(GetID());
    }

    XorConcreteFunctor::~XorConcreteFunctor()
    {
        // Nothing here
    }

    void XorConcreteFunctor::operator () (EvalMap Args,
                                          ConcreteValueBase* Result)
    {
        int64 TheValue;
        TheValue = ((Args[0]->GetValue() == 0 && Args[1]->GetValue() == 1) ||
                    (Args[1]->GetValue() == 0 && Args[0]->GetValue() == 1)) ? (int64)1 : (int64)0;
        new (Result) ConcreteValueBase(Args[0]->GetType(), TheValue);
    }

    string XorConcreteFunctor::ToString() const
    {
        return "ITEConcreteFunctor";
    }

    ConcFunctorBase* XorConcreteFunctor::Clone() const
    {
        return new XorConcreteFunctor(GetID());
    }
    
    // The TP op functors
    AndSymbolicFunctor::~AndSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr AndSymbolicFunctor::operator () (TheoremProver* TP,
                                             const vector<SMTExpr>& Children,
                                             vector<SMTExpr>& Assumptions)
    {
        return TP->CreateAndExpr(Children[0], Children[1]);
    }

    string AndSymbolicFunctor::ToString() const
    {
        return "AndSymbolicFunctor";
    }

    SymbFunctorBase* AndSymbolicFunctor::Clone() const
    {
        return new AndSymbolicFunctor(GetID());
    }

    OrSymbolicFunctor::~OrSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr OrSymbolicFunctor::operator () (TheoremProver* TP,
                                            const vector<SMTExpr>& Children,
                                            vector<SMTExpr>& Assumptions)
    {
        return TP->CreateOrExpr(Children[0], Children[1]);
    }

    string OrSymbolicFunctor::ToString() const
    {
        return "OrSymbolicFunctor";
    }

    SymbFunctorBase* OrSymbolicFunctor::Clone() const
    {
        return new OrSymbolicFunctor(GetID());
    }
    
    NegSymbolicFunctor::~NegSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr NegSymbolicFunctor::operator () (TheoremProver* TP,
                                             const vector<SMTExpr>& Children,
                                             vector<SMTExpr>& Assumptions)
    {
        return TP->CreateNotExpr(Children[0]);
    }

    string NegSymbolicFunctor::ToString() const
    {
        return "NegSymbolicFunctor";
    }

    SymbFunctorBase* NegSymbolicFunctor::Clone() const
    {
        return new NegSymbolicFunctor(GetID());
    }

    ImpliesSymbolicFunctor::~ImpliesSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr ImpliesSymbolicFunctor::operator () (TheoremProver* TP,
                                                 const vector<SMTExpr>& Children,
                                                 vector<SMTExpr>& Assumptions)
    {
        return TP->CreateImpliesExpr(Children[0], Children[1]);
    }

    string ImpliesSymbolicFunctor::ToString() const
    {
        return "ImpliesSymbolicFunctor";
    }

    SymbFunctorBase* ImpliesSymbolicFunctor::Clone() const
    {
        return new ImpliesSymbolicFunctor(GetID());
    }

    IffSymbolicFunctor::~IffSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr IffSymbolicFunctor::operator () (TheoremProver* TP,
                                             const vector<SMTExpr>& Children,
                                             vector<SMTExpr>& Assumptions)
    {
        return TP->CreateIffExpr(Children[0], Children[1]);
    }

    string IffSymbolicFunctor::ToString() const
    {
        return "IffSymbolicFunctor";
    }

    SymbFunctorBase* IffSymbolicFunctor::Clone() const
    {
        return new IffSymbolicFunctor(GetID());
    }

    EQSymbolicFunctor::~EQSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr EQSymbolicFunctor::operator () (TheoremProver* TP,
                                            const vector<SMTExpr>& Children,
                                            vector<SMTExpr>& Assumptions)
    {
        return TP->CreateEQExpr(Children[0], Children[1]);
    }

    string EQSymbolicFunctor::ToString() const
    {
        return "EQSymbolicFunctor";
    }

    SymbFunctorBase* EQSymbolicFunctor::Clone() const
    {
        return new EQSymbolicFunctor(GetID());
    }

    ITESymbolicFunctor::~ITESymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr ITESymbolicFunctor::operator () (TheoremProver* TP,
                                             const vector<SMTExpr>& Children,
                                             vector<SMTExpr>& Assumptions)
    {
        return TP->CreateITEExpr(Children[0], Children[1], Children[2]);
    }

    string ITESymbolicFunctor::ToString() const
    {
        return "ITESymbolicFunctor";
    }

    SymbFunctorBase* ITESymbolicFunctor::Clone() const
    {
        return new ITESymbolicFunctor(GetID());
    }

    XorSymbolicFunctor::~XorSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr XorSymbolicFunctor::operator () (TheoremProver* TP,
                                             const vector<SMTExpr>& Children,
                                             vector<SMTExpr>& Assumptions)
    {
        return TP->CreateOrExpr(TP->CreateAndExpr(Children[0], TP->CreateNotExpr(Children[1])),
                                TP->CreateAndExpr(Children[1], TP->CreateNotExpr(Children[0])));
    }

    string XorSymbolicFunctor::ToString() const
    {
        return "XorSymbolicFunctor";
    }

    SymbFunctorBase* XorSymbolicFunctor::Clone() const
    {
        return new XorSymbolicFunctor(GetID());
    }

    void ESolver::AddBuiltins()
    {
        BoolType = TypeMgr->CreateType<ESBoolType>();
        IntType = TypeMgr->CreateType<ESIntType>();
        
        // Add the builtin ops now
        vector<const ESFixedTypeBase*> ArgVectorBin;
        ArgVectorBin.push_back(BoolType);
        ArgVectorBin.push_back(BoolType);
        vector<const ESFixedTypeBase*> ArgVectorUn;
        ArgVectorUn.push_back(BoolType);
        vector<const ESFixedTypeBase*> ArgVectorIntEQ;
        ArgVectorIntEQ.push_back(IntType);
        ArgVectorIntEQ.push_back(IntType);
        vector<const ESFixedTypeBase*> ArgVectorIntITE;
        ArgVectorIntITE.push_back(BoolType);
        ArgVectorIntITE.push_back(IntType);
        ArgVectorIntITE.push_back(IntType);

        CreateFunction("and", ArgVectorBin, BoolType, new AndSymbolicFunctor(),
                       new AndConcreteFunctor(), true, true);
        CreateFunction("or", ArgVectorBin, BoolType, new OrSymbolicFunctor(),
                       new OrConcreteFunctor(), true, true);
        CreateFunction("not", ArgVectorUn, BoolType, new NegSymbolicFunctor(),
                       new NegConcreteFunctor(), false, true);
        CreateFunction("=>", ArgVectorBin, BoolType, new ImpliesSymbolicFunctor(),
                       new ImpliesConcreteFunctor(), false, true);
        CreateFunction("<=>", ArgVectorBin, BoolType, new IffSymbolicFunctor(),
                       new IffConcreteFunctor(), true, true);
        CreateFunction("xor", ArgVectorBin, BoolType, new XorSymbolicFunctor(),
                       new XorConcreteFunctor(), true, true);

        // Add the EQ op for integers
        // EQ is always symmetric by definition
        CreateFunction("=", ArgVectorIntEQ, BoolType, new EQSymbolicFunctor(),
                       new EQConcreteFunctor(), true, true);

        // Add the EQ op for booleans
        CreateFunction("=", ArgVectorBin, BoolType, new EQSymbolicFunctor(),
                       new EQConcreteFunctor(), true, true);
        
        // Add the ITE Op for integers
        CreateFunction("ite", ArgVectorIntITE, IntType, new ITESymbolicFunctor(),
                       new ITEConcreteFunctor(), false, true);
        
        TrueValue = ValMgr->GetValue(BoolType, 1);
        FalseValue = ValMgr->GetValue(BoolType, 0);

        // Load logics
        auto LIA = new LIALogic(this);
        LIA->Init();
        LoadedLogics.push_back(LIA);
        auto BV = new BVLogic(this);
        BV->Init();
        LoadedLogics.push_back(BV);
        LoadedBVLogic = BV;
    }

} /* End namespace */

// 
// Builtins.cpp ends here
