// LIALogic.cpp --- 
// 
// Filename: LIALogic.cpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:55:19 2014 (-0500)
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


#include "LIALogic.hpp"
#include "../z3interface/Z3Objects.hpp"
#include "../z3interface/TheoremProver.hpp"
#include "../values/ConcreteValueBase.hpp"
#include "../descriptions/ESType.hpp"
#include "../solvers/ESolver.hpp"

namespace ESolverLIALogic {

    LIAConcreteFunctor::LIAConcreteFunctor(const ESFixedTypeBase* IntType,
                                           const ESFixedTypeBase* BoolType)
        : ConcFunctorBase(), IntType(IntType), BoolType(BoolType)
    {
        // Nothing here
    }

    LIAConcreteFunctor::LIAConcreteFunctor(const ESFixedTypeBase* IntType,
                                           const ESFixedTypeBase* BoolType,
                                           uint64 UID)
        : ConcFunctorBase(UID), IntType(IntType), BoolType(BoolType)
    {
        // Nothing here
    }

    LIAConcreteFunctor::~LIAConcreteFunctor()
    {
        // Nothing here
    }

    LIASymbolicFunctor::LIASymbolicFunctor(const ESFixedTypeBase* IntType,
                                           const ESFixedTypeBase* BoolType)
        : SymbFunctorBase(), IntType(IntType), BoolType(BoolType)
    {
        // Nothing here
    }

    LIASymbolicFunctor::LIASymbolicFunctor(const ESFixedTypeBase* IntType,
                                           const ESFixedTypeBase* BoolType,
                                           uint64 UID)
        : SymbFunctorBase(UID), IntType(IntType), BoolType(BoolType)
    {
        // Nothing here
    }

    LIASymbolicFunctor::~LIASymbolicFunctor()
    {
        // Nothing here
    }

    AddConcreteFunctor::~AddConcreteFunctor()
    {
        // Nothing here
    }

    void AddConcreteFunctor::operator() (EvalMap Args,
                                         ConcreteValueBase* Result)
    {
        new (Result) ConcreteValueBase(IntType, Args[0]->GetValue() + Args[1]->GetValue());
    }

    string AddConcreteFunctor::ToString() const
    {
        return "AddConcreteFunctor";
    }

    ConcFunctorBase* AddConcreteFunctor::Clone() const
    {
        return new AddConcreteFunctor(IntType, BoolType, GetID());
    }

    AddSymbolicFunctor::~AddSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr AddSymbolicFunctor::operator () (TheoremProver* TP,
                                             const vector<SMTExpr>& Args,
                                             vector<SMTExpr>& Assumptions)
    {
        return TP->CreatePlusExpr(Args[0], Args[1]);
    }

    string AddSymbolicFunctor::ToString() const
    {
        return "AddSymbolicFunctor";
    }

    SymbFunctorBase* AddSymbolicFunctor::Clone() const
    {
        return new AddSymbolicFunctor(IntType, BoolType, GetID());
    }

    SubConcreteFunctor::~SubConcreteFunctor()
    {
        // Nothing here
    }

    void SubConcreteFunctor::operator () (EvalMap Args,
                                          ConcreteValueBase* Result)
    {
        new (Result) ConcreteValueBase(IntType, Args[0]->GetValue() - Args[1]->GetValue());
    }

    string SubConcreteFunctor::ToString() const
    {
        return "SubConcreteFunctor";
    }

    ConcFunctorBase* SubConcreteFunctor::Clone() const
    {
        return new SubConcreteFunctor(IntType, BoolType, GetID());
    }
    
    SubSymbolicFunctor::~SubSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr SubSymbolicFunctor::operator () (TheoremProver* TP,
                                             const vector<SMTExpr>& Args,
                                             vector<SMTExpr>& Assumptions)
    {
        return TP->CreateMinusExpr(Args[0], Args[1]);
    }

    string SubSymbolicFunctor::ToString() const
    {
        return "SubSymbolicFunctor";
    }

    SymbFunctorBase* SubSymbolicFunctor::Clone() const
    {
        return new SubSymbolicFunctor(IntType, BoolType, GetID());
    }

    MinusConcreteFunctor::~MinusConcreteFunctor()
    {
        // Nothing here
    }

    void MinusConcreteFunctor::operator () (EvalMap Args,
                                            ConcreteValueBase* Result)
    {
        new (Result) ConcreteValueBase(IntType, (- Args[0]->GetValue()));
    }

    string MinusConcreteFunctor::ToString() const
    {
        return "MinusConcreteFunctor";
    }

    ConcFunctorBase* MinusConcreteFunctor::Clone() const
    {
        return new MinusConcreteFunctor(IntType, BoolType, GetID());
    }

    MinusSymbolicFunctor::~MinusSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr MinusSymbolicFunctor::operator () (TheoremProver* TP,
                                               const vector<SMTExpr>& Args,
                                               vector<SMTExpr>& Assumptions)
    {
        return TP->CreateNegExpr(Args[0]);
    }

    string MinusSymbolicFunctor::ToString() const
    {
        return "MinusSymbolicFunctor";
    }
    
    SymbFunctorBase* MinusSymbolicFunctor::Clone() const
    {
        return new MinusSymbolicFunctor(IntType, BoolType, GetID());
    }

    MulConcreteFunctor::~MulConcreteFunctor()
    {
        // Nothing here
    }

    void MulConcreteFunctor::operator () (EvalMap Args,
                                          ConcreteValueBase* Result)
    {
        new (Result) ConcreteValueBase(IntType, Args[0]->GetValue() * Args[1]->GetValue());
    }

    string MulConcreteFunctor::ToString() const
    {
        return "MulConcreteFunctor";
    }

    ConcFunctorBase* MulConcreteFunctor::Clone() const
    {
        return new MulConcreteFunctor(IntType, BoolType, GetID());
    }

    MulSymbolicFunctor::~MulSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr MulSymbolicFunctor::operator () (TheoremProver* TP,
                                             const vector<SMTExpr>& Args,
                                             vector<SMTExpr>& Assumptions)
    {
        return TP->CreateMulExpr(Args[0], Args[1]);
    }

    string MulSymbolicFunctor::ToString() const
    {
        return "MulSymbolicFunctor";
    }

    SymbFunctorBase* MulSymbolicFunctor::Clone() const
    {
        return new MulSymbolicFunctor(IntType, BoolType, GetID());
    }

    GTConcreteFunctor::~GTConcreteFunctor()
    {
        // Nothing here
    }

    void GTConcreteFunctor::operator() (EvalMap Args,
                                        ConcreteValueBase* Result)
    {
        new (Result) ConcreteValueBase(BoolType, 
                                       Args[0]->GetValue() > Args[1]->GetValue() ? (int64)1 : (int64)0);
    }

    string GTConcreteFunctor::ToString() const
    {
        return "GTConcreteFunctor";
    }

    ConcFunctorBase* GTConcreteFunctor::Clone() const
    {
        return new GTConcreteFunctor(IntType, BoolType, GetID());
    }

    GTSymbolicFunctor::~GTSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr GTSymbolicFunctor::operator () (TheoremProver* TP,
                                            const vector<SMTExpr>& Args,
                                            vector<SMTExpr>& Assumptions)
    {
        return TP->CreateGTExpr(Args[0], Args[1]);
    }

    string GTSymbolicFunctor::ToString() const
    {
        return "GTSymbolicFunctor";
    }

    SymbFunctorBase* GTSymbolicFunctor::Clone() const
    {
        return new GTSymbolicFunctor(IntType, BoolType, GetID());
    }

    GEConcreteFunctor::~GEConcreteFunctor()
    {
        // Nothing here
    }

    void GEConcreteFunctor::operator() (EvalMap Args,
                                        ConcreteValueBase* Result)
    {
        new (Result) ConcreteValueBase(BoolType, 
                                       Args[0]->GetValue() >= Args[1]->GetValue() ? (int64)1 : (int64)0);
    }

    string GEConcreteFunctor::ToString() const
    {
        return "GEConcreteFunctor";
    }

    ConcFunctorBase* GEConcreteFunctor::Clone() const
    {
        return new GEConcreteFunctor(IntType, BoolType, GetID());
    }

    GESymbolicFunctor::~GESymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr GESymbolicFunctor::operator () (TheoremProver* TP,
                                            const vector<SMTExpr>& Args,
                                            vector<SMTExpr>& Assumptions)
    {
        return TP->CreateGEExpr(Args[0], Args[1]);
    }

    string GESymbolicFunctor::ToString() const
    {
        return "GESymbolicFunctor";
    }

    SymbFunctorBase* GESymbolicFunctor::Clone() const
    {
        return new GESymbolicFunctor(IntType, BoolType, GetID());
    }

    LTConcreteFunctor::~LTConcreteFunctor()
    {
        // Nothing here
    }

    void LTConcreteFunctor::operator() (EvalMap Args,
                                        ConcreteValueBase* Result)
    {
        new (Result) ConcreteValueBase(BoolType,
                                       Args[0]->GetValue() < Args[1]->GetValue() ? (int64)1 : (int64)0);
    }

    string LTConcreteFunctor::ToString() const
    {
        return "LTConcreteFunctor";
    }

    ConcFunctorBase* LTConcreteFunctor::Clone() const
    {
        return new LTConcreteFunctor(IntType, BoolType, GetID());
    }

    LTSymbolicFunctor::~LTSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr LTSymbolicFunctor::operator () (TheoremProver* TP,
                                            const vector<SMTExpr>& Args,
                                            vector<SMTExpr>& Assumptions)
    {
        return TP->CreateLTExpr(Args[0], Args[1]);
    }

    string LTSymbolicFunctor::ToString() const
    {
        return "LTSymbolicFunctor";
    }

    SymbFunctorBase* LTSymbolicFunctor::Clone() const
    {
        return new LTSymbolicFunctor(IntType, BoolType, GetID());
    }

    LEConcreteFunctor::~LEConcreteFunctor()
    {
        // Nothing here
    }

    void LEConcreteFunctor::operator() (EvalMap Args,
                                        ConcreteValueBase* Result)
    {
        new (Result) ConcreteValueBase(BoolType,
                                       Args[0]->GetValue() <= Args[1]->GetValue() ? (int64)1 : (int64)0);
    }

    string LEConcreteFunctor::ToString() const
    {
        return "GEConcreteFunctor";
    }

    ConcFunctorBase* LEConcreteFunctor::Clone() const
    {
        return new LEConcreteFunctor(IntType, BoolType, GetID());
    }

    LESymbolicFunctor::~LESymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr LESymbolicFunctor::operator () (TheoremProver* TP,
                                            const vector<SMTExpr>& Args,
                                            vector<SMTExpr>& Assumptions)
    {
        return TP->CreateLEExpr(Args[0], Args[1]);
    }

    string LESymbolicFunctor::ToString() const
    {
        return "GESymbolicFunctor";
    }

    SymbFunctorBase* LESymbolicFunctor::Clone() const
    {
        return new LESymbolicFunctor(IntType, BoolType, GetID());
    }
    
} /* End ESolverLIALogic namespace */

using namespace ESolverLIALogic;

namespace ESolver {

    LIALogic::LIALogic(ESolver* Solver)
        : ESolverLogic("LIALogic", Solver)
    {
        // Nothing here
    }

    LIALogic::~LIALogic()
    {

    }

    void LIALogic::Init()
    {
        auto IntType = Solver->CreateIntType();
        auto BoolType = Solver->CreateBoolType();

        vector<const ESFixedTypeBase*> BinOpArgTypes(2);
        vector<const ESFixedTypeBase*> UnOpArgTypes(1);

        UnOpArgTypes[0] = BinOpArgTypes[0] = 
            BinOpArgTypes[1] = Solver->CreateIntType();

        Solver->CreateFunction("+", BinOpArgTypes, IntType,
                               new AddSymbolicFunctor(IntType, BoolType),
                               new AddConcreteFunctor(IntType, BoolType),
                               true, true);

        Solver->CreateFunction("-", BinOpArgTypes, IntType,
                               new SubSymbolicFunctor(IntType, BoolType), 
                               new SubConcreteFunctor(IntType, BoolType), 
                               false, true);

        Solver->CreateFunction("-", UnOpArgTypes, IntType,
                               new MinusSymbolicFunctor(IntType, BoolType), 
                               new MinusConcreteFunctor(IntType, BoolType), 
                               false, true);

        Solver->CreateFunction("*", BinOpArgTypes, IntType,
                               new MulSymbolicFunctor(IntType, BoolType), 
                               new MulConcreteFunctor(IntType, BoolType), 
                               true, true);

        Solver->CreateFunction(">", BinOpArgTypes, BoolType,
                               new GTSymbolicFunctor(IntType, BoolType), 
                               new GTConcreteFunctor(IntType, BoolType), 
                               false, true);

        Solver->CreateFunction(">=", BinOpArgTypes, BoolType,
                               new GESymbolicFunctor(IntType, BoolType), 
                               new GEConcreteFunctor(IntType, BoolType), 
                               false, true);

        Solver->CreateFunction("<", BinOpArgTypes, BoolType,
                               new LTSymbolicFunctor(IntType, BoolType), 
                               new LTConcreteFunctor(IntType, BoolType), 
                               false, true);

        Solver->CreateFunction("<=", BinOpArgTypes, BoolType,
                               new LESymbolicFunctor(IntType, BoolType), 
                               new LEConcreteFunctor(IntType, BoolType), 
                               false, true);
    }

} /* End namespace */

// 
// LIALogic.cpp ends here
