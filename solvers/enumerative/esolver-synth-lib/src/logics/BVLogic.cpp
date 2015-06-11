// BVLogic.cpp ---
//
// Filename: BVLogic.cpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:55:11 2014 (-0500)
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


#include "BVLogic.hpp"
#include "../descriptions/ESType.hpp"
#include "../z3interface/TheoremProver.hpp"
#include "../descriptions/Builtins.hpp"
#include "../values/ConcreteValueBase.hpp"
#include "../solvers/ESolver.hpp"
#include <iostream>
#include <iomanip>

using namespace std;

namespace ESolver {

    set<string> BVLogic::ReservedNames = { "bvnot",
                                           "bvand",
                                           "bvor",
                                           "bvneg",
                                           "bvadd",
                                           "bvmul",
                                           "bvudiv",
                                           "bvurem",
                                           "bvshl",
                                           "bvlshr",
                                           "bvult",
                                           "bvnand",
                                           "bvnor",
                                           "bvxor",
                                           "bvxnor",
                                           "bvcomp",
                                           "bvsub",
                                           "bvsdiv",
                                           "bvsrem",
                                           "bvsmod",
                                           "bvashr",
                                           "bvule",
                                           "bvugt",
                                           "bvuge",
                                           "bvslt",
                                           "bvsle",
                                           "bvsgt",
                                           "bvtouint",
                                           "bvtosint",
                                           "bvtobool",
                                           "bvredor",
                                           "bvredand",
                                           "bvconcat",
                                           "bvextract" };

}

namespace ESolverBVLogic {

    BVConcreteFunctor::BVConcreteFunctor(const ESFixedTypeBase* Type,
                                         const ESFixedTypeBase* BoolType)
        : ConcFunctorBase(), Type(Type), BoolType(BoolType)
    {
        // Construct the mask
        Mask = 0;
        const uint32 NumBits = Type->As<ESBVType>()->GetSize();
        if (NumBits == 64) {
            Mask = (uint64)0xFFFFFFFFFFFFFFFF;
        } else {
            Mask = (((uint64)1 << NumBits) - 1);
        }
    }

    BVConcreteFunctor::BVConcreteFunctor(const ESFixedTypeBase* Type,
                                         const ESFixedTypeBase* BoolType,
                                         uint64 ID)
        : ConcFunctorBase(ID), Type(Type), BoolType(BoolType)
    {
        // Construct the mask
        Mask = 0;
        const uint32 NumBits = Type->As<ESBVType>()->GetSize();
        if (NumBits == 64) {
            Mask = (uint64)0xFFFFFFFFFFFFFFFF;
        } else {
            Mask = (((uint64)1 << NumBits) - 1);
        }
    }

    BVConcreteFunctor::~BVConcreteFunctor()
    {
        // Nothing here
    }

    BVSymbolicFunctor::BVSymbolicFunctor(const ESFixedTypeBase* Type,
                                         const ESFixedTypeBase* BoolType)
        : SymbFunctorBase(), Type(Type), BoolType(BoolType)
    {
        // Nothing here
    }

    BVSymbolicFunctor::BVSymbolicFunctor(const ESFixedTypeBase* Type,
                                         const ESFixedTypeBase* BoolType,
                                         uint64 ID)
        : SymbFunctorBase(ID), Type(Type), BoolType(BoolType)
    {
        // Nothing here
    }

    BVSymbolicFunctor::~BVSymbolicFunctor()
    {
        // Nothing here
    }

    BVAddConcreteFunctor::~BVAddConcreteFunctor()
    {
        // Nothing here
    }

    void BVAddConcreteFunctor::operator () (EvalMap Args,
                                            ConcreteValueBase* Result)
    {
        int64 Arg1 = Args[0]->GetValue();
        int64 Arg2 = Args[1]->GetValue();
        uint32 Shift = 64 - Type->As<ESBVType>()->GetSize();

        if (Shift != 0) {
            // Sign extend the args
            Arg1 = (Arg1 << Shift) >> Shift;
            Arg2 = (Arg2 << Shift) >> Shift;
        }

        // Add the args
        int64 ResultVal = Arg1 + Arg2;
        // Mask off the higher bits
        ResultVal = ResultVal & Mask;
        new (Result) ConcreteValueBase(Type, ResultVal);
    }

    ConcFunctorBase* BVAddConcreteFunctor::Clone() const
    {
        return new BVAddConcreteFunctor(Type, BoolType, GetID());
    }

    string BVAddConcreteFunctor::ToString() const
    {
        return "BVAddConcreteFunctor";
    }

    BVAddSymbolicFunctor::~BVAddSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVAddSymbolicFunctor::operator () (TheoremProver* TP,
                                               const vector<SMTExpr>& Args,
                                               vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVAddExpr(Args[0], Args[1]);
    }

    SymbFunctorBase* BVAddSymbolicFunctor::Clone() const
    {
        return new BVAddSymbolicFunctor(Type, BoolType, GetID());
    }

    string BVAddSymbolicFunctor::ToString() const
    {
        return "BVAddSymbolicFunctor";
    }

    BVSubConcreteFunctor::~BVSubConcreteFunctor()
    {
        // Nothing here
    }

    void BVSubConcreteFunctor::operator () (EvalMap Args,
                                            ConcreteValueBase* Result)
    {
        int64 Arg1 = Args[0]->GetValue();
        int64 Arg2 = Args[1]->GetValue();
        const uint32 Shift = 64 - Type->As<ESBVType>()->GetSize();

        // Sign extend the args
        if (Shift != 0) {
            Arg1 = (Arg1 << Shift) >> Shift;
            Arg2 = (Arg2 << Shift) >> Shift;
        }

        // Do the sub
        int64 ResultVal = Arg1 - Arg2;
        // Mask off the higher bits
        ResultVal = ResultVal & Mask;
        new (Result) ConcreteValueBase(Type, ResultVal);
    }

    ConcFunctorBase* BVSubConcreteFunctor::Clone() const
    {
        return new BVSubConcreteFunctor(Type, BoolType, GetID());
    }

    string BVSubConcreteFunctor::ToString() const
    {
        return "BVSubConcreteFunctor";
    }

    BVSubSymbolicFunctor::~BVSubSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVSubSymbolicFunctor::operator () (TheoremProver* TP,
                                               const vector<SMTExpr>& Args,
                                               vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVSubExpr(Args[0], Args[1]);
    }

    SymbFunctorBase* BVSubSymbolicFunctor::Clone() const
    {
        return new BVSubSymbolicFunctor(Type, BoolType, GetID());
    }

    string BVSubSymbolicFunctor::ToString() const
    {
        return "BVSubSymbolicFunctor";
    }

    BVAndConcreteFunctor::~BVAndConcreteFunctor()
    {
        // Nothing here
    }

    void BVAndConcreteFunctor::operator () (EvalMap Args,
                                            ConcreteValueBase* Result)
    {
        int64 Arg1 = Args[0]->GetValue();
        int64 Arg2 = Args[1]->GetValue();

        int64 ResultVal = Arg1 & Arg2;
        ResultVal = ResultVal & Mask;
        new (Result) ConcreteValueBase(Type, ResultVal);
    }

    ConcFunctorBase* BVAndConcreteFunctor::Clone() const
    {
        return new BVAndConcreteFunctor(Type, BoolType, GetID());
    }

    string BVAndConcreteFunctor::ToString() const
    {
        return "BVAndConcreteFunctor";
    }

    BVAndSymbolicFunctor::~BVAndSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVAndSymbolicFunctor::operator () (TheoremProver* TP,
                                               const vector<SMTExpr>& Args,
                                               vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVAndExpr(Args[0], Args[1]);
    }

    SymbFunctorBase* BVAndSymbolicFunctor::Clone() const
    {
        return new BVAndSymbolicFunctor(Type, BoolType, GetID());
    }

    string BVAndSymbolicFunctor::ToString() const
    {
        return "BVAndSymbolicFunctor";
    }

    BVOrConcreteFunctor::~BVOrConcreteFunctor()
    {
        // Nothing here
    }

    void BVOrConcreteFunctor::operator () (EvalMap Args,
                                           ConcreteValueBase* Result)
    {
        int64 Arg1 = Args[0]->GetValue();
        int64 Arg2 = Args[1]->GetValue();
        int64 ResultVal = Arg1 | Arg2;
        ResultVal = ResultVal & Mask;
        new (Result) ConcreteValueBase(Type, ResultVal);
    }

    ConcFunctorBase* BVOrConcreteFunctor::Clone() const
    {
        return new BVOrConcreteFunctor(Type, BoolType, GetID());
    }

    string BVOrConcreteFunctor::ToString() const
    {
        return "BVOrConcreteFunctor";
    }

    BVOrSymbolicFunctor::~BVOrSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVOrSymbolicFunctor::operator () (TheoremProver* TP,
                                              const vector<SMTExpr>& Args,
                                              vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVOrExpr(Args[0], Args[1]);
    }

    SymbFunctorBase* BVOrSymbolicFunctor::Clone() const
    {
        return new BVOrSymbolicFunctor(Type, BoolType, GetID());
    }

    string BVOrSymbolicFunctor::ToString() const
    {
        return "BVOrSymbolicFunctor";
    }

    BVNotConcreteFunctor::~BVNotConcreteFunctor()
    {
        // Nothing here
    }

    void BVNotConcreteFunctor::operator () (EvalMap Args,
                                            ConcreteValueBase* Result)
    {
        int64 Arg = Args[0]->GetValue();
        int64 ResultVal = ~Arg;
        ResultVal = ResultVal & Mask;
        new (Result) ConcreteValueBase(Type, ResultVal);
    }

    ConcFunctorBase* BVNotConcreteFunctor::Clone() const
    {
        return new BVNotConcreteFunctor(Type, BoolType, GetID());
    }

    string BVNotConcreteFunctor::ToString() const
    {
        return "BVNotConcreteFunctor";
    }

    BVNotSymbolicFunctor::~BVNotSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVNotSymbolicFunctor::operator () (TheoremProver* TP,
                                               const vector<SMTExpr>& Args,
                                               vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVNotExpr(Args[0]);
    }

    SymbFunctorBase* BVNotSymbolicFunctor::Clone() const
    {
        return new BVNotSymbolicFunctor(Type, BoolType, GetID());
    }

    string BVNotSymbolicFunctor::ToString() const
    {
        return "BVNotSymbolicFunctor";
    }

    BVNandConcreteFunctor::~BVNandConcreteFunctor()
    {
        // Nothing here
    }

    void BVNandConcreteFunctor::operator () (EvalMap Args,
                                             ConcreteValueBase* Result)
    {
        int64 Arg1 = Args[0]->GetValue();
        int64 Arg2 = Args[1]->GetValue();

        int64 ResultVal = Arg1 & Arg2;
        ResultVal = ~ResultVal;
        ResultVal = ResultVal & Mask;
        new (Result) ConcreteValueBase(Type, ResultVal);
    }

    ConcFunctorBase* BVNandConcreteFunctor::Clone() const
    {
        return new BVNandConcreteFunctor(Type, BoolType, GetID());
    }

    string BVNandConcreteFunctor::ToString() const
    {
        return "BVNandConcreteFunctor";
    }

    BVNandSymbolicFunctor::~BVNandSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVNandSymbolicFunctor::operator () (TheoremProver* TP,
                                                const vector<SMTExpr>& Args,
                                                vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVNotExpr(TP->CreateBVAndExpr(Args[0], Args[1]));
    }

    SymbFunctorBase* BVNandSymbolicFunctor::Clone() const
    {
        return new BVNandSymbolicFunctor(Type, BoolType, GetID());
    }

    string BVNandSymbolicFunctor::ToString() const
    {
        return "BVNandSymbolicFunctor";
    }

    BVNorConcreteFunctor::~BVNorConcreteFunctor()
    {
        // Nothing here
    }

    void BVNorConcreteFunctor::operator () (EvalMap Args,
                                            ConcreteValueBase* Result)
    {
        int64 Arg1 = Args[0]->GetValue();
        int64 Arg2 = Args[1]->GetValue();

        int64 ResultVal = Arg1 | Arg2;
        ResultVal = ~ResultVal;
        ResultVal = ResultVal & Mask;
        new (Result) ConcreteValueBase(Type, ResultVal);
    }

    ConcFunctorBase* BVNorConcreteFunctor::Clone() const
    {
        return new BVNorConcreteFunctor(Type, BoolType, GetID());
    }

    string BVNorConcreteFunctor::ToString() const
    {
        return "BVNorConcreteFunctor";
    }

    BVNorSymbolicFunctor::~BVNorSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVNorSymbolicFunctor::operator () (TheoremProver* TP,
                                               const vector<SMTExpr>& Args,
                                               vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVNotExpr(TP->CreateBVOrExpr(Args[0], Args[1]));
    }

    SymbFunctorBase* BVNorSymbolicFunctor::Clone() const
    {
        return new BVNorSymbolicFunctor(Type, BoolType, GetID());
    }

    string BVNorSymbolicFunctor::ToString() const
    {
        return "BVNorSymbolicFunctor";
    }

    BVXorConcreteFunctor::~BVXorConcreteFunctor()
    {
        // Nothing here
    }

    void BVXorConcreteFunctor::operator () (EvalMap Args,
                                            ConcreteValueBase* Result)
    {
        int64 Arg1 = Args[0]->GetValue();
        int64 Arg2 = Args[1]->GetValue();

        int64 ResultVal = Arg1 ^ Arg2;
        ResultVal = ResultVal & Mask;
        new (Result) ConcreteValueBase(Type, ResultVal);
    }

    ConcFunctorBase* BVXorConcreteFunctor::Clone() const
    {
        return new BVXorConcreteFunctor(Type, BoolType, GetID());
    }

    string BVXorConcreteFunctor::ToString() const
    {
        return "BVXorConcreteFunctor";
    }

    BVXorSymbolicFunctor::~BVXorSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVXorSymbolicFunctor::operator () (TheoremProver* TP,
                                               const vector<SMTExpr>& Args,
                                               vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVXorExpr(Args[0], Args[1]);
    }

    SymbFunctorBase* BVXorSymbolicFunctor::Clone() const
    {
        return new BVXorSymbolicFunctor(Type, BoolType, GetID());
    }

    string BVXorSymbolicFunctor::ToString() const
    {
        return "BVXorSymbolicFunctor";
    }

    BVXNorConcreteFunctor::~BVXNorConcreteFunctor()
    {
        // Nothing here
    }

    void BVXNorConcreteFunctor::operator () (EvalMap Args,
                                             ConcreteValueBase* Result)
    {
        int64 Arg1 = Args[0]->GetValue();
        int64 Arg2 = Args[1]->GetValue();

        int64 ResultVal = Arg1 ^ Arg2;
        ResultVal = ~ResultVal;
        ResultVal = ResultVal & Mask;
        new (Result) ConcreteValueBase(Type, ResultVal);
    }

    ConcFunctorBase* BVXNorConcreteFunctor::Clone() const
    {
        return new BVXNorConcreteFunctor(Type, BoolType, GetID());
    }

    string BVXNorConcreteFunctor::ToString() const
    {
        return "BVXNorConcreteFunctor";
    }

    BVXNorSymbolicFunctor::~BVXNorSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVXNorSymbolicFunctor::operator () (TheoremProver* TP,
                                                const vector<SMTExpr>& Args,
                                                vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVNotExpr(TP->CreateBVXorExpr(Args[0], Args[1]));
    }

    SymbFunctorBase* BVXNorSymbolicFunctor::Clone() const
    {
        return new BVXNorSymbolicFunctor(Type, BoolType, GetID());
    }

    string BVXNorSymbolicFunctor::ToString() const
    {
        return "BVXNorSymbolicFunctor";
    }

    BVShlConcreteFunctor::~BVShlConcreteFunctor()
    {
        // Nothing here
    }

    void BVShlConcreteFunctor::operator () (EvalMap Args,
                                            ConcreteValueBase* Result)
    {
        uint64 Arg1 = (uint64)Args[0]->GetValue();
        uint64 Arg2 = (uint64)Args[1]->GetValue();
        uint64 ResultBits;
        if(Arg2 == 0) {
            ResultBits = Arg1;
        } else if (Arg2 >= 64) {
            ResultBits = (int64)0;
        } else {
            ResultBits = Arg1 << Arg2;
        }
        ResultBits = ResultBits & Mask;
        new (Result) ConcreteValueBase(Type, ResultBits);
    }

    ConcFunctorBase* BVShlConcreteFunctor::Clone() const
    {
        return new BVShlConcreteFunctor(Type, BoolType, GetID());
    }

    string BVShlConcreteFunctor::ToString() const
    {
        return "BVShlConcreteFunctor";
    }

    BVShlSymbolicFunctor::~BVShlSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVShlSymbolicFunctor::operator () (TheoremProver* TP,
                                               const vector<SMTExpr>& Args,
                                               vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVShLExpr(Args[0], Args[1]);
    }

    SymbFunctorBase* BVShlSymbolicFunctor::Clone() const
    {
        return new BVShlSymbolicFunctor(Type, BoolType, GetID());
    }

    string BVShlSymbolicFunctor::ToString() const
    {
        return "BVShlSymbolicFunctor";
    }

    BVAShrConcreteFunctor::~BVAShrConcreteFunctor()
    {
        // Nothing here
    }

    // Arithmetic shift left
    void BVAShrConcreteFunctor::operator () (EvalMap Args,
                                             ConcreteValueBase* Result)
    {
        int64 Arg1 = Args[0]->GetValue();
        uint64 Arg2 = (uint64)Args[1]->GetValue();
        const uint32 Shift = 64 - Type->As<ESBVType>()->GetSize();

        // Sign extend the argument
        if (Shift != 0) {
            Arg1 = (Arg1 << Shift) >> Shift;
        }

        int64 ResultBits;
        if(Arg2 == 0) {
            ResultBits = Arg1;
        } else if ((uint64)Arg2 < 64) {
            ResultBits = Arg1 >> Arg2;
        } else {
            if (Arg1 >= 0) {
                ResultBits = 0;
            } else {
                ResultBits = -1;
            }
        }
        ResultBits = ResultBits & Mask;
        new (Result) ConcreteValueBase(Type, ResultBits);
    }

    ConcFunctorBase* BVAShrConcreteFunctor::Clone() const
    {
        return new BVAShrConcreteFunctor(Type, BoolType, GetID());
    }

    string BVAShrConcreteFunctor::ToString() const
    {
        return "BVAShrConcreteFunctor";
    }

    BVAShrSymbolicFunctor::~BVAShrSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVAShrSymbolicFunctor::operator () (TheoremProver* TP,
                                                const vector<SMTExpr>& Args,
                                                vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVAShRExpr(Args[0], Args[1]);
    }

    SymbFunctorBase* BVAShrSymbolicFunctor::Clone() const
    {
        return new BVAShrSymbolicFunctor(Type, BoolType, GetID());
    }

    string BVAShrSymbolicFunctor::ToString() const
    {
        return "BVAShrSymbolicFunctor";
    }

    BVLShrConcreteFunctor::~BVLShrConcreteFunctor()
    {
        // Nothing here
    }

    void BVLShrConcreteFunctor::operator () (EvalMap Args,
                                             ConcreteValueBase* Result)
    {
        uint64 Arg1 = (uint64)Args[0]->GetValue();
        uint64 Arg2 = (uint64)Args[1]->GetValue();
        uint64 ResultBits;

        if(Arg2 == 0) {
            ResultBits = Arg1;
        } else if (Arg2 < 64) {
            ResultBits = Arg1 >> Arg2;
        } else {
            ResultBits = 0;
        }
        ResultBits = ResultBits & Mask;
        new (Result) ConcreteValueBase(Type, ResultBits);
    }

    ConcFunctorBase* BVLShrConcreteFunctor::Clone() const
    {
        return new BVLShrConcreteFunctor(Type, BoolType, GetID());
    }

    string BVLShrConcreteFunctor::ToString() const
    {
        return "BVLShrConcreteFunctor";
    }

    BVLShrSymbolicFunctor::~BVLShrSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVLShrSymbolicFunctor::operator () (TheoremProver* TP,
                                                const vector<SMTExpr>& Args,
                                                vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVLShRExpr(Args[0], Args[1]);
    }

    SymbFunctorBase* BVLShrSymbolicFunctor::Clone() const
    {
        return new BVLShrSymbolicFunctor(Type, BoolType, GetID());
    }

    string BVLShrSymbolicFunctor::ToString() const
    {
        return "BVLShrSymbolicFunctor";
    }

    BVNegConcreteFunctor::~BVNegConcreteFunctor()
    {
        // Nothing here
    }

    void BVNegConcreteFunctor::operator () (EvalMap Args,
                                            ConcreteValueBase* Result)
    {
        int64 Arg = Args[0]->GetValue();
        const uint32 Shift = 64 - Type->As<ESBVType>()->GetSize();

        // Sign extend
        if (Shift != 0) {
            Arg = (Arg << Shift) >> Shift;
        }

        // Negate
        int64 ResultBits = -Arg;
        // Mask
        ResultBits = ResultBits & Mask;
        new (Result) ConcreteValueBase(Type, ResultBits);
    }

    ConcFunctorBase* BVNegConcreteFunctor::Clone() const
    {
        return new BVNegConcreteFunctor(Type, BoolType, GetID());
    }

    string BVNegConcreteFunctor::ToString() const
    {
        return "BVNegConcreteFunctor";
    }

    BVNegSymbolicFunctor::~BVNegSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVNegSymbolicFunctor::operator () (TheoremProver* TP,
                                               const vector<SMTExpr>& Args,
                                               vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVNegExpr(Args[0]);
    }

    SymbFunctorBase* BVNegSymbolicFunctor::Clone() const
    {
        return new BVNegSymbolicFunctor(Type, BoolType, GetID());
    }

    string BVNegSymbolicFunctor::ToString() const
    {
        return "BVNegSymbolicFunctor";
    }

    BVUSLEConcreteFunctor::~BVUSLEConcreteFunctor()
    {
        // Nothing here
    }

    void BVUSLEConcreteFunctor::operator () (EvalMap Args,
                                             ConcreteValueBase* Result)
    {
        uint64 Arg1 = (uint64)Args[0]->GetValue();
        uint64 Arg2 = (uint64)Args[1]->GetValue();

        int64 ResultVal = (Arg1 <= Arg2) ? 1 : 0;
        new (Result) ConcreteValueBase(BoolType, ResultVal);
    }

    ConcFunctorBase* BVUSLEConcreteFunctor::Clone() const
    {
        return new BVUSLEConcreteFunctor(Type, BoolType, GetID());
    }

    string BVUSLEConcreteFunctor::ToString() const
    {
        return "BVUSLEConcreteFunctor";
    }

    BVUSLESymbolicFunctor::~BVUSLESymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVUSLESymbolicFunctor::operator () (TheoremProver* TP,
                                                const vector<SMTExpr>& Args,
                                                vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVUSLEExpr(Args[0], Args[1]);
    }

    SymbFunctorBase* BVUSLESymbolicFunctor::Clone() const
    {
        return new BVUSLESymbolicFunctor(Type, BoolType, GetID());
    }

    string BVUSLESymbolicFunctor::ToString() const
    {
        return "BVULESymbolicFunctor";
    }

    BVUSGTConcreteFunctor::~BVUSGTConcreteFunctor()
    {
        // Nothing here
    }

    void BVUSGTConcreteFunctor::operator () (EvalMap Args,
                                             ConcreteValueBase* Result)
    {
        uint64 Arg1 = (uint64)Args[0]->GetValue();
        uint64 Arg2 = (uint64)Args[1]->GetValue();

        int64 ResultVal = (Arg1 > Arg2) ? 1 : 0;
        new (Result) ConcreteValueBase(BoolType, ResultVal);
    }

    ConcFunctorBase* BVUSGTConcreteFunctor::Clone() const
    {
        return new BVUSGTConcreteFunctor(Type, BoolType, GetID());
    }

    string BVUSGTConcreteFunctor::ToString() const
    {
        return "BVUSGTConcreteFunctor";
    }

    BVUSGTSymbolicFunctor::~BVUSGTSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVUSGTSymbolicFunctor::operator () (TheoremProver* TP,
                                                const vector<SMTExpr>& Args,
                                                vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVUSGTExpr(Args[0], Args[1]);
    }

    SymbFunctorBase* BVUSGTSymbolicFunctor::Clone() const
    {
        return new BVUSGTSymbolicFunctor(Type, BoolType, GetID());
    }

    string BVUSGTSymbolicFunctor::ToString() const
    {
        return "BVUSGTSymbolicFunctor";
    }

    BVUSDivConcreteFunctor::~BVUSDivConcreteFunctor()
    {
        // Nothing here
    }

    void BVUSDivConcreteFunctor::operator () (EvalMap Args,
                                              ConcreteValueBase* Result)
    {
        uint64 Arg1 = (uint64)Args[0]->GetValue();
        uint64 Arg2 = (uint64)Args[1]->GetValue();
        uint64 ResultVal;

        if(Arg2 == 0) {
            ConcreteException = true;
            ResultVal = UINT64_MAX;
        } else {
            ResultVal = Arg1 / Arg2;
        }

        // Mask off the result
        ResultVal = ResultVal & Mask;
        new (Result) ConcreteValueBase(Type, ResultVal);
    }

    ConcFunctorBase* BVUSDivConcreteFunctor::Clone() const
    {
        return new BVUSDivConcreteFunctor(Type, BoolType, GetID());
    }

    string BVUSDivConcreteFunctor::ToString() const
    {
        return "BVDivConcreteFunctor";
    }

    BVUSDivSymbolicFunctor::~BVUSDivSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVUSDivSymbolicFunctor::operator () (TheoremProver* TP,
                                                 const vector<SMTExpr>& Args,
                                                 vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVUSDivExpr(Args[0], Args[1]);
    }

    SymbFunctorBase* BVUSDivSymbolicFunctor::Clone() const
    {
        return new BVUSDivSymbolicFunctor(Type, BoolType, GetID());
    }

    string BVUSDivSymbolicFunctor::ToString() const
    {
        return "BVUSDivSymbolicFunctor";
    }

    BVSDivConcreteFunctor::~BVSDivConcreteFunctor()
    {
        // Nothing here
    }

    void BVSDivConcreteFunctor::operator () (EvalMap Args,
                                             ConcreteValueBase* Result)
    {
        int64 Arg1 = (uint64)Args[0]->GetValue();
        int64 Arg2 = (uint64)Args[1]->GetValue();
        int64 ResultVal;
        const uint32 Shift = 64 - Type->As<ESBVType>()->GetSize();

        if (Shift != 0) {
            Arg1 = (Arg1 << Shift) >> Shift;
            Arg2 = (Arg2 << Shift) >> Shift;
        }

        if(Arg2 == 0) {
            ConcreteException = true;
            ResultVal = (Arg1 < 0 ? INT64_MIN : INT64_MAX);
        } else {
            if (Arg1 > 0 && Arg2 > 0) {
                ResultVal = (uint64)Arg1 / (uint64)Arg2;
            } else if (Arg1 < 0 && Arg2 > 0) {
                ResultVal = -((int64)(((uint64)(-Arg1)) / (uint64)Arg2));
            } else if (Arg1 > 0 && Arg2 < 0) {
                ResultVal = -((int64)((uint64)Arg1 / ((uint64)(-Arg2))));
            } else {
                ResultVal = (uint64)(-Arg1) / (uint64)(-Arg2);
            }
        }

        // Mask off the result
        ResultVal = ResultVal & Mask;

        new (Result) ConcreteValueBase(Type, ResultVal);
    }

    ConcFunctorBase* BVSDivConcreteFunctor::Clone() const
    {
        return new BVSDivConcreteFunctor(Type, BoolType, GetID());
    }

    string BVSDivConcreteFunctor::ToString() const
    {
        return "BVSDivConcreteFunctor";
    }

    BVSDivSymbolicFunctor::~BVSDivSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVSDivSymbolicFunctor::operator () (TheoremProver* TP,
                                                const vector<SMTExpr>& Args,
                                                vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVSDivExpr(Args[0], Args[1]);
    }

    SymbFunctorBase* BVSDivSymbolicFunctor::Clone() const
    {
        return new BVSDivSymbolicFunctor(Type, BoolType, GetID());
    }

    string BVSDivSymbolicFunctor::ToString() const
    {
        return "BVSDivSymbolicFunctor";
    }

    BVUSRemConcreteFunctor::~BVUSRemConcreteFunctor()
    {
        // Nothing here
    }

    void BVUSRemConcreteFunctor::operator () (EvalMap Args,
                                              ConcreteValueBase* Result)
    {
        uint64 Arg1 = (uint64)Args[0]->GetValue();
        uint64 Arg2 = (uint64)Args[1]->GetValue();
        uint64 ResultVal;
        if(Arg2 == 0) {
            ConcreteException = true;
            ResultVal = UINT64_MAX;
        } else {
            ResultVal = Arg1 % Arg2;
        }

        ResultVal = ResultVal & Mask;
        new (Result) ConcreteValueBase(Type, ResultVal);
    }

    ConcFunctorBase* BVUSRemConcreteFunctor::Clone() const
    {
        return new BVUSRemConcreteFunctor(Type, BoolType, GetID());
    }

    string BVUSRemConcreteFunctor::ToString() const
    {
        return "BVUSRemConcreteFunctor";
    }

    BVUSRemSymbolicFunctor::~BVUSRemSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVUSRemSymbolicFunctor::operator () (TheoremProver* TP,
                                                 const vector<SMTExpr>& Args,
                                                 vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVUSRemExpr(Args[0], Args[1]);
    }

    SymbFunctorBase* BVUSRemSymbolicFunctor::Clone() const
    {
        return new BVUSRemSymbolicFunctor(Type, BoolType, GetID());
    }

    string BVUSRemSymbolicFunctor::ToString() const
    {
        return "BVUSRemSymbolicFunctor";
    }

    BVSRemConcreteFunctor::~BVSRemConcreteFunctor()
    {
        // Nothing here
    }

    void BVSRemConcreteFunctor::operator () (EvalMap Args,
                                             ConcreteValueBase* Result)
    {
        int64 Arg1 = Args[0]->GetValue();
        int64 Arg2 = Args[1]->GetValue();
        const uint32 Shift = 64 - Type->As<ESBVType>()->GetSize();
        int64 ResultVal;

        // Sign extend
        if (Shift != 0) {
            Arg1 = (Arg1 << Shift) >> Shift;
            Arg2 = (Arg2 << Shift) >> Shift;
        }

        if(Arg2 == 0) {
            ConcreteException = true;
            ResultVal = INT64_MAX;
        } else {
            if (Arg1 >= 0 && Arg2 > 0) {
                ResultVal = (uint64)Arg1 % (uint64)Arg2;
            } else if (Arg1 < 0 && Arg2 > 0) {
                ResultVal = -((int64)(((uint64)(-Arg1)) % (uint64)Arg2));
            } else if (Arg1 >= 0 && Arg2 < 0) {
                ResultVal = (int64)((uint64)Arg1 % ((uint64)(-Arg2)));
            } else {
                ResultVal = -((int64)(((uint64)(-Arg1)) % ((uint64)(-Arg2))));
            }
        }

        new (Result) ConcreteValueBase(Type, ResultVal);
    }

    ConcFunctorBase* BVSRemConcreteFunctor::Clone() const
    {
        return new BVSRemConcreteFunctor(Type, BoolType, GetID());
    }

    string BVSRemConcreteFunctor::ToString() const
    {
        return "BVSRemConcreteFunctor";
    }

    BVSRemSymbolicFunctor::~BVSRemSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVSRemSymbolicFunctor::operator () (TheoremProver* TP,
                                                const vector<SMTExpr>& Args,
                                                vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVSRemExpr(Args[0], Args[1]);
    }

    SymbFunctorBase* BVSRemSymbolicFunctor::Clone() const
    {
        return new BVSRemSymbolicFunctor(Type, BoolType, GetID());
    }

    string BVSRemSymbolicFunctor::ToString() const
    {
        return "BVSRemSymbolicFunctor";
    }

    BVMulConcreteFunctor::~BVMulConcreteFunctor()
    {
        // Nothing here
    }

    void BVMulConcreteFunctor::operator () (EvalMap Args,
                                            ConcreteValueBase* Result)
    {
        uint64 Arg1 = (uint64)Args[0]->GetValue();
        uint64 Arg2 = (uint64)Args[1]->GetValue();

        uint64 ResultVal = Arg1 * Arg2;
        ResultVal = ResultVal & Mask;
        new (Result) ConcreteValueBase(Type, ResultVal);
    }

    ConcFunctorBase* BVMulConcreteFunctor::Clone() const
    {
        return new BVMulConcreteFunctor(Type, BoolType, GetID());
    }

    string BVMulConcreteFunctor::ToString() const
    {
        return "BVMulConcreteFunctor";
    }

    BVMulSymbolicFunctor::~BVMulSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVMulSymbolicFunctor::operator () (TheoremProver* TP,
                                               const vector<SMTExpr>& Args,
                                               vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVMulExpr(Args[0], Args[1]);
    }

    SymbFunctorBase* BVMulSymbolicFunctor::Clone() const
    {
        return new BVMulSymbolicFunctor(Type, BoolType, GetID());
    }

    string BVMulSymbolicFunctor::ToString() const
    {
        return "BVMulSymbolicFunctor";
    }

    BVToBoolConcreteFunctor::~BVToBoolConcreteFunctor()
    {
        // Nothing here
    }

    void BVToBoolConcreteFunctor::operator () (EvalMap Args,
                                               ConcreteValueBase* Result)
    {
        int64 Arg = Args[0]->GetValue();
        int64 ResultVal = Arg != 0 ? 1 : 0;
        new (Result) ConcreteValueBase(BoolType, ResultVal);
    }

    ConcFunctorBase* BVToBoolConcreteFunctor::Clone() const
    {
        return new BVToBoolConcreteFunctor(Type, BoolType, GetID());
    }

    string BVToBoolConcreteFunctor::ToString() const
    {
        return "BVToBoolConcreteFunctor";
    }

    BVToBoolSymbolicFunctor::~BVToBoolSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVToBoolSymbolicFunctor::operator () (TheoremProver* TP,
                                                  const vector<SMTExpr>& Args,
                                                  vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVRedOrExpr(Args[0]);
    }

    SymbFunctorBase* BVToBoolSymbolicFunctor::Clone() const
    {
        return new BVToBoolSymbolicFunctor(Type, BoolType, GetID());
    }

    string BVToBoolSymbolicFunctor::ToString() const
    {
        return "BVToBoolSymbolicFunctor";
    }

    BVToSIntConcreteFunctor::BVToSIntConcreteFunctor(const ESFixedTypeBase* BVType,
                                                     const ESFixedTypeBase* IntType,
                                                     uint64 UID)
        : ConcFunctorBase(UID), BVType(BVType), IntType(IntType)
    {
        // Nothing here
    }

    BVToSIntConcreteFunctor::BVToSIntConcreteFunctor(const ESFixedTypeBase* BVType,
                                                     const ESFixedTypeBase* IntType)
        : ConcFunctorBase(), BVType(BVType), IntType(IntType)
    {
        // Nothing here
    }

    BVToSIntConcreteFunctor::~BVToSIntConcreteFunctor()
    {
        // Nothing here
    }

    void BVToSIntConcreteFunctor::operator () (EvalMap Args,
                                               ConcreteValueBase* Result)
    {
        int64 Arg = Args[0]->GetValue();
        const uint32 Shift = 64 - BVType->As<ESBVType>()->GetSize();
        int64 ResultVal;
        if (Shift != 0) {
            ResultVal = (Arg << Shift) >> Shift;
        } else {
            ResultVal = Arg;
        }
        new (Result) ConcreteValueBase(IntType, ResultVal);
    }

    ConcFunctorBase* BVToSIntConcreteFunctor::Clone() const
    {
        return new BVToSIntConcreteFunctor(BVType, IntType, GetID());
    }

    string BVToSIntConcreteFunctor::ToString() const
    {
        return "BVToSIntConcreteFunctor";
    }


    BVToSIntSymbolicFunctor::BVToSIntSymbolicFunctor(const ESFixedTypeBase* BVType,
                                                     const ESFixedTypeBase* IntType,
                                                     uint64 UID)
        : SymbFunctorBase(UID), BVType(BVType), IntType(IntType)
    {
        // Nothing here
    }

    BVToSIntSymbolicFunctor::BVToSIntSymbolicFunctor(const ESFixedTypeBase* BVType,
                                                     const ESFixedTypeBase* IntType)
        : SymbFunctorBase(), BVType(BVType), IntType(IntType)
    {
        // Nothing here
    }

    BVToSIntSymbolicFunctor::~BVToSIntSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVToSIntSymbolicFunctor::operator () (TheoremProver* TP,
                                                  const vector<SMTExpr>& Args,
                                                  vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVToSIntExpr(Args[0]);
    }

    SymbFunctorBase* BVToSIntSymbolicFunctor::Clone() const
    {
        return new BVToSIntSymbolicFunctor(BVType, IntType, GetID());
    }

    string BVToSIntSymbolicFunctor::ToString() const
    {
        return "BVToSIntSymbolicFunctor";
    }

    BVToUSIntConcreteFunctor::~BVToUSIntConcreteFunctor()
    {
        // Nothing here
    }

    void BVToUSIntConcreteFunctor::operator () (EvalMap Args,
                                                ConcreteValueBase* Result)
    {
        int64 Arg = (uint64)Args[0]->GetValue();
        new (Result) ConcreteValueBase(IntType, Arg);
    }

    ConcFunctorBase* BVToUSIntConcreteFunctor::Clone() const
    {
        return new BVToUSIntConcreteFunctor(BVType, IntType, GetID());
    }

    string BVToUSIntConcreteFunctor::ToString() const
    {
        return "BVToUSIntConcreteFunctor";
    }

    BVToUSIntSymbolicFunctor::~BVToUSIntSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVToUSIntSymbolicFunctor::operator () (TheoremProver* TP,
                                                   const vector<SMTExpr>& Args,
                                                   vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVToUSIntExpr(Args[0]);
    }

    SymbFunctorBase* BVToUSIntSymbolicFunctor::Clone() const
    {
        return new BVToUSIntSymbolicFunctor(BVType, IntType, GetID());
    }

    string BVToUSIntSymbolicFunctor::ToString() const
    {
        return "BVToUSIntSymbolicFunctor";
    }

    BVUSLTConcreteFunctor::~BVUSLTConcreteFunctor()
    {
        // Nothing here
    }

    void BVUSLTConcreteFunctor::operator () (EvalMap Args,
                                             ConcreteValueBase* Result)
    {
        uint64 Arg1 = (uint64)Args[0]->GetValue();
        uint64 Arg2 = (uint64)Args[1]->GetValue();
        int64 Bits = Arg1 < Arg2 ? 1 : 0;
        new (Result) ConcreteValueBase(BoolType, Bits);
    }

    ConcFunctorBase* BVUSLTConcreteFunctor::Clone() const
    {
        return new BVUSLTConcreteFunctor(Type, BoolType, GetID());
    }

    string BVUSLTConcreteFunctor::ToString() const
    {
        return "BVUSLTConcreteFunctor";
    }

    BVUSLTSymbolicFunctor::~BVUSLTSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVUSLTSymbolicFunctor::operator () (TheoremProver* TP,
                                                const vector<SMTExpr>& Args,
                                                vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVUSLTExpr(Args[0], Args[1]);
    }

    SymbFunctorBase* BVUSLTSymbolicFunctor::Clone() const
    {
        return new BVUSLTSymbolicFunctor(Type, BoolType, GetID());
    }

    string BVUSLTSymbolicFunctor::ToString() const
    {
        return "BVUSLTSymbolicFunctor";
    }

    BVUSGEConcreteFunctor::~BVUSGEConcreteFunctor()
    {
        // Nothing here
    }

    void BVUSGEConcreteFunctor::operator () (EvalMap Args,
                                             ConcreteValueBase* Result)
    {
        uint64 Arg1 = (uint64)Args[0]->GetValue();
        uint64 Arg2 = (uint64)Args[1]->GetValue();
        int64 Bits = Arg1 >= Arg2 ? 1 : 0;
        new (Result) ConcreteValueBase(BoolType, Bits);
    }

    ConcFunctorBase* BVUSGEConcreteFunctor::Clone() const
    {
        return new BVUSGEConcreteFunctor(Type, BoolType, GetID());
    }

    string BVUSGEConcreteFunctor::ToString() const
    {
        return "BVUSGEConcreteFunctor";
    }

    BVUSGESymbolicFunctor::~BVUSGESymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVUSGESymbolicFunctor::operator () (TheoremProver* TP,
                                                const vector<SMTExpr>& Args,
                                                vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVUSGEExpr(Args[0], Args[1]);
    }

    SymbFunctorBase* BVUSGESymbolicFunctor::Clone() const
    {
        return new BVUSGESymbolicFunctor(Type, BoolType, GetID());
    }

    string BVUSGESymbolicFunctor::ToString() const
    {
        return "BVUSGESymbolicFunctor";
    }

    BVSLEConcreteFunctor::~BVSLEConcreteFunctor()
    {
        // Nothing here
    }

    void BVSLEConcreteFunctor::operator () (EvalMap Args,
                                            ConcreteValueBase* Result)
    {
        uint64 Arg1 = (int64)Args[0]->GetValue();
        uint64 Arg2 = (int64)Args[1]->GetValue();
        int64 Bits = Arg1 <= Arg2 ? 1 : 0;
        new (Result) ConcreteValueBase(BoolType, Bits);
    }

    ConcFunctorBase* BVSLEConcreteFunctor::Clone() const
    {
        return new BVSLEConcreteFunctor(Type, BoolType, GetID());
    }

    string BVSLEConcreteFunctor::ToString() const
    {
        return "BVSLEConcreteFunctor";
    }

    BVSLESymbolicFunctor::~BVSLESymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVSLESymbolicFunctor::operator () (TheoremProver* TP,
                                               const vector<SMTExpr>& Args,
                                               vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVSLEExpr(Args[0], Args[1]);
    }

    SymbFunctorBase* BVSLESymbolicFunctor::Clone() const
    {
        return new BVSLESymbolicFunctor(Type, BoolType, GetID());
    }

    string BVSLESymbolicFunctor::ToString() const
    {
        return "BVSLESymbolicFunctor";
    }

    BVSLTConcreteFunctor::~BVSLTConcreteFunctor()
    {
        // Nothing here
    }

    void BVSLTConcreteFunctor::operator () (EvalMap Args,
                                            ConcreteValueBase* Result)
    {
        uint64 Arg1 = (int64)Args[0]->GetValue();
        uint64 Arg2 = (int64)Args[1]->GetValue();
        int64 Bits = Arg1 < Arg2 ? 1 : 0;
        new (Result) ConcreteValueBase(BoolType, Bits);
    }

    ConcFunctorBase* BVSLTConcreteFunctor::Clone() const
    {
        return new BVSLTConcreteFunctor(Type, BoolType, GetID());
    }

    string BVSLTConcreteFunctor::ToString() const
    {
        return "BVSLTConcreteFunctor";
    }

    BVSLTSymbolicFunctor::~BVSLTSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVSLTSymbolicFunctor::operator () (TheoremProver* TP,
                                               const vector<SMTExpr>& Args,
                                               vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVSLTExpr(Args[0], Args[1]);
    }

    SymbFunctorBase* BVSLTSymbolicFunctor::Clone() const
    {
        return new BVSLTSymbolicFunctor(Type, BoolType, GetID());
    }

    string BVSLTSymbolicFunctor::ToString() const
    {
        return "BVSLTSymbolicFunctor";
    }

    BVSGEConcreteFunctor::~BVSGEConcreteFunctor()
    {
        // Nothing here
    }

    void BVSGEConcreteFunctor::operator () (EvalMap Args,
                                            ConcreteValueBase* Result)
    {
        uint64 Arg1 = (int64)Args[0]->GetValue();
        uint64 Arg2 = (int64)Args[1]->GetValue();
        int64 Bits = Arg1 >= Arg2 ? 1 : 0;
        new (Result) ConcreteValueBase(BoolType, Bits);
    }

    ConcFunctorBase* BVSGEConcreteFunctor::Clone() const
    {
        return new BVSGEConcreteFunctor(Type, BoolType, GetID());
    }

    string BVSGEConcreteFunctor::ToString() const
    {
        return "BVSGEConcreteFunctor";
    }

    BVSGESymbolicFunctor::~BVSGESymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVSGESymbolicFunctor::operator () (TheoremProver* TP,
                                               const vector<SMTExpr>& Args,
                                               vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVSGEExpr(Args[0], Args[1]);
    }

    SymbFunctorBase* BVSGESymbolicFunctor::Clone() const
    {
        return new BVSGESymbolicFunctor(Type, BoolType, GetID());
    }

    string BVSGESymbolicFunctor::ToString() const
    {
        return "BVSGESymbolicFunctor";
    }

    BVSGTConcreteFunctor::~BVSGTConcreteFunctor()
    {
        // Nothing here
    }

    void BVSGTConcreteFunctor::operator () (EvalMap Args,
                                            ConcreteValueBase* Result)
    {
        uint64 Arg1 = (int64)Args[0]->GetValue();
        uint64 Arg2 = (int64)Args[1]->GetValue();
        int64 Bits = Arg1 > Arg2 ? 1 : 0;
        new (Result) ConcreteValueBase(BoolType, Bits);
    }

    ConcFunctorBase* BVSGTConcreteFunctor::Clone() const
    {
        return new BVSGTConcreteFunctor(Type, BoolType, GetID());
    }

    string BVSGTConcreteFunctor::ToString() const
    {
        return "BVSGTConcreteFunctor";
    }

    BVSGTSymbolicFunctor::~BVSGTSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVSGTSymbolicFunctor::operator () (TheoremProver* TP,
                                               const vector<SMTExpr>& Args,
                                               vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVSGTExpr(Args[0], Args[1]);
    }

    SymbFunctorBase* BVSGTSymbolicFunctor::Clone() const
    {
        return new BVSGTSymbolicFunctor(Type, BoolType, GetID());
    }

    string BVSGTSymbolicFunctor::ToString() const
    {
        return "BVSGTSymbolicFunctor";
    }

    BVRedOrConcreteFunctor::~BVRedOrConcreteFunctor()
    {
        // Nothing here
    }

    void BVRedOrConcreteFunctor::operator () (EvalMap Args,
                                              ConcreteValueBase* Result)
    {
        int64 Arg = Args[0]->GetValue();
        int64 ResultVal = Arg == 0 ? 0 : 1;
        new (Result) ConcreteValueBase(BoolType, ResultVal);
    }

    ConcFunctorBase* BVRedOrConcreteFunctor::Clone() const
    {
        return new BVRedOrConcreteFunctor(Type, BoolType, GetID());
    }

    string BVRedOrConcreteFunctor::ToString() const
    {
        return "BVRedOrConcreteFunctor";
    }

    BVRedOrSymbolicFunctor::~BVRedOrSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVRedOrSymbolicFunctor::operator () (TheoremProver* TP,
                                                 const vector<SMTExpr>& Args,
                                                 vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVRedOrExpr(Args[0]);
    }

    SymbFunctorBase* BVRedOrSymbolicFunctor::Clone() const
    {
        return new BVRedOrSymbolicFunctor(Type, BoolType, GetID());
    }

    string BVRedOrSymbolicFunctor::ToString() const
    {
        return "BVRedOrSymbolicFunctor";
    }

    BVRedAndConcreteFunctor::~BVRedAndConcreteFunctor()
    {
        // Nothing here
    }

    void BVRedAndConcreteFunctor::operator () (EvalMap Args,
                                               ConcreteValueBase* Result)
    {
        int64 Arg = Args[0]->GetValue();
        int64 Retval = ((Arg & Mask) == Mask) ? 1 : 0;
        new (Result) ConcreteValueBase(BoolType, Retval);
    }

    ConcFunctorBase* BVRedAndConcreteFunctor::Clone() const
    {
        return new BVRedAndConcreteFunctor(Type, BoolType, GetID());
    }

    string BVRedAndConcreteFunctor::ToString() const
    {
        return "BVRedAndConcreteFunctor";
    }

    BVRedAndSymbolicFunctor::~BVRedAndSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVRedAndSymbolicFunctor::operator () (TheoremProver* TP,
                                                  const vector<SMTExpr>& Args,
                                                  vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVRedAndExpr(Args[0]);
    }

    SymbFunctorBase* BVRedAndSymbolicFunctor::Clone() const
    {
        return new BVRedAndSymbolicFunctor(Type, BoolType, GetID());
    }

    string BVRedAndSymbolicFunctor::ToString() const
    {
        return "BVRedAndSymbolicFunctor";
    }

    BVConcatConcreteFunctor::BVConcatConcreteFunctor(const ESFixedTypeBase* Arg1Type,
                                                     const ESFixedTypeBase* Arg2Type,
                                                     const ESFixedTypeBase* RetType,
                                                     uint64 UID)
        : ConcFunctorBase(UID), Arg1Type(Arg1Type), Arg2Type(Arg2Type), RetType(RetType)
    {
        if (Arg1Type->As<ESBVType>()->GetSize() == 64) {
            Arg1Mask = (uint64)0xFFFFFFFFFFFFFFFF;
        } else {
            Arg1Mask  = ((uint64)1 << Arg1Type->As<ESBVType>()->GetSize()) - 1;
        }
        if (Arg2Type->As<ESBVType>()->GetSize() == 64) {
            Arg2Mask = (uint64)0xFFFFFFFFFFFFFFFF;
        } else {
            Arg2Mask  = ((uint64)1 << Arg2Type->As<ESBVType>()->GetSize()) - 1;
        }
        if (RetType->As<ESBVType>()->GetSize() == 64) {
            RetMask = (uint64)0xFFFFFFFFFFFFFFFF;
        } else {
            RetMask  = ((uint64)1 << RetType->As<ESBVType>()->GetSize()) - 1;
        }
    }

    BVConcatConcreteFunctor::BVConcatConcreteFunctor(const ESFixedTypeBase* Arg1Type,
                                                     const ESFixedTypeBase* Arg2Type,
                                                     const ESFixedTypeBase* RetType)
        : ConcFunctorBase(), Arg1Type(Arg1Type), Arg2Type(Arg2Type), RetType(RetType)
    {
        if (Arg1Type->As<ESBVType>()->GetSize() == 64) {
            Arg1Mask = (uint64)0xFFFFFFFFFFFFFFFF;
        } else {
            Arg1Mask  = (1 << Arg1Type->As<ESBVType>()->GetSize()) - 1;
        }
        if (Arg2Type->As<ESBVType>()->GetSize() == 64) {
            Arg2Mask = (uint64)0xFFFFFFFFFFFFFFFF;
        } else {
            Arg2Mask  = (1 << Arg2Type->As<ESBVType>()->GetSize()) - 1;
        }
        if (RetType->As<ESBVType>()->GetSize() == 64) {
            RetMask = (uint64)0xFFFFFFFFFFFFFFFF;
        } else {
            RetMask  = (1 << RetType->As<ESBVType>()->GetSize()) - 1;
        }
    }

    BVConcatConcreteFunctor::~BVConcatConcreteFunctor()
    {
        // Nothing here
    }

    void BVConcatConcreteFunctor::operator() (EvalMap Args,
                                              ConcreteValueBase* Result)
    {
        uint64 Arg1 = (uint64)Args[0]->GetValue() & Arg1Mask;
        uint64 Arg2 = (uint64)Args[1]->GetValue() & Arg2Mask;
        // Mask the args for good measure

        uint64 ResultBits = (Arg1 << Arg1Type->As<ESBVType>()->GetSize() | Arg2) & RetMask;
        new (Result) ConcreteValueBase(RetType, ResultBits);
    }

    string BVConcatConcreteFunctor::ToString() const
    {
        return "BVConcatConcreteFunctor";
    }

    ConcFunctorBase* BVConcatConcreteFunctor::Clone() const
    {
        return new BVConcatConcreteFunctor(Arg1Type, Arg2Type, RetType, GetID());
    }

    BVConcatSymbolicFunctor::BVConcatSymbolicFunctor(const ESFixedTypeBase* Arg1Type,
                                                     const ESFixedTypeBase* Arg2Type,
                                                     const ESFixedTypeBase* RetType,
                                                     uint64 UID)
        : SymbFunctorBase(UID), Arg1Type(Arg1Type), Arg2Type(Arg2Type), RetType(RetType)
    {
        // Nothing here
    }

    BVConcatSymbolicFunctor::BVConcatSymbolicFunctor(const ESFixedTypeBase* Arg1Type,
                                                     const ESFixedTypeBase* Arg2Type,
                                                     const ESFixedTypeBase* RetType)
        : SymbFunctorBase(), Arg1Type(Arg1Type), Arg2Type(Arg2Type), RetType(RetType)
    {
        // Nothing here
    }

    BVConcatSymbolicFunctor::~BVConcatSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVConcatSymbolicFunctor::operator () (TheoremProver* TP,
                                                  const vector<SMTExpr>& Args,
                                                  vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVConcatExpr(Args[0], Args[1]);
    }

    string BVConcatSymbolicFunctor::ToString() const
    {
        return "BVConcatSymbolicFunctor";
    }

    SymbFunctorBase* BVConcatSymbolicFunctor::Clone() const
    {
        return new BVConcatSymbolicFunctor(Arg1Type, Arg2Type, RetType, GetID());
    }

    BVExtractConcreteFunctor::BVExtractConcreteFunctor(const ESFixedTypeBase* ArgType,
                                                       const ESFixedTypeBase* RetType,
                                                       uint32 Low, uint32 High,
                                                       uint64 UID)
        : ConcFunctorBase(UID), ArgType(ArgType), RetType(RetType),
          Low(Low), High(High)
    {

        if (Low == 0 && High == 63) {
            ExtractMask = (uint64)0xFFFFFFFFFFFFFFFF;
            ResultMask = (uint64)0xFFFFFFFFFFFFFFFF;
            ExtractShift = 0;
        } else if (High == 63) {
            ExtractMask = (uint64)0xFFFFFFFFFFFFFFFF - (((uint64)1 << Low) - 1);
            ResultMask = ((uint64)1 << (High - Low)) - 1;
            ExtractShift = Low;
        } else {
            ExtractMask = (((uint64)1 << High) - 1) - (((uint64)1 << Low) - 1);
            ResultMask = ((uint64)1 << (High - 1)) - 1;
            ExtractShift = Low;
        }
    }

    BVExtractConcreteFunctor::BVExtractConcreteFunctor(const ESFixedTypeBase* ArgType,
                                                       const ESFixedTypeBase* RetType,
                                                       uint32 Low, uint32 High)
        : ConcFunctorBase(), ArgType(ArgType), RetType(RetType),
          Low(Low), High(High)
    {
        if (Low == 0 && High == 63) {
            ExtractMask = (uint64)0xFFFFFFFFFFFFFFFF;
            ResultMask = (uint64)0xFFFFFFFFFFFFFFFF;
            ExtractShift = 0;
        } else if (High == 63) {
            ExtractMask = (uint64)0xFFFFFFFFFFFFFFFF - (((uint64)1 << Low) - 1);
            ResultMask = ((uint64)1 << (High - Low)) - 1;
            ExtractShift = Low;
        } else {
            ExtractMask = (((uint64)1 << High) - 1) - (((uint64)1 << Low) - 1);
            ResultMask = ((uint64)1 << (High - 1)) - 1;
            ExtractShift = Low;
        }
    }

    BVExtractConcreteFunctor::~BVExtractConcreteFunctor()
    {
        // Nothing here
    }

    void BVExtractConcreteFunctor::operator () (EvalMap Args,
                                                ConcreteValueBase* Result)
    {
        uint64 ResultBits = (uint64)Args[0]->GetValue();
        ResultBits &= ExtractMask;
        if (ExtractShift != 0) {
            ResultBits >>= ExtractShift;
        }
        ResultBits &= ResultMask;
        new (Result) ConcreteValueBase(RetType, ResultBits);
    }

    string BVExtractConcreteFunctor::ToString() const
    {
        return "BVExtractConcreteFunctor";
    }

    ConcFunctorBase* BVExtractConcreteFunctor::Clone() const
    {
        return new BVExtractConcreteFunctor(ArgType, RetType, Low, High, GetID());
    }

    BVExtractSymbolicFunctor::BVExtractSymbolicFunctor(const ESFixedTypeBase* ArgType,
                                                       const ESFixedTypeBase* RetType,
                                                       uint32 Low, uint32 High,
                                                       uint64 UID)
        : SymbFunctorBase(UID), ArgType(ArgType), RetType(RetType),
          Low(Low), High(High)
    {
        // Nothing here
    }

    BVExtractSymbolicFunctor::BVExtractSymbolicFunctor(const ESFixedTypeBase* ArgType,
                                                       const ESFixedTypeBase* RetType,
                                                       uint32 Low, uint32 High)
        : SymbFunctorBase(), ArgType(ArgType), RetType(RetType), Low(Low), High(High)
    {
        // Nothing here
    }

    BVExtractSymbolicFunctor::~BVExtractSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr BVExtractSymbolicFunctor::operator () (TheoremProver* TP,
                                                   const vector<SMTExpr>& Args,
                                                   vector<SMTExpr>& Assumptions)
    {
        return TP->CreateBVExtractExpr(Args[0], High, Low);
    }

    string BVExtractSymbolicFunctor::ToString() const
    {
        return "BVExtractSymbolicFunctor";
    }

    SymbFunctorBase* BVExtractSymbolicFunctor::Clone() const
    {
        return new BVExtractSymbolicFunctor(ArgType, RetType, Low, High);
    }

} /* End ESolverBVLogic namespace */

using namespace ESolverBVLogic;

namespace ESolver {

    BVLogic::BVLogic(ESolver* Solver)
        : ESolverLogic("BVLogic", Solver)
    {
        // Nothing here
    }

    BVLogic::~BVLogic()
    {
        // Nothing here
    }

    void BVLogic::Init()
    {
        // Do nothing right now
    }

    bool BVLogic::IsNameReserved(const string& Name) const
    {
        return (ReservedNames.find(Name) != ReservedNames.end());
    }

    static inline void CheckType(const vector<const ESFixedTypeBase*>& DomainTypes)
    {
        if (DomainTypes.size() == 1 && DomainTypes[0]->As<ESBVType>() == nullptr) {
            throw TypeException((string)"Could not find appropriate types to instantiate BV Op with");
        }
        if (DomainTypes.size() == 2 &&
            (DomainTypes[0]->As<ESBVType>() == nullptr ||
             DomainTypes[1]->As<ESBVType>() == nullptr ||
             DomainTypes[0] != DomainTypes[1])) {
            throw TypeException((string)"Could not find appropriate types to instantiate BV Op with");
        }
    }

    inline bool BVLogic::InstantiateOperator(const string& Name,
                                             const vector<const ESFixedTypeBase*>& DomainTypes)
    {
        if (!IsNameReserved(Name)) {
            return false;
        }
        vector<const ESFixedTypeBase*> UnOpArgs;
        vector<const ESFixedTypeBase*> BinOpArgs;

        if (DomainTypes.size() == 1) {
            UnOpArgs.push_back(DomainTypes[0]);
        }
        if (DomainTypes.size() == 2) {
            BinOpArgs.push_back(DomainTypes[0]);
            BinOpArgs.push_back(DomainTypes[1]);
        }

        const ESFixedTypeBase* Type = DomainTypes[0];

        if (Name == "bvnot") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvnot", UnOpArgs, Type,
                                   new BVNotSymbolicFunctor(Type, Solver->CreateBoolType()),
                                   new BVNotConcreteFunctor(Type, Solver->CreateBoolType()),
                                   false, true);
            return true;
        }
        if (Name == "bvand") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvand", BinOpArgs, Type,
                                   new BVAndSymbolicFunctor(Type, Solver->CreateBoolType()),
                                   new BVAndConcreteFunctor(Type, Solver->CreateBoolType()),
                                   true, true);
            return true;
        }
        if (Name == "bvor") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvor", BinOpArgs, Type,
                                   new BVOrSymbolicFunctor(Type, Solver->CreateBoolType()),
                                   new BVOrConcreteFunctor(Type, Solver->CreateBoolType()),
                                   true, true);
            return true;
        }
        if (Name == "bvneg") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvneg", UnOpArgs, Type,
                                   new BVNegSymbolicFunctor(Type, Solver->CreateBoolType()),
                                   new BVNegConcreteFunctor(Type, Solver->CreateBoolType()),
                                   false, true);
            return true;
        }
        if (Name == "bvadd") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvadd", BinOpArgs, Type,
                                   new BVAddSymbolicFunctor(Type, Solver->CreateBoolType()),
                                   new BVAddConcreteFunctor(Type, Solver->CreateBoolType()),
                                   true, true);
            return true;
        }
        if (Name == "bvmul") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvmul", BinOpArgs, Type,
                                   new BVMulSymbolicFunctor(Type, Solver->CreateBoolType()),
                                   new BVMulConcreteFunctor(Type, Solver->CreateBoolType()),
                                   true, true);
            return true;
        }
        if (Name == "bvudiv") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvudiv", BinOpArgs, Type,
                                   new BVUSDivSymbolicFunctor(Type, Solver->CreateBoolType()),
                                   new BVUSDivConcreteFunctor(Type, Solver->CreateBoolType()),
                                   false, true);
            return true;
        }
        if (Name == "bvurem") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvurem", BinOpArgs, Type,
                                   new BVUSRemSymbolicFunctor(Type, Solver->CreateBoolType()),
                                   new BVUSRemConcreteFunctor(Type, Solver->CreateBoolType()),
                                   false, true);
            return true;
        }
        if (Name == "bvshl") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvshl", BinOpArgs, Type,
                                   new BVShlSymbolicFunctor(Type, Solver->CreateBoolType()),
                                   new BVShlConcreteFunctor(Type, Solver->CreateBoolType()),
                                   false, true);
            return true;
        }
        if (Name == "bvlshr") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvlshr", BinOpArgs, Type,
                                   new BVLShrSymbolicFunctor(Type, Solver->CreateBoolType()),
                                   new BVLShrConcreteFunctor(Type, Solver->CreateBoolType()),
                                   false, true);
            return true;
        }
        if (Name == "bvult") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvult", BinOpArgs, Solver->CreateBoolType(),
                                   new BVUSLTSymbolicFunctor(Type, Solver->CreateBoolType()),
                                   new BVUSLTConcreteFunctor(Type, Solver->CreateBoolType()),
                                   false, true);
            return true;
        }
        if (Name == "bvnand") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvnand", BinOpArgs, Type,
                                   new BVNandSymbolicFunctor(Type, Solver->CreateBoolType()),
                                   new BVNandConcreteFunctor(Type, Solver->CreateBoolType()),
                                   true, true);
            return true;
        }
        if (Name == "bvnor") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvnor", BinOpArgs, Type,
                                   new BVNorSymbolicFunctor(Type, Solver->CreateBoolType()),
                                   new BVNorConcreteFunctor(Type, Solver->CreateBoolType()),
                                   true, true);
            return true;
        }
        if (Name == "bvxor") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvxor", BinOpArgs, Type,
                                   new BVXorSymbolicFunctor(Type, Solver->CreateBoolType()),
                                   new BVXorConcreteFunctor(Type, Solver->CreateBoolType()),
                                   true, true);
            return true;
        }
        if (Name == "bvxnor") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvxnor", BinOpArgs, Type,
                                   new BVXNorSymbolicFunctor(Type, Solver->CreateBoolType()),
                                   new BVXNorConcreteFunctor(Type, Solver->CreateBoolType()),
                                   true, true);
            return true;
        }
        if (Name == "bvcomp") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvcomp", BinOpArgs, Solver->CreateBoolType(),
                                   new EQSymbolicFunctor(), new EQConcreteFunctor(), true, true);
            return true;
        }
        if (Name == "bvsub") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvsub", BinOpArgs, Type,
                                   new BVSubSymbolicFunctor(Type, Solver->CreateBoolType()),
                                   new BVSubConcreteFunctor(Type, Solver->CreateBoolType()),
                                   false, true);
            return true;
        }
        if (Name == "bvsdiv") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvsdiv", BinOpArgs, Type,
                                   new BVSDivSymbolicFunctor(Type, Solver->CreateBoolType()),
                                   new BVSDivConcreteFunctor(Type, Solver->CreateBoolType()),
                                   false, true);
            return true;
        }
        if (Name == "bvsrem") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvsrem", BinOpArgs, Type,
                                   new BVSRemSymbolicFunctor(Type, Solver->CreateBoolType()),
                                   new BVSRemConcreteFunctor(Type, Solver->CreateBoolType()),
                                   false, true);
            return true;
        }

            // bvsmod is not currently supported!
            // Solver->CreateFunction("bvsmod", BinOpArgs, Type, new BVSModSymbolicFunctor(Type),
            //                        new BVSModConcreteFunctor(Type), false);

        if (Name == "bvashr") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvashr", BinOpArgs, Type,
                                   new BVAShrSymbolicFunctor(Type, Solver->CreateBoolType()),
                                   new BVAShrConcreteFunctor(Type, Solver->CreateBoolType()),
                                   false, true);
            return true;
        }
        if (Name == "bvule") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvule", BinOpArgs, Solver->CreateBoolType(),
                                   new BVUSLESymbolicFunctor(Type, Solver->CreateBoolType()),
                                   new BVUSLEConcreteFunctor(Type, Solver->CreateBoolType()),
                                   false, true);
            return true;
        }
        if (Name == "bvugt") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvugt", BinOpArgs, Solver->CreateBoolType(),
                                   new BVUSGTSymbolicFunctor(Type, Solver->CreateBoolType()),
                                   new BVUSGTConcreteFunctor(Type, Solver->CreateBoolType()),
                                   false, true);
            return true;
        }
        if (Name == "bvuge") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvuge", BinOpArgs, Solver->CreateBoolType(),
                                   new BVUSGESymbolicFunctor(Type, Solver->CreateBoolType()),
                                   new BVUSGEConcreteFunctor(Type, Solver->CreateBoolType()),
                                   false, true);
            return true;
        }
        if (Name == "bvslt") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvslt", BinOpArgs, Solver->CreateBoolType(),
                                   new BVSLTSymbolicFunctor(Type, Solver->CreateBoolType()),
                                   new BVSLTConcreteFunctor(Type, Solver->CreateBoolType()),
                                   false, true);
            return true;
        }
        if (Name == "bvsle") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvsle", BinOpArgs, Solver->CreateBoolType(),
                                   new BVSLESymbolicFunctor(Type, Solver->CreateBoolType()),
                                   new BVSLEConcreteFunctor(Type, Solver->CreateBoolType()),
                                   false, true);
            return true;
        }
        if (Name == "bvsge") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvsge", BinOpArgs, Solver->CreateBoolType(),
                                   new BVSGESymbolicFunctor(Type, Solver->CreateBoolType()),
                                   new BVSGEConcreteFunctor(Type, Solver->CreateBoolType()),
                                   false, true);
            return true;
        }
        if (Name == "bvsgt") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvsgt", BinOpArgs, Solver->CreateBoolType(),
                                   new BVSGTSymbolicFunctor(Type, Solver->CreateBoolType()),
                                   new BVSGTConcreteFunctor(Type, Solver->CreateBoolType()),
                                   false, true);
            return true;
        }
        if (Name == "bvtouint") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvtouint", UnOpArgs, Solver->CreateBoolType(),
                                   new BVToUSIntSymbolicFunctor(Type, Solver->CreateBoolType()),
                                   new BVToUSIntConcreteFunctor(Type, Solver->CreateBoolType()),
                                   false, true);
            return true;
        }
        if (Name == "bvtosint") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvtosint", UnOpArgs, Solver->CreateIntType(),
                                   new BVToSIntSymbolicFunctor(Type, Solver->CreateBoolType()),
                                   new BVToSIntConcreteFunctor(Type, Solver->CreateBoolType()),
                                   false, true);
            return true;
        }
        if (Name == "bvtobool") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvtobool", UnOpArgs, Solver->CreateBoolType(),
                                   new BVToBoolSymbolicFunctor(Type, Solver->CreateBoolType()),
                                   new BVToBoolConcreteFunctor(Type, Solver->CreateBoolType()),
                                   false, true);
            return true;
        }


        if (Name == "bvredor") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvredor", UnOpArgs, Solver->CreateBoolType(),
                                   new BVRedOrSymbolicFunctor(Type, Solver->CreateBoolType()),
                                   new BVRedOrConcreteFunctor(Type, Solver->CreateBoolType()),
                                   false, true);
            return true;
        }
        if (Name == "bvredand") {
            CheckType(DomainTypes);
            Solver->CreateFunction("bvredand", UnOpArgs, Solver->CreateBoolType(),
                                   new BVRedAndSymbolicFunctor(Type, Solver->CreateBoolType()),
                                   new BVRedAndConcreteFunctor(Type, Solver->CreateBoolType()),
                                   false, true);
            return true;
        }
        if (Name == "bvconcat") {
            if (DomainTypes.size() != 2) {
                throw TypeException((string)"bvconcat could not be instantiated");
            }
            auto RetType = Solver->CreateBitVectorType(DomainTypes[0]->As<ESBVType>()->GetSize() +
                                                       DomainTypes[1]->As<ESBVType>()->GetSize());
            Solver->CreateFunction("bvconcat", BinOpArgs, RetType,
                                   new BVConcatSymbolicFunctor(DomainTypes[0], DomainTypes[1], RetType),
                                   new BVConcatConcreteFunctor(DomainTypes[0], DomainTypes[1], RetType),
                                   false, true);
            return true;
        }
        return false;
    }

    bool BVLogic::InstantiateExtractOperator(const ESFixedTypeBase* BVType,
                                             uint64 Low, uint64 High)
    {
        auto BVPtr = BVType->As<ESBVType>();
        if (BVPtr == nullptr) {
            throw TypeException((string)"Error: bvextract must be applied to bitvectors");
        }
        if (High >= BVPtr->GetSize()) {
            throw TypeException((string)"Error, bvextract out of bounds for bit vector");
        }
        auto RetType = Solver->CreateBitVectorType(High - Low + 1);
        // okay to instantiate
        auto Name = (string)"bvextract@@@" + to_string(Low) + "@@@" + to_string(High) + "@@@";
        vector<const ESFixedTypeBase*> DomainTypes = { BVType };
        Solver->CreateFunction(Name, DomainTypes, RetType,
                               new BVExtractSymbolicFunctor(BVType, RetType, Low, High),
                               new BVExtractConcreteFunctor(BVType, RetType, Low, High),
                               false,
                               true);
        return true;
    }

    string BVLogic::GetExtractOpName(const ESFixedTypeBase* BVType, uint64 Low, uint64 High)
    {
        return (string)"bvextract@@@" + to_string(Low) + "@@@" + to_string(High) + "@@@_@" +
            to_string(BVType->GetID()) ;
    }

} /* End namespace */

//
// BVLogic.cpp ends here
