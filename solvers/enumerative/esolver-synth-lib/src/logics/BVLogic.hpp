// BVLogic.hpp --- 
// 
// Filename: BVLogic.hpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:51:02 2014 (-0500)
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


#if !defined __ESOLVER_BV_LOGIC_HPP
#define __ESOLVER_BV_LOGIC_HPP

#include "../common/ESolverForwardDecls.hpp"
#include "../logics/ESolverLogic.hpp"
#include "../z3interface/Z3Objects.hpp"
#include "../descriptions/FunctorBase.hpp"

using namespace ESolver; 

namespace ESolverBVLogic {

    class BVConcreteFunctor : public ConcFunctorBase
    {
    protected:
        const ESFixedTypeBase* Type;
        const ESFixedTypeBase* BoolType;
        uint64 Mask;
        BVConcreteFunctor(const ESFixedTypeBase* Type, 
                          const ESFixedTypeBase* BoolType, 
                          uint64 UID);

    public:
        BVConcreteFunctor(const ESFixedTypeBase* Type,
                          const ESFixedTypeBase* BoolType);

        virtual ~BVConcreteFunctor();
    };

    class BVSymbolicFunctor : public SymbFunctorBase
    {
    protected:
        const ESFixedTypeBase* Type;
        const ESFixedTypeBase* BoolType;
        BVSymbolicFunctor(const ESFixedTypeBase* Type,
                          const ESFixedTypeBase* BoolType, 
                          uint64 UID);

    public:
        BVSymbolicFunctor(const ESFixedTypeBase* Type,
                          const ESFixedTypeBase* BoolType);

        virtual ~BVSymbolicFunctor();
    };

    class BVAddConcreteFunctor : public BVConcreteFunctor
    {
    public:
        using BVConcreteFunctor::BVConcreteFunctor;
        virtual ~BVAddConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVAddSymbolicFunctor : public BVSymbolicFunctor
    {
    public:
        using BVSymbolicFunctor::BVSymbolicFunctor;
        virtual ~BVAddSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class BVSubConcreteFunctor : public BVConcreteFunctor
    {
    public:
        using BVConcreteFunctor::BVConcreteFunctor;
        virtual ~BVSubConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVSubSymbolicFunctor : public BVSymbolicFunctor
    {
    public:
        using BVSymbolicFunctor::BVSymbolicFunctor;
        virtual ~BVSubSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class BVAndConcreteFunctor : public BVConcreteFunctor
    {
    public:
        using BVConcreteFunctor::BVConcreteFunctor;
        virtual ~BVAndConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVAndSymbolicFunctor : public BVSymbolicFunctor
    {
    public:
        using BVSymbolicFunctor::BVSymbolicFunctor;
        virtual ~BVAndSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class BVOrConcreteFunctor : public BVConcreteFunctor
    {
    public:
        using BVConcreteFunctor::BVConcreteFunctor;
        virtual ~BVOrConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVOrSymbolicFunctor : public BVSymbolicFunctor
    {
    public:
        using BVSymbolicFunctor::BVSymbolicFunctor;
        virtual ~BVOrSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    // Bitwise negation
    class BVNotConcreteFunctor : public BVConcreteFunctor
    {
    public:
        using BVConcreteFunctor::BVConcreteFunctor;
        virtual ~BVNotConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVNotSymbolicFunctor : public BVSymbolicFunctor
    {
    public:
        using BVSymbolicFunctor::BVSymbolicFunctor;
        virtual ~BVNotSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class BVNandConcreteFunctor : public BVConcreteFunctor
    {
    public:
        using BVConcreteFunctor::BVConcreteFunctor;
        virtual ~BVNandConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVNandSymbolicFunctor : public BVSymbolicFunctor
    {
    public:
        using BVSymbolicFunctor::BVSymbolicFunctor;
        virtual ~BVNandSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class BVNorConcreteFunctor : public BVConcreteFunctor
    {
    public:
        using BVConcreteFunctor::BVConcreteFunctor;
        virtual ~BVNorConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVNorSymbolicFunctor : public BVSymbolicFunctor
    {
    public:
        using BVSymbolicFunctor::BVSymbolicFunctor;
        virtual ~BVNorSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class BVXorConcreteFunctor : public BVConcreteFunctor
    {
    public:
        using BVConcreteFunctor::BVConcreteFunctor;
        virtual ~BVXorConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVXorSymbolicFunctor : public BVSymbolicFunctor
    {
    public:
        using BVSymbolicFunctor::BVSymbolicFunctor;
        virtual ~BVXorSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class BVXNorConcreteFunctor : public BVConcreteFunctor
    {
    public:
        using BVConcreteFunctor::BVConcreteFunctor;
        virtual ~BVXNorConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVXNorSymbolicFunctor : public BVSymbolicFunctor
    {
    public:
        using BVSymbolicFunctor::BVSymbolicFunctor;
        virtual ~BVXNorSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class BVShlConcreteFunctor : public BVConcreteFunctor
    {
    public:
        using BVConcreteFunctor::BVConcreteFunctor;
        virtual ~BVShlConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };
    
    class BVShlSymbolicFunctor : public BVSymbolicFunctor
    {
        using BVSymbolicFunctor::BVSymbolicFunctor;
        virtual ~BVShlSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class BVAShrConcreteFunctor : public BVConcreteFunctor
    {
    public:
        using BVConcreteFunctor::BVConcreteFunctor;
        virtual ~BVAShrConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVAShrSymbolicFunctor : public BVSymbolicFunctor
    {
    public:
        using BVSymbolicFunctor::BVSymbolicFunctor;
        virtual ~BVAShrSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class BVLShrConcreteFunctor : public BVConcreteFunctor
    {
    public:
        using BVConcreteFunctor::BVConcreteFunctor;
        virtual ~BVLShrConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVLShrSymbolicFunctor : public BVSymbolicFunctor
    {
    public:
        using BVSymbolicFunctor::BVSymbolicFunctor;
        virtual ~BVLShrSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class BVNegConcreteFunctor : public BVConcreteFunctor
    {
    public:
        using BVConcreteFunctor::BVConcreteFunctor;
        virtual ~BVNegConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVNegSymbolicFunctor : public BVSymbolicFunctor
    {
    public:
        using BVSymbolicFunctor::BVSymbolicFunctor;
        virtual ~BVNegSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions);
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class BVUSLEConcreteFunctor : public BVConcreteFunctor
    {
    public:
        using BVConcreteFunctor::BVConcreteFunctor;
        virtual ~BVUSLEConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVUSLESymbolicFunctor : public BVSymbolicFunctor
    {
    public:
        using BVSymbolicFunctor::BVSymbolicFunctor;
        virtual ~BVUSLESymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class BVUSGTConcreteFunctor : public BVConcreteFunctor
    {
    public:
        using BVConcreteFunctor::BVConcreteFunctor;
        virtual ~BVUSGTConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVUSGTSymbolicFunctor : public BVSymbolicFunctor
    {
    public:
        using BVSymbolicFunctor::BVSymbolicFunctor;
        virtual ~BVUSGTSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class BVUSDivConcreteFunctor : public BVConcreteFunctor
    {
    public:
        using BVConcreteFunctor::BVConcreteFunctor;
        virtual ~BVUSDivConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVUSDivSymbolicFunctor : public BVSymbolicFunctor
    {
    public:
        using BVSymbolicFunctor::BVSymbolicFunctor;
        virtual ~BVUSDivSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class BVSDivConcreteFunctor : public BVConcreteFunctor
    {
    public:
        using BVConcreteFunctor::BVConcreteFunctor;
        virtual ~BVSDivConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVSDivSymbolicFunctor : public BVSymbolicFunctor
    {
    public:
        using BVSymbolicFunctor::BVSymbolicFunctor;
        virtual ~BVSDivSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class BVUSRemConcreteFunctor : public BVConcreteFunctor
    {
    public:
        using BVConcreteFunctor::BVConcreteFunctor;
        virtual ~BVUSRemConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVUSRemSymbolicFunctor : public BVSymbolicFunctor
    {
    public:
        using BVSymbolicFunctor::BVSymbolicFunctor;
        virtual ~BVUSRemSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class BVSRemConcreteFunctor : public BVConcreteFunctor
    {
    public:
        using BVConcreteFunctor::BVConcreteFunctor;
        virtual ~BVSRemConcreteFunctor();
        virtual void operator () (EvalMap Args,
                             ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVSRemSymbolicFunctor : public BVSymbolicFunctor
    {
    public:
        using BVSymbolicFunctor::BVSymbolicFunctor;
        virtual ~BVSRemSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class BVMulConcreteFunctor : public BVConcreteFunctor
    {
    public:
        using BVConcreteFunctor::BVConcreteFunctor;
        virtual ~BVMulConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVMulSymbolicFunctor : public BVSymbolicFunctor
    {
    public:
        using BVSymbolicFunctor::BVSymbolicFunctor;
        virtual ~BVMulSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    // Utilty functor to convert BV to boolean
    class BVToBoolConcreteFunctor : public BVConcreteFunctor
    {
    public:
        using BVConcreteFunctor::BVConcreteFunctor;
        virtual ~BVToBoolConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVToBoolSymbolicFunctor : public BVSymbolicFunctor
    {
    public:
        using BVSymbolicFunctor::BVSymbolicFunctor;
        virtual ~BVToBoolSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override; 
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    // Utility functors to convert BV to integer
    class BVToSIntConcreteFunctor : public ConcFunctorBase
    {
    protected:
        const ESFixedTypeBase* BVType;
        const ESFixedTypeBase* IntType;
        
    protected:
        BVToSIntConcreteFunctor(const ESFixedTypeBase* BVType,
                                const ESFixedTypeBase* IntType,
                                uint64 UID);
        
    public:
        BVToSIntConcreteFunctor(const ESFixedTypeBase* BVType,
                                const ESFixedTypeBase* IntType);

        virtual ~BVToSIntConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;

        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVToSIntSymbolicFunctor : public SymbFunctorBase
    {
    protected:
        const ESFixedTypeBase* BVType;
        const ESFixedTypeBase* IntType;

    protected:
        BVToSIntSymbolicFunctor(const ESFixedTypeBase* BVType,
                                const ESFixedTypeBase* IntType,
                                uint64 UID);

    public:
        BVToSIntSymbolicFunctor(const ESFixedTypeBase* BVType,
                                const ESFixedTypeBase* IntType);

        virtual ~BVToSIntSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class BVToUSIntConcreteFunctor : public BVToSIntConcreteFunctor
    {
    public:
        using BVToSIntConcreteFunctor::BVToSIntConcreteFunctor;
        virtual ~BVToUSIntConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVToUSIntSymbolicFunctor : public BVToSIntSymbolicFunctor
    {
    public:
        using BVToSIntSymbolicFunctor::BVToSIntSymbolicFunctor;
        virtual ~BVToUSIntSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class BVUSLTConcreteFunctor : public BVConcreteFunctor
    {
    public:
        using BVConcreteFunctor::BVConcreteFunctor;
        virtual ~BVUSLTConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;        
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVUSLTSymbolicFunctor : public BVSymbolicFunctor
    {
    public:
        using BVSymbolicFunctor::BVSymbolicFunctor;
        virtual ~BVUSLTSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class BVUSGEConcreteFunctor : public BVConcreteFunctor
    {
    public:
        using BVConcreteFunctor::BVConcreteFunctor;
        virtual ~BVUSGEConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;        
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVUSGESymbolicFunctor : public BVSymbolicFunctor
    {
    public:
        using BVSymbolicFunctor::BVSymbolicFunctor;
        virtual ~BVUSGESymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class BVSLEConcreteFunctor : public BVConcreteFunctor
    {
    public:
        using BVConcreteFunctor::BVConcreteFunctor;
        virtual ~BVSLEConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;        
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVSLESymbolicFunctor : public BVSymbolicFunctor
    {
    public:
        using BVSymbolicFunctor::BVSymbolicFunctor;
        virtual ~BVSLESymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class BVSLTConcreteFunctor : public BVConcreteFunctor
    {
    public:
        using BVConcreteFunctor::BVConcreteFunctor;
        virtual ~BVSLTConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;        
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVSLTSymbolicFunctor : public BVSymbolicFunctor
    {
    public:
        using BVSymbolicFunctor::BVSymbolicFunctor;
        virtual ~BVSLTSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class BVSGEConcreteFunctor : public BVConcreteFunctor
    {
    public:
        using BVConcreteFunctor::BVConcreteFunctor;
        virtual ~BVSGEConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;        
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVSGESymbolicFunctor : public BVSymbolicFunctor
    {
    public:
        using BVSymbolicFunctor::BVSymbolicFunctor;
        virtual ~BVSGESymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class BVSGTConcreteFunctor : public BVConcreteFunctor
    {
    public:
        using BVConcreteFunctor::BVConcreteFunctor;
        virtual ~BVSGTConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVSGTSymbolicFunctor : public BVSymbolicFunctor
    {
    public:
        using BVSymbolicFunctor::BVSymbolicFunctor;
        virtual ~BVSGTSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class BVConcatConcreteFunctor : public ConcFunctorBase
    {
    private:
        const ESFixedTypeBase* Arg1Type;
        const ESFixedTypeBase* Arg2Type;
        const ESFixedTypeBase* RetType;
        uint64 Arg1Mask;
        uint64 Arg2Mask;
        uint64 RetMask;

    protected:
        BVConcatConcreteFunctor(const ESFixedTypeBase* Arg1Type,
                                const ESFixedTypeBase* Arg2Type,
                                const ESFixedTypeBase* RetType,
                                uint64 UID);

    public:
        BVConcatConcreteFunctor(const ESFixedTypeBase* Arg1Type,
                                const ESFixedTypeBase* Arg2Type,
                                const ESFixedTypeBase* RetType);
        virtual ~BVConcatConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVConcatSymbolicFunctor : public SymbFunctorBase
    {
    private:
        const ESFixedTypeBase* Arg1Type;
        const ESFixedTypeBase* Arg2Type;
        const ESFixedTypeBase* RetType;
        
    protected:
        BVConcatSymbolicFunctor(const ESFixedTypeBase* Arg1Type,
                                const ESFixedTypeBase* Arg2Type,
                                const ESFixedTypeBase* RetType,
                                uint64 UID);
        
    public:
        BVConcatSymbolicFunctor(const ESFixedTypeBase* Arg1Type,
                                const ESFixedTypeBase* Arg2Type,
                                const ESFixedTypeBase* RetType);
        virtual ~BVConcatSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class BVExtractConcreteFunctor : public ConcFunctorBase
    {
    private:
        const ESFixedTypeBase* ArgType;
        const ESFixedTypeBase* RetType;
        uint32 Low;
        uint32 High;
        uint64 ExtractMask;
        uint32 ExtractShift;
        uint64 ResultMask;

    protected:
        BVExtractConcreteFunctor(const ESFixedTypeBase* ArgType,
                                 const ESFixedTypeBase* RetType,
                                 uint32 Low, uint32 High,
                                 uint64 UID);

    public:
        BVExtractConcreteFunctor(const ESFixedTypeBase* ArgType,
                                 const ESFixedTypeBase* RetType,
                                 uint32 Low, uint32 High);

        virtual ~BVExtractConcreteFunctor();

        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;

        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVExtractSymbolicFunctor : public SymbFunctorBase
    {
    private:
        const ESFixedTypeBase* ArgType;
        const ESFixedTypeBase* RetType;
        uint32 Low;
        uint32 High;
        
    protected:
        BVExtractSymbolicFunctor(const ESFixedTypeBase* ArgType,
                                 const ESFixedTypeBase* RetType,
                                 uint32 Low, uint32 High,
                                 uint64 UID);
        
    public:
        BVExtractSymbolicFunctor(const ESFixedTypeBase* ArgType,
                                 const ESFixedTypeBase* RetType,
                                 uint32 Low, uint32 High);
        virtual ~BVExtractSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class BVRedOrConcreteFunctor : public BVConcreteFunctor
    {
    public:
        using BVConcreteFunctor::BVConcreteFunctor;
        virtual ~BVRedOrConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVRedOrSymbolicFunctor : public BVSymbolicFunctor
    {
    public:
        using BVSymbolicFunctor::BVSymbolicFunctor;
        virtual ~BVRedOrSymbolicFunctor();

        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class BVRedAndConcreteFunctor : public BVConcreteFunctor
    {
    public:
        using BVConcreteFunctor::BVConcreteFunctor;
        virtual ~BVRedAndConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class BVRedAndSymbolicFunctor : public BVSymbolicFunctor
    {
    public:
        using BVSymbolicFunctor::BVSymbolicFunctor;
        virtual ~BVRedAndSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

} /* End ESolverBVLogic namespace */

namespace ESolver {

    class BVLogic : public ESolverLogic
    {
    private:
        static set<string> ReservedNames;

    public:
        BVLogic(ESolver* Solver);
        virtual ~BVLogic();

        virtual void Init() override;
        virtual bool InstantiateOperator(const string& OpName,
                                         const vector<const ESFixedTypeBase*>& DomainTypes) override;

        bool InstantiateExtractOperator(const ESFixedTypeBase* BVType,
                                        uint64 Low, uint64 High);

        static string GetExtractOpName(const ESFixedTypeBase* BVType, uint64 Low, uint64 High);

        virtual bool IsNameReserved(const string& Name) const override;
    };

} /* End namespace */

#endif /* __ESOLVER_BV_LOGIC_HPP */

// 
// BVLogic.hpp ends here
