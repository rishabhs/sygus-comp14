// LIALogic.hpp --- 
// 
// Filename: LIALogic.hpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:51:10 2014 (-0500)
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


#if !defined __ESOLVER_LIA_LOGIC_HPP
#define __ESOLVER_LIA_LOGIC_HPP

#include "../common/ESolverForwardDecls.hpp"
#include "../logics/ESolverLogic.hpp"
#include "../descriptions/FunctorBase.hpp"
#include "../z3interface/Z3Objects.hpp"

using namespace ESolver;

namespace ESolverLIALogic {

    class LIAConcreteFunctor : public ConcFunctorBase
    {
    protected:
        const ESFixedTypeBase* IntType;
        const ESFixedTypeBase* BoolType;

        LIAConcreteFunctor(const ESFixedTypeBase* IntType,
                           const ESFixedTypeBase* BoolType,
                           uint64 UID);

    public:
        LIAConcreteFunctor(const ESFixedTypeBase* IntType,
                           const ESFixedTypeBase* BoolType);
        virtual ~LIAConcreteFunctor();
    };

    class LIASymbolicFunctor : public SymbFunctorBase
    {
    protected:
        const ESFixedTypeBase* IntType;
        const ESFixedTypeBase* BoolType;

        LIASymbolicFunctor(const ESFixedTypeBase* IntType,
                           const ESFixedTypeBase* BoolType,
                           uint64 UID);

    public:
        LIASymbolicFunctor(const ESFixedTypeBase* IntType,
                           const ESFixedTypeBase* BoolType);
        virtual ~LIASymbolicFunctor();
    };

    class AddConcreteFunctor : public LIAConcreteFunctor
    {
    public:
        using LIAConcreteFunctor::LIAConcreteFunctor;
        virtual ~AddConcreteFunctor();
        virtual void operator()(EvalMap Args,
                                ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class AddSymbolicFunctor : public LIASymbolicFunctor
    {
    public:
        using LIASymbolicFunctor::LIASymbolicFunctor;
        virtual ~AddSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class SubConcreteFunctor : public LIAConcreteFunctor
    {
    public:
        using LIAConcreteFunctor::LIAConcreteFunctor;
        virtual ~SubConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class SubSymbolicFunctor : public LIASymbolicFunctor
    {
    public:
        using LIASymbolicFunctor::LIASymbolicFunctor;
        virtual ~SubSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class MinusConcreteFunctor : public LIAConcreteFunctor
    {
    public:
        using LIAConcreteFunctor::LIAConcreteFunctor;
        virtual ~MinusConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;        
    };

    class MinusSymbolicFunctor : public LIASymbolicFunctor
    {
    public:
        using LIASymbolicFunctor::LIASymbolicFunctor;
        virtual ~MinusSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class MulConcreteFunctor : public LIAConcreteFunctor
    {
    public:
        using LIAConcreteFunctor::LIAConcreteFunctor;
        virtual ~MulConcreteFunctor();
        virtual void operator () (EvalMap Args,
                                  ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class MulSymbolicFunctor : public LIASymbolicFunctor
    {
    public:
        using LIASymbolicFunctor::LIASymbolicFunctor;
        virtual ~MulSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class GTConcreteFunctor : public LIAConcreteFunctor
    {
    public:
        using LIAConcreteFunctor::LIAConcreteFunctor;
        virtual ~GTConcreteFunctor();
        virtual void operator() (EvalMap Args,
                                 ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class GTSymbolicFunctor : public LIASymbolicFunctor
    {
    public:
        using LIASymbolicFunctor::LIASymbolicFunctor;
        virtual ~GTSymbolicFunctor();
        virtual SMTExpr operator() (TheoremProver* TP,
                                    const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class GEConcreteFunctor : public LIAConcreteFunctor
    {
    public:
        using LIAConcreteFunctor::LIAConcreteFunctor;
        virtual ~GEConcreteFunctor();
        virtual void operator() (EvalMap Args,
                                 ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class GESymbolicFunctor : public LIASymbolicFunctor
    {
    public:
        using LIASymbolicFunctor::LIASymbolicFunctor;
        virtual ~GESymbolicFunctor();
        virtual SMTExpr operator() (TheoremProver* TP,
                                    const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };


    class LTConcreteFunctor : public LIAConcreteFunctor
    {
    public:
        using LIAConcreteFunctor::LIAConcreteFunctor;
        virtual ~LTConcreteFunctor();
        virtual void operator() (EvalMap Args,
                                 ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class LTSymbolicFunctor : public LIASymbolicFunctor
    {
    public:
        using LIASymbolicFunctor::LIASymbolicFunctor;
        virtual ~LTSymbolicFunctor();
        virtual SMTExpr operator() (TheoremProver* TP,
                                    const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class LEConcreteFunctor : public LIAConcreteFunctor
    {
    public:
        using LIAConcreteFunctor::LIAConcreteFunctor;
        virtual ~LEConcreteFunctor();
        virtual void operator() (EvalMap Args,
                                 ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class LESymbolicFunctor : public LIASymbolicFunctor
    {
    public:
        using LIASymbolicFunctor::LIASymbolicFunctor;
        virtual ~LESymbolicFunctor();
        virtual SMTExpr operator() (TheoremProver* TP,
                                    const vector<SMTExpr>& Args,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };
    

} /* End ESolverLIALogic namespace */

namespace ESolver {

    class LIALogic : public ESolverLogic
    {
    public:
        LIALogic(ESolver* Solver);
        virtual ~LIALogic();

        virtual void Init() override;
    };


} /* End namespace */

#endif /* __ESOLVER_LIA_LOGIC_HPP */


// 
// LIALogic.hpp ends here
