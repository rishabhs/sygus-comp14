// Builtins.hpp --- 
// 
// Filename: Builtins.hpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:51:54 2014 (-0500)
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


#if !defined __ESOLVER_BUILTINS_HPP
#define __ESOLVER_BUILTINS_HPP

#include "../common/ESolverForwardDecls.hpp"
#include "FunctorBase.hpp"

namespace ESolver {

    /**
       This file contains the declarations for builtin
       functions and types
       The builtin types are:
         1. Boolean ("BoolType")
         2. Int ("IntType")
       Some operators on booleans are also predefined:
         1. Disjunction ("Or")
         2. Conjunction ("And")
         3. Negation ("Neg")
         4. Implication ("Implies")
         5. Equivalence ("Iff")
    */

    class AndConcreteFunctor : public ConcFunctorBase
    {
    public:
        using ConcFunctorBase::ConcFunctorBase;
        virtual ~AndConcreteFunctor();
        virtual void operator () (EvalMap ChildEvals, ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class OrConcreteFunctor : public ConcFunctorBase
    {
    public:
        using ConcFunctorBase::ConcFunctorBase;
        virtual ~OrConcreteFunctor();
        virtual void operator () (EvalMap ChildEvals, ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class NegConcreteFunctor : public ConcFunctorBase
    {
    public:
        using ConcFunctorBase::ConcFunctorBase;
        virtual ~NegConcreteFunctor();
        virtual void operator () (EvalMap ChildEvals, ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class ImpliesConcreteFunctor : public ConcFunctorBase
    {
    public:
        using ConcFunctorBase::ConcFunctorBase;
        virtual ~ImpliesConcreteFunctor();
        virtual void operator () (EvalMap ChildEvals, ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class IffConcreteFunctor : public ConcFunctorBase
    {
    public:
        using ConcFunctorBase::ConcFunctorBase;
        virtual ~IffConcreteFunctor();
        virtual void operator () (EvalMap ChildEvals, ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    // Generic equality functor.
    class EQConcreteFunctor : public ConcFunctorBase
    {
    public:
        using ConcFunctorBase::ConcFunctorBase;
        virtual ~EQConcreteFunctor();
        virtual void operator () (EvalMap ChildEvals, ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    // Generic ITE functor
    class ITEConcreteFunctor : public ConcFunctorBase
    {
    public:
        using ConcFunctorBase::ConcFunctorBase;
        virtual ~ITEConcreteFunctor();
        virtual void operator () (EvalMap ChildEvals, ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
   };

    class AndSymbolicFunctor : public SymbFunctorBase
    {
    public:
        using SymbFunctorBase::SymbFunctorBase;
        virtual ~AndSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Children,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class OrSymbolicFunctor : public SymbFunctorBase
    {
    public:
        using SymbFunctorBase::SymbFunctorBase;
        virtual ~OrSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Children,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class NegSymbolicFunctor : public SymbFunctorBase
    {
    public:
        using SymbFunctorBase::SymbFunctorBase;
        virtual ~NegSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Children, 
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class ImpliesSymbolicFunctor : public SymbFunctorBase
    {
    public:
        using SymbFunctorBase::SymbFunctorBase;
        virtual ~ImpliesSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Children,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class IffSymbolicFunctor : public SymbFunctorBase
    {
    public:
        using SymbFunctorBase::SymbFunctorBase;
        virtual ~IffSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Children,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    // Generic symbolic EQ Op functor
    class EQSymbolicFunctor : public SymbFunctorBase
    {
    public:
        using SymbFunctorBase::SymbFunctorBase;
        virtual ~EQSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Children,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    // Generic symbolic ITE op functor
    class ITESymbolicFunctor : public SymbFunctorBase
    {
    public:
        using SymbFunctorBase::SymbFunctorBase;
        virtual ~ITESymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Children,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

    class XorConcreteFunctor : public ConcFunctorBase
    {
    public:
        using ConcFunctorBase::ConcFunctorBase;
        virtual ~XorConcreteFunctor();
        virtual void operator () (EvalMap ChildEvals, ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class XorSymbolicFunctor : public SymbFunctorBase
    {
    public:
        using SymbFunctorBase::SymbFunctorBase;
        virtual ~XorSymbolicFunctor();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Children,
                                     vector<SMTExpr>& Assumptions) override;
        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };


} /* End namespace */

#endif /* __ESOLVER_BUILTINS_HPP */


// 
// Builtins.hpp ends here
