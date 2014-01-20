// Functors.hpp --- 
// 
// Filename: Functors.hpp
// Author: Abhishek Udupa
// Created: Wed Jan  1 19:35:54 2014 (-0500)
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

#include "../common/ESolverForwardDecls.hpp"
#include "../utils/UIDGenerator.hpp"
#include "../containers/ESSmartPtr.hpp"
#include "../expressions/UserExpression.hpp"

#if !defined __ESOLVER_FUNCTOR_BASE_HPP
#define __ESOLVER_FUNCTOR_BASE_HPP

namespace ESolver {

    extern UIDGenerator ConcFunctorUIDGenerator;
    extern UIDGenerator SymbFunctorUIDGenerator;

    /**
       This is the ABC for all concrete functors.
       Clients must supply a functor for use with
       each operator they define. Such functors must be
       of types which inherit from this base class

       The functor must be capable of receiving a vector
       of pointers to BaseValue object and needs to return
       a BaseValue object
    */

    class ConcFunctorBase
    {
    private:
        uint64 FunctorID;

    protected:
        // protected constructor used for cloning
        ConcFunctorBase(uint64 FunctorID);

    public:
        // Default constructor
        ConcFunctorBase();
        virtual ~ConcFunctorBase();

        virtual void operator () (EvalMap ChildEvals, ConcreteValueBase* Result) = 0;

        // A stringification method which needs to be implemented by clients
        virtual string ToString() const = 0;
        // A clone method that needs to be implemented by clients
        virtual ConcFunctorBase* Clone() const = 0;

        uint64 GetID() const;
    };

    /**
       This is the ABC for all operator functor builders.
       The purpose of operator functors is to provide
       functors for operators based, given a validity checker
       object.
       
       This is required because there is no easy way for us
       to reset the Validity checker once it is created
     */

    class SymbFunctorBase
    {
    private:
        uint64 FunctorID;

    protected:
        // protected constructor for cloning
        SymbFunctorBase(uint64 FunctorID);

    public:
        // Constructor
        SymbFunctorBase();
        virtual ~SymbFunctorBase();
        virtual SMTExpr operator () (TheoremProver* TP,
                                     const vector<SMTExpr>& Children,
                                     vector<SMTExpr>& Assumptions) = 0;
        virtual string ToString() const = 0;
        // A clone method which needs to be implemented by clients
        virtual SymbFunctorBase* Clone() const = 0;
        uint64 GetID() const;
    };

    class MacroConcreteFunctor : public ConcFunctorBase
    {
    private:
        string Name;
        Expression MacroExpression;
        
    protected:
        MacroConcreteFunctor(const string& Name, 
                             const Expression& MacroExpression, 
                             uint64 FunctorID);

    public:
        MacroConcreteFunctor(const string& Name, 
                             const Expression& MacroExpression);

        virtual ~MacroConcreteFunctor();

        virtual void operator () (EvalMap ChildEvals, ConcreteValueBase* Result) override;
        virtual string ToString() const override;
        virtual ConcFunctorBase* Clone() const override;
    };

    class MacroSymbolicFunctor : public SymbFunctorBase
    {
    private:
        string Name;
        Expression MacroExpression;

    protected:
        MacroSymbolicFunctor(const string& Name,
                             const Expression& MacroExpression, 
                             uint64 FunctorID);

    public:
        MacroSymbolicFunctor(const string& Name, 
                             const Expression& MacroExpression);

        virtual ~MacroSymbolicFunctor();

        SMTExpr operator () (TheoremProver* TP,
                             const vector<SMTExpr>& Children,
                             vector<SMTExpr>& Assumptions) override;

        virtual string ToString() const override;
        virtual SymbFunctorBase* Clone() const override;
    };

} /* End namespace */

#endif /* __ESOLVER_FUNCTOR_BASE_HPP */

// 
// Functors.hpp ends here
