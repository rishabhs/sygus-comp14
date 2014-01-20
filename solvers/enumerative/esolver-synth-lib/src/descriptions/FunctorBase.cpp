// FunctorBase.cpp --- 
// 
// Filename: FunctorBase.cpp
// Author: Abhishek Udupa
// Created: Wed Jan  1 19:46:11 2014 (-0500)
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

#include "FunctorBase.hpp"
#include "../z3interface/Z3Objects.hpp"
#include "../z3interface/TheoremProver.hpp"

namespace ESolver {

    UIDGenerator ConcFunctorUIDGenerator;
    UIDGenerator SymbFunctorUIDGenerator;

    ConcFunctorBase::ConcFunctorBase()
        : FunctorID(ConcFunctorUIDGenerator.GetUID())
    {
        // Nothing here
    }

    ConcFunctorBase::ConcFunctorBase(uint64 FunctorID)
        : FunctorID(FunctorID)
    {
        // Nothing here
    }

    ConcFunctorBase::~ConcFunctorBase()
    {
        // Nothing here
    }

    uint64 ConcFunctorBase::GetID() const
    {
        return FunctorID;
    }

    SymbFunctorBase::SymbFunctorBase()
        : FunctorID(SymbFunctorUIDGenerator.GetUID())
    {
        // Nothing here
    }

    SymbFunctorBase::SymbFunctorBase(uint64 FunctorID)
        : FunctorID(FunctorID)
    {
        // Nothing here
    }
    
    SymbFunctorBase::~SymbFunctorBase()
    {
        // Nothing here
    }

    uint64 SymbFunctorBase::GetID() const
    {
        return FunctorID;
    }
    
    MacroConcreteFunctor::MacroConcreteFunctor(const string& Name,
                                               const Expression& MacroExpression)
        : ConcFunctorBase(), Name(Name), MacroExpression(MacroExpression)
    {
        // Nothing here
    }

    MacroConcreteFunctor::MacroConcreteFunctor(const string& Name,
                                               const Expression& MacroExpression,
                                               uint64 FunctorID)
        : ConcFunctorBase(FunctorID), Name(Name), MacroExpression(MacroExpression)
    {
        // Nothing here
    }

    MacroConcreteFunctor::~MacroConcreteFunctor()
    {
        // Nothing here
    }

    void MacroConcreteFunctor::operator () (EvalMap ChildEvals,
                                            ConcreteValueBase* Result)
    {
        // okay to pass nullptr, since we are guaranteed
        // that there will be no synth function in the 
        // rewritten spec
        MacroExpression->Evaluate(nullptr, ChildEvals, Result);
    }

    string MacroConcreteFunctor::ToString() const
    {
        return (string)"MacroConcreteFunctor (" + Name + ")";
    }

    ConcFunctorBase* MacroConcreteFunctor::Clone() const
    {
        return new MacroConcreteFunctor(Name, MacroExpression, GetID());
    }

    MacroSymbolicFunctor::MacroSymbolicFunctor(const string& Name,
                                               const Expression& MacroExpression,
                                               uint64 FunctorID)
        : SymbFunctorBase(FunctorID), Name(Name), MacroExpression(MacroExpression)
    {
        // Nothing here
    }

    MacroSymbolicFunctor::MacroSymbolicFunctor(const string& Name,
                                               const Expression& MacroExpression)
        : SymbFunctorBase(), Name(Name), MacroExpression(MacroExpression)
    {
        // Nothing here
    }

    MacroSymbolicFunctor::~MacroSymbolicFunctor()
    {
        // Nothing here
    }

    SMTExpr MacroSymbolicFunctor::operator () (TheoremProver* TP,
                                               const vector<SMTExpr>& Children,
                                               vector<SMTExpr>& Assumptions)
    {
        return MacroExpression->ToSMT(TP, nullptr, Children, Assumptions);
    }

    string MacroSymbolicFunctor::ToString() const
    {
        return (string)"MacroSymbolicFunctor (" + Name + ")";
    }

    SymbFunctorBase* MacroSymbolicFunctor::Clone() const
    {
        return new MacroSymbolicFunctor(Name, MacroExpression, GetID());
    }


} /* end namespace */

// 
// FunctorBase.cpp ends here
