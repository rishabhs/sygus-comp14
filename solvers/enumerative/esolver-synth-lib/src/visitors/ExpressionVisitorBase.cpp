// ExpressionVisitorBase.cpp --- 
// 
// Filename: ExpressionVisitorBase.cpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:53:07 2014 (-0500)
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


#include "ExpressionVisitorBase.hpp"
#include "../expressions/UserExpression.hpp"

namespace ESolver {

    ExpressionVisitorBase::ExpressionVisitorBase(const string& VistorName)
        : VistorName(VistorName)
    {
        // Nothing here
    }

    ExpressionVisitorBase::~ExpressionVisitorBase()
    {
        // Nothing here
    }

    const string& ExpressionVisitorBase::GetName() const
    {
        return VistorName;
    }

    void ExpressionVisitorBase::VisitUserUQVarExpression(const UserUQVarExpression* Exp)
    {
        return;
    }

    void ExpressionVisitorBase::VisitUserLetBoundVarExpression(const UserLetBoundVarExpression* Exp)
    {
        return;
    }

    void ExpressionVisitorBase::VisitUserFormalParamExpression(const UserFormalParamExpression* Exp)
    {
        return;
    }

    void ExpressionVisitorBase::VisitUserAuxVarExpression(const UserAuxVarExpression* Exp)
    {
        return;
    }

    void ExpressionVisitorBase::VisitUserConstExpression(const UserConstExpression* Exp)
    {
        return;
    }

    void ExpressionVisitorBase::VisitUserInterpretedFuncExpression(const UserInterpretedFuncExpression* Exp)
    {
        for (auto const& Child : Exp->GetChildren()) {
            Child->Accept(this);
        }
    }

    void ExpressionVisitorBase::VisitUserSynthFuncExpression(const UserSynthFuncExpression* Exp)
    {
        for (auto const& Child : Exp->GetChildren()) {
            Child->Accept(this);
        }        
    }

    void ExpressionVisitorBase::VisitUserLetExpression(const UserLetExpression* Exp)
    {
        // Visit the bindings first
        for (auto const& Binding : Exp->GetLetBoundVars()) {
            Binding.second->Accept(this);
        }
        Exp->GetBoundInExpression()->Accept(this);
    }

} /* End namespace */


// 
// ExpressionVisitorBase.cpp ends here
