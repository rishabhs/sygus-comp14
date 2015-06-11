// MacroExpChecker.cpp ---
//
// Filename: MacroExpChecker.cpp
// Author: Abhishek Udupa
// Created: Mon Jan  6 02:14:07 2014 (-0500)
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

#include "ExpCheckers.hpp"
#include "../expressions/UserExpression.hpp"
#include "../descriptions/Operators.hpp"
#include "../exceptions/ESException.hpp"

namespace ESolver {

    MacroExpChecker::MacroExpChecker()
        : ExpressionVisitorBase("MacroExpChecker")
    {
        // Nothing here
    }

    MacroExpChecker::~MacroExpChecker()
    {
        // Nothing here
    }

    void MacroExpChecker::VisitUserInterpretedFuncExpression(const UserInterpretedFuncExpression* Exp)
    {
        ExpressionVisitorBase::VisitUserInterpretedFuncExpression(Exp);
    }

    void MacroExpChecker::VisitUserFormalParamExpression(const UserFormalParamExpression* Exp)
    {
        auto Pos = Exp->GetOp()->GetPosition();
        auto it = FormalParamExpressions.find(Pos);
        if (it == FormalParamExpressions.end()) {
            FormalParamExpressions[Pos] = Exp;
        } else {
            if (Exp != it->second) {
                throw TypeException((string)"Multiple formal parameters bound to position " +
                                    to_string(Pos) + " in macro definition");
            }
        }
        ExpressionVisitorBase::VisitUserFormalParamExpression(Exp);
    }

    void MacroExpChecker::VisitUserSynthFuncExpression(const UserSynthFuncExpression* Exp)
    {
        ostringstream sstr;
        sstr <<  "Terms involving functions to be synthesized are "
             << "not allowed in define-fun commands." << endl;
        sstr << Exp->ToString() << " involves a function to be synthesized and "
             << "appears in a define-fun command." << endl;
        throw TypeException(sstr.str());
    }

    void MacroExpChecker::VisitUserUQVarExpression(const UserUQVarExpression* Exp)
    {
        throw TypeException("Universally quantified variables are not allowed in macro definitions!");
    }

    void MacroExpChecker::VisitUserAuxVarExpression(const UserAuxVarExpression* Exp)
    {
        throw InternalError((string)"INTERNAL: Aux variables are not allowed in macro definitions!\n" +
                            "At " + __FILE__ + ":" + to_string(__LINE__));
    }

    void MacroExpChecker::Do(const Expression& Exp,
                             const vector<const ESFixedTypeBase*>& DomainTypes,
                             const ESFixedTypeBase* RangeType,
                             vector<Expression>& FormalParamExps)
    {
        if (Exp->GetType() != RangeType) {
            throw TypeException((string)"Macro Expression has mismatched type");
        }

        MacroExpChecker Checker;
        Exp->Accept(&Checker);

        // Check if the formal param expressions obtained have the same type as expected
        // Also, ALL formal params MUST be used
        for (uint32 i = 0; i < DomainTypes.size(); ++i) {
            auto it = Checker.FormalParamExpressions.find(i);
            if (it == Checker.FormalParamExpressions.end()) {
                throw TypeException((string)"Formal parameter " + to_string(i) + " unused in macro. " +
                                    "Please eliminate unused parameters from macro definitions.");
            }
            if (it->second->GetType() != DomainTypes[i]) {
                throw TypeException((string)"Formal parameter type mismatch at position " + to_string(i) +
                                    " in macro definition");
            }
            FormalParamExps.push_back(it->second);
        }
    }

    // Let binding checker

    LetBindingChecker::LetBindingChecker()
        : ExpressionVisitorBase("LetBindingChecker")
    {
        // Nothing here
    }

    LetBindingChecker::~LetBindingChecker()
    {
        // Nothing here
    }

    void LetBindingChecker::VisitUserLetExpression(const UserLetExpression* Exp)
    {
        set<const LetBoundVarOperator*> NewBindings;

        // Visit the binding expressions first
        for (auto const& Binding : Exp->GetLetBoundVars()) {
            Binding.second->Accept(this);
            NewBindings.insert(Binding.first->GetOp()->As<LetBoundVarOperator>());
        }

        // Push the new bindings and recurse on the actual expression
        BoundOperators.push_back(NewBindings);
        Exp->GetBoundInExpression()->Accept(this);
        BoundOperators.pop_back();
    }

    void LetBindingChecker::VisitUserLetBoundVarExpression(const UserLetBoundVarExpression* Exp)
    {
        auto Op = Exp->GetOp();
        for (auto BindingMapIt = BoundOperators.rbegin();
             BindingMapIt != BoundOperators.rend(); ++BindingMapIt) {
            if (BindingMapIt->find(Op) != BindingMapIt->end()) {
                return;
            }
        }
        throw TypeException((string)"Error: Unbound let variable: \"" + Op->GetName() + "\"");
    }

    void LetBindingChecker::Do(const Expression& Exp)
    {
        LetBindingChecker Checker;
        Exp->Accept(&Checker);
        return;
    }

} /* end namespace */

//
// MacroExpChecker.cpp ends here
