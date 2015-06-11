// SpecRewriter.hpp ---
//
// Filename: SpecRewriter.hpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:48:35 2014 (-0500)
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


#if !defined __ESOLVER_SPEC_REWRITER_HPP
#define __ESOLVER_SPEC_REWRITER_HPP

#include "../common/ESolverForwardDecls.hpp"
#include "../visitors/ExpressionVisitorBase.hpp"
#include "../utils/UIDGenerator.hpp"
#include "../expressions/UserExpression.hpp"
#include "../containers/ESSmartPtr.hpp"
#include "../solverutils/EvalRule.hpp"

namespace ESolver {

    class ParamMapFixup : public ExpressionVisitorBase
    {
    public:
        ParamMapFixup();
        virtual ~ParamMapFixup();

        virtual void VisitUserSynthFuncExpression(const UserSynthFuncExpression* Exp) override;
        static void Do(const Expression& Exp);
    };

    class SpecRewriter : public ExpressionVisitorBase
    {
    private:
        map<Expression, Expression> ExpMap;
        vector<EvalRule> EvalRules;
        // Anything that flows into a function to be synthesized
        // is a base aux variable, and is universally quantified
        // In addition, all user specified universally quantified
        // variables are also translated into base aux variables.
        set<const AuxVarOperator*> BaseAuxVarOps;
        // A derived aux variable is something that is NOT a base
        // aux variable
        vector<const AuxVarOperator*> DerivedAuxVarOps;
        // all aux variables created during this process
        vector<const AuxVarOperator*> AllAuxVarOps;
        // The set of argument tuples for each occurence
        // of a synth function
        vector<map<vector<const AuxVarOperator*>, const AuxVarOperator*>> SynthFunArgOps;
        ESolver* Solver;
        uint64 AuxIDCounter;
        vector<Expression> RewriteStack;

    public:
        SpecRewriter(ESolver* Solver, uint32 NumSynthFuncs);
        virtual ~SpecRewriter();

        virtual void VisitUserSynthFuncExpression(const UserSynthFuncExpression* Exp) override;
        virtual void VisitUserUQVarExpression(const UserUQVarExpression* Exp) override;
        virtual void VisitUserInterpretedFuncExpression(const UserInterpretedFuncExpression* Exp) override;
        virtual void VisitUserLetExpression(const UserLetExpression* Exp) override;

        virtual void VisitUserLetBoundVarExpression(const UserLetBoundVarExpression* Exp) override;
        virtual void VisitUserConstExpression(const UserConstExpression* Exp) override;
        virtual void VisitUserFormalParamExpression(const UserFormalParamExpression* Exp) override;
        virtual void VisitUserAuxVarExpression(const UserAuxVarExpression* Exp) override;


        static Expression Do(ESolver* Solver, const Expression& Exp,
                             vector<const AuxVarOperator*>& BaseAuxVarsOps,
                             vector<const AuxVarOperator*>& DerivedAuxVarOps,
                             vector<map<vector<uint32>, uint32>>& SynthFunAppMaps);
    };

} /* End namespace */

#endif /* __ESOLVER_SPEC_REWRITER_HPP */


//
// SpecRewriter.hpp ends here
