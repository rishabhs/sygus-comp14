// CEGSolver.hpp --- 
// 
// Filename: CEGSolver.hpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:50:33 2014 (-0500)
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


#if !defined __ESOLVER_CEG_SOLVER_HPP
#define __ESOLVER_CEG_SOLVER_HPP

#include "../common/ESolverForwardDecls.hpp"
#include "../solvers/ESolver.hpp"
#include "../expressions/UserExpression.hpp"
#include "../containers/ESSmartPtr.hpp"
#include "../z3interface/Z3Objects.hpp"
#include "../utils/Hashers.hpp"

namespace ESolver {

    class CEGSolver : public ESolver
    {
        friend class ConcreteEvaluator;

    private:
        ConcreteEvaluator* ConcEval;
        EnumeratorBase* ExpEnumerator;
        Expression OrigConstraint;
        Expression RewrittenConstraint;
        vector<const AuxVarOperator*> BaseAuxVars;
        vector<const AuxVarOperator*> DerivedAuxVars;
        set<string> RelevantVars;
        vector<EvalRule> EvalRules;
        vector<const SynthFuncOperator*> SynthFuncs;
        // SMT expressions for the aux vars
        vector<SMTExpr> BaseExprs;
        // The rewritten constraint as an SMT constraint
        SMTExpr SMTConstraint;
        bool Complete;
        SolutionMap Solutions;
        bool Restart;

        uint64 NumExpressionsTried;
        uint64 NumDistExpressions;

        // Single function case
        inline bool CheckSymbolicValidity(const GenExpressionBase* Exp);
        // Multifunction case
        inline bool CheckSymbolicValidity(GenExpressionBase const* const* Exps);

    public:
        CEGSolver(const ESolverOpts* Opts);
        virtual ~CEGSolver();
        
        virtual CallbackStatus ExpressionCallBack(const GenExpressionBase* Exp, 
                                                  const ESFixedTypeBase* Type, 
                                                  uint32 ExpansionTypeID,
                                                  bool Complete,
                                                  uint32 EnumeratorIndex = 0) override;
        // For multifunction synthesis
        virtual CallbackStatus ExpressionCallBack(GenExpressionBase const* const* Exp,
                                                  ESFixedTypeBase const* const* Type, 
                                                  uint32 const* ExpansionTypeID) override;

        virtual SolutionMap Solve(const Expression& Constraint) override;

        virtual void EndSolve() override;
    };

} /* End namespace */

#endif /* __ESOLVER_CEG_SOLVER_HPP */


// 
// CEGSolver.hpp ends here
