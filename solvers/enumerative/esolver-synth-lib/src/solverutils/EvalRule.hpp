// EvalRule.hpp ---
//
// Filename: EvalRule.hpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:50:16 2014 (-0500)
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


#if !defined __ESOLVER_EVAL_RULE_HPP
#define __ESOLVER_EVAL_RULE_HPP

#include "../common/ESolverForwardDecls.hpp"
#include "../expressions/UserExpression.hpp"
#include "../containers/ESSmartPtr.hpp"

namespace ESolver {

    /*
       An eval rule is a recipe to obtain the value or SMT representation of a derived
       auxiliary variable. It essentially takes a derived aux variable to it's value
       or it's SMT representation.

       As such it needs the following:
       1. The derived variable under question
       2. The (symbolic) expression which the derived variable goes to.
       3. A ParameterMap which indicates what params are to be substituted for
          each formal param of any SynthFuncs that might be present
       4. A SubstitutionMap which indicates what SMT expressions to substitute
          for each formal parameter of a SynthFunc expression

       Thus, given a GenExpression, evaluation proceeds by
       calling Eval on the symbolic expression with the appropriate params

       ToSMT proceeds by calling ToSMT on the symbolic expression
       with the appropriate params
    */

    class EvalRule
    {
    private:
        const AuxVarOperator* LHS;
        Expression RHS;

    public:
        // Default constructor
        EvalRule();
        EvalRule(const AuxVarOperator* LHS,
                 const Expression& RHS);
        // Copy constructor
        EvalRule(const EvalRule& Other);
        ~EvalRule();

        // Assignment operator
        EvalRule& operator = (const EvalRule& Other);

        // Accessors
        const AuxVarOperator* GetLHS() const;
        const Expression& GetRHS() const;

        // Evaluation
        void Evaluate(ExpSubstMap SubstExps,
                      VariableMap VarMap,
                      ConcreteValueBase* Result) const;

        SMTExpr ToSMT(TheoremProver* TP, ExpSubstMap SubstExps,
                      const vector<SMTExpr>& BaseExprs,
                      vector<SMTExpr>& Assumptions) const;

        // Stringification
        string ToString() const;
    };

    extern ostream& operator << (ostream& str, const EvalRule& Rule);

} /* End namespace */

#endif /* __ESOLVER_EVAL_RULE_HPP */


//
// EvalRule.hpp ends here
