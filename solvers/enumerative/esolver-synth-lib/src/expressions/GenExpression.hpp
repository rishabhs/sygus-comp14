// GenExpression.hpp --- 
// 
// Filename: GenExpression.hpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:51:28 2014 (-0500)
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


#if !defined __ESOLVER_GEN_EXPRESSION_HPP
#define __ESOLVER_GEN_EXPRESSION_HPP

#include "../common/ESolverForwardDecls.hpp"
#include "../descriptions/Operators.hpp"
#include "../z3interface/Z3Objects.hpp"
#include "../values/ConcreteValueBase.hpp"

// tunable parameters
#define ESOLVER_MAX_LET_BOUND_VARS (2048)
#define ESOLVER_MAX_LET_BINDING_STACK_SIZE (2048)

#define ESOLVER_CVPOOL_SIZE (8192)
#define ESOLVER_GEN_EVAL_STACK_SIZE (8192)

namespace ESolver {

    class GenExpressionBase
    {
    protected:
        // A preallocated stack for varmaps
        static ConcreteValueBase const* const** LetBindingValStack;
        static uint32 LetBindingValStackTop;

        static vector<map<uint32, SMTExpr>> LetBindingSMTStack;

        // Preallocated space for storing evaluations
        static ConcreteValueBase** CVPool;
        static uint32 CVPoolTop;

        // A stack to store evaluations
        static ConcreteValueBase** EvalStack;
        static uint32 EvalStackTop;
        static uint64 FreshVarID;
        
    public:
        static void Initialize();
        static void Finalize();

        static ConcreteValueBase* GetCV();
        
        static void Evaluate(const GenExpressionBase* Exp, VariableMap VarMap,
                             const uint32* ParamMap, ConcreteValueBase* Result);
        static SMTExpr ToSMT(const GenExpressionBase* Exp, TheoremProver* TP, const uint32* ParamMap,
                             const vector<SMTExpr>& BaseExprs, vector<SMTExpr>& Assumptions);

        static Expression ToUserExpression(const GenExpressionBase* Exp,
                                           ESolver* Solver);

        GenExpressionBase();
        virtual ~GenExpressionBase();

        virtual string ToString() const = 0;

        virtual void Evaluate(const uint32* ParamMap,
                              VariableMap VarMap) const = 0;


        virtual SMTExpr ToSMT(TheoremProver* TP, const uint32* ParamMap,
                              const vector<SMTExpr>& BaseExprs,
                              vector<SMTExpr>& Assumptions) const = 0;

        virtual const ESFixedTypeBase* GetType() const = 0;
        virtual Expression ToUserExpression(ESolver* Solver, 
                                            const map<uint32, const LetBoundVarOperator*>& BoundOps) const = 0;
    };

    class GenLetVarExpression : public GenExpressionBase
    {
    private:
        const LetBoundVarOperator* Op;

    public:
        GenLetVarExpression(const LetBoundVarOperator* Op);
        virtual ~GenLetVarExpression();

        virtual string ToString() const override;

        virtual void Evaluate(const uint32* ParamMap,
                              VariableMap VarMap) const override;
        
        virtual SMTExpr ToSMT(TheoremProver* TP, const uint32* ParamMap,
                              const vector<SMTExpr>& BaseExprs,
                              vector<SMTExpr>& Assumptions) const override;

        virtual const ESFixedTypeBase* GetType() const override;

        uint32 GetVarID() const;
        void SetVarID(uint32 VarID) const;
        virtual Expression ToUserExpression(ESolver* Solver,
                                            const map<uint32, const LetBoundVarOperator*>& BoundOps) const override;
    };

    class GenFPExpression : public GenExpressionBase
    {
    private:
        const FormalParamOperator* Op;
        
    public:
        GenFPExpression(const FormalParamOperator* Op);
        virtual ~GenFPExpression();

        virtual string ToString() const override;

        virtual void Evaluate(const uint32* ParamMap,
                              VariableMap VarMap) const override;
        
        virtual SMTExpr ToSMT(TheoremProver* TP, const uint32* ParamMap,
                              const vector<SMTExpr>& BaseExprs,
                              vector<SMTExpr>& Assumptions) const override;

        virtual const ESFixedTypeBase* GetType() const override;
        virtual Expression ToUserExpression(ESolver* Solver,
                                            const map<uint32, const LetBoundVarOperator*>& BoundsOps) const override;
    };

    class GenConstExpression : public GenExpressionBase
    {
    private:
        const ConstOperator* Op;
        
    public:
        GenConstExpression(const ConstOperator* Op);
        virtual ~GenConstExpression();
        
        virtual string ToString() const override;
        virtual void Evaluate(const uint32* ParamMap,
                              VariableMap VarMap) const override;

        virtual SMTExpr ToSMT(TheoremProver* TP, const uint32* ParamMap,
                              const vector<SMTExpr>& BaseExprs,
                              vector<SMTExpr>& Assumptions) const override;

        virtual const ESFixedTypeBase* GetType() const override;
        virtual Expression ToUserExpression(ESolver* Solver,
                                            const map<uint32, const LetBoundVarOperator*>& BoundOps) const override;
    };

    class GenFuncExpression : public GenExpressionBase
    {
    private:
        const InterpretedFuncOperator* Op;
        mutable GenExpressionBase const* const* Children;

    public:
        // Takes ownership of children
        GenFuncExpression(const InterpretedFuncOperator* Op,
                          GenExpressionBase const* const* Children);
        virtual ~GenFuncExpression();

        virtual string ToString() const override;
        virtual void Evaluate(const uint32* ParamMap,
                              VariableMap VarMap) const override;

        virtual SMTExpr ToSMT(TheoremProver* TP, const uint32* ParamMap,
                              const vector<SMTExpr>& BaseExprs,
                              vector<SMTExpr>& Assumptions) const override;
        
        virtual const ESFixedTypeBase* GetType() const override;
        virtual Expression ToUserExpression(ESolver* Solver,
                                            const map<uint32, const LetBoundVarOperator*>& BoundOps) const override;
    };

    class GenLetExpression : public GenExpressionBase
    {
    private:
        mutable GenExpressionBase const* const* Bindings;
        GenExpressionBase const* LetBoundExp;
        uint32 NumBindings;
        
    public:
        GenLetExpression(GenExpressionBase const* const* Bindings,
                         GenExpressionBase const* LetBoundExp,
                         uint32 NumBindings);

        virtual ~GenLetExpression();

        virtual string ToString() const override;
        virtual void Evaluate(const uint32* ParamMap,
                              VariableMap VarMap) const override;

        virtual SMTExpr ToSMT(TheoremProver* TP, const uint32* ParamMap,
                              const vector<SMTExpr>& BaseExprs,
                              vector<SMTExpr>& Assumptions) const override;

        virtual const ESFixedTypeBase* GetType() const override;

        virtual Expression ToUserExpression(ESolver* Solver,
                                            const map<uint32, const LetBoundVarOperator*>& BoundOps) const override;
    };

} /* End namespace */

#endif /* __ESOLVER_GEN_EXPRESSION_HPP */


// 
// GenExpression.hpp ends here
