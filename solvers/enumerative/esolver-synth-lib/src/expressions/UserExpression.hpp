// UserExpression.hpp --- 
// 
// Filename: UserExpression.hpp
// Author: Abhishek Udupa
// Created: Thu Jan  2 00:47:41 2014 (-0500)
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

#if !defined __ESOLVER_USER_EXPRESSION_HPP
#define __ESOLVER_USER_EXPRESSION_HPP

#include "../common/ESolverForwardDecls.hpp"
#include "../containers/ESRefCountable.hpp"
#include "../containers/ESSmartPtr.hpp"

namespace ESolver {

    class UserExpressionBase : public ESRefCountable
    {
    protected:
        static const vector<Expression> EmptyChildVec;
        virtual void ComputeHashValue() const = 0;
   
        const OperatorBase* Op;
        mutable uint64 HashValue;
        mutable bool HashValid;
     
    public:
        UserExpressionBase(const OperatorBase* Op);
        virtual ~UserExpressionBase();

        virtual const vector<Expression>& GetChildren() const;

        virtual void Evaluate(ExpSubstMap SubstExps,
                              VariableMap VarMap,
                              ConcreteValueBase* Result) const = 0;

        virtual SMTExpr ToSMT(TheoremProver* TP,
                              ExpSubstMap SubstExps,
                              const vector<SMTExpr>& BaseExprs,
                              vector<SMTExpr>& Assumptions) const = 0;
        
        virtual string ToString() const = 0;
        virtual const ESFixedTypeBase* GetType() const;
        virtual bool Equals(const UserExpressionBase& Other) const = 0;

        // Visitors
        virtual void Accept(ExpressionVisitorBase* Visitor) const = 0;

        // two level API
        template<typename T>
        T* As()
        {
            return dynamic_cast<T*>(this);
        }

        template<typename T>
        const T* As() const
        {
            return dynamic_cast<const T*>(this);
        }

        const OperatorBase* GetOp() const;
        
        uint64 Hash() const;
    };

    class UserVarExpressionBase : public UserExpressionBase
    {
    protected:
        virtual void ComputeHashValue() const override;

    public:
        UserVarExpressionBase(const VarOperatorBase* Op);

        virtual ~UserVarExpressionBase();
        const VarOperatorBase* GetOp() const;

        virtual void Evaluate(ExpSubstMap SubstExps,
                              VariableMap VarMap,
                              ConcreteValueBase* Result) const override;

        virtual SMTExpr ToSMT(TheoremProver* TP,
                              ExpSubstMap SubstExps,
                              const vector<SMTExpr>& BaseExprs,
                              vector<SMTExpr>& Assumptions) const override;

        virtual string ToString() const override;
    };

    class UserUQVarExpression : public UserVarExpressionBase
    {
    public:
        UserUQVarExpression(const UQVarOperator* Op);
        virtual ~UserUQVarExpression();

        const UQVarOperator* GetOp() const;
        virtual bool Equals(const UserExpressionBase& Other) const override;
        virtual void Accept(ExpressionVisitorBase* Visitor) const override;
    };

    class UserLetBoundVarExpression : public UserVarExpressionBase
    {
    public:
        UserLetBoundVarExpression(const LetBoundVarOperator* Op);
        virtual ~UserLetBoundVarExpression();
        
        virtual void Evaluate(ExpSubstMap SubstExps,
                              VariableMap VarMap,
                              ConcreteValueBase* Result) const override;

        virtual SMTExpr ToSMT(TheoremProver* TP, 
                              ExpSubstMap SubstExps,
                              const vector<SMTExpr>& BaseExprs,
                              vector<SMTExpr>& Assumptions) const override;

        virtual bool Equals(const UserExpressionBase& Other) const override;
        const LetBoundVarOperator* GetOp() const;
        const Expression& GetBoundToExpression() const;
        virtual void Accept(ExpressionVisitorBase* Visitor) const override;
    };

    class UserFormalParamExpression : public UserVarExpressionBase
    {
    public:
        UserFormalParamExpression(const FormalParamOperator* Op);
        virtual ~UserFormalParamExpression();
        
        virtual void Evaluate(ExpSubstMap SubstExps,
                              VariableMap VarMap,
                              ConcreteValueBase* Result) const override;

        virtual SMTExpr ToSMT(TheoremProver* TP, 
                              ExpSubstMap SubstExps,
                              const vector<SMTExpr>& BaseExprs,
                              vector<SMTExpr>& Assumptions) const override;

        virtual bool Equals(const UserExpressionBase& Other) const override;
        const FormalParamOperator* GetOp() const;
        virtual void Accept(ExpressionVisitorBase* Visitor) const override;
    };

    class UserAuxVarExpression : public UserVarExpressionBase
    {
    public:
        UserAuxVarExpression(const AuxVarOperator* Op);
        virtual ~UserAuxVarExpression();
        
        const AuxVarOperator* GetOp() const;
        virtual bool Equals(const UserExpressionBase& Other) const override;
        virtual void Accept(ExpressionVisitorBase* Visitor) const override;
    };

    class UserFuncExpressionBase : public UserExpressionBase
    {
    public:
        UserFuncExpressionBase(const FuncOperatorBase* Op);
        virtual ~UserFuncExpressionBase();
        
        const FuncOperatorBase* GetOp() const;
    };

    class UserConstExpression : public UserFuncExpressionBase
    {
    protected:
        virtual void ComputeHashValue() const override;

    public:
        UserConstExpression(const ConstOperator* Op);
        virtual ~UserConstExpression();

        virtual void Evaluate(ExpSubstMap SubstExps,
                              VariableMap VarMap,
                              ConcreteValueBase* Result) const override;

        virtual SMTExpr ToSMT(TheoremProver* TP, 
                              ExpSubstMap SubstExps,
                              const vector<SMTExpr>& BaseExprs,
                              vector<SMTExpr>& Assumptions) const override;

        virtual string ToString() const override;
        virtual bool Equals(const UserExpressionBase& Other) const override;
        const ConstOperator* GetOp() const;
        virtual void Accept(ExpressionVisitorBase* Visitor) const override;
    };

    class UserInterpretedFuncExpression : public UserFuncExpressionBase
    {
    protected:
        const uint32 NumChildren;
        vector<Expression> Children;
        ConcreteValueBase const** ChildEvals;

    protected:
        virtual void ComputeHashValue() const override;

    public:
        UserInterpretedFuncExpression(const InterpretedFuncOperator* Op,
                                      const vector<Expression> Children);
        virtual ~UserInterpretedFuncExpression();

        
        virtual const vector<Expression>& GetChildren() const override;

        virtual void Evaluate(ExpSubstMap SubstExps,
                              VariableMap VarMap,
                              ConcreteValueBase* Result) const override;

        virtual SMTExpr ToSMT(TheoremProver* TP, 
                              ExpSubstMap SubstExps,
                              const vector<SMTExpr>& BaseExprs,
                              vector<SMTExpr>& Assumptions) const override;

        virtual string ToString() const override;
        virtual bool Equals(const UserExpressionBase& Other) const override;
        virtual void Accept(ExpressionVisitorBase* Visitor) const override;
        const InterpretedFuncOperator* GetOp() const;
    };

    class UserSynthFuncExpression : public UserFuncExpressionBase
    {
    private:
        // Indicates where I get my parameters from
        // A vector of indices into the VarMap
        mutable uint32* ParameterMap;
        vector<Expression> Children;
        const uint32 NumChildren;

    protected:
        virtual void ComputeHashValue() const override;

    public:
        UserSynthFuncExpression(const SynthFuncOperator* Op, 
                                const vector<Expression>& Children);
        virtual ~UserSynthFuncExpression();
        
        virtual const vector<Expression>& GetChildren() const override;
        virtual void Evaluate(ExpSubstMap SubstExps,
                              VariableMap VarMap,
                              ConcreteValueBase* Result) const override;

        virtual SMTExpr ToSMT(TheoremProver* TP,
                              ExpSubstMap SubstExps,
                              const vector<SMTExpr>& BaseExprs,
                              vector<SMTExpr>& Assumptions) const override;

        virtual bool Equals(const UserExpressionBase& Other) const override;
        virtual void Accept(ExpressionVisitorBase* Visitor) const override;
        virtual string ToString() const override;

        const SynthFuncOperator* GetOp() const;
        uint32* GetParamMap() const;
    };

    class UserLetExpression : public UserExpressionBase
    {
    protected:
        virtual void ComputeHashValue() const override;

    private:
        map<Expression, Expression> LetBoundVars;
        Expression BoundInExpression;

    public:
        UserLetExpression(const map<Expression, Expression>& LetBoundVars,
                          const Expression& BoundInExpression);
        ~UserLetExpression();
        
        virtual void Evaluate(ExpSubstMap SubstExps,
                              VariableMap VarMap,
                              ConcreteValueBase* Result) const override;

        virtual SMTExpr ToSMT(TheoremProver* TP,
                              ExpSubstMap SubstExps,
                              const vector<SMTExpr>& BaseExprs,
                              vector<SMTExpr>& Assumptions) const override;

        virtual string ToString() const override;
        virtual bool Equals(const UserExpressionBase& Other) const override;
        virtual void Accept(ExpressionVisitorBase* Visitor) const override;
        virtual const ESFixedTypeBase* GetType() const override;
        
        const Expression& GetBoundInExpression() const;
        const map<Expression, Expression>& GetLetBoundVars() const;
    };

    extern ostream& operator << (ostream& out, const Expression& Exp);
    extern ostream& operator << (ostream& out, const UserExpressionBase& Exp);


} /* end namespace */

#endif /* __ESOLVER_USER_EXPRESSION_HPP */


// 
// UserExpression.hpp ends here
