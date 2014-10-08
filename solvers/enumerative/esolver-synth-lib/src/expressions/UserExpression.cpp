// UserExpression.cpp --- 
// 
// Filename: UserExpression.cpp
// Author: Abhishek Udupa
// Created: Thu Jan  2 03:34:55 2014 (-0500)
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

#include "UserExpression.hpp"
#include "../descriptions/Operators.hpp"
#include "../descriptions/ESType.hpp"
#include <boost/functional/hash.hpp>
#include "../z3interface/TheoremProver.hpp"
#include "../values/ConcreteValueBase.hpp"
#include "../visitors/ExpressionVisitorBase.hpp"
#include "../descriptions/FunctorBase.hpp"
#include "GenExpression.hpp"

namespace ESolver {

    const vector<Expression> UserExpressionBase::EmptyChildVec;

    UserExpressionBase::UserExpressionBase(const OperatorBase* Op)
        : Op(Op), HashValid(false)
    {
        // Nothing here
    }

    UserExpressionBase::~UserExpressionBase()
    {
        // Nothing here
    }

    const vector<Expression>& UserExpressionBase::GetChildren() const
    {
        return EmptyChildVec;
    }

    const ESFixedTypeBase* UserExpressionBase::GetType() const
    {
        return Op->GetEvalType();
    }

    const OperatorBase* UserExpressionBase::GetOp() const
    {
        return Op;
    }

    uint64 UserExpressionBase::Hash() const
    {
        if (!HashValid) {
            ComputeHashValue();
            HashValid = true;
        }
        return HashValue;
    }

    UserVarExpressionBase::UserVarExpressionBase(const VarOperatorBase* Op)
        : UserExpressionBase(Op)
    {
        // Nothing here
    }

    UserVarExpressionBase::~UserVarExpressionBase()
    {
        // Nothing here
    }

    void UserVarExpressionBase::ComputeHashValue() const 
    {
        HashValue = (uint64)0;
        boost::hash_combine(HashValue, Op->Hash());
    }

    const VarOperatorBase* UserVarExpressionBase::GetOp() const
    {
        return static_cast<const VarOperatorBase*>(Op);
    }

    void UserVarExpressionBase::Evaluate(ExpSubstMap SubstExps,
                                         VariableMap VarMap,
                                         ConcreteValueBase* Result) const
    {
        new (Result) ConcreteValueBase(*(VarMap[static_cast<const VarOperatorBase*>(Op)->GetPosition()]));
    }

    SMTExpr UserVarExpressionBase::ToSMT(TheoremProver* TP, 
                                         ExpSubstMap SubstExps,
                                         const vector<SMTExpr>& BaseExprs,
                                         vector<SMTExpr>& Assumptions) const
    {
        return BaseExprs[GetOp()->GetPosition()];
    }

    string UserVarExpressionBase::ToString() const 
    {
        return (Op->GetName());
    }

    UserUQVarExpression::UserUQVarExpression(const UQVarOperator* Op)
        : UserVarExpressionBase(Op)
    {
        // Nothing here
    }

    UserUQVarExpression::~UserUQVarExpression()
    {
        // Nothing here
    }

    const UQVarOperator* UserUQVarExpression::GetOp() const
    {
        return static_cast<const UQVarOperator*>(Op);
    }

    bool UserUQVarExpression::Equals(const UserExpressionBase& Other) const
    {
        auto OtherPtr = Other.As<UserUQVarExpression>();
        if (OtherPtr == nullptr) {
            return false;
        }
        return (Op->GetID() == OtherPtr->Op->GetID());
    }

    void UserUQVarExpression::Accept(ExpressionVisitorBase* Visitor) const
    {
        Visitor->VisitUserUQVarExpression(this);
    }

    UserLetBoundVarExpression::UserLetBoundVarExpression(const LetBoundVarOperator* Op)
        : UserVarExpressionBase(Op)
    {
        // Nothing here
    }

    UserLetBoundVarExpression::~UserLetBoundVarExpression()
    {
        // Nothing here
    }

    void UserLetBoundVarExpression::Evaluate(ExpSubstMap SubstExps,
                                             VariableMap VarMap,
                                             ConcreteValueBase* Result) const
    {
        throw InternalError((string)"LetBoundVarExpression::Evaluate() must never have been called\n" + 
                            "At " + __FILE__ + ":" + to_string(__LINE__));
    }

    SMTExpr UserLetBoundVarExpression::ToSMT(TheoremProver* TP,
                                             ExpSubstMap SubstExps,
                                             const vector<SMTExpr>& BaseExprs,
                                             vector<SMTExpr>& Assumptions) const
    {
        throw InternalError((string)"LetBoundVarExpression::ToSMT() must never have been called\n" + 
                            "At " + __FILE__ + ":" + to_string(__LINE__));        
    }

    bool UserLetBoundVarExpression::Equals(const UserExpressionBase& Other) const
    {
        auto OtherPtr = Other.As<UserLetBoundVarExpression>();
        if (OtherPtr == nullptr) {
            return false;
        }
        return (Op->GetID() == OtherPtr->Op->GetID());
    }

    const LetBoundVarOperator* UserLetBoundVarExpression::GetOp() const
    {
        return static_cast<const LetBoundVarOperator*>(Op);
    }

    void UserLetBoundVarExpression::Accept(ExpressionVisitorBase* Visitor) const
    {
        Visitor->VisitUserLetBoundVarExpression(this);
    }

    UserFormalParamExpression::UserFormalParamExpression(const FormalParamOperator* Op)
        : UserVarExpressionBase(Op)
    {
        // Nothing here
    }

    UserFormalParamExpression::~UserFormalParamExpression()
    {
        // Nothing here
    }

    void UserFormalParamExpression::Evaluate(ExpSubstMap SubstExps,
                                             VariableMap VarMap,
                                             ConcreteValueBase* Result) const
    {
        new (Result) ConcreteValueBase(*(VarMap[GetOp()->GetPosition()]));
    }

    SMTExpr UserFormalParamExpression::ToSMT(TheoremProver* TP,
                                             ExpSubstMap SubstExps,
                                             const vector<SMTExpr>& BaseExprs,
                                             vector<SMTExpr>& Assumptions) const
    {
        return BaseExprs[GetOp()->GetPosition()];
    }

    bool UserFormalParamExpression::Equals(const UserExpressionBase& Other) const
    {
        auto OtherPtr = Other.As<UserFormalParamExpression>();
        if (OtherPtr == nullptr) {
            return false;
        }

        return (OtherPtr->Op->GetID() == Op->GetID());
    }

    const FormalParamOperator* UserFormalParamExpression::GetOp() const
    {
        return static_cast<const FormalParamOperator*>(Op);
    }

    void UserFormalParamExpression::Accept(ExpressionVisitorBase* Visitor) const
    {
        Visitor->VisitUserFormalParamExpression(this);
    }

    UserAuxVarExpression::UserAuxVarExpression(const AuxVarOperator* Op)
        : UserVarExpressionBase(Op)
    {
        // Nothing here
    }

    UserAuxVarExpression::~UserAuxVarExpression()
    {
        // Nothing here
    }

    const AuxVarOperator* UserAuxVarExpression::GetOp() const
    {
        return static_cast<const AuxVarOperator*>(Op);
    }

    bool UserAuxVarExpression::Equals(const UserExpressionBase& Other) const
    {
        auto OtherPtr = Other.As<UserAuxVarExpression>();
        if (OtherPtr == nullptr) {
            return false;
        }
        return (OtherPtr->Op->GetID() == Op->GetID());
    }

    void UserAuxVarExpression::Accept(ExpressionVisitorBase* Visitor) const
    {
        Visitor->VisitUserAuxVarExpression(this);
    }

    UserFuncExpressionBase::UserFuncExpressionBase(const FuncOperatorBase* Op)
        : UserExpressionBase(Op)
    {
        // Nothing here
    }

    UserFuncExpressionBase::~UserFuncExpressionBase()
    {
        // Nothing here
    }

    const FuncOperatorBase* UserFuncExpressionBase::GetOp() const
    {
        return static_cast<const FuncOperatorBase*>(Op);
    }

    UserConstExpression::UserConstExpression(const ConstOperator* Op)
        : UserFuncExpressionBase(Op)
    {
        // Nothing here
    }

    UserConstExpression::~UserConstExpression()
    {
        // Nothing here
    }

    void UserConstExpression::ComputeHashValue() const
    {
        HashValue = (uint64)0;
        boost::hash_combine(HashValue, Op->Hash());
    }

    void UserConstExpression::Evaluate(ExpSubstMap SubstExps,
                                       VariableMap VarMap,
                                       ConcreteValueBase* Result) const

    {
        new (Result) ConcreteValueBase(*static_cast<const ConstOperator*>(Op)->GetConstantValue());
    }

    SMTExpr UserConstExpression::ToSMT(TheoremProver* TP,
                                       ExpSubstMap SubstExps,
                                       const vector<SMTExpr>& BaseExprs,
                                       vector<SMTExpr>& Assumptions) const
    {
        return static_cast<const ConstOperator*>(Op)->GetConstantValue()->ToSMT(TP);
    }

    bool UserConstExpression::Equals(const UserExpressionBase& Other) const
    {
        auto OtherPtr = Other.As<UserConstExpression>();
        if (OtherPtr == nullptr) {
            return false;
        }
        return (OtherPtr->Op->GetID() == Op->GetID());
    }

    string UserConstExpression::ToString() const
    {
        auto Op = GetOp();
        if (Op->IsAnon()) {
            return Op->GetConstantValue()->ToString();
        } else {
            return Op->GetName();
        }
    }

    const ConstOperator* UserConstExpression::GetOp() const
    {
        return static_cast<const ConstOperator*>(Op);
    }

    void UserConstExpression::Accept(ExpressionVisitorBase* Visitor) const
    {
        Visitor->VisitUserConstExpression(this);
    }

    UserInterpretedFuncExpression::UserInterpretedFuncExpression(const InterpretedFuncOperator* Op,
                                                                 const vector<Expression> Children)
        : UserFuncExpressionBase(Op), NumChildren(Children.size()), Children(Children)
    {
        const uint32 NumChildren = Op->GetArity();
        ChildEvals = (const ConcreteValueBase**)malloc(NumChildren * sizeof(ConcreteValueBase*));
        for (uint32 i = 0; i < NumChildren; ++i) {
            ChildEvals[i] = new ConcreteValueBase();
        }
    }

    UserInterpretedFuncExpression::~UserInterpretedFuncExpression()
    {
        for (uint32 i = 0; i < NumChildren; ++i) {
            delete ChildEvals[i];
        }
        free(ChildEvals);
    }

    void UserInterpretedFuncExpression::ComputeHashValue() const
    {
        HashValue = (uint64)0;
        boost::hash_combine(HashValue, Op->Hash());
        for (uint32 i = 0; i < NumChildren; ++i) {
            boost::hash_combine(HashValue, Children[i]->Hash());
        }
    }

    const vector<Expression>& UserInterpretedFuncExpression::GetChildren() const
    {
        return Children;
    }

    void UserInterpretedFuncExpression::Evaluate(ExpSubstMap SubstExps,
                                                 VariableMap VarMap,
                                                 ConcreteValueBase* Result) const
    {
        for (uint32 i = 0; i < NumChildren; ++i) {
            Children[i]->Evaluate(SubstExps, VarMap, 
                                  const_cast<ConcreteValueBase*>(ChildEvals[i]));
        }
        auto Functor = static_cast<const InterpretedFuncOperator*>(Op)->GetConcFunctor();
        (*Functor)(ChildEvals, Result);
    }

    SMTExpr UserInterpretedFuncExpression::ToSMT(TheoremProver* TP,
                                                 ExpSubstMap SubstExps,
                                                 const vector<SMTExpr>& BaseExprs,
                                                 vector<SMTExpr>& Assumptions) const
    {
        vector<SMTExpr> ChildSMTExps(NumChildren);
        for (uint32 i = 0; i < NumChildren; ++i) {
            ChildSMTExps[i] = Children[i]->ToSMT(TP, SubstExps, BaseExprs, Assumptions);
        }
        auto Functor = static_cast<const InterpretedFuncOperator*>(Op)->GetSymbFunctor();
        return (*Functor)(TP, ChildSMTExps, Assumptions);
    }

    string UserInterpretedFuncExpression::ToString() const
    {
        ostringstream sstr;
        sstr << "(" << static_cast<const InterpretedFuncOperator*>(Op)->GetName();
        for (uint32 i = 0; i < NumChildren; ++i) {
            sstr << " " << Children[i]->ToString();
        }
        sstr << ")";
        return sstr.str();
    }

    bool UserInterpretedFuncExpression::Equals(const UserExpressionBase& Other) const
    {
        auto OtherPtr = Other.As<UserInterpretedFuncExpression>();
        if (OtherPtr == nullptr) {
            return false;
        }
        if (OtherPtr->Op->GetID() != Op->GetID()) {
            return false;
        }

        for (uint32 i = 0; i < NumChildren; ++i) {
            if (Children[i] != OtherPtr->Children[i]) {
                return false;
            }
        }
        return true;
    }

    void UserInterpretedFuncExpression::Accept(ExpressionVisitorBase* Visitor) const
    {
        Visitor->VisitUserInterpretedFuncExpression(this);
    }

    const InterpretedFuncOperator* UserInterpretedFuncExpression::GetOp() const
    {
        return static_cast<const InterpretedFuncOperator*>(Op);
    }

    UserSynthFuncExpression::UserSynthFuncExpression(const SynthFuncOperator* Op,
                                                     const vector<Expression>& Children)
        : UserFuncExpressionBase(Op), Children(Children), NumChildren(Children.size())
    {
        ParameterMap = (uint32*)calloc(NumChildren, sizeof(uint32));
    }

    UserSynthFuncExpression::~UserSynthFuncExpression()
    {
        free(ParameterMap);
    }
    
    void UserSynthFuncExpression::ComputeHashValue() const
    {
        HashValue = (uint64)0;
        boost::hash_combine(HashValue, Op->Hash());
        for (uint32 i = 0; i < NumChildren; ++i) {
            boost::hash_combine(HashValue, Children[i]->Hash());
        }
    }
    
    void UserSynthFuncExpression::Evaluate(ExpSubstMap SubstExps,
                                           VariableMap VarMap,
                                           ConcreteValueBase* Result) const
    {
        auto MyID = GetOp()->GetPosition();
        GenExpressionBase::Evaluate(const_cast<GenExpressionBase*>(SubstExps[MyID]),
                                    VarMap, ParameterMap, Result);
    }

    SMTExpr UserSynthFuncExpression::ToSMT(TheoremProver* TP,
                                           ExpSubstMap SubstExps,
                                           const vector<SMTExpr>& BaseExprs,
                                           vector<SMTExpr>& Assumptions) const
    {
        auto MyID = GetOp()->GetPosition();
        return GenExpressionBase::ToSMT(SubstExps[MyID], TP, ParameterMap, BaseExprs, Assumptions);
    }
    
    bool UserSynthFuncExpression::Equals(const UserExpressionBase& Other) const
    {
        auto OtherPtr = Other.As<UserSynthFuncExpression>();
        if (OtherPtr == nullptr) {
            return false;
        }
        
        if (OtherPtr->GetOp()->GetID() != Op->GetID()) {
            return false;
        }

        const uint32 NumChildren = Children.size();
        for (uint32 i = 0; i < NumChildren; ++i) {
            if (OtherPtr->Children[i] != Children[i]) {
                return false;
            }
        }
        return true;
    }

    void UserSynthFuncExpression::Accept(ExpressionVisitorBase* Visitor) const
    {
        Visitor->VisitUserSynthFuncExpression(this);
    }

    const SynthFuncOperator* UserSynthFuncExpression::GetOp() const
    {
        return static_cast<const SynthFuncOperator*>(Op);
    }

    string UserSynthFuncExpression::ToString() const
    {
        ostringstream sstr;
        const uint32 NumChildren = Children.size();
        
        sstr << "(" << Op->GetName();
        
        for (uint32 i = 0; i < NumChildren; ++i) {
            sstr << " " << Children[i]->ToString();
        }
        sstr << ")";
        return sstr.str();
    }

    const vector<Expression>& UserSynthFuncExpression::GetChildren() const
    {
        return Children;
    }

    uint32* UserSynthFuncExpression::GetParamMap() const
    {
        return ParameterMap;
    }

    UserLetExpression::UserLetExpression(const map<Expression, Expression>& LetBoundVars,
                                         const Expression& BoundInExpression)
        : UserExpressionBase(NULL), LetBoundVars(LetBoundVars), 
          BoundInExpression(BoundInExpression)
    {
        // Nothing here
    }

    UserLetExpression::~UserLetExpression()
    {
        // Nothing here
    }

    void UserLetExpression::ComputeHashValue() const
    {
        HashValue = (uint64)0;
        for (auto const& VarExpPair : LetBoundVars) {
            boost::hash_combine(HashValue, VarExpPair.first->Hash());
            boost::hash_combine(HashValue, VarExpPair.second->Hash());
        }

        boost::hash_combine(HashValue, BoundInExpression->Hash());
    }

    bool UserLetExpression::Equals(const UserExpressionBase& Other) const
    {
        auto OtherPtr = Other.As<UserLetExpression>();
        if (OtherPtr == nullptr) {
            return false;
        }
        for (auto const& Binding : LetBoundVars) {
            auto OtherIt = OtherPtr->LetBoundVars.find(Binding.first);
            if (OtherIt == OtherPtr->LetBoundVars.end() || !(OtherIt->second->Equals(*(Binding.second)))) {
                return false;
            }
        }

        return BoundInExpression->Equals(*(OtherPtr->BoundInExpression));
    }

    void UserLetExpression::Evaluate(ExpSubstMap SubstExps,
                                     VariableMap VarMap,
                                     ConcreteValueBase* Result) const
    {
        throw InternalError((string)"Internal Error: UserLetExpression::Evaluate() must never have been called.\n" +
                            "At: " + __FILE__ + ":" + to_string(__LINE__));
    }

    SMTExpr UserLetExpression::ToSMT(TheoremProver* TP, 
                                     ExpSubstMap SubstExps,
                                     const vector<SMTExpr>& BaseExprs,
                                     vector<SMTExpr>& Assumptions) const
    {
        throw InternalError((string)"Internal Error: UserLetExpression::ToSMT() must never have been called.\n" +
                            "At: " + __FILE__ + ":" + to_string(__LINE__));
    }

    string UserLetExpression::ToString() const
    {
        ostringstream sstr;
        sstr << "(let (";
        for (auto const& VarExpPair : LetBoundVars) {
            auto BoundVar = VarExpPair.first;
            auto Binding = VarExpPair.second;
            auto BoundVarType = BoundVar->GetOp()->GetEvalType();
            sstr << "(" << BoundVar->ToString() << " "
                 << BoundVarType->ToString() << " " 
                 << Binding->ToString() << ")";
        }
        sstr << ")";
        sstr << BoundInExpression->ToString() << ")";
        return sstr.str();
    }

    void UserLetExpression::Accept(ExpressionVisitorBase* Visitor) const
    {
        Visitor->VisitUserLetExpression(this);
    }

    const ESFixedTypeBase* UserLetExpression::GetType() const
    {
        return BoundInExpression->GetType();
    }

    const Expression& UserLetExpression::GetBoundInExpression() const
    {
        return BoundInExpression;
    }

    const map<Expression, Expression>& UserLetExpression::GetLetBoundVars() const
    {
        return LetBoundVars;
    }

    ostream& operator << (ostream& out, const Expression& Exp)
    {
        out << Exp->ToString();
        return out;
    }

    ostream& operator << (ostream& out, const UserExpressionBase& Exp)
    {
        out << Exp.ToString();
        return out;
    }

} /* end namespace */


// 
// UserExpression.cpp ends here
