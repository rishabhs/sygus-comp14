// GrammarNodes.cpp --- 
// 
// Filename: GrammarNodes.cpp
// Author: Abhishek Udupa
// Created: Thu Jan  9 14:17:59 2014 (-0500)
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

#include "GrammarNodes.hpp"
#include "Operators.hpp"
#include <boost/functional/hash.hpp>
#include "../exceptions/ESException.hpp"
#include "../descriptions/Operators.hpp"
#include "../values/ConcreteValueBase.hpp"
#include "../descriptions/ESType.hpp"

namespace ESolver {

    GrammarNode::GrammarNode(const Grammar* TheGrammar,
                             const ESFixedTypeBase* Type)
        : TheGrammar(TheGrammar), Type(Type), HashValid(false)
    {
        // Nothing here
    }

    GrammarNode::~GrammarNode()
    {
        // Nothing here
    }

    uint64 GrammarNode::Hash() const
    {
        if (!HashValid) {
            ComputeHashValue();
            HashValid = true;
        }
        return HashValue;
    }

    const ESFixedTypeBase* GrammarNode::GetType() const
    {
        return Type;
    }

    const Grammar* GrammarNode::GetGrammar() const
    {
        return TheGrammar;
    }

    GrammarNonTerminal::GrammarNonTerminal(const Grammar* TheGrammar,
                                           const string& Name,
                                           const ESFixedTypeBase* Type)
        : GrammarNode(TheGrammar, Type), Name(Name)
    {
        // Nothing here
    }

    GrammarNonTerminal::~GrammarNonTerminal()
    {
        // Nothing here
    }

    const string& GrammarNonTerminal::GetName() const
    {
        return Name;
    }

    void GrammarNonTerminal::ComputeHashValue() const
    {
        HashValue = boost::hash_value(Name);
    }

    string GrammarNonTerminal::ToString() const
    {
        return Name;
    }

    bool GrammarNonTerminal::operator == (const GrammarNode& Other) const
    {
        auto OtherPtr = Other.As<GrammarNonTerminal>();
        if (OtherPtr == nullptr) {
            return false;
        }
        return (OtherPtr->TheGrammar == TheGrammar && 
                OtherPtr->Name == Name);
    }

    GrammarVarBase::GrammarVarBase(const Grammar* TheGrammar,
                                   const VarOperatorBase* Op)
        : GrammarNode(TheGrammar, Op->GetEvalType()), Op(Op)
    {
        // Nothing here
    }

    GrammarVarBase::~GrammarVarBase()
    {
        // Nothing here
    }

    void GrammarVarBase::ComputeHashValue() const
    {
        HashValue = (uint64)0;
        boost::hash_combine(HashValue, Op->Hash());
    }

    const VarOperatorBase* GrammarVarBase::GetOp() const
    {
        return static_cast<const VarOperatorBase*>(Op);
    }

    GrammarFPVar::GrammarFPVar(const Grammar* TheGrammar,
                               const FormalParamOperator* Op)
        : GrammarVarBase(TheGrammar, Op)
    {
        // Nothing here
    }

    GrammarFPVar::~GrammarFPVar()
    {
        // Nothing here
    }

    const FormalParamOperator* GrammarFPVar::GetOp() const
    {
        return static_cast<const FormalParamOperator*>(Op);
    }

    string GrammarFPVar::ToString() const
    {
        return Op->GetName();
    }

    bool GrammarFPVar::operator == (const GrammarNode& Other) const
    {
        auto OtherPtr = Other.As<GrammarFPVar>();
        if (OtherPtr == nullptr) {
            return false;
        }
        return (OtherPtr->GetOp()->GetID() == GetOp()->GetID());
    }

    GrammarLetVar::GrammarLetVar(const Grammar* TheGrammar,
                                 const LetBoundVarOperator* Op)
        : GrammarVarBase(TheGrammar, Op)
    {
        // Nothing here
    }

    GrammarLetVar::~GrammarLetVar()
    {
        // Nothing here
    }

    const LetBoundVarOperator* GrammarLetVar::GetOp() const
    {
        return static_cast<const LetBoundVarOperator*>(Op);
    }

    string GrammarLetVar::ToString() const
    {
        return Op->GetName();
    }

    bool GrammarLetVar::operator == (const GrammarNode& Other) const
    {
        auto OtherPtr = Other.As<GrammarLetVar>();
        if (OtherPtr == nullptr) {
            return false;
        }
        return (OtherPtr->GetOp()->GetID() == GetOp()->GetID());
    }

    GrammarConst::GrammarConst(const Grammar* TheGrammar,
                               const ConstOperator* Op)
        : GrammarNode(TheGrammar, Op->GetEvalType()), Op(Op)
    {
        // Nothing here
    }

    GrammarConst::~GrammarConst()
    {
        // Nothing here
    }

    const ConstOperator* GrammarConst::GetOp() const
    {
        return static_cast<const ConstOperator*>(Op);
    }

    void GrammarConst::ComputeHashValue() const
    {
        HashValue = (uint64)0;
        boost::hash_combine(HashValue, Op->Hash());
    }

    string GrammarConst::ToString() const
    {
        if (Op->IsAnon()) {
            return Op->GetConstantValue()->ToString();
        } else {
            return (string)"(" + Op->GetName() + ":" + Op->GetConstantValue()->ToString();
        }
    }

    bool GrammarConst::operator == (const GrammarNode& Other) const
    {
        auto OtherPtr = Other.As<GrammarConst>();
        if (OtherPtr == nullptr) {
            return false;
        }
        return (OtherPtr->GetOp()->GetID() == GetOp()->GetID());
    }

    GrammarFunc::GrammarFunc(const Grammar* TheGrammar, 
                             const FuncOperatorBase* FuncOp,
                             const vector<GrammarNode*>& Children)
        : GrammarNode(TheGrammar, FuncOp->GetEvalType()), Op(FuncOp), Children(Children)
    {
        // Check that all children belong to the same grammar
        for (auto const& Child : Children) {
            if (Child->GetGrammar() != TheGrammar) {
                throw InternalError((string)"Error: Attempted to combine nodes from different grammars.\n" + 
                                    "At " + __FILE__ + ":" + to_string(__LINE__));
            }
        }

        // Check that the types match
        auto FuncType = FuncOp->GetFuncType();
        const uint32 Arity = FuncOp->GetArity();
        if (Children.size() != Arity) {
            throw TypeException((string)"Operator \"" + FuncOp->GetName() + "\" expects " + 
                                to_string(Arity) + " operands, but received " + to_string(Children.size()) + 
                                " operands.");
        }

        for (uint32 i = 0; i < Arity; ++i) {
            if (Children[i]->GetType() != FuncType->GetDomainTypes()[i]) {
                throw TypeException((string)"Type mismatch in arguments to operator \"" + 
                                    FuncOp->GetName() + "\"");
            }
        }
    }

    GrammarFunc::~GrammarFunc()
    {
        // Nothing here
    }

    void GrammarFunc::ComputeHashValue() const
    {
        HashValue = (uint64)0;
        boost::hash_combine(HashValue, Op->Hash());
        for (auto const& Child : Children) {
            boost::hash_combine(HashValue, Child->Hash());
        }
    }

    string GrammarFunc::ToString() const
    {
        ostringstream sstr;
        sstr << "(" << Op->GetName();
        for (auto const& Child : Children) {
            sstr << " " << Child->ToString();
        }
        sstr << ")";
        return sstr.str();
    }

    bool GrammarFunc::operator == (const GrammarNode& Other) const
    {
        auto OtherPtr = Other.As<GrammarFunc>();
        if (OtherPtr == nullptr) {
            return false;
        }

        if (OtherPtr->GetOp()->GetID() != GetOp()->GetID()) {
            return false;
        }
        
        const uint32 NumChildren = Children.size();
        for (uint32 i = 0; i < NumChildren; ++i) {
            if (Children[i] != OtherPtr->Children[i]) {
                return false;
            }
        }
        return true;
    }

    const FuncOperatorBase* GrammarFunc::GetOp() const
    {
        return static_cast<const FuncOperatorBase*>(Op);
    }

    const vector<GrammarNode*>& GrammarFunc::GetChildren() const
    {
        return Children;
    }

    GrammarLet::GrammarLet(const Grammar* TheGrammar,
                           const map<GrammarLetVar*, GrammarNode*>& Bindings,
                           GrammarNode* BoundExpression)
        : GrammarNode(TheGrammar, BoundExpression->GetType()),
          Bindings(Bindings), BoundExpression(BoundExpression)
    {
        // Check that everything belongs to the same grammar
        for (auto const& KV : Bindings) {
            if (KV.first->GetGrammar() != TheGrammar || 
                KV.second->GetGrammar() != TheGrammar) {
                throw InternalError((string)"Error: Attempted to mix nodes from different grammars.\n" + 
                                    "At " + __FILE__ + ":" + to_string(__LINE__));
            }
        }
        if (BoundExpression->GetGrammar() != TheGrammar) {
            throw InternalError((string)"Error: Attempted to mix nodes from different grammars.\n" + 
                                "At " + __FILE__ + ":" + to_string(__LINE__));
        }
    }

    GrammarLet::~GrammarLet()
    {
        // Nothing here
    }

    void GrammarLet::ComputeHashValue() const
    {
        HashValue = (uint64)0;
        for (auto const& KV : Bindings) {
            boost::hash_combine(HashValue, KV.first->Hash());
            boost::hash_combine(HashValue, KV.second->Hash());
        }
        boost::hash_combine(HashValue, BoundExpression->Hash());
    }

    string GrammarLet::ToString() const
    {
        ostringstream sstr;
        sstr << "(let (";
        uint32 CurBinding = 0;
        for (auto const& KV : Bindings) {
            if (CurBinding != 0) {
                sstr << " ";
            }
            sstr << "(" << KV.first->ToString() << " " << KV.first->GetType()->ToString()
                 << " " << KV.second->ToString() << ")";
            CurBinding++;
        }
        sstr << ") " << BoundExpression->ToString() << ")";
        return sstr.str();
    }

    bool GrammarLet::operator == (const GrammarNode& Other) const
    {
        auto OtherPtr = Other.As<GrammarLet>();
        if (OtherPtr == nullptr) {
            return false;
        }
        if (OtherPtr->Bindings.size() != Bindings.size()) {
            return false;
        }

        for (auto const KV : Bindings) {
            auto it = OtherPtr->Bindings.find(KV.first);
            if (it == OtherPtr->Bindings.end()) {
                return false;
            }
            if (it->second != KV.second) {
                return false;
            }
        }
        return (BoundExpression == OtherPtr->BoundExpression);
    }

    const map<GrammarLetVar*, GrammarNode*>& GrammarLet::GetBindings() const
    {
        return Bindings;
    }

    GrammarNode* GrammarLet::GetBoundExpression() const
    {
        return BoundExpression;
    }

    ostream& operator << (ostream& Out, const GrammarNode& GNode) 
    {
        Out << GNode.ToString();
        return Out;
    }

} /* end namespace */

// 
// GrammarNodes.cpp ends here
