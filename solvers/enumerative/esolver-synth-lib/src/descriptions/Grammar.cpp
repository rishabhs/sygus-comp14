// Grammar.cpp --- 
// 
// Filename: Grammar.cpp
// Author: Abhishek Udupa
// Created: Thu Jan  9 18:16:44 2014 (-0500)
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

#include "Grammar.hpp"
#include "GrammarNodes.hpp"
#include "../solvers/ESolver.hpp"
#include "../utils/SetUtils.hpp"
#include <boost/functional/hash.hpp>

namespace ESolver {

    const string Grammar::StartNTName = (string)"Start";
    const vector<GrammarNode*> Grammar::EmptyExpVec;

    Grammar::Grammar(const string& GrammarName, ESolver* Solver)
        : Solver(Solver), Name(GrammarName), LetCounter(0)
    {
        // Nothing here
    }

    Grammar::~Grammar()
    {
        // delete all the nodes that we've created
        for (auto const& Node : GNSet) {
            delete Node;
        }
    }

    GrammarNonTerminal* Grammar::MakeStartNT(const ESFixedTypeBase* Type)
    {
        return MakeNT(StartNTName, Type);
    }

    GrammarNonTerminal* Grammar::MakeStartNT() const
    {
        return MakeNT(StartNTName);
    }

    GrammarNonTerminal* Grammar::MakeNT(const string& NTName, const ESFixedTypeBase* NTType)
    {
        auto it = NonTerminalMap.find(NTName);
        if (it == NonTerminalMap.end()) {
            auto Retval = Get<GrammarNonTerminal>(this, NTName, NTType);
            NonTerminalMap[NTName] = Retval;
            return Retval;
        } else {
            if (it->second->GetType() != NTType) {
                throw TypeException((string)"Error: Attempted to create a grammar non-terminal \"" + 
                                    StartNTName + "\" with mismatched types.");
            }
            return it->second;
        }
    }

    GrammarNonTerminal* Grammar::MakeNT(const string& NTName) const
    {
        auto it = NonTerminalMap.find(NTName);
        if (it != NonTerminalMap.end()) {
            return it->second;
        } else {
            throw IdentifierException((string)"Non-terminal with name \"" + NTName + "\" has not " + 
                                      "yet been created");
        }
    }

    GrammarFPVar* Grammar::MakeFP(const string& FPName, const ESFixedTypeBase* FPType,
                                  uint32 Position)
    {
        auto it = FormalParamVars.find(FPName);
        if (it == FormalParamVars.end()) {
            auto FPOp = Solver->CreateFormalParamOperator(FPName, FPType, Position);
            auto Retval = new GrammarFPVar(this, FPOp);
            FormalParamVars[FPName] = Retval;
            GNSet.insert(Retval);
            return Retval;
        } else {
            // make sure the types match
            if (it->second->GetType() != FPType) {
                throw TypeException((string)"Error: Attempted to create a a grammar formal param \"" + 
                                    FPName + "\" with mismatched types");
            }
            return it->second;
        }
    }

    GrammarFPVar* Grammar::MakeFP(const string& FPName) const
    {
        auto it = FormalParamVars.find(FPName);
        if (it == FormalParamVars.end()) {
            throw IdentifierException((string)"Formal Parameter with name \"" + FPName + "\" has not " + 
                                      "yet been created");
        } 
        return it->second;
    }

    GrammarLetVar* Grammar::MakeLetVar(const string& LetVarName, 
                                       const ESFixedTypeBase* LetVarType)
    {
        auto it = LetBoundVars.find(LetVarName);
        if (it == LetBoundVars.end()) {
            auto LetOp = Solver->CreateLetBoundVariable(LetVarName, LetVarType);
            LetOp->SetPosition(LetCounter++);
            auto Retval = new GrammarLetVar(this, LetOp);
            LetBoundVars[LetVarName] = Retval;
            GNSet.insert(Retval); 
            return Retval;
        } else {
            // Make sure the types match
            if (it->second->GetType() != LetVarType) {
                throw TypeException((string)"Error: Attempted to create a a grammar let variable \"" + 
                                    LetVarName + "\" with mismatched types");
            }
            return it->second;
        }
    }

    GrammarLetVar* Grammar::MakeLetVar(const string& LetVarName) const
    {
        auto it = LetBoundVars.find(LetVarName);
        if (it != LetBoundVars.end()) {
            return it->second;
        } else {
            throw IdentifierException((string)"Let bound variable with name \"" + LetVarName + "\" has not " + 
                                      "yet been created");
        }
    }

    GrammarConst* Grammar::MakeConst(const string& ConstName)
    {
        auto Op = Solver->LookupOperator(ConstName);
        if (Op == nullptr) {
            throw TypeException((string)"Error: No constant named \"" + ConstName + "\" could be resolved");
        }
        auto ConstOp = Op->As<ConstOperator>();
        if (ConstOp == nullptr) {
            throw TypeException((string)"Error: No constant named \"" + ConstName + "\" could be resolved");
        }
        return Get<GrammarConst>(this, ConstOp);
    }

    GrammarConst* Grammar::MakeConst(const ConstOperator* Op)
    {
        return Get<GrammarConst>(this, Op);
    }

    GrammarConst* Grammar::MakeConstFromLiteral(const string& LiteralString, const ESFixedTypeBase* Type)
    {
        auto Value = Solver->CreateValue(Type, LiteralString);
        auto Op = Solver->CreateConstant(Value);
        return Get<GrammarConst>(this, Op);
    }

    GrammarFunc* Grammar::MakeFunc(const string& FuncName, const vector<GrammarNode*>& Args)
    {
        // extract the types
        const uint32 NumArgs = Args.size();
        vector<const ESFixedTypeBase*> ArgTypes(NumArgs);
        
        for (uint32 i = 0; i < NumArgs; ++i) {
            ArgTypes[i] = Args[i]->GetType();
        }

        auto Op = Solver->LookupOperator(FuncName, ArgTypes);
        if (Op == nullptr) {
            throw TypeException((string)"Could not resolve operator \"" + FuncName + 
                                "\" to anything meaningful.\n" + "This could be due to " + 
                                "mismatched parameters");
        }
        return Get<GrammarFunc>(this, Op, Args);
    }

    GrammarLet* Grammar::MakeLet(const map<GrammarLetVar*, GrammarNode*>& Bindings,
                                 GrammarNode* BoundExpression)
    {
        return Get<GrammarLet>(this, Bindings, BoundExpression);
    }

    void Grammar::AddExpansion(GrammarNonTerminal* NonTerm, GrammarNode* Expansion)
    {
        auto it = ExpansionMap.find(NonTerm);
        if (it == ExpansionMap.end()) {
            ExpansionMap[NonTerm] = vector<GrammarNode*>(1, Expansion);
        } else {
            // Check that the expansion isn't already there
            for (auto const& Exp : it->second) {
                if (Exp == Expansion) {
                    return;
                }
            }
            it->second.push_back(Expansion);
        }
    }

    void Grammar::AddExpansion(const string& NTName, GrammarNode* Expansion)
    {
        auto it = NonTerminalMap.find(NTName);
        if (it == NonTerminalMap.end()) {
            throw IdentifierException((string)"Could not find non-terminal with name \"" + NTName + 
                                      "\" to add expansion");
        }
        AddExpansion(it->second, Expansion);
    }

    const string& Grammar::GetName() const
    {
        return Name;
    }

    const vector<GrammarNode*>& Grammar::GetExpansions(const string& NonTermName) const
    {
        auto it = NonTerminalMap.find(NonTermName);
        if (it == NonTerminalMap.end()) {
            throw IdentifierException((string)"Could not find non-terminal with name \"" + NonTermName + 
                                      "\" to get expansions");
        }
        return GetExpansions(it->second);
    }

    const vector<GrammarNode*>& Grammar::GetExpansions(const GrammarNonTerminal* NonTerm) const
    {
        auto ExpIt = ExpansionMap.find(const_cast<GrammarNonTerminal*>(NonTerm));
        if (ExpIt == ExpansionMap.end()) {
            return EmptyExpVec;
        } else {
            return ExpIt->second;
        }
    }

    

    bool Grammar::InstantiateDFSNT(const NTExtNode& Node, CEMapType& CanonExpansions)
    {
        // Mark ourselves as having been visited
        CanonExpansions[Node] = vector<GenExtNode>();

        // Recurse on each expansion if necessary
        auto it = ExpansionMap.find(Node.GetNode());
        if (it == ExpansionMap.end()) {
            return false;
        }
        bool FoundOne = false;
        for (auto const& Exp : it->second) {
            if (InstantiateDFS(Exp, Node.GetDefLetVars(), CanonExpansions)) {
                CanonExpansions[Node].push_back(GenExtNode(Exp, Node.GetDefLetVars()));
                FoundOne = true;
            }
        }
        if (FoundOne) {
            return true;
        } else {
            return false;
        }
    }

    bool Grammar::InstantiateDFSFunc(const FuncExtNode& Node, CEMapType& CanonExpansions)
    {
        auto FuncNode = Node.GetNode();
        for (auto const& Child : FuncNode->GetChildren()) {
            if (!InstantiateDFS(const_cast<GrammarNode*>(Child), Node.GetDefLetVars(), CanonExpansions)) {
                return false;
            }
        }
        return true;
    }

    bool Grammar::InstantiateDFS(GrammarNode* GNode, const set<string>& CurVars,
                                 CEMapType& CanonExpansions)
    {
        auto FuncNode = GNode->As<GrammarFunc>();
        if (FuncNode != nullptr) {
            return InstantiateDFSFunc(FuncExtNode(FuncNode, CurVars), CanonExpansions);
        }
        auto NTNode = GNode->As<GrammarNonTerminal>();
        if (NTNode != nullptr) {
            auto it = CanonExpansions.find(NTExtNode(NTNode, CurVars));
            if (it == CanonExpansions.end()) {
                return InstantiateDFSNT(NTExtNode(NTNode, CurVars), CanonExpansions);
            } else {
                return true;
            }
        }
        auto LetVarNode = GNode->As<GrammarLetVar>();
        if (LetVarNode != nullptr) {
            // Check if we can instantiate
            if (CurVars.find(LetVarNode->GetOp()->GetName()) != CurVars.end()) {
                return true;
            } else {
                return false;
            }
        }
        auto LetNode = GNode->As<GrammarLet>();
        if (LetNode != nullptr) {
            // Check if the bindings can be done successfully
            for (auto const& KV : LetNode->GetBindings()) {
                if (!InstantiateDFS(const_cast<GrammarNode*>(KV.second), CurVars, CanonExpansions)) {
                    return false;
                }
            }
            // Bindings okay.
            // Recurse with new set of vars
            set<string> NewVars = CurVars;
            for (auto const& KV : LetNode->GetBindings()) {
                NewVars.insert(KV.first->GetOp()->GetName());
            }
            return InstantiateDFS(const_cast<GrammarNode*>(LetNode->GetBoundExpression()), 
                                  NewVars, CanonExpansions);
        }

        // return true for everything else
        return true;
    }

    void Grammar::UnrollCanonExpansions(const CEMapType& CanonExpansions)
    {
        // first create non-terminals
        for (auto const& KV : CanonExpansions) {
            auto const& NT = KV.first.GetNode();
            auto&& NTName = NT->GetName() + GetStringForSet(KV.first.GetDefLetVars());
            if (NonTerminalMap.find(NTName) == NonTerminalMap.end()) {
                MakeNT(NTName, NT->GetType());
            }
        }
        // Now that all the non-terminals are created, create a new expansion map
        ExpansionMap.clear();
        for (auto const& KV : CanonExpansions) {
            auto const& NT = KV.first.GetNode();
            auto&& NTName = NT->GetName() + GetStringForSet(KV.first.GetDefLetVars());
            auto NewNT = MakeNT(NTName);
            for (auto const& Exp : KV.second) {
                ExpansionMap[NewNT].push_back(UnrollExpansion(Exp));
            }
        }
    }

    GrammarNode* Grammar::UnrollExpansion(const GenExtNode& Node)
    {
        auto GNode = Node.GetNode();
        auto const& DefVars = Node.GetDefLetVars();

        auto FuncNode = GNode->As<GrammarFunc>();
        if (FuncNode != nullptr) {
            return UnrollFuncExpansion(FuncNode, DefVars);
        }
        auto LetNode = GNode->As<GrammarLet>();
        if (LetNode != nullptr) {
            return UnrollLetExpansion(LetNode, DefVars);
        }
        auto NTNode = GNode->As<GrammarNonTerminal>();
        if (NTNode != nullptr) {
            return UnrollNTExpansion(NTNode, DefVars);
        }

        // Just return the node otherwise
        return GNode;
    }

    GrammarNode* Grammar::UnrollNTExpansion(GrammarNonTerminal* Node,
                                            const set<string>& DefVars)
    {
        auto&& NTName = Node->GetName() + GetStringForSet(DefVars);
        return MakeNT(NTName);
    }

    GrammarNode* Grammar::UnrollFuncExpansion(GrammarFunc* Node,
                                              const set<string>& DefVars)
    {
        auto const& Children = Node->GetChildren();
        const uint32 NumChildren = Children.size();
        vector<GrammarNode*> UnrolledChildren(NumChildren);
        
        for (uint32 i = 0; i < NumChildren; ++i) {
            UnrolledChildren[i] = UnrollExpansion(GenExtNode(Children[i], DefVars));
        }
        return MakeFunc(Node->GetOp()->GetName(), UnrolledChildren);
    }

    GrammarNode* Grammar::UnrollLetExpansion(GrammarLet* Node,
                                             const set<string>& DefVars)
    {
        // Unroll the bindings first
        map<GrammarLetVar*, GrammarNode*> NewBindings;
        auto NewDefVars = DefVars;
        for (auto const& KV : Node->GetBindings()) {
            NewDefVars.insert(KV.first->GetOp()->GetName());
            NewBindings[KV.first] = UnrollExpansion(GenExtNode(KV.second, DefVars));
        }
        // Recurse on the expression with a new set
        auto UnrolledExp = UnrollExpansion(GenExtNode(Node->GetBoundExpression(), NewDefVars));
        return MakeLet(NewBindings, UnrolledExp);
    }

    void Grammar::Canonicalize()
    {
        CEMapType CanonExpansions;
        
        auto it = NonTerminalMap.find(StartNTName);
        if (it == NonTerminalMap.end()) {
            throw GrammarException((string)"Error: Attempted to canonicalize grammar \"" + Name + "\"" +
                                   " without having defined a start non-terminal");
        }

        InstantiateDFS(it->second, set<string>(), CanonExpansions);

        // Now, we need to unroll the canonical nonterminals
        UnrollCanonExpansions(CanonExpansions);
        // DONE! Whew!
    }

    string Grammar::ToString() const
    {
        ostringstream sstr;
        for (auto const& KV : ExpansionMap) {
            auto const& NTName = KV.first->GetName();
            auto Prefix = NTName + " ::= ";
            for (auto const& Exp : KV.second) {
                sstr << Prefix << Exp->ToString() << endl;
            }
            sstr << endl;
        }
        return sstr.str();
    }

    const map<string, GrammarLetVar*>& Grammar::GetLetBoundVars() const
    {
        return LetBoundVars;
    }

    const map<string, GrammarFPVar*>& Grammar::GetFormalParamVars() const
    {
        return FormalParamVars;
    }

    const uint32 Grammar::GetNumLetBoundVars() const
    {
        return LetBoundVars.size();
    }

} /* end namespace */

// 
// Grammar.cpp ends here
