// Grammar.hpp --- 
// 
// Filename: Grammar.hpp
// Author: Abhishek Udupa
// Created: Thu Jan  9 18:05:07 2014 (-0500)
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

#if !defined __ESOLVER_GRAMMAR_HPP
#define __ESOLVER_GRAMMAR_HPP

#include "../common/ESolverForwardDecls.hpp"
#include "../utils/Hashers.hpp"
#include "../utils/SetUtils.hpp"

namespace ESolver {

    extern ostream& operator << (ostream& Out, const Grammar& TheGrammar);

    // For canonicalization
    template<typename T>
    class ExtGrammarNode
    {
    private:
        T* Node;
        set<string> DefinedLetVars;
        mutable uint64 HashValue;
        mutable bool HashValid;
        
    public:
        ExtGrammarNode(T* Node, const set<string>& DefinedLetVars) : 
            Node(Node), DefinedLetVars(DefinedLetVars), HashValue((uint64)0),
            HashValid(false)
        {
            // Nothing here
        }

        ExtGrammarNode(const ExtGrammarNode<T>& Other)
            : Node(Other.Node), DefinedLetVars(Other.DefinedLetVars),
              HashValue(Other.HashValue), HashValid(Other.HashValid)
        {
            // Nothing here
        }

        ~ExtGrammarNode()
        {
            // Nothing here
        }

        ExtGrammarNode<T>& operator = (const ExtGrammarNode<T>& Other)
        {
            if (&Other == this) {
                return *this;
            }
            
            Node = Other.Node;
            DefinedLetVars = Other.DefinedLetVars;
            HashValue = Other.HashValue;
            HashValid = Other.HashValid;
            return *this;
        }

        uint64 Hash()
        {
            if (!HashValid) {
                HashValue = (uint64)0;
                boost::hash_combine(HashValue, Node->Hash());
                for (auto const& DefLetVar : DefinedLetVars) {
                    boost::hash_combine(HashValue, DefLetVar);
                }
                HashValid = true;
            }
            return HashValue;
        }

        bool operator == (const ExtGrammarNode<T>& Other) const
        {
            SetCompare<string> Cmp;
            return (Node == Other.Node &&
                    !Cmp(DefinedLetVars, Other.DefinedLetVars) &&
                    !Cmp(Other.DefinedLetVars, DefinedLetVars));
        }

        bool operator < (const ExtGrammarNode<T>& Other) const
        {
            SetCompare<string> Cmp;
            if (Node < Other.Node) {
                return true;
            } else if (Node > Other.Node) {
                return false;
            } else {
                return Cmp(DefinedLetVars, Other.DefinedLetVars);
            }
        }

        T* GetNode() const
        {
            return Node;
        }

        const set<string>& GetDefLetVars() const
        {
            return DefinedLetVars;
        }
    };

    template<typename T>
    class ExtGrammarNodeHasher
    {
    public:
        uint64 operator () (const ExtGrammarNode<T>& Node) { return Node.Hash(); }
    };

    class Grammar
    {
    private:
        typedef unordered_set<GrammarNode*, GrammarNodePtrHasher, GrammarNodePtrEquals> GrammarNodeSet;

        typedef ExtGrammarNode<GrammarNode> GenExtNode;
        typedef ExtGrammarNode<GrammarNonTerminal> NTExtNode;
        typedef ExtGrammarNode<GrammarLetVar> LetVarExtNode;
        typedef ExtGrammarNode<GrammarFunc> FuncExtNode;
        typedef ExtGrammarNode<GrammarLet> LetExtNode;

        typedef map<NTExtNode, vector<GenExtNode>> CEMapType;

        ESolver* Solver;
        string Name;
        map<GrammarNonTerminal*, vector<GrammarNode*>> ExpansionMap;
        map<string, GrammarLetVar*> LetBoundVars;
        map<string, GrammarFPVar*> FormalParamVars;
        map<string, GrammarNonTerminal*> NonTerminalMap;
        GrammarNodeSet GNSet;
        uint32 LetCounter;
        
        static const string StartNTName;
        static const vector<GrammarNode*> EmptyExpVec;

        template<typename T, typename... ArgTypes>
        T* Get(ArgTypes&&... Args)
        {
            T Node(forward<ArgTypes>(Args)...);
            GrammarNodeSet::iterator it;
            if ((it = GNSet.find(&Node)) == GNSet.end()) {
                it = (GNSet.insert(new T(forward<ArgTypes>(Args)...))).first;
            }
            return static_cast<T*>(*it);
        }

        bool InstantiateDFS(GrammarNode* GNode, const set<string>& CurVars,
                            CEMapType& CanonExpansions);
        bool InstantiateDFSNT(const NTExtNode& Node, CEMapType& CanonExpansions);
        bool InstantiateDFSFunc(const FuncExtNode& Node, CEMapType& CanonExpansions);

        void UnrollCanonExpansions(const CEMapType& CanonExpansions);

        GrammarNode* UnrollNTExpansion(GrammarNonTerminal* Node,
                                       const set<string>& DefVars);
        GrammarNode* UnrollFuncExpansion(GrammarFunc* Node, 
                                         const set<string>& DefVars);
        GrammarNode* UnrollLetExpansion(GrammarLet* Node,
                                        const set<string>& DefVars);
        GrammarNode* UnrollExpansion(const GenExtNode& Node);

    public:
        Grammar(const string& GrammarName, ESolver* Solver);
        ~Grammar();

        GrammarNonTerminal* MakeStartNT(const ESFixedTypeBase* Type);
        GrammarNonTerminal* MakeStartNT() const;
        GrammarNonTerminal* MakeNT(const string& NTName, const ESFixedTypeBase* NTType);
        GrammarNonTerminal* MakeNT(const string& NTName) const;
        GrammarFPVar* MakeFP(const string& FPName, const ESFixedTypeBase* FPType,
                                   uint32 Position);
        GrammarFPVar* MakeFP(const string& FPName) const;
        GrammarLetVar* MakeLetVar(const string& LetVarName, const ESFixedTypeBase* LetVarType);
        GrammarLetVar* MakeLetVar(const string& LetVarName) const;
        GrammarConst* MakeConst(const string& ConstName);
        GrammarConst* MakeConst(const ConstOperator* Op);
        GrammarConst* MakeConstFromLiteral(const string& LiteralString, const ESFixedTypeBase* Type);
        GrammarFunc* MakeFunc(const string& FuncName, const vector<GrammarNode*>& Args);
        GrammarLet* MakeLet(const map<GrammarLetVar*, GrammarNode*>& Bindings,
                            GrammarNode* BoundExpression);

        void AddExpansion(GrammarNonTerminal* NonTerm, GrammarNode* Expansion);
        void AddExpansion(const string& NTName, GrammarNode* Expansion);

        void Canonicalize();

        const string& GetName() const;
        const vector<GrammarNode*>& GetExpansions(const string& NonTermName) const;
        const vector<GrammarNode*>& GetExpansions(const GrammarNonTerminal* NonTerm) const;
        string ToString() const;

        const map<string, GrammarLetVar*>& GetLetBoundVars() const;
        const map<string, GrammarFPVar*>& GetFormalParamVars() const;

        const uint32 GetNumLetBoundVars() const;
    };


} /* end namespace */

#endif /* __ESOLVER_GRAMMAR_HPP */


// 
// Grammar.hpp ends here
