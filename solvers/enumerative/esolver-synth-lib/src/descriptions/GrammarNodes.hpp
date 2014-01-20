// GrammarNodes.hpp --- 
// 
// Filename: GrammarNodes.hpp
// Author: Abhishek Udupa
// Created: Wed Jan  8 19:10:12 2014 (-0500)
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


#if !defined __ESOLVER_GRAMMAR_NODES_HPP
#define __ESOLVER_GRAMMAR_NODES_HPP

#include "../common/ESolverForwardDecls.hpp"

namespace ESolver {

    // This file declares the classes used in grammars
    
    // The base class for all grammar nodes
    class GrammarNode
    {
    protected:
        // The grammar that this node belongs to
        const Grammar* TheGrammar;
        const ESFixedTypeBase* Type;
        mutable uint64 HashValue;
        mutable bool HashValid;
        

        virtual void ComputeHashValue() const = 0;

    public:
        GrammarNode(const Grammar* TheGrammar, 
                    const ESFixedTypeBase* Type);
        virtual ~GrammarNode();
        
        uint64 Hash() const;
        const ESFixedTypeBase* GetType() const;
        const Grammar* GetGrammar() const;

        virtual string ToString() const = 0;
        virtual bool operator == (const GrammarNode& Other) const = 0;

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
    };

    class GrammarNonTerminal : public GrammarNode
    {
    private:
        string Name;

    protected:
        virtual void ComputeHashValue() const override;

    public:
        GrammarNonTerminal(const Grammar* TheGrammar,
                           const string& Name, 
                           const ESFixedTypeBase* Type);

        virtual ~GrammarNonTerminal();
        
        const string& GetName() const;
        virtual string ToString() const override;
        virtual bool operator == (const GrammarNode& Other) const override;
    };

    class GrammarVarBase : public GrammarNode
    {
    protected:
        const VarOperatorBase* Op;

        virtual void ComputeHashValue() const override;

    public:
        GrammarVarBase(const Grammar* TheGrammar,
                       const VarOperatorBase* Op);
        virtual ~GrammarVarBase();

        const VarOperatorBase* GetOp() const;
    };

    class GrammarFPVar : public GrammarVarBase
    {
    public:
        GrammarFPVar(const Grammar* TheGrammar,
                     const FormalParamOperator* Op);
        virtual ~GrammarFPVar();

        const FormalParamOperator* GetOp() const;

        virtual string ToString() const override;
        virtual bool operator == (const GrammarNode& Other) const override;
    };

    class GrammarLetVar : public GrammarVarBase
    {
    public:
        GrammarLetVar(const Grammar* TheGrammar,
                      const LetBoundVarOperator* Op);
        virtual ~GrammarLetVar();

        const LetBoundVarOperator* GetOp() const;
        
        virtual string ToString() const override;
        virtual bool operator == (const GrammarNode& Other) const override;
    };

    class GrammarConst : public GrammarNode
    {
    private:
        const ConstOperator* Op;

    protected:
        virtual void ComputeHashValue() const override;

    public:
        GrammarConst(const Grammar* TheGrammar,
                     const ConstOperator* Op);
        virtual ~GrammarConst();

        const ConstOperator* GetOp() const;
        
        virtual string ToString() const override;
        virtual bool operator == (const GrammarNode& Other) const override;
    };

    class GrammarFunc : public GrammarNode
    {
    private:
        const FuncOperatorBase* Op;
        vector<GrammarNode*> Children;

    protected:
        virtual void ComputeHashValue() const override;

    public:
        GrammarFunc(const Grammar* TheGrammar,
                    const FuncOperatorBase* FuncOp,
                    const vector<GrammarNode*>& Children);
        virtual ~GrammarFunc();

        virtual string ToString() const override;
        virtual bool operator == (const GrammarNode& Other) const override;

        const FuncOperatorBase* GetOp() const;
        const vector<GrammarNode*>& GetChildren() const;
    };

    class GrammarLet : public GrammarNode
    {
    private:
        map<GrammarLetVar*, GrammarNode*> Bindings;
        GrammarNode* BoundExpression;

    protected:
        virtual void ComputeHashValue() const override;

    public:
        GrammarLet(const Grammar* TheGrammar,
                   const map<GrammarLetVar*, GrammarNode*>& Bindings,
                   GrammarNode* BoundExpression);
        virtual ~GrammarLet();

        virtual string ToString() const override;
        virtual bool operator == (const GrammarNode& Other) const override;

        const map<GrammarLetVar*, GrammarNode*>& GetBindings() const;
        GrammarNode* GetBoundExpression() const;
    };

    extern ostream& operator << (ostream& Out, const GrammarNode& GNode);

} /* End namespace */

#endif /* __ESOLVER_GRAMMAR_NODES_HPP */

// 
// GrammarNodes.hpp ends here
