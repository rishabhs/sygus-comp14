// SynthLib2Solver.hpp --- 
// 
// Filename: SynthLib2Solver.hpp
// Author: Abhishek Udupa
// Created: Fri Jan 10 04:23:32 2014 (-0500)
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


#if !defined __ESOLVER_SYNTH_LIB2_SOLVER_HPP
#define __ESOLVER_SYNTH_LIB2_SOLVER_HPP 

#include "../common/ESolverForwardDecls.hpp"
#include "../synthlib2parser/src/include/SynthLib2ParserIFace.hpp"
#include "../utils/Hashers.hpp"
#include "../utils/UIDGenerator.hpp"

namespace ESolver {

    // A visitor to gather up the let bound variables of the grammar
    class GrammarLetVarGatherer : public SynthLib2Parser::ASTVisitorBase
    {
    private:
        map<string, const SynthLib2Parser::SortExpr*> LetBoundVarMap;

    public:
        GrammarLetVarGatherer();
        virtual ~GrammarLetVarGatherer();

        virtual void VisitLetGTerm(const SynthLib2Parser::LetGTerm* TheTerm) override;

        static map<string, const SynthLib2Parser::SortExpr*> Do(const vector<SynthLib2Parser::NTDef*>& Defs);
    };

    // A visitor to set up the context for synthlib2 file in ESolver
    class SynthLib2ESolver : public SynthLib2Parser::ASTVisitorBase
    {
    private:
        bool InFunDef;
        bool InSynthFun;
        bool InSortDef;
        bool InConstraintCmd;

        vector<Expression> ProcessedTermStack;
        vector<GrammarNode*> ProcessedGTermStack;
        map<string, Expression> ArgMap;
        set<string> GArgs;
        set<string> GLetVars;
        set<string> GNonTerms;
        vector<const ESFixedTypeBase*> SortStack;
        Grammar* SynthGrammar;
        string SortName;
        uint32 CurArgNum;
        Expression ConstraintExpression;
        ESolver* Solver;
        vector<map<string, Expression>> LetVarExpressionStack;
        vector<map<Expression, Expression>> LetVarBindingStack;

        Expression GetVarExpression(const string& VarName);

    public:
        SynthLib2ESolver(ESolver* Solver);
        virtual ~SynthLib2ESolver();

        // Visit methods
        virtual void VisitProgram(const SynthLib2Parser::Program* Prog) override;

        virtual void VisitFunDefCmd(const SynthLib2Parser::FunDefCmd* Cmd) override;
        virtual void VisitFunDeclCmd(const SynthLib2Parser::FunDeclCmd* Cmd) override;
        virtual void VisitSynthFunCmd(const SynthLib2Parser::SynthFunCmd* Cmd) override;
        virtual void VisitSortDefCmd(const SynthLib2Parser::SortDefCmd* Cmd) override;
        virtual void VisitSetOptsCmd(const SynthLib2Parser::SetOptsCmd* Cmd) override;
        virtual void VisitVarDeclCmd(const SynthLib2Parser::VarDeclCmd* Cmd) override;
        virtual void VisitConstraintCmd(const SynthLib2Parser::ConstraintCmd* Cmd) override;
        virtual void VisitSetLogicCmd(const SynthLib2Parser::SetLogicCmd* Cmd) override;
        virtual void VisitCheckSynthCmd(const SynthLib2Parser::CheckSynthCmd* Cmd) override;

        virtual void VisitIntSortExpr(const SynthLib2Parser::IntSortExpr* Sort) override;
        virtual void VisitBVSortExpr(const SynthLib2Parser::BVSortExpr* Sort) override;
        virtual void VisitNamedSortExpr(const SynthLib2Parser::NamedSortExpr* Sort) override;
        virtual void VisitArraySortExpr(const SynthLib2Parser::ArraySortExpr* Sort) override;
        virtual void VisitRealSortExpr(const SynthLib2Parser::RealSortExpr* Sort) override;
        virtual void VisitFunSortExpr(const SynthLib2Parser::FunSortExpr* Sort) override;
        virtual void VisitBoolSortExpr(const SynthLib2Parser::BoolSortExpr* Sort) override;
        virtual void VisitEnumSortExpr(const SynthLib2Parser::EnumSortExpr* Sort) override;

        virtual void VisitFunTerm(const SynthLib2Parser::FunTerm* TheTerm) override;
        virtual void VisitLiteralTerm(const SynthLib2Parser::LiteralTerm* TheTerm) override;
        virtual void VisitSymbolTerm(const SynthLib2Parser::SymbolTerm* TheTerm) override;
        virtual void VisitLetTerm(const SynthLib2Parser::LetTerm* TheTerm) override;


        virtual void VisitFunGTerm(const SynthLib2Parser::FunGTerm* TheTerm) override;
        virtual void VisitLiteralGTerm(const SynthLib2Parser::LiteralGTerm* TheTerm) override;
        virtual void VisitSymbolGTerm(const SynthLib2Parser::SymbolGTerm* TheTerm) override;
        virtual void VisitLetGTerm(const SynthLib2Parser::LetGTerm* TheTerm) override;
        virtual void VisitConstantGTerm(const SynthLib2Parser::ConstantGTerm* TheTerm) override;
        virtual void VisitVariableGTerm(const SynthLib2Parser::VariableGTerm* TheTerm) override;

        static void Solve(const string& InFileName, const ESolverOpts& Opts);
    };

} /* End namespace */

#endif /* __ESOLVER_SYNTH_LIB2_SOLVER_HPP */


// 
// SynthLib2Solver.hpp ends here
