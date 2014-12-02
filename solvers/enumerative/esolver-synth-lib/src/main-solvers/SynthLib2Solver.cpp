// SynthLib2Solver.cpp ---
//
// Filename: SynthLib2Solver.cpp
// Author: Abhishek Udupa
// Created: Fri Jan 10 04:23:59 2014 (-0500)
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

#include "SynthLib2Solver.hpp"
#include "../solvers/ESolver.hpp"
#include "../descriptions/Grammar.hpp"
#include "../common/ESolverOpts.hpp"
#include "../solvers/CEGSolver.hpp"

using namespace SynthLib2Parser;

namespace ESolver {

    static inline void ReThrow(const ESException& Ex, const SourceLocation& Loc)
    {
        throw SynthLib2Exception(Loc.GetLineNum(), Loc.GetColNum(), Ex.what());
    }

    SynthLib2ESolver::SynthLib2ESolver(ESolver* Solver)
        : ASTVisitorBase("SynthLib2ESolver"),
          InFunDef(false),
          InSynthFun(false),
          InSortDef(false),
          InConstraintCmd(false),
          Solver(Solver)
    {
        // Nothing here
    }

    SynthLib2ESolver::~SynthLib2ESolver()
    {
        // Nothing here
    }

    void SynthLib2ESolver::VisitProgram(const Program* Prog)
    {
        ASTVisitorBase::VisitProgram(Prog);
    }

    void SynthLib2ESolver::VisitFunDeclCmd(const FunDeclCmd* Cmd)
    {
        throw UnimplementedException((string)"Uninterpreted functions are not supported yet.");
    }

    void SynthLib2ESolver::VisitSetOptsCmd(const SetOptsCmd* Cmd)
    {
        ASTVisitorBase::VisitSetOptsCmd(Cmd);
    }

    void SynthLib2ESolver::VisitSetLogicCmd(const SetLogicCmd* Cmd)
    {
        ASTVisitorBase::VisitSetLogicCmd(Cmd);
    }

    void SynthLib2ESolver::VisitFunDefCmd(const FunDefCmd* Cmd)
    {
        InFunDef = true;
        // Populate the arg maps
        ArgMap.clear();
        uint32 CurPosition = 0;
        vector<const ESFixedTypeBase*> ArgTypes;
        for (auto const ASPair : Cmd->GetArgs()) {
            if (ArgMap.find(ASPair->GetName()) != ArgMap.end()) {
                throw SynthLib2Exception(ASPair->GetLocation().GetLineNum(),
                                         ASPair->GetLocation().GetColNum(),
                                         (string)"Error, parameter identifer \"" + ASPair->GetName() +
                                         "\" has been reused");
            }
            // Visit the sort
            ASPair->GetSort()->Accept(this);
            auto Type = SortStack.back();
            ArgTypes.push_back(Type);
            SortStack.pop_back();
            ArgMap[ASPair->GetName()] = Solver->CreateFreshFormalParamExpression(ASPair->GetName(),
                                                                                 Type, CurPosition++);
        }
        // Process the return type
        Cmd->GetSort()->Accept(this);
        const ESFixedTypeBase* Type = SortStack.back();
        SortStack.pop_back();
        // now process the term
        Cmd->GetTerm()->Accept(this);
        // Create the function
        auto Exp = ProcessedTermStack.back();
        ProcessedTermStack.pop_back();
        try {
            Solver->CreateFunction(Cmd->GetFunName(), ArgTypes, Type, Exp);
        } catch(const ESException& Ex) {
            ReThrow(Ex, Cmd->GetLocation());
        }
        InFunDef = false;
        ArgMap.clear();
        CurPosition = 0;
    }

    void SynthLib2ESolver::VisitSynthFunCmd(const SynthFunCmd* Cmd)
    {
        InSynthFun = true;
        ArgMap.clear();
        CurArgNum = 0;

        // Create a grammar
        SynthGrammar = new Grammar(Cmd->GetFunName() + "_Grammar", Solver);
        GNonTerms.clear();

        // Create the appropriate non-terminals, let vars and FP vars
        for (auto const& Def : Cmd->GetGrammarRules()) {
            Def->GetSort()->Accept(this);
            auto Type = SortStack.back();
            SortStack.pop_back();
            try {
                SynthGrammar->MakeNT(Def->GetName(), Type);
                GNonTerms.insert(Def->GetName());
            } catch (const ESException& Ex) {
                ReThrow(Ex, Def->GetLocation());
            }
        }

        GArgs.clear();
        GLetVars.clear();
        vector<string> ParamNames;
        vector<const ESFixedTypeBase*> ArgTypes;
        // The formal params now
        for (auto const& ASPair : Cmd->GetArgs()) {
            ASPair->GetSort()->Accept(this);
            auto Type = SortStack.back();
            ArgTypes.push_back(Type);
            GArgs.insert(ASPair->GetName());
            ParamNames.push_back(ASPair->GetName());
            SortStack.pop_back();
            try {
                SynthGrammar->MakeFP(ASPair->GetName(), Type, CurArgNum++);
            } catch (const ESException& Ex) {
                ReThrow(Ex, ASPair->GetLocation());
            }
        }

        // The return type
        Cmd->GetSort()->Accept(this);
        auto RetType = SortStack.back();
        SortStack.pop_back();

        // The let vars now
        auto&& LetVars = GrammarLetVarGatherer::Do(Cmd->GetGrammarRules());

        for (auto const& KV : LetVars) {
            GLetVars.insert(KV.first);
            KV.second->Accept(this);
            auto Type = SortStack.back();
            SortStack.pop_back();
            if (GArgs.find(KV.first) != GArgs.end()) {
                throw SynthLib2Exception(KV.second->GetLocation().GetLineNum(),
                                         KV.second->GetLocation().GetColNum(),
                                         (string)"Error: Let var \"" + KV.first + "\" aliases a " +
                                         " formal parameter. This is disallowed in this implementation");
            }
            try {
                SynthGrammar->MakeLetVar(KV.first, Type);
            } catch (const ESException& Ex) {
                ReThrow(Ex, KV.second->GetLocation());
            }
        }

        // Recurse on the actual definitions
        for (auto const& Def : Cmd->GetGrammarRules()) {
            for (auto const& Exp : Def->GetExpansions()) {
                Exp->Accept(this);
                SynthGrammar->AddExpansion(Def->GetName(), ProcessedGTermStack.back());
                ProcessedGTermStack.pop_back();
            }
        }

        // Canonicalize the grammar
        SynthGrammar->Canonicalize();

        if (Solver->GetOpts().StatsLevel >= 2) {
            auto& TheLogger = Solver->GetLogger();
            TheLogger.Log2("Canonicalized Grammar:\n");
            TheLogger.Log2(SynthGrammar->ToString()).Log2("\n");
        }

        if (SynthGrammar->MakeStartNT()->GetType() != RetType) {
            throw SynthLib2Exception(Cmd->GetLocation().GetLineNum(),
                                     Cmd->GetLocation().GetColNum(),
                                     (string)"Error: Type of synth function does not match " +
                                     "type of terms generated by its grammar");
        }
        // Finally, make the synth fun operator
        Solver->CreateFunction(Cmd->GetFunName(), ArgTypes, ParamNames, RetType, SynthGrammar);

        SynthGrammar = nullptr;
        CurArgNum = 0;
        ArgMap.clear();
        InSynthFun = false;
    }

    void SynthLib2ESolver::VisitSortDefCmd(const SortDefCmd* Cmd)
    {
        InSortDef = true;
        SortName = Cmd->GetName();
        try {
            ASTVisitorBase::VisitSortDefCmd(Cmd);
        } catch (const ESException& Ex) {
            ReThrow(Ex, Cmd->GetLocation());
        }
        // The type should already have been bound
        InSortDef = false;
    }

    void SynthLib2ESolver::VisitVarDeclCmd(const VarDeclCmd* Cmd)
    {
        ASTVisitorBase::VisitVarDeclCmd(Cmd);
        // Register the variable
        if (SortStack.size() != 1) {
            throw InternalError((string)"Internal Error: Expected to see exactly one sort on stack!");
        }
        try {
            Solver->CreateQuantifiedVariable(Cmd->GetName(), SortStack[0]);
        } catch(const ESException& Ex) {
            ReThrow(Ex, Cmd->GetLocation());
        }
        SortStack.pop_back();
    }

    void SynthLib2ESolver::VisitConstraintCmd(const ConstraintCmd* Cmd)
    {
        InConstraintCmd = true;
        ASTVisitorBase::VisitConstraintCmd(Cmd);
        InConstraintCmd = false;

        if (ProcessedTermStack.size() != 1) {
            throw InternalError((string)"Internal Error: Expected to see exactly one term on stack!");
        }

        // again the expression will be on top of the stack
        if (ConstraintExpression == nullptr) {
            ConstraintExpression = ProcessedTermStack.back();
            ProcessedTermStack.pop_back();
        } else {
            ConstraintExpression = Solver->CreateAndExpression(ConstraintExpression, ProcessedTermStack.back());
            if (ConstraintExpression->GetType() != Solver->CreateBoolType()) {
                throw SynthLib2Exception(Cmd->GetLocation().GetLineNum(),
                                         Cmd->GetLocation().GetColNum(),
                                         (string)"Error, constraint must be a boolean typed term.");
            }
            ProcessedTermStack.pop_back();
        }
    }

    void SynthLib2ESolver::VisitCheckSynthCmd(const CheckSynthCmd* Cmd)
    {
        auto Solutions = Solver->Solve(ConstraintExpression);
        if (Solutions.size() == 0) {
            cout << "No Solutions!" << endl;
        }
        uint32 SolNum = 0;
        for (auto const& Solution : Solutions) {
            cout << "Solution " << SolNum++ << ":" << endl;
            for (auto const& SolPair : Solution) {
                cout << "(define-fun " << SolPair.first->GetName() << " (";
                for (uint32 i = 0; i < SolPair.first->GetFuncType()->GetDomainTypes().size(); ++i) {
                    if (i != 0) {
                        cout << " ";
                    }
                    cout << "(" << SolPair.first->GetParamNames()[i] << " "
                         << SolPair.first->GetFuncType()->GetDomainTypes()[i]->ToString() << ")";
                }
                cout << ") " << SolPair.first->GetFuncType()->GetRangeType()->ToString() << endl;
                cout << "    " << SolPair.second->ToString() << ")" << endl << endl;
            }
            cout << "-----------------------------------------------" << endl << endl;
        }
    }

    void SynthLib2ESolver::VisitIntSortExpr(const IntSortExpr* Sort)
    {
        auto Type = Solver->CreateIntType();
        if (InSortDef) {
            Solver->BindType(SortName, Type);
        } else {
            SortStack.push_back(Type);
        }
    }

    void SynthLib2ESolver::VisitBVSortExpr(const BVSortExpr* Sort)
    {
        auto Type = Solver->CreateBitVectorType(Sort->GetSize());
        if (InSortDef) {
            Solver->BindType(SortName, Type);
        } else {
            SortStack.push_back(Type);
        }
    }

    void SynthLib2ESolver::VisitBoolSortExpr(const BoolSortExpr* Sort)
    {
        auto Type = Solver->CreateBoolType();
        if (InSortDef) {
            Solver->BindType(SortName, Type);
        } else {
            SortStack.push_back(Type);
        }
    }

    void SynthLib2ESolver::VisitNamedSortExpr(const NamedSortExpr* Sort)
    {
        auto Type = Solver->LookupType(Sort->GetName());
        if (Type == nullptr) {
            throw SynthLib2Exception(Sort->GetLocation().GetLineNum(),
                                     Sort->GetLocation().GetColNum(),
                                     "Could not resolve sort with name \"" + Sort->GetName() + "\"");
        } else {
            if (InSortDef) {
                Solver->BindType(SortName, Type);
            } else {
                SortStack.push_back(Type);
            }
        }
    }

    void SynthLib2ESolver::VisitArraySortExpr(const ArraySortExpr* Sort)
    {
        throw UnimplementedException((string)"Arrays are not yet supported");
    }

    void SynthLib2ESolver::VisitRealSortExpr(const RealSortExpr* Sort)
    {
        throw UnimplementedException((string)"Reals are not yet supported");
    }

    void SynthLib2ESolver::VisitFunSortExpr(const FunSortExpr* Sort)
    {
        throw UnimplementedException((string)"Function sorts are not yet supported");
    }

    void SynthLib2ESolver::VisitEnumSortExpr(const EnumSortExpr* Sort)
    {
        if (!InSortDef) {
            throw SynthLib2Exception(Sort->GetLocation().GetLineNum(),
                                     Sort->GetLocation().GetColNum(),
                                     "Anonymous enumerated sorts are meaningless and are disallowed");
        } else {
            try {
                Solver->CreateEnumType(SortName, Sort->GetConstructors());
            } catch (ESException& Ex) {
                ReThrow(Ex, Sort->GetLocation());
            }
        }
    }

    Expression SynthLib2ESolver::GetVarExpression(const string& VarName)
    {
        for (auto it = LetVarExpressionStack.rbegin(); it != LetVarExpressionStack.rend(); ++it) {
            auto const& CurMap = *it;
            auto MapIt = CurMap.find(VarName);
            if (MapIt != CurMap.end()) {
                return MapIt->second;
            }
        }

        // We now try the ArgMap, IF we are in a fun def or a synth fun cmd
        if (InFunDef || InSynthFun) {
            auto it = ArgMap.find(VarName);
            if (it != ArgMap.end()) {
                return it->second;
            }
        }
        return Expression();
    }

    void SynthLib2ESolver::VisitLetTerm(const LetTerm* TheTerm)
    {
        map<string, Expression> NewLetVarExpressionMap;
        map<Expression, Expression> NewLetVarBindingMap;

        // Process each of the bindings
        auto const& Bindings = TheTerm->GetBindings();
        const uint32 NumBindings = Bindings.size();
        for (uint32 i = 0; i < NumBindings; ++i) {
            Bindings[i]->GetVarSort()->Accept(this);
            auto CurSort = SortStack.back();
            SortStack.pop_back();
            auto const& CurVarName = Bindings[i]->GetVarName();

            // Check that it does not shadow a parameter
            if (ArgMap.find(CurVarName) != ArgMap.end()) {
                throw SynthLib2Exception(Bindings[i]->GetLocation().GetLineNum(),
                                         Bindings[i]->GetLocation().GetColNum(),
                                         (string)"Error: Let bound identifier shadows a parameter.\n" +
                                         "This is not allowed by this implementation.");
            }

            if (NewLetVarExpressionMap.find(CurVarName) != NewLetVarExpressionMap.end()) {
                throw SynthLib2Exception(Bindings[i]->GetLocation().GetLineNum(),
                                         Bindings[i]->GetLocation().GetColNum(),
                                         (string)"Error: identifier \"" + CurVarName + "\" bound multiple " +
                                         "times in let term.");
            }
            auto CurVarExp = Solver->CreateFreshLetBoundVarExpression(CurVarName, CurSort);
            NewLetVarExpressionMap[CurVarName] = CurVarExp;
            // Now process the actual binding
            Bindings[i]->Accept(this);
            NewLetVarBindingMap[CurVarExp] = ProcessedTermStack.back();
            ProcessedTermStack.pop_back();
        }

        // We're done with all the bindings
        LetVarExpressionStack.push_back(NewLetVarExpressionMap);
        LetVarBindingStack.push_back(NewLetVarBindingMap);
        // Now visit the bound expression
        TheTerm->GetBoundInTerm()->Accept(this);
        // Pop the stacks
        LetVarExpressionStack.pop_back();
        LetVarBindingStack.pop_back();
    }

    void SynthLib2ESolver::VisitFunTerm(const FunTerm* TheTerm)
    {
        ASTVisitorBase::VisitFunTerm(TheTerm);

        // The arguments to this term must be on top of the stack now
        const uint32 NumArgs = TheTerm->GetArgs().size();
        vector<Expression> ArgExps(NumArgs);
        for (uint32 i = 0; i < NumArgs; ++i) {
            ArgExps[NumArgs - i - 1] = ProcessedTermStack.back();
            ProcessedTermStack.pop_back();
        }
        try {
            auto FunExp = Solver->CreateExpression(TheTerm->GetFunName(), ArgExps);
            ProcessedTermStack.push_back(FunExp);
        } catch (const ESException& Ex) {
            ReThrow(Ex, TheTerm->GetLocation());
        }
    }

    void SynthLib2ESolver::VisitLiteralTerm(const LiteralTerm* TheTerm)
    {
        auto TheLit = TheTerm->GetLiteral();
        TheLit->GetSort()->Accept(this);
        auto Type = SortStack.back();
        SortStack.pop_back();
        auto Val = Solver->CreateValue(Type, TheLit->GetLiteralString());
        auto Exp = Solver->CreateExpression(Val);
        ProcessedTermStack.push_back(Exp);
    }

    void SynthLib2ESolver::VisitSymbolTerm(const SymbolTerm* TheTerm)
    {
        // We need to resolve this symbol
        // Try the let var binding stack first
        auto Exp = GetVarExpression(TheTerm->GetSymbol());
        if (Exp != nullptr) {
            ProcessedTermStack.push_back(Exp);
            return;
        }
        // We need to resolve this operator with the solver
        try {
            auto Exp2 = Solver->CreateExpression(TheTerm->GetSymbol());
            ProcessedTermStack.push_back(Exp2);
        } catch (const ESException& Ex) {
            ReThrow(Ex, TheTerm->GetLocation());
        }
    }

    void SynthLib2ESolver::VisitFunGTerm(const FunGTerm* TheTerm)
    {
        auto const& Args = TheTerm->GetArgs();
        const uint32 NumArgs = Args.size();
        // recurse on the children
        for (auto const& Arg : TheTerm->GetArgs()) {
            Arg->Accept(this);
        }

        vector<GrammarNode*> GArgs(NumArgs);
        for (uint32 i = NumArgs; i > 0; --i) {
            GArgs[i - 1] = ProcessedGTermStack.back();
            ProcessedGTermStack.pop_back();
        }

        // Make the grammar node
        auto GNode = SynthGrammar->MakeFunc(TheTerm->GetName(), GArgs);
        ProcessedGTermStack.push_back(GNode);
    }

    void SynthLib2ESolver::VisitLiteralGTerm(const LiteralGTerm* TheTerm)
    {
        auto Lit = TheTerm->GetLiteral();
        auto const& LitString = Lit->GetLiteralString();
        auto LitType = Lit->GetSort();
        LitType->Accept(this);
        auto Type = SortStack.back();
        SortStack.pop_back();
        ProcessedGTermStack.push_back(SynthGrammar->MakeConstFromLiteral(LitString, Type));
    }

    void SynthLib2ESolver::VisitSymbolGTerm(const SymbolGTerm* TheTerm)
    {
        auto const& Symbol = TheTerm->GetSymbol();
        // Find out what kind of symbol it is
        if (GNonTerms.find(Symbol) != GNonTerms.end()) {
            ProcessedGTermStack.push_back(SynthGrammar->MakeNT(Symbol));
        } else if (GLetVars.find(Symbol) != GLetVars.end()) {
            ProcessedGTermStack.push_back(SynthGrammar->MakeLetVar(Symbol));
        } else if (GArgs.find(Symbol) != GArgs.end()) {
            ProcessedGTermStack.push_back(SynthGrammar->MakeFP(Symbol));
        } else {
            // Check if this is a defined constant, etc
            auto ConstOp = Solver->LookupOperator(Symbol);
            if (ConstOp->As<ConstOperator>() == nullptr) {
                throw SynthLib2Exception(TheTerm->GetLocation().GetLineNum(),
                                         TheTerm->GetLocation().GetColNum(),
                                         (string)"Symbol \"" + Symbol + "\" could not be resolved to " +
                                         "anything meaningful");
            }
            else {
                ProcessedGTermStack.push_back(SynthGrammar->MakeConst(ConstOp->As<ConstOperator>()));
            }
        }
    }

    void SynthLib2ESolver::VisitLetGTerm(const LetGTerm* TheTerm)
    {
        map<GrammarLetVar*, GrammarNode*> GBindings;
        auto const& Bindings = TheTerm->GetBindings();
        for (auto const& Binding : Bindings) {
            auto const& VarName = Binding->GetVarName();
            Binding->GetVarSort()->Accept(this);
            auto Type = SortStack.back();
            SortStack.pop_back();
            Binding->GetBoundToTerm()->Accept(this);
            auto BoundToGNode = ProcessedGTermStack.back();
            ProcessedGTermStack.pop_back();

            if (BoundToGNode->GetType() != Type) {
                throw SynthLib2Exception(Binding->GetLocation().GetLineNum(),
                                         Binding->GetLocation().GetColNum(),
                                         (string)"Error: Binding has incompatible types");
            }

            GBindings[SynthGrammar->MakeLetVar(VarName)] = BoundToGNode;
        }

        // Process the bound in term
        TheTerm->GetBoundInTerm()->Accept(this);
        auto BoundInGNode = ProcessedGTermStack.back();
        ProcessedGTermStack.pop_back();
        // Make the binding
        ProcessedGTermStack.push_back(SynthGrammar->MakeLet(GBindings, BoundInGNode));

    }

    void SynthLib2ESolver::VisitConstantGTerm(const ConstantGTerm* TheTerm)
    {
        throw UnimplementedException((string)"(Constant <Type>) constructs are not yet supported");
    }

    void SynthLib2ESolver::VisitVariableGTerm(const VariableGTerm* TheTerm)
    {
        throw UnimplementedException((string)"(Variable <Type>) constructs are not yet supported");
    }

    GrammarLetVarGatherer::GrammarLetVarGatherer()
        : ASTVisitorBase("GrammarLetVarGatherer")
    {
        // Nothing here
    }

    GrammarLetVarGatherer::~GrammarLetVarGatherer()
    {
        // Nothing here
    }

    void GrammarLetVarGatherer::VisitLetGTerm(const LetGTerm* TheTerm)
    {
        for (auto const& Binding : TheTerm->GetBindings()) {
            auto it = LetBoundVarMap.find(Binding->GetVarName());
            if (it == LetBoundVarMap.end()) {
                LetBoundVarMap[Binding->GetVarName()] = Binding->GetVarSort();
            } else {
                if (!it->second->Equals(*Binding->GetVarSort())) {
                    throw SynthLib2Exception(Binding->GetLocation().GetLineNum(),
                                             Binding->GetLocation().GetColNum(),
                                             (string)"Error: Let bound variable \"" + Binding->GetVarName() +
                                             "\" bound multiple times with incompatible types");
                }
            }
        }
        ASTVisitorBase::VisitLetGTerm(TheTerm);
    }

    map<string, const SortExpr*> GrammarLetVarGatherer::Do(const vector<NTDef*>& Defs)
    {
        GrammarLetVarGatherer Gatherer;
        for (auto const& Def : Defs) {
            Def->Accept(&Gatherer);
        }
        return Gatherer.LetBoundVarMap;
    }

    void SynthLib2ESolver::Solve(const string& InFileName, const ESolverOpts& Opts)
    {
        ESolver* Solver = new CEGSolver(&Opts);
        SynthLib2ESolver SL2ESolver(Solver);
        SynthLib2Parser::SynthLib2Parser Parser;
        Parser(InFileName);
        Parser.GetProgram()->Accept(&SL2ESolver);
        delete Solver;
        return;
    }

} /* end namespace */

//
// SynthLib2Solver.cpp ends here
