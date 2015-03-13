// CEGSolver.cpp ---
//
// Filename: CEGSolver.cpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:54:32 2014 (-0500)
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


#include "CEGSolver.hpp"
#include "../solverutils/ConcreteEvaluator.hpp"
#include "../exceptions/ESException.hpp"
#include "../enumerators/CFGEnumerator.hpp"
#include "../descriptions/ESType.hpp"
#include "../descriptions/Operators.hpp"
#include "../z3interface/TheoremProver.hpp"
#include "../descriptions/Grammar.hpp"
#include "../descriptions/GrammarNodes.hpp"
#include "../utils/TimeValue.hpp"
#include "../solverutils/EvalRule.hpp"
#include "../visitors/ExpCheckers.hpp"
#include "../visitors/SpecRewriter.hpp"
#include "../visitors/Gatherers.hpp"


namespace ESolver {

    CEGSolver::CEGSolver(const ESolverOpts* Opts)
        : ESolver(Opts), ConcEval(nullptr), ExpEnumerator(nullptr)
    {
        // Nothing here
    }

    CEGSolver::~CEGSolver()
    {
        if (ConcEval != nullptr) {
            delete ConcEval;
        }
        if (ExpEnumerator != nullptr) {
            delete ExpEnumerator;
        }
    }

    inline bool CEGSolver::CheckSymbolicValidity(GenExpressionBase const* const* Exps)
    {
        vector<SMTExpr> Assumptions;
        auto FinConstraint = RewrittenConstraint->ToSMT(TP, Exps, BaseExprs, Assumptions);
        auto Antecedent = TP->CreateAndExpr(Assumptions);
        FinConstraint = TP->CreateImpliesExpr(Antecedent, FinConstraint);

        if (Opts.StatsLevel >= 3) {
            TheLogger.Log2("Validity Query:").Log2("\n");
            TheLogger.Log2(FinConstraint.ToString()).Log2("\n");
        }
        auto TPRes = TP->CheckValidity(FinConstraint);

        switch (TPRes) {
        case SOLVE_VALID:
            return true;
        case SOLVE_INVALID:
        {
            if (Opts.StatsLevel >= 4) {
                TheLogger.Log4("Validity failed\nModel:\n");
                SMTModel Model;
                TP->GetConcreteModel(RelevantVars, Model, this);
                for (auto ValuePair : Model) {
                    TheLogger.Log4(ValuePair.first).Log4(" : ").Log4(ValuePair.second.ToString()).Log4("\n");
                }
            }
            return false;
        }
        default:
            throw Z3Exception((string)"Error: Z3 returned an UNKNOWN result.\n" +
                              "Make sure all theories are decidable.");
        }
    }

    inline bool CEGSolver::CheckSymbolicValidity(const GenExpressionBase* Exp)
    {
        GenExpressionBase const* Arr[1];
        Arr[0] = Exp;
        return CheckSymbolicValidity(Arr);
    }

    CallbackStatus CEGSolver::SubExpressionCallBack(const GenExpressionBase *Exp,
                                                    const ESFixedTypeBase *Type,
                                                    uint32 ExpansionTypeID)
    {
        // Check if the subexpression is distinguishable
        uint32 StatusRet = 0;

        if (Opts.StatsLevel >= 4) {
            TheLogger.Log4("Checking Subexpression ").Log4(Exp->ToString()).Log4("... ");
        }

        CheckResourceLimits();

        auto Distinguishable = ConcEval->CheckSubExpression(const_cast<GenExpressionBase*>(Exp),
                                                            Type, ExpansionTypeID, StatusRet);
        if (Distinguishable) {
            ++NumDistExpressions;
            if (Opts.StatsLevel >= 4) {
                if (StatusRet & CONCRETE_EVAL_PART) {
                    TheLogger.Log4("Dist (Partial).").Log4("\n");
                } else {
                    TheLogger.Log4("Dist.").Log4("\n");
                }
            }
            return NONE_STATUS;
        } else {
            if (Opts.StatsLevel >= 4) {
                TheLogger.Log4("Indist.").Log4("\n");
            }
            return DELETE_EXPRESSION;
        }
    }

    // Callbacks
    CallbackStatus CEGSolver::ExpressionCallBack(const GenExpressionBase* Exp,
                                                 const ESFixedTypeBase* Type,
                                                 uint32 ExpansionTypeID,
                                                 uint32 EnumeratorIndex)
    {
        uint32 StatusRet = 0;

        NumExpressionsTried++;
        if (Opts.StatsLevel >= 4) {
            TheLogger.Log4(Exp->ToString()).Log4("... ");
        }

        CheckResourceLimits();

        auto ConcValid = ConcEval->CheckConcreteValidity(Exp, Type, ExpansionTypeID, StatusRet);
        if (!ConcValid && (StatusRet & CONCRETE_EVAL_DIST) == 0) {
            if (Opts.StatsLevel >= 4) {
                TheLogger.Log4("Invalid, Indist.").Log4("\n");
            }
            return DELETE_EXPRESSION;
        } else if (!ConcValid) {
            NumDistExpressions++;
            if (Opts.StatsLevel >= 4) {
                if ((StatusRet & CONCRETE_EVAL_PART) != 0) {
                    TheLogger.Log4("Invalid, Dist (Partial).").Log4("\n");
                } else {
                    TheLogger.Log4("Invalid, Dist.").Log4("\n");
                }
            }
            return NONE_STATUS;
        }

        NumDistExpressions++;
        if (Opts.StatsLevel >= 4) {
            TheLogger.Log4("Valid.").Log4("\n");
        }

        // ConcValid, check for symbolic validity
        bool SymbValid = CheckSymbolicValidity(Exp);
        if (SymbValid) {
            // We're done
            this->Complete = true;
            Solutions.push_back(vector<pair<const SynthFuncOperator*, Expression>>());
            Solutions.back().push_back(pair<const SynthFuncOperator*,
                                       Expression>(SynthFuncs[0],
                                                   GenExpressionBase::ToUserExpression(Exp, this)));
            return STOP_ENUMERATION;
        } else {
            // Get the counter example and add it as a point
            SMTModel TheSMTModel;
            SMTConcreteValueModel ConcSMTModel;
            TP->GetConcreteModel(RelevantVars, TheSMTModel, ConcSMTModel, this);
            ConcEval->AddPoint(ConcSMTModel);
            if (!Opts.NoDist) {
                Restart = true;
                return STOP_ENUMERATION;
            } else {
                return NONE_STATUS;
            }
        }
    }

    // For multifunction synthesis
    CallbackStatus CEGSolver::ExpressionCallBack(GenExpressionBase const* const* Exps,
                                                 ESFixedTypeBase const* const* Types,
                                                 uint32 const* ExpansionTypeIDs)
    {
        NumExpressionsTried++;
        NumDistExpressions++;
        CheckResourceLimits();

        if (Opts.StatsLevel >= 4) {
            TheLogger.Log4("Trying Expressions:\n");
            for (uint32 i = 0; i < SynthFuncs.size(); ++i) {
                TheLogger.Log4(i).Log4((string)". " + Exps[i]->ToString()).Log4("\n");
            }
            TheLogger.Log4("\n");
        }

        auto ConcValid = ConcEval->CheckConcreteValidity(Exps, Types, ExpansionTypeIDs);
        if (!ConcValid) {
            return NONE_STATUS;
        }
        bool SymbValid = CheckSymbolicValidity(Exps);
        if (SymbValid) {
            this->Complete = true;
            Solutions.push_back(vector<pair<const SynthFuncOperator*, Expression>>());
            for (uint32 i = 0; i < SynthFuncs.size(); ++i) {
                Solutions.back().push_back(pair<const SynthFuncOperator*,
                                           Expression>(SynthFuncs[i],
                                                       GenExpressionBase::ToUserExpression(Exps[i], this)));
            }
            return STOP_ENUMERATION;
        } else {
            SMTModel TheSMTModel;
            SMTConcreteValueModel ConcSMTModel;
            TP->GetConcreteModel(RelevantVars, TheSMTModel, ConcSMTModel, this);
            ConcEval->AddPoint(ConcSMTModel);
            return NONE_STATUS;
        }
    }

    SolutionMap CEGSolver::Solve(const Expression& Constraint)
    {
        NumExpressionsTried = NumDistExpressions = (uint64)0;
        Solutions.clear();
        // Announce that we're at the beginning of a solve
        Complete = false;
        // Gather all the synth funcs
        auto&& SFSet = SynthFuncGatherer::Do(Constraint);
        SynthFuncs = vector<const SynthFuncOperator*>(SFSet.begin(), SFSet.end());
        // Check the spec
        LetBindingChecker::Do(Constraint);
        // Rewrite the spec
        RewrittenConstraint = SpecRewriter::Do(this, Constraint, BaseAuxVars, DerivedAuxVars,
                                               SynthFunAppMaps);

        if (Opts.StatsLevel >= 2) {
            TheLogger.Log2("Rewritten Constraint:").Log2("\n");
            TheLogger.Log2(RewrittenConstraint).Log2("\n");
        }

        OrigConstraint = Constraint;

        // Set up SMT expressions for  aux vars
        BaseExprs = vector<SMTExpr>(BaseAuxVars.size() + DerivedAuxVars.size());
        for (auto const& Op : BaseAuxVars) {
            BaseExprs[Op->GetPosition()] =
                TP->CreateVarExpr(Op->GetName(), Op->GetEvalType()->GetSMTType());
        }

        for (auto const& Op : DerivedAuxVars) {
            BaseExprs[Op->GetPosition()] =
                TP->CreateVarExpr(Op->GetName(), Op->GetEvalType()->GetSMTType());
        }


        // Set up the relevant variables as the aux vars
        // which are essentially universally quantified
        // as well as any aux vars which are used as an
        // argument to a synth function
        for (auto const& Op : BaseAuxVars) {
            RelevantVars.insert(Op->GetName());
        }

        // Assign IDs and delayed bindings to SynthFuncs
        // also gather the grammars
        const uint32 NumSynthFuncs = SynthFuncs.size();
        vector<const ESFixedTypeBase*> SynthFuncTypes(NumSynthFuncs);
        vector<Grammar*> SynthGrammars(NumSynthFuncs);
        for (uint32 i = 0; i < NumSynthFuncs; ++i) {
            auto CurGrammar = SynthFuncs[i]->GetSynthGrammar();
            SynthGrammars[i] = const_cast<Grammar*>(CurGrammar);
            SynthFuncs[i]->SetPosition(i);
            SynthFuncs[i]->SetNumLetVars(CurGrammar->GetNumLetBoundVars());
            SynthFuncs[i]->SetNumParams(CurGrammar->GetFormalParamVars().size());
            SynthFuncTypes[i] = SynthFuncs[i]->GetEvalType();
        }

        // Create the concrete evaluator
        ConcEval = new ConcreteEvaluator(this, RewrittenConstraint, SynthFuncs.size(),
                                         BaseAuxVars, DerivedAuxVars, SynthFunAppMaps,
                                         SynthFuncTypes, TheLogger);
        // Create the enumerator
        if (NumSynthFuncs == 1) {
            ExpEnumerator = new CFGEnumeratorSingle(this, SynthGrammars[0]);
        } else {
            ExpEnumerator = new CFGEnumeratorMulti(this, SynthGrammars);
        }

        // Set up evaluation buffers/stacks for generated expressions
        GenExpressionBase::Initialize();

        uint32 NumRestarts = 0;
        PreSolve();
        do {
            Restart = false;
            for (uint32 i = NumSynthFuncs; i <= Opts.CostBudget && !Complete; ++i) {
                if (Opts.StatsLevel >= 1) {
                    TheLogger.Log1("Trying expressions of size ").Log1(i).Log1("\n");
                }
                ExpEnumerator->EnumerateOfCost(i);
                if (Restart) {
                    ExpEnumerator->Reset();
                    break;
                }
            }
            if (Restart && Opts.StatsLevel >= 1) {
                TheLogger.Log1("Restarting enumeration... (").Log1(++NumRestarts).Log1(")\n");
            }
        } while (Restart && !Complete);
        // We're done
        PostSolve();

        if (Opts.StatsLevel >= 1) {
            TheLogger.Log1("Tried ").Log1(NumExpressionsTried).Log1(" expressions in all.\n");
            TheLogger.Log1(NumDistExpressions).Log1(" were distinguishable.\n");
            TheLogger.Log1("Needed ").Log1(NumRestarts).Log1(" Restarts.\n");
            double Time, Memory;
            ResourceLimitManager::GetUsage(Time, Memory);
            TheLogger.Log1("Total Time : ").Log1(Time).Log1(" seconds.\n");
            TheLogger.Log1("Peak Memory: ").Log1(Memory).Log1(" MB.\n");
        }

        GenExpressionBase::Finalize();
        delete ConcEval;
        ConcEval = nullptr;
        delete ExpEnumerator;
        ExpEnumerator = nullptr;
        return Solutions;
    }

    void CEGSolver::EndSolve()
    {
        GenExpressionBase::Finalize();
        delete ConcEval;
        ConcEval = nullptr;
        delete ExpEnumerator;
        ExpEnumerator = nullptr;
    }

} /* End namespace */


//
// CEGSolver.cpp ends here
