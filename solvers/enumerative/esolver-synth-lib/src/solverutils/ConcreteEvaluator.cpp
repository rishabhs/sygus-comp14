// ConcreteEvaluator.cpp ---
//
// Filename: ConcreteEvaluator.cpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:54:03 2014 (-0500)
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


#include "ConcreteEvaluator.hpp"
#include "../descriptions/Operators.hpp"
#include "../exceptions/ESException.hpp"
#include "../values/Signature.hpp"
#include "../solvers/ESolver.hpp"
#include "../values/ConcreteValueBase.hpp"
#include "../solverutils/EvalRule.hpp"
#include "../expressions/GenExpression.hpp"

namespace ESolver {

    // Flag indicating that an exception occurred
    bool ConcreteException = false;
    // Flag indicating that an expression is partial
    // and could not be evaluated
    bool PartialExpression = false;

    boost::pool<>* ConcreteEvaluator::SigVecPool = nullptr;

    ConcreteEvaluator::ConcreteEvaluator(ESolver* Solver, const Expression& RewrittenSpec,
                                         uint32 NumSynthFuncs,
                                         const vector<const AuxVarOperator*>& BaseAuxVars,
                                         const vector<const AuxVarOperator*>& DerivedAuxVars,
                                         const vector<map<vector<uint32>, uint32>>& SynthFunAppMaps,
                                         const vector<const ESFixedTypeBase*>& SynthFuncTypes,
                                         Logger& TheLogger)
        : Solver(Solver),
          RewrittenSpec(RewrittenSpec),
          BaseAuxVars(BaseAuxVars), DerivedAuxVars(DerivedAuxVars),
          SynthFunAppMaps(SynthFunAppMaps.size()),
          SynthFuncTypes(SynthFuncTypes),
          NumSynthFunApps(0),
          NumBaseAuxVars(BaseAuxVars.size()), NumDerivedAuxVars(DerivedAuxVars.size()),
          NumTotalAuxVars(BaseAuxVars.size() + DerivedAuxVars.size()),
          NumSynthFuncs(NumSynthFuncs),
          NoDist(Solver->GetOpts().NoDist), TheLogger(TheLogger),
          NumPoints(0), SigPool(nullptr)
    {
        for (uint32 i = 0, last = SynthFunAppMaps.size(); i < last; ++i) {
            this->SynthFunAppMaps[i] =
                vector<pair<vector<uint32>, uint32>>(SynthFunAppMaps[i].begin(),
                                                     SynthFunAppMaps[i].end());
            NumSynthFunApps += SynthFunAppMaps[i].size();
        }
    }

    ConcreteEvaluator::~ConcreteEvaluator()
    {
        if (SigVecPool != nullptr) {
            delete SigVecPool;
        }
        if (SigPool != nullptr) {
            delete SigPool;
        }

        for (uint32 i = 0; i < NumPoints; ++i) {
            for (uint32 j = 0; j < NumSynthFunApps; ++j) {
                delete SubExpEvalPoints[i][j];
            }
        }
    }

    void ConcreteEvaluator::AddPoint(const SMTConcreteValueModel& Model)
    {
        // Add another point
        Points.push_back(vector<const ConcreteValueBase*>((size_t)NumBaseAuxVars, nullptr));
        // Add another row to EvalPoints
        EvalPoints.push_back(vector<const ConcreteValueBase*>((size_t)NumTotalAuxVars, nullptr));
        // Add another row to SubExpEvalPoints
        SubExpEvalPoints.push_back(vector<const ConcreteValueBase*>((size_t)NumSynthFunApps,
                                                                    nullptr));

        // Recreate the pool for the new size
        if (SigVecPool != nullptr) {
            delete SigVecPool;
            SigVecPool = nullptr;
        }

        SigVecPool =
            new boost::pool<>(sizeof(ConcreteValueBase const*) *
                              NumSynthFunApps * (NumPoints + 1));

        // Clear all the accumulated signatures
        SigSet.clear();
        if (SigPool != nullptr) {
            delete SigPool;
        }

        SigPool = new boost::pool<>(sizeof(Signature));

        for(uint32 i = 0; i < NumBaseAuxVars; ++i) {
            auto it = Model.find(BaseAuxVars[i]->GetName());
            if (it == Model.end()) {
                throw InternalError((string)"Internal Error: Could not find model for " +
                                    "variable \"" + BaseAuxVars[i]->GetName() +
                                    "\".\nAt: " + __FILE__ + ":" + to_string(__LINE__));
            }

            EvalPoints[NumPoints][BaseAuxVars[i]->GetPosition()] = it->second;
            Points[NumPoints][BaseAuxVars[i]->GetPosition()] = it->second;
        }

        uint32 k = 0;
        for (uint32 i = 0; i < NumSynthFuncs; ++i) {
            for (uint32 j = 0; j < SynthFunAppMaps[i].size(); ++j) {
                EvalPoints[NumPoints][SynthFunAppMaps[i][j].second] =
                    SubExpEvalPoints[NumPoints][k] = new ConcreteValueBase();
                ++k;
            }
        }

        if (Solver->GetOpts().StatsLevel >= 3) {
            TheLogger.Log3("Adding point: <");
            for(uint32 i = 0; i < NumBaseAuxVars; ++i) {
                TheLogger.Log2(Points.back()[i]->ToSimpleString());
                if(i != NumBaseAuxVars - 1) {
                    TheLogger.Log3(", ");
                }
            }
            TheLogger.Log3(">\n");
        }

        // Check for duplicates
        for(uint32 i = 0; i < NumPoints; ++i) {
            if(memcmp(Points[NumPoints].data(), Points[i].data(),
                      sizeof(ConcreteValueBase const*) * NumBaseAuxVars) == 0) {
                throw InternalError((string)"Error: Tried to add a duplicate point to the " +
                                    "Concrete Evaluator!\nAt: " + __FILE__ + ":" +
                                    to_string(__LINE__));
            }
        }

        ++NumPoints;
    }

    bool ConcreteEvaluator::CheckSubExpressions(GenExpressionBase const* const* Exps,
                                                ESFixedTypeBase const* const* Types,
                                                uint32 const* EvalTypeIDs,
                                                uint32& Status)
    {
        Status |= CONCRETE_EVAL_DIST;
        if (NumPoints == 0) {
            return true;
        }

        for (uint32 i = 0; i < NumPoints; ++i) {
            auto const& CurPoint = Points[i];
            uint32 j = 0;
            for (uint32 SynthFunIndex = 0; SynthFunIndex < NumSynthFuncs; ++SynthFunIndex) {
                for (auto const& AppMapTargetPos : SynthFunAppMaps[SynthFunIndex]) {
                    auto const& AppMap = AppMapTargetPos.first;
                    GenExpressionBase::Evaluate(const_cast<GenExpressionBase*>(Exps[SynthFunIndex]),
                                                CurPoint.data(), AppMap.data(),
                                                const_cast<ConcreteValueBase*>
                                                (SubExpEvalPoints[i][j]));

                    if (PartialExpression || ConcreteException) {
                        if (PartialExpression) {
                            Status |= CONCRETE_EVAL_PART;
                        }
                        PartialExpression = ConcreteException = false;
                        return false;
                    }
                    ++j;
                }
            }
        }
        return true;
    }

    // returns if subexpression is distinguishable or not
    bool ConcreteEvaluator::CheckSubExpression(GenExpressionBase* Exp,
                                               const ESFixedTypeBase* Type,
                                               uint32 EvalTypeID, uint32& Status)
    {
        // expects NumSynthFuncs = 1
        // return true;
        Status |= CONCRETE_EVAL_DIST;
        if (NumPoints == 0) {
            return true;
        }

        for (uint32 i = 0; i < NumPoints; ++i) {
            auto const& CurPoint = Points[i];
            uint32 j = 0;
            for (auto const& AppMapTargetPos : SynthFunAppMaps[0]) {
                auto const& AppMap = AppMapTargetPos.first;
                GenExpressionBase::Evaluate(Exp, CurPoint.data(), AppMap.data(),
                                            const_cast<ConcreteValueBase*>
                                            (SubExpEvalPoints[i][j]));

                if (PartialExpression || ConcreteException) {
                    if (PartialExpression) {
                        Status |= CONCRETE_EVAL_PART;
                    }
                    PartialExpression = ConcreteException = false;
                    return false;
                }
                ++j;
            }
        }

        // Check if we have encountered this signature before
        auto Sig =
            new (SigPool->malloc()) Signature(NumPoints * NumSynthFunApps,
                                              EvalTypeID, SigVecPool);

        for (uint32 i = 0; i < NumPoints; ++i) {
            const uint32 Offset = i * NumSynthFunApps;
            for (uint32 j = 0; j < NumSynthFunApps; ++j) {
                (*Sig)[Offset + j] = SubExpEvalPoints[i][j];
            }
        }

        // Have we see this signature before?
        if (SigSet.find(Sig) != SigSet.end()) {
            SigVecPool->free(Sig->ValVec);
            SigPool->free(Sig);
            Status &= ~(CONCRETE_EVAL_DIST);
            return false;
        } else {
            // Canonicalize and insert
            for (uint32 i = 0; i < NumPoints * NumSynthFunApps; ++i) {
                auto CurVal = (*Sig)[i];
                (*Sig)[i] = Solver->CreateValue(CurVal->GetType(), CurVal->GetValue());
            }
            SigSet.insert(Sig);
            return true;
        }
    }

    bool ConcreteEvaluator::CheckConcreteValidity(GenExpressionBase const* const* Exps,
                                                  ESFixedTypeBase const* const* Types,
                                                  uint32 const* ExpansionTypeIDs)
    {
        if (NumPoints == 0) {
            return true;
        }

        uint32 Status = 0;
        CheckSubExpressions(Exps, Types, ExpansionTypeIDs, Status);

        // Check the spec now that the derived aux vars are all created
        for (uint32 i = 0; i < NumPoints; ++i) {
            ConcreteValueBase Result;
            RewrittenSpec->Evaluate(Exps, EvalPoints[i].data(), &Result);
            if (ConcreteException) {
                ConcreteException = false;
                return false;
            }

            if (Result.GetValue() == 0) {
                return false;
            }
        }
        return true;
    }

    bool ConcreteEvaluator::CheckConcreteValidity(const GenExpressionBase* Exp,
                                                  const ESFixedTypeBase* Type,
                                                  uint32 EvalTypeID, uint32& Status)
    {
        if (NumPoints == 0) {
            return true;
        }

        GenExpressionBase* Arr[1];
        Arr[0] = const_cast<GenExpressionBase*>(Exp);

        bool Distinguishable = true;
        if (!NoDist) {
            Distinguishable = CheckSubExpression(const_cast<GenExpressionBase*>(Exp),
                                                 Type, EvalTypeID, Status);
        }
        if (!Distinguishable) {
            Status &= ~(CONCRETE_EVAL_DIST);
            return false;
        }

        // Proceed now to evaluate the spec
        // The EvalPoints are already initialized
        // as a side effect of checking subexpression
        for (uint32 i = 0; i < NumPoints; ++i) {
            ConcreteValueBase Result;
            RewrittenSpec->Evaluate(Arr, EvalPoints[i].data(), &Result);
            if (ConcreteException) {
                ConcreteException = false;
                return false;
            }
            if (Result.GetValue() == 0) {
                return false;
            }
        }
        return true;
    }

    uint32 ConcreteEvaluator::GetSize() const
    {
        return Points.size();
    }

} /* End namespace */


//
// ConcreteEvaluator.cpp ends here
