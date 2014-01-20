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

namespace ESolver {

    // Flag indicating that an exception occurred
    bool ConcreteException = false;
    // Flag indicating that an expression is partial
    // and could not be evaluated
    bool PartialExpression = false;

    boost::pool<>* ConcreteEvaluator::SigVecPool = nullptr;

    ConcreteEvaluator::ConcreteEvaluator(ESolver* Solver, const Expression& RewrittenSpec,
                                         uint32 NumSynthFuncs, const vector<const AuxVarOperator*>& BaseAuxVars,
                                         const vector<const AuxVarOperator*>& DerivedAuxVars,
                                         const vector<EvalRule>& EvalRules,
                                         const vector<const ESFixedTypeBase*>& SynthFuncTypes, Logger& TheLogger)
        : Solver(Solver), 
          RewrittenSpec(RewrittenSpec), 
          EvalPoints(nullptr),
          BaseAuxVars(BaseAuxVars), DerivedAuxVars(DerivedAuxVars), 
          SynthFuncTypes(SynthFuncTypes), EvalRules(EvalRules),
          NumBaseAuxVars(BaseAuxVars.size()), NumDerivedAuxVars(DerivedAuxVars.size()),
          NumTotalAuxVars(BaseAuxVars.size() + DerivedAuxVars.size()),
          NumSynthFuncs(NumSynthFuncs), NumEvalRules(EvalRules.size()), 
          NoDist(Solver->GetOpts().NoDist), TheLogger(TheLogger),
          NumPoints(0), SigPool(nullptr)
    {
        // Set the empty key for sigset
        // SigSet.set_empty_key(nullptr);
    }

    ConcreteEvaluator::~ConcreteEvaluator()
    {
        for (auto const& Point : Points) {
            free(const_cast<void*>(static_cast<const void*>(Point)));
        }
        Points.clear();
        for (uint32 i = 0; i < NumPoints; ++i) {
            for (uint32 j = NumBaseAuxVars; j < NumTotalAuxVars; ++j) {
                delete EvalPoints[i][j];
            }
            free(EvalPoints[i]);
        }
        free(EvalPoints);
        
        if (SigVecPool != nullptr) {
            delete SigVecPool;
        }
        if (SigPool != nullptr) {
            delete SigPool;
        }
    }

    void ConcreteEvaluator::AddPoint(const SMTConcreteValueModel& Model)
    {
        ConcreteValueBase const** NewPoint = 
            (ConcreteValueBase const**)malloc(sizeof(ConcreteValueBase const*) * NumBaseAuxVars);
        
        // Resize the eval points, i.e, add another row and allocate pointers into it
        EvalPoints = (ConcreteValueBase const***)realloc(EvalPoints, 
                                                         sizeof(ConcreteValueBase const**) * (NumPoints + 1));

        EvalPoints[NumPoints] = (ConcreteValueBase const**)malloc(sizeof(ConcreteValueBase const*) * 
                                                                  NumTotalAuxVars);
        // Allocate value buffers for each var in this new row
        for (uint32 i = NumBaseAuxVars; i < NumTotalAuxVars; ++i) {
            EvalPoints[NumPoints][i] = new ConcreteValueBase();
        }

        // Recreate the pool for the new size
        if (SigVecPool != nullptr) {
            delete SigVecPool;
        }
        SigVecPool = new boost::pool<>(sizeof(ConcreteValueBase const*) * NumDerivedAuxVars * (NumPoints + 1));

        // Clear all the accumulated signatures
        SigSet.clear();
        if (SigPool != nullptr) {
            delete SigPool;
        }
        SigPool = new boost::pool<>(sizeof(Signature));
        
        for(uint32 i = 0; i < NumBaseAuxVars; ++i) {
            auto it = Model.find(BaseAuxVars[i]->GetName());
            if (it == Model.end()) {
                throw InternalError((string)"Internal Error: Could not find model for variable \"" + 
                                    BaseAuxVars[i]->GetName() + "\".\nAt: " + __FILE__ + 
                                    ":" + to_string(__LINE__));
            }

            EvalPoints[NumPoints][BaseAuxVars[i]->GetPosition()] = it->second;
            NewPoint[BaseAuxVars[i]->GetPosition()] = it->second;
        }

        if (Solver->GetOpts().StatsLevel >= 3) {
            TheLogger.Log3("Adding point: <");
            for(uint32 i = 0; i < NumBaseAuxVars; ++i) {
                TheLogger.Log2(NewPoint[i]->ToSimpleString());
                if(i != NumBaseAuxVars - 1) {
                    TheLogger.Log3(", ");
                }
            }
            TheLogger.Log3(">\n");
        }
        
        // Check for duplicates
        for(uint32 i = 0; i < NumPoints; ++i) {
            if(memcmp(NewPoint, Points[i], sizeof(ConcreteValueBase const*) * NumBaseAuxVars) == 0) {
                throw InternalError((string)"Error: Tried to add a duplicate point to the " + 
                                    "Concrete Evaluator!\nAt: " + __FILE__ + ":" + to_string(__LINE__));
            }
        }

        Points.push_back(NewPoint);
        NumPoints++;
    }

    bool ConcreteEvaluator::CheckConcreteValidity(GenExpressionBase const* const* Exps)
    {
        if (NumPoints == 0) {
            return true;
        }
        for (uint32 i = 0; i < NumEvalRules; ++i) {
            auto const CurEvalRule = EvalRules[i];
            auto DVIndex = CurEvalRule.GetLHS()->GetPosition();
            for (uint32 j = 0; j < NumPoints; ++j) {
                EvalRules[i].Evaluate(Exps, EvalPoints[j], 
                                      const_cast<ConcreteValueBase*>(EvalPoints[j][DVIndex]));
                if (ConcreteException || PartialExpression) {
                    ConcreteException = PartialExpression = false;
                    return false;
                }
            }
        }

        // Check the spec now that the derived aux vars are all created
        for (uint32 i = 0; i < NumPoints; ++i) {
            ConcreteValueBase Result;
            RewrittenSpec->Evaluate(Exps, EvalPoints[i], &Result);
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
        Status |= CONCRETE_EVAL_DIST;
        if (NumPoints == 0 && (Status & CONCRETE_EVAL_COMP) != 0) {
            return true;
        } else if (NumPoints == 0) {
            return false;
        }
        // for substexps
        GenExpressionBase const* Arr[1];
        Arr[0] = Exp;
        for (uint32 i = 0; i < NumEvalRules; ++i) {
            auto const CurEvalRule = EvalRules[i];
            auto DVIndex = CurEvalRule.GetLHS()->GetPosition();
            for (uint32 j = 0; j < NumPoints; ++j) {
                EvalRules[i].Evaluate(Arr, EvalPoints[j], 
                                      const_cast<ConcreteValueBase*>(EvalPoints[j][DVIndex]));
                if (ConcreteException || PartialExpression) {
                    if (PartialExpression) {
                        Status |= CONCRETE_EVAL_PART;
                    }
                    ConcreteException = PartialExpression = false;
                    return false;
                }
            }
        }

        if (!NoDist) {
            
            auto Sig = new (SigPool->malloc()) Signature(NumDerivedAuxVars * NumPoints, EvalTypeID);
            
            for (uint32 i = 0; i < NumPoints; ++i) {
                const uint32 Offset = i * NumDerivedAuxVars;
                for (uint32 j = 0; j < NumTotalAuxVars - NumBaseAuxVars; ++j) {
                    auto CurValue = EvalPoints[i][NumBaseAuxVars + j];
                    (*Sig)[Offset + j] = CurValue;
                }
            }
            
            // Check if we have encountered this signature before
            if (SigSet.find(Sig) != SigSet.end()) {
                SigVecPool->free(Sig->ValVec);
                SigPool->free(Sig);
                Status &= ~(CONCRETE_EVAL_DIST);
                return false;
            } else {
                
                // Canonicalize and insert
                for (uint32 i = 0; i < NumPoints * NumDerivedAuxVars; ++i) {
                    auto CurValue = (*Sig)[i];
                    (*Sig)[i] = Solver->CreateValue(CurValue->GetType(), CurValue->GetValue());
                }
                
                SigSet.insert(Sig);
            }
        }

        // Is this expression of the type we expect?
        if ((Status & CONCRETE_EVAL_COMP) == 0) {
            return false;
        }

        // Proceed now to evaluate the spec
        for (uint32 i = 0; i < NumPoints; ++i) {
            ConcreteValueBase Result;
            RewrittenSpec->Evaluate(Arr, EvalPoints[i], &Result);
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
