// CFGEnumerator.cpp --- 
// 
// Filename: CFGEnumerator.cpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:47:42 2014 (-0500)
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


#include "CFGEnumerator.hpp"
#include "../descriptions/Grammar.hpp"
#include "../utils/GNCostPair.hpp"
#include "../descriptions/GrammarNodes.hpp"
#include "../descriptions/Operators.hpp"
#include "../solvers/ESolver.hpp"
#include "../partitions/PartitionGenerator.hpp"
#include "../partitions/SymPartitionGenerator.hpp"
#include "../partitions/CrossProductGenerator.hpp"
#include "../expressions/GenExpression.hpp"

namespace ESolver {

    // Implementation of the enumerator
    // private utility functions
    inline GenExpTLVec*
    CFGEnumeratorSingle::GetVecForGNCost(const GrammarNode* GN, uint32 Cost)
    {
        ExpsOfGNCost::const_iterator it = ExpRepository.find(GNCostPair(GN, Cost));
        if(it == ExpRepository.end()) {
            return nullptr;
        } else {
            return it->second;
        }
    }

    inline GenExpTLVec*
    CFGEnumeratorSingle::MakeVecForGNCost(const GrammarNode* GN, uint32 Cost)
    {
        GNCostPair CP(GN, Cost);
        ExpsOfGNCost::const_iterator it = ExpRepository.find(CP);
        if(it == ExpRepository.end()) {
            auto NewVec = new GenExpTLVec();
            ExpRepository[CP] = NewVec;
            return NewVec;
        } else {
            return it->second;
        }
    }

    inline uint32
    CFGEnumeratorSingle::GetExpansionTypeID()
    {
        if(ExpansionStack.size() == 0) {
            return 0;
        }
        auto it = ExpansionToTypeID.find(ExpansionStack.back());
        if(it == ExpansionToTypeID.end()) {
            uint32 CurUID = (uint32)ExpansionTypeUIDGenerator.GetUID();
            ExpansionToTypeID[ExpansionStack.back()] = CurUID;
            return CurUID;
        } else {
            return it->second;
        }
    }

    inline void CFGEnumeratorSingle::PushExpansion(const string& NTName)
    {
        if(ExpansionStack.size() > 0) {
            auto const& CurExp = ExpansionStack.back();
            auto NewExp = CurExp + "->" + NTName;
            ExpansionStack.push_back(NewExp);
        } else {
            ExpansionStack.push_back(NTName);
        }
    }

    inline void CFGEnumeratorSingle::PopExpansion()
    {
        ExpansionStack.pop_back();
    }

    inline boost::pool<>* CFGEnumeratorSingle::GetPoolForSize(uint32 Size)
    {
        auto it = CPPools.find(Size);
        if (it == CPPools.end()) {
            auto Retval = CPPools[Size] = new boost::pool<>(Size * sizeof(GenExpressionBase const*));
            return Retval;
        } else {
            return it->second;
        }
    }

    GenExpTLVec*
    CFGEnumeratorSingle::PopulateExpsOfGNCost(const GrammarNode* GN, uint32 Cost, bool Complete)
    {
        auto Retval = new GenExpTLVec();
        GNCostPair Key(GN, Cost);
        Done = false;
        auto Type = GN->GetType();
        PushExpansion(GN->ToString());
        auto const ExpansionTypeID = GetExpansionTypeID();

        auto FPVar = GN->As<GrammarFPVar>();
        // The base cases
        if (FPVar != nullptr) {
            return MakeBaseExpression<GenFPExpression>(Retval, FPVar->GetOp(), Type, 
                                                       ExpansionTypeID, Cost, Key, Complete);
        }

        auto LetVar = GN->As<GrammarLetVar>();
        if (LetVar != nullptr) {
            return MakeBaseExpression<GenLetVarExpression>(Retval, LetVar->GetOp(), Type, 
                                                           ExpansionTypeID, Cost, Key, Complete);
        }

        auto Const = GN->As<GrammarConst>();
        if (Const != nullptr) {
            return MakeBaseExpression<GenConstExpression>(Retval, Const->GetOp(), Type, 
                                                          ExpansionTypeID, Cost, Key, Complete);
        }

        auto Func = GN->As<GrammarFunc>();
        
        if (Func != nullptr) {
            auto const& Args = Func->GetChildren();
            auto Op = Func->GetOp();
            const uint32 OpCost = Op->GetCost();
            const uint32 Arity = Op->GetArity();

            if (Cost < Arity + OpCost) {
                Retval->Freeze();
                ExpRepository[Key] = Retval;
                PopExpansion();
                return Retval;
            }
            PartitionGenerator* PG;
            if (Op->IsSymmetric() && Args[0] == Args[1]) {
                PG = new SymPartitionGenerator(Cost - OpCost);
            } else {
                PG = new PartitionGenerator(Cost - OpCost, Arity);
            }

            const uint32 NumPartitions = PG->Size();
            for (uint32 i = 0; i < NumPartitions; ++i) {

                auto Feasible = true;
                vector<const GenExpTLVec*> ArgExpVecs(Arity, nullptr);
                auto CurPartition = (*PG)[i];
                vector<GenExpTLVec::ConstIterator> Begins(Arity);
                vector<GenExpTLVec::ConstIterator> Ends(Arity);

                for (uint32 j = 0; j < Arity; ++j) {
                    auto CurVec = GetVecForGNCost(Args[j], CurPartition[j]);
                    if (CurVec == nullptr) {
                        CurVec = PopulateExpsOfGNCost(Args[j], CurPartition[j], false);
                    }
                    if (CurVec->Size() == 0) {
                        Feasible = false; 
                        break;
                    } else {
                        ArgExpVecs[j] = CurVec;
                        Begins[j] = CurVec->Begin();
                        Ends[j] = CurVec->End();
                    }
                }

                if (!Feasible) {
                    continue;
                }

                // Iterate over the cross product
                auto CPGen = new CrossProductGenerator(Begins, Ends, GetPoolForSize(Arity));
                
                for (auto CurArgs = CPGen->GetNext(); CurArgs != nullptr; CurArgs = CPGen->GetNext()) {
                    // Static cast okay, because this can never be a synth function
                    auto CurExp = new (FuncExpPool->malloc()) 
                        GenFuncExpression(static_cast<const InterpretedFuncOperator*>(Op), CurArgs);

                    auto Status = Solver->ExpressionCallBack(CurExp, Type, ExpansionTypeID, Complete, Index);
                    
                    if ((Status & DELETE_EXPRESSION) == 0) {
                        CPGen->RelinquishOwnerShip();
                        Retval->PushBack(CurExp);
                    } else {
                        FuncExpPool->free(CurExp);
                    }
                    if ((Status & STOP_ENUMERATION) != 0) {
                        Done = true;
                        break;
                    }
                }
                delete CPGen;
                if (Done) {
                    break;
                }
            }
            delete PG;
            
            Retval->Freeze();
            ExpRepository[Key] = Retval;
            PopExpansion();
            return Retval;
        }

        auto Let = GN->As<GrammarLet>();
        
        // We handle this in similar spirit as functions
        if (Let != nullptr) {
            auto const& Bindings = Let->GetBindings();
            const uint32 NumBindings = Bindings.size();
            const uint32 Arity = NumBindings + 1;
            auto BoundNode = Let->GetBoundExpression();
            const uint32 NumLetBoundVars = TheGrammar->GetNumLetBoundVars();
            
            if (Cost < Arity + 1) {
                Retval->Freeze();
                ExpRepository[Key] = Retval;
                PopExpansion();
                return Retval;
            }

            // Making a let binding incurs a cost of 1!
            auto PG = new PartitionGenerator(Cost - 1, Arity);
            const uint32 NumPartitions = PG->Size();
            for (uint32 i = 0; i < NumPartitions; ++i) {
                auto Feasible = true;
                vector<const GenExpTLVec*> ArgExpVecs(Arity, nullptr);
                auto CurPartition = (*PG)[i];
                vector<GenExpTLVec::ConstIterator> Begins(Arity);
                vector<GenExpTLVec::ConstIterator> Ends(Arity);
                
                uint32 j = 0;
                uint32* Positions = new uint32[NumBindings];

                for (auto it = Bindings.begin(); it != Bindings.end(); ++it) {
                    auto CurVec = GetVecForGNCost(it->second, CurPartition[j]);
                    if (CurVec == nullptr) {
                        CurVec = PopulateExpsOfGNCost(it->second, CurPartition[j], false);
                    }
                    if (CurVec->Size() == 0) {
                        Feasible = false;
                        break;
                    } else {
                        ArgExpVecs[j] = CurVec;
                        Begins[j] = CurVec->Begin();
                        Ends[j] = CurVec->End();
                    }
                    Positions[j] = it->first->GetOp()->GetPosition();
                    ++j;
                }

                if (!Feasible) {
                    delete[] Positions;
                    continue;
                }

                // Finally, the expression set for the bound expression
                auto BoundVec = GetVecForGNCost(BoundNode, CurPartition[j]);
                if (BoundVec == nullptr) {
                    BoundVec = PopulateExpsOfGNCost(BoundNode, CurPartition[j], true);
                }
                if (BoundVec->Size() == 0) {
                    // cross product is empty not feasible
                    delete[] Positions;
                    continue;
                } else {
                    ArgExpVecs[NumBindings] = BoundVec;
                    Begins[NumBindings] = BoundVec->Begin();
                    Ends[NumBindings] = BoundVec->End();
                }


                // Iterate over the cross product of expressions
                // The bindings object will be of size of the NUMBER 
                // of let bound vars for the whole grammar
                auto CPGen = new CrossProductGenerator(Begins, Ends, 
                                                       GetPoolForSize(Arity));
                GenExpressionBase const** BindVec = nullptr;
                auto BindVecPool = GetPoolForSize(NumLetBoundVars);

                for (auto CurArgs = CPGen->GetNext(); CurArgs != nullptr; CurArgs = CPGen->GetNext()) {
                    // We need to build the binding vector based on the position
                    if (BindVec == nullptr) {
                        BindVec = (GenExpressionBase const**)BindVecPool->malloc();
                        memset(BindVec, 0, sizeof(GenExpressionBase const*) * NumLetBoundVars);
                    }
                    for (uint32 k = 0; k < NumBindings; ++k) {
                        BindVec[Positions[k]] = CurArgs[k];
                    }

                    auto CurExp = new (LetExpPool->malloc())
                        GenLetExpression(BindVec, CurArgs[NumBindings], NumLetBoundVars);
                    auto Status = Solver->ExpressionCallBack(CurExp, Type, ExpansionTypeID, Complete, Index);
                    if ((Status & DELETE_EXPRESSION) == 0) {
                        BindVec = nullptr;
                        Retval->PushBack(CurExp);
                    } else {
                        LetExpPool->free(CurExp);
                    }
                    if ((Status & STOP_ENUMERATION) != 0) {
                        Done = true;
                        break;
                    }
                }

                delete CPGen;
                delete[] Positions;

                if (Done) {
                    break;
                }
            }

            delete PG;

            Retval->Freeze();
            ExpRepository[Key] = Retval;
            PopExpansion();
            return Retval;
        }

        auto NT = GN->As<GrammarNonTerminal>();
        if (NT != nullptr) {
            const vector<GrammarNode*>& Expansions = TheGrammar->GetExpansions(NT);
            for (auto const& Expansion : Expansions) {
                auto CurVec = GetVecForGNCost(Expansion, Cost);
                if (CurVec == nullptr) {
                    CurVec = PopulateExpsOfGNCost(Expansion, Cost, Complete);
                }
                Retval->Merge(*CurVec);
                if (Done) {
                    break;
                }
            }
            Retval->Freeze();
            ExpRepository[Key] = Retval;
            PopExpansion();
            return Retval;
        }
        
        // Should NEVER get here
        throw InternalError((string)"You probably subclassed GrammarNode and forgot to change " + 
                            "CFGEnumerator.cpp.\nAt: " + __FILE__ + ":" + to_string(__LINE__));
    }

    // Assumption: Grammar has already been canonicalized
    CFGEnumeratorSingle::CFGEnumeratorSingle(ESolver* Solver,
                                             const Grammar* InputGrammar,
                                             uint32 Index)
        : EnumeratorBase(Solver), TheGrammar(InputGrammar),
          ExpansionTypeUIDGenerator(1), Index(Index)
    {
        FuncExpPool = new boost::pool<>(sizeof(GenFuncExpression));
        LetExpPool = new boost::pool<>(sizeof(GenLetExpression));
    }

    CFGEnumeratorSingle::~CFGEnumeratorSingle()
    {
        // We just delete the expressions that we're managing
        // the pools will take care of the rest
        for (auto const& Exp : ExpsToDelete) {
            delete Exp;
        }
        ExpsToDelete.clear();
        delete FuncExpPool;
        delete LetExpPool;
        for (auto const& KV : CPPools) {
            delete KV.second;
        }
        CPPools.clear();
        for (auto const& KV : ExpRepository) {
            delete KV.second;
        }
        ExpRepository.clear();
    }

    void CFGEnumeratorSingle::EnumerateOfCost(uint32 Cost)
    {
        auto StartNT = TheGrammar->MakeStartNT();
        auto Vec = GetVecForGNCost(StartNT, Cost);
        if (Vec != nullptr) {
            PushExpansion(StartNT->GetName());
            auto ExpansionTypeID = GetExpansionTypeID();
            auto Type = StartNT->GetType();
            auto const Begin = Vec->Begin();
            auto const End = Vec->End();
            for (auto it = Begin; it != End; ++it) {
                Solver->ExpressionCallBack(*it, Type, ExpansionTypeID, true, Index);
            }
        } else {
            PopulateExpsOfGNCost(StartNT, Cost, true);
        }
    }

    void CFGEnumeratorSingle::OnReset()
    {
        for (auto const& Exp : ExpsToDelete) {
            delete Exp;
        }
        ExpsToDelete.clear();
        delete FuncExpPool;
        delete LetExpPool;
        for (auto const& KV : CPPools) {
            delete KV.second;
        }
        CPPools.clear();
        
        // Clear all the built up state
        for (auto const& KV : ExpRepository) {
            delete KV.second;
        }
        ExpRepository.clear();
        ExpansionTypeUIDGenerator.Reset();
        ExpansionStack.clear();
        ExpansionToTypeID.clear();

        // Recreate basic pool types
        FuncExpPool = new boost::pool<>(sizeof(GenFuncExpression));
        LetExpPool = new boost::pool<>(sizeof(GenLetExpression));
    }

    uint32 CFGEnumeratorSingle::GetIndex() const
    {
        return Index;
    }

    // CFGEnumeratorMulti::ESolverMultiStub implementation
    CFGEnumeratorMulti::ESolverMultiStub::ESolverMultiStub(ESolverOpts* Opts,
                                                           ESolver* Solver,
                                                           const vector<CFGEnumeratorSingle*>& Enumerators,
                                                           const vector<const ESFixedTypeBase*>& TargetTypes)
        : ESolver(Opts), Solver(Solver), Enumerators(Enumerators), 
          TargetTypes(TargetTypes), NumExpressions(Enumerators.size())
    {
        ExpVec = (GenExpressionBase const**)calloc(NumExpressions, sizeof(GenExpressionBase const*));
        TypeVec = (ESFixedTypeBase const**)calloc(NumExpressions, sizeof(ESFixedTypeBase const*));
        ExpansionTypeIDVec = (uint32*)calloc(NumExpressions, sizeof(uint32));
    }

    CFGEnumeratorMulti::ESolverMultiStub::~ESolverMultiStub()
    {
        free(ExpVec);
        free(TypeVec);
        free(ExpansionTypeIDVec);
    }

    // Evil mutual recursion trickery.
    // I know I'm going to regret doing this
    // if I ever have to debug this stuff. 
    // But hey, I think I know what I'm doing (TM)
    CallbackStatus 
    CFGEnumeratorMulti::ESolverMultiStub::ExpressionCallBack(const GenExpressionBase* Exp, 
                                                             const ESFixedTypeBase* Type, 
                                                             uint32 ExpansionTypeID,
                                                             bool Complete,
                                                             uint32 EnumeratorIndex)
    {
        // Do nothing if the type is not what we expect!
        if (!Complete) {
            return NONE_STATUS;
        }

        ExpVec[EnumeratorIndex] = Exp;
        TypeVec[EnumeratorIndex] = Type;
        ExpansionTypeIDVec[EnumeratorIndex] = ExpansionTypeID;

        if (EnumeratorIndex != NumExpressions - 1) {
            // We've run out of expressions at the higher levels
            // Enumerate from the next higher level
            Enumerators[EnumeratorIndex + 1]->EnumerateOfCost(CurrentSizes[EnumeratorIndex + 1]);
        } else {
            // We have a complete ExpVec
            Solver->ExpressionCallBack(ExpVec, TypeVec, ExpansionTypeIDVec);
        }
        return NONE_STATUS;
    }
    
    CallbackStatus 
    CFGEnumeratorMulti::ESolverMultiStub::ExpressionCallBack(GenExpressionBase const* const* Exp,
                                                             ESFixedTypeBase const* const* Type, 
                                                             uint32 const* ExpansionTypeID)
    {
        return NONE_STATUS;
    }
    
    SolutionMap CFGEnumeratorMulti::ESolverMultiStub::Solve(const Expression& Constraint)
    {
        return SolutionMap();
    }
    
    void CFGEnumeratorMulti::ESolverMultiStub::EndSolve()
    {
        // Nothing here
    }
    
    void CFGEnumeratorMulti::ESolverMultiStub::EnumerateOfCosts(const vector<uint32>& Sizes)
    {
        memset(ExpVec, 0, sizeof(GenExpressionBase const*) * NumExpressions);
        CurrentSizes = Sizes;
        // Kick off the chain of dominoes by calling 
        // Enumerate on the first enumerator
        Enumerators[0]->EnumerateOfCost(Sizes[0]);
    }


    // CFGEnumeratorMulti implementation
    CFGEnumeratorMulti::CFGEnumeratorMulti(ESolver* Solver, const vector<Grammar*>& InputGrammars)
        : EnumeratorBase(Solver), Enumerators(InputGrammars.size(), nullptr), 
          TargetTypes(InputGrammars.size(), nullptr)
    {
        ESolverOpts Opts;
        const uint32 NumGrammars = InputGrammars.size();

        for (uint32 i = 0; i < NumGrammars; ++i) {
            Enumerators[i] = new CFGEnumeratorSingle(Stub, InputGrammars[i], i);
            TargetTypes[i] = InputGrammars[i]->MakeStartNT()->GetType();
        }

        Stub = new ESolverMultiStub(&Opts, Solver, Enumerators, TargetTypes);
    }

    CFGEnumeratorMulti::~CFGEnumeratorMulti()
    {
        delete Stub;
        for(uint32 i = 0; i < Enumerators.size(); ++i) {
            delete Enumerators[i];
        }
    }

    void CFGEnumeratorMulti::EnumerateOfCost(uint32 Size)
    {
        const uint32 NumEnumerators = Enumerators.size();
        // We enumerate over all partitions of the size
        if (Size < NumEnumerators) {
            return;
        }
        auto PG = new PartitionGenerator(Size, NumEnumerators);
        const uint32 NumPartitions = PG->Size();
        for (uint32 i = 0; i < NumPartitions; ++i) {
            auto CurPart = (*PG)[i];
            Stub->EnumerateOfCosts(CurPart);
        }
    }

    void CFGEnumeratorMulti::OnReset() 
    {
        for (auto const& Enumerator : Enumerators) {
            Enumerator->Reset();
        }
    }

} /* End namespace */

// 
// CFGEnumerator.cpp ends here
