// CFGEnumerator.hpp --- //
// Filename: CFGEnumerator.hpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:47:52 2014 (-0500)
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


#if !defined __ESOLVER_CFG_ENUMERATOR_HPP
#define __ESOLVER_CFG_ENUMERATOR_HPP

#include "../common/ESolverForwardDecls.hpp"
#include "../enumerators/EnumeratorBase.hpp"
#include "../utils/Hashers.hpp"
#include "../utils/GNCostPair.hpp"
#include "../expressions/GenExpression.hpp"
#include "../containers/TwoLevelVec.hpp"
#include "../solvers/ESolver.hpp"
#include <boost/pool/pool.hpp>

namespace ESolver {

    // Some typedefs to avoid long template instantiations
    typedef unordered_map<GNCostPair, GenExpTLVec*,
                          GNCostPairHasher, GNCostPairEquals> ExpsOfGNCost;

    class CFGEnumeratorSingle : public EnumeratorBase
    {
    private:
        const Grammar* TheGrammar;
        ExpsOfGNCost ExpRepository;
        vector<string> ExpansionStack;
        unordered_map<string, uint32> ExpansionToTypeID;
        vector<const GenExpressionBase*> ExpsToDelete;
        // To recursively propagate a STOP_ENUMERATION signal
        bool Done;
        uint32 Index;
        uint64 NumExpsCached;

        // memory pools for fast allocation/deallocation
        // We use the type unsafe versions here :-( for speed
        boost::pool<>* FuncExpPool;
        boost::pool<>* LetExpPool;
        unordered_map<uint32, boost::pool<>*> CPPools;

        // Utility functions
        inline boost::pool<>* GetPoolForSize(uint32 Size);

        template<typename T, typename O>
        inline GenExpTLVec* MakeBaseExpression(GenExpTLVec* ExpVec,
                                               const O* Op,
                                               const ESFixedTypeBase* Type,
                                               uint32 ExpansionTypeID,
                                               uint32 Cost,
                                               const GNCostPair& Key,
                                               bool Complete)
        {
            if (Cost != 1) {
                ExpRepository[Key] = ExpVec;
                return ExpVec;
            }
            auto Exp = new T(Op);
            auto Status =
                (Complete ?
                 Solver->ExpressionCallBack(Exp, Type, ExpansionTypeID, Index) :
                 Solver->SubExpressionCallBack(Exp, Type, ExpansionTypeID));

            if ((Status & DELETE_EXPRESSION) != 0) {
                delete Exp;
            } else {
                ExpVec->PushBack(Exp);
                ExpsToDelete.push_back(Exp);
            }
            if ((Status & STOP_ENUMERATION) != 0) {
                Done = true;
            }

            ExpVec->Freeze();
            ExpRepository[Key] = ExpVec;
            PopExpansion();
            return ExpVec;
        }

        inline GenExpTLVec*
        GetVecForGNCost(const GrammarNode* GN, uint32 Cost);
        inline GenExpTLVec*
        MakeVecForGNCost(const GrammarNode* GN, uint32 Cost);
        inline uint32 GetExpansionTypeID();
        inline void PushExpansion(const string& NTName);
        inline void PopExpansion();

        GenExpTLVec*
        PopulateExpsOfGNCost(const GrammarNode* GN, uint32 Cost, bool Complete);

    public:
        CFGEnumeratorSingle(ESolver* Solver, const Grammar* TheGrammar, uint32 Index = 0);
        virtual ~CFGEnumeratorSingle();

        virtual void EnumerateOfCost(uint32 Size) override;
        virtual void OnReset() override;
        uint32 GetIndex() const;
    };

    // A wrapper class for multiple functions
    class CFGEnumeratorMulti : public EnumeratorBase
    {
    private:
        // A stub ESolver which doesn't do anything
        class ESolverMultiStub : public ESolver
        {
        private:
            ESolver* Solver;
            vector<CFGEnumeratorSingle*> Enumerators;
            vector<const ESFixedTypeBase*> TargetTypes;
            GenExpressionBase const** ExpVec;
            ESFixedTypeBase const** TypeVec;
            uint32* ExpansionTypeIDVec;
            const uint32 NumExpressions;
            vector<uint32> CurrentSizes;

        public:
            ESolverMultiStub(ESolverOpts* Opts, ESolver* Solver,
                             const vector<CFGEnumeratorSingle*>& Enumerators,
                             const vector<const ESFixedTypeBase*>& TargetTypes);
            virtual ~ESolverMultiStub();

            virtual CallbackStatus SubExpressionCallBack(const GenExpressionBase* Exp,
                                                         const ESFixedTypeBase* Type,
                                                         uint32 ExpansionTypeID) override;

            virtual CallbackStatus ExpressionCallBack(const GenExpressionBase* Exp,
                                                      const ESFixedTypeBase* Type,
                                                      uint32 ExpansionTypeID,
                                                      uint32 EnumeratorIndex) override;

            virtual CallbackStatus ExpressionCallBack(GenExpressionBase const* const* Exp,
                                                      ESFixedTypeBase const* const* Type,
                                                      uint32 const* ExpansionTypeID) override;

            virtual SolutionMap Solve(const Expression& Constraint) override;

            virtual void EndSolve() override;

            void SetEnumerator (uint32 Index, CFGEnumeratorSingle* Enumerator);
            void EnumerateOfCosts(const vector<uint32>& Sizes);
        };

        vector<CFGEnumeratorSingle*> Enumerators;
        vector<const ESFixedTypeBase*> TargetTypes;
        ESolverMultiStub* Stub;

    public:
        CFGEnumeratorMulti(ESolver* Solver, const vector<Grammar*>& InputGrammars);
        virtual ~CFGEnumeratorMulti();

        virtual void EnumerateOfCost(uint32 Size) override;
        virtual void OnReset() override;
    };

} /* End namespace */

#endif /* __ESOLVER_CFG_ENUMERATOR_HPP */


//
// CFGEnumerator.hpp ends here
