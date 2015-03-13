// ConcreteEvaluator.hpp ---
//
// Filename: ConcreteEvaluator.hpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:49:55 2014 (-0500)
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


#if !defined __ESOLVER_CONCRETE_EVALUATOR_HPP
#define __ESOLVER_CONCRETE_EVALUATOR_HPP

#include "../common/ESolverForwardDecls.hpp"
#include "../expressions/UserExpression.hpp"
#include <boost/pool/pool.hpp>
#include "../utils/Hashers.hpp"

#define CONCRETE_EVAL_DIST ((uint32)0x1)
#define CONCRETE_EVAL_PART ((uint32)0x2)
#define CONCRETE_EVAL_COMP ((uint32)0x4)

namespace ESolver {

    /*
      This is a class for managing concrete examples
      and evaluating them
    */

    class ConcreteEvaluator
    {
    private:
        ESolver* Solver;
        Expression RewrittenSpec;
        // Points consist only of base aux vars
        vector<vector<const ConcreteValueBase*>> Points;
        // Buffers for evaluation, also contain space for derived aux vars
        vector<vector<const ConcreteValueBase*>> EvalPoints;
        // Buffers for evaluation of subexpressions
        vector<vector<const ConcreteValueBase*>> SubExpEvalPoints;

        vector<const AuxVarOperator*> BaseAuxVars;
        vector<const AuxVarOperator*> DerivedAuxVars;
        vector<vector<pair<vector<uint32>, uint32> > > SynthFunAppMaps;
        vector<const ESFixedTypeBase*> SynthFuncTypes;
        uint32 NumSynthFunApps;
        const uint32 NumBaseAuxVars;
        const uint32 NumDerivedAuxVars;
        const uint32 NumTotalAuxVars;
        const uint32 NumSynthFuncs;
        const bool NoDist;
        Logger& TheLogger;
        uint32 NumPoints;
        SigSetType SigSet;

        // Pool for the signature objects
        boost::pool<>* SigPool;

        // The pool for signatures
        static boost::pool<>* SigVecPool;

    public:
        ConcreteEvaluator(ESolver* Solver,
                          const Expression& RewrittenSpec,
                          uint32 NumSynthFuncs,
                          const vector<const AuxVarOperator*>& BaseAuxVars,
                          const vector<const AuxVarOperator*>& DerivedAuxVars,
                          const vector<map<vector<uint32>, uint32>>& SynthFunAppMaps,
                          const vector<const ESFixedTypeBase*>& SynthFuncTypes,
                          Logger& TheLogger);


        ~ConcreteEvaluator();

        void AddPoint(const SMTConcreteValueModel& Model);

        // For multiple function synthesis
        bool CheckConcreteValidity(GenExpressionBase const* const* Exps,
                                   ESFixedTypeBase const* const* Types,
                                   const uint32* ExpansionTypeIDs);
        // For single function synthesis
        bool CheckConcreteValidity(GenExpressionBase const* Exp,
                                   const ESFixedTypeBase* Type,
                                   uint32 EvalTypeID, uint32& Status);
        bool CheckSubExpression(GenExpressionBase* Exp,
                                const ESFixedTypeBase* Type,
                                uint32 EvalTypeID, uint32& Status);

        uint32 GetSize() const;
    };

} /* End namespace */

#endif /* __ESOLVER_CONCRETE_EVALUATOR_HPP */

//
// ConcreteEvaluator.hpp ends here
