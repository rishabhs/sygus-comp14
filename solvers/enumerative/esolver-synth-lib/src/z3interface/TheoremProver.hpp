// TheoremProver.hpp --- 
// 
// Filename: TheoremProver.hpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:48:00 2014 (-0500)
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


#if !defined __ESOLVER_THEOREM_PROVER_HPP
#define __ESOLVER_THEOREM_PROVER_HPP

#include "../common/ESolverCommon.hpp"
#include "../common/ESolverForwardDecls.hpp"

namespace ESolver {

    enum SolveStatus {
        SOLVE_SATISFIABLE,
        SOLVE_UNSATISFIABLE,
        SOLVE_UNKNOWN,
        SOLVE_VALID,
        SOLVE_INVALID
    };

    typedef map<string, SMTExpr> SMTModel;
    typedef map<string, const ConcreteValueBase*> SMTConcreteValueModel;

    class TheoremProver
    {
    public:
        TheoremProver();
        virtual ~TheoremProver();
        
        // Context management methods
        virtual void Push() = 0;
        virtual void Pop(uint32 NumContexts) = 0;

        // Type creation methods
        virtual SMTType CreateEnumType(const string& TypeName, 
                                       const vector<string>& Constructors) = 0;
        virtual SMTType CreateBVType(uint32 NumBits) = 0;
        virtual SMTType CreateSetType(const SMTType& ElementType) = 0;
        virtual SMTType CreateRealType() = 0;
        virtual SMTType CreateArrayType(const SMTType& IndexType, const SMTType& ElementType) = 0;
        virtual SMTType CreateIntType() = 0;
        virtual SMTType CreateBoolType() = 0;

        // Constant Expression creation methods
        virtual SMTExpr CreateIntConstant(int64 IntValue) = 0;
        virtual SMTExpr CreateIntConstant(const string& IntValue) = 0;
        virtual SMTExpr CreateBVConstant(uint64 BVValue, uint32 BVSize) = 0;
        virtual SMTExpr CreateBVConstant(const string& BVValue) = 0;
        virtual SMTExpr CreateEnumConstant(const string& EnumValue) = 0;
        virtual SMTExpr CreateRealConstant(int32 Numerator, int32 Denominator) = 0;
        virtual SMTExpr CreateRealConstant(const string& RealValue) = 0;
        virtual SMTExpr CreateRealConstant(double RealValue) = 0;
        
        // Expression creation methods
        // arithmetic, real and core
        virtual SMTExpr CreateVarExpr(const string& VarName, const SMTType& VarType) = 0;
        virtual SMTExpr CreateOrExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;
        virtual SMTExpr CreateAndExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;
        virtual SMTExpr CreateOrExpr(const vector<SMTExpr>& Disjuncts) = 0;
        virtual SMTExpr CreateAndExpr(const vector<SMTExpr>& Conjuncts) = 0;
        virtual SMTExpr CreateImpliesExpr(const SMTExpr& Antecedent, const SMTExpr& Consequent) = 0;
        virtual SMTExpr CreateIffExpr(const SMTExpr& Antecedent, const SMTExpr& Consequent) = 0;
        virtual SMTExpr CreateEQExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;
        virtual SMTExpr CreateNotExpr(const SMTExpr& Exp1) = 0;
        virtual SMTExpr CreateNegExpr(const SMTExpr& Exp1) = 0;
        virtual SMTExpr CreatePlusExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;
        virtual SMTExpr CreateMinusExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;
        virtual SMTExpr CreateDivExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;
        virtual SMTExpr CreateMulExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;
        virtual SMTExpr CreateTrueExpr() = 0;
        virtual SMTExpr CreateFalseExpr() = 0;
        virtual SMTExpr CreateITEExpr(const SMTExpr& Pred, const SMTExpr& IfExp, 
                                      const SMTExpr& ElseExp) = 0;
        virtual SMTExpr CreateLEExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;
        virtual SMTExpr CreateLTExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;
        virtual SMTExpr CreateGEExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;
        virtual SMTExpr CreateGTExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;

        // bit vector expressions
        virtual SMTExpr CreateBVAndExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;
        virtual SMTExpr CreateBVOrExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;
        // bitwise negation
        virtual SMTExpr CreateBVNotExpr(const SMTExpr& Exp1) = 0;

        // Added to support Jha's PLDI 2011 benchmarks
        // Bitwise ops
        virtual SMTExpr CreateBVXorExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;
        // Reduce OR
        virtual SMTExpr CreateBVRedOrExpr(const SMTExpr& Exp1) = 0;
        virtual SMTExpr CreateBVRedAndExpr(const SMTExpr& Exp1) = 0;

        // Arithmetic
        virtual SMTExpr CreateBVSubExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;
        virtual SMTExpr CreateBVAddExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;
        virtual SMTExpr CreateBVSDivExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;
        virtual SMTExpr CreateBVUSDivExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;
        virtual SMTExpr CreateBVSRemExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;
        virtual SMTExpr CreateBVUSRemExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;
        virtual SMTExpr CreateBVSModExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;
        virtual SMTExpr CreateBVMulExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;
        virtual SMTExpr CreateBVNegExpr(const SMTExpr& Exp1) = 0;

        // Shifts
        virtual SMTExpr CreateBVLShRExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;
        virtual SMTExpr CreateBVAShRExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;
        virtual SMTExpr CreateBVShLExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;

        // Comparison
        virtual SMTExpr CreateBVUSLEExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;
        virtual SMTExpr CreateBVSLEExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;
        virtual SMTExpr CreateBVUSGEExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;
        virtual SMTExpr CreateBVSGEExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;
        virtual SMTExpr CreateBVUSLTExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;
        virtual SMTExpr CreateBVSLTExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;
        virtual SMTExpr CreateBVUSGTExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;
        virtual SMTExpr CreateBVSGTExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;


        // conversion to boolean and int
        virtual SMTExpr CreateBVToBoolExpr(const SMTExpr& Exp1) = 0;
        virtual SMTExpr CreateBVToSIntExpr(const SMTExpr& Exp1) = 0;
        virtual SMTExpr CreateBVToUSIntExpr(const SMTExpr& Exp1) = 0;

        // extraction and concatenation
        virtual SMTExpr CreateBVExtractExpr(const SMTExpr& Exp, 
                                            uint32 High, uint32 Low) = 0;
        virtual SMTExpr CreateBVConcatExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) = 0;

        // end additions to support Jha's PLDI 2011 benchmarks

        // Sets and arrays
        virtual SMTExpr CreateEmptySetExpr(const SMTType& ElemType) = 0;
        virtual SMTExpr CreateFullSetExpr(const SMTType& ElemType) = 0;
        virtual SMTExpr CreateSetAddExpr(const SMTExpr& SetExpr, const SMTExpr& ElemExpr) = 0;
        virtual SMTExpr CreateSetDelExpr(const SMTExpr& SetExpr, const SMTExpr& ElemExpr) = 0;
        virtual SMTExpr CreateSetUnionExpr(const SMTExpr& SetExpr1, const SMTExpr& SetExpr2) = 0;
        virtual SMTExpr CreateSetInterExpr(const SMTExpr& SetExpr1, const SMTExpr& SetExpr2) = 0;
        virtual SMTExpr CreateSetDiffExpr(const SMTExpr& SetExpr1, const SMTExpr& SetExpr2) = 0;
        virtual SMTExpr CreateSetComplementExpr(const SMTExpr& SetExpr) = 0;
        virtual SMTExpr CreateSetIsMemberExpr(const SMTExpr& SetExpr, const SMTExpr& ElemExpr) = 0;
        virtual SMTExpr CreateSetIsSubsetExpr(const SMTExpr& SetExpr1, const SMTExpr& SetExpr2) = 0;

        virtual SMTExpr CreateStoreExpr(const SMTExpr& ArrayExpr, const SMTExpr& IndexExpr,
                                        const SMTExpr& ValueExpr) = 0;
        virtual SMTExpr CreateSelectExpr(const SMTExpr& ArrayExpr, const SMTExpr& IndexExpr) = 0;

        // Assertion methods
        virtual void AssertFormula(const SMTExpr& Exp) = 0;
        
        // Query methods
        virtual SolveStatus CheckValidity(const SMTExpr& QueryExpr) = 0;
        virtual SolveStatus CheckSatisfiability(const SMTExpr& QueryExpr) = 0;
        
        // Model generation
        virtual void GetConcreteModel(const set<string>& RelevantVars, 
                                      SMTModel& Model,
                                      ESolver* Solver) = 0;
        // ESolver specific model generation
        virtual void GetConcreteModel(const set<string>& RelevantVars,
                                      SMTModel& Model,
                                      SMTConcreteValueModel& ConcModel,
                                      ESolver* Solver) = 0;

        virtual void GetAllAssertions(vector<SMTExpr>& Assertions) = 0;

        // Simplification
        virtual SMTExpr Simplify(const SMTExpr& Exp) = 0;

        // Identification
        virtual string GetSMTSolverInUse() const = 0;

        // hash routines for exprs
        virtual uint64 GetHash(const SMTExpr& Exp) = 0;

        // Stringification routine
        virtual string SMTExprToString(const SMTExpr& Exp) = 0;
    };

} /* End namespace */

#endif /* __ESOLVER_THEOREM_PROVER_HPP */


// 
// TheoremProver.hpp ends here
