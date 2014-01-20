// Z3TheoremProver.hpp --- 
// 
// Filename: Z3TheoremProver.hpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:48:11 2014 (-0500)
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


#if !defined __ESOLVER_Z3_THEOREM_PROVER_HPP
#define __ESOLVER_Z3_THEOREM_PROVER_HPP

#include "../common/ESolverCommon.hpp"
#include "../z3interface/TheoremProver.hpp"
#include "../z3interface/Z3Objects.hpp"

namespace ESolver {

    class Z3TheoremProver : public TheoremProver
    {
    private:
        Z3_context TheContext;
        Z3_solver TheSolver;
        map<string, Z3_func_decl> EnumConstructorToConsFuncMap;
        map<string, Z3_func_decl> EnumConstructorToTestFuncMap;

        Z3Model TheModel;

        SMTSolverParams TheParams;
        Z3Sort BoolType;
        Z3Sort IntType;

        // Utility function
        SMTExpr GenBVToIntExpr(const SMTExpr& Expr, uint32 BitNum);

    public:
        Z3TheoremProver(const SMTSolverParams& Params);
        virtual ~Z3TheoremProver();
        
        // Context management methods
        virtual void Push() override;
        virtual void Pop(uint32 NumContexts = 1) override;

        // Type creation methods
        virtual SMTType CreateEnumType(const string& TypeName, 
                                       const vector<string>& Constructors) override;
        virtual SMTType CreateBVType(uint32 NumBits) override;
        virtual SMTType CreateSetType(const SMTType& ElementType) override;
        virtual SMTType CreateRealType() override;
        virtual SMTType CreateArrayType(const SMTType& IndexType, const SMTType& ElementType) override;
        virtual SMTType CreateIntType() override;
        virtual SMTType CreateBoolType() override;

        // Constant Expression creation methods
        virtual SMTExpr CreateIntConstant(int64 IntValue) override;
        virtual SMTExpr CreateIntConstant(const string& IntValue) override;
        virtual SMTExpr CreateBVConstant(uint64 BVValue, uint32 BVSize) override;
        virtual SMTExpr CreateBVConstant(const string& BVValue) override;
        virtual SMTExpr CreateEnumConstant(const string& EnumValue) override;
        virtual SMTExpr CreateRealConstant(int32 Numerator, int32 Denominator) override;
        virtual SMTExpr CreateRealConstant(const string& RealValue) override;
        virtual SMTExpr CreateRealConstant(double RealValue) override;

        
        // Expression creation methods
        virtual SMTExpr CreateVarExpr(const string& VarName, const SMTType& VarType) override;
        virtual SMTExpr CreateOrExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;
        virtual SMTExpr CreateAndExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;
        virtual SMTExpr CreateOrExpr(const vector<SMTExpr>& Disjuncts) override;
        virtual SMTExpr CreateAndExpr(const vector<SMTExpr>& Conjuncts) override;
        virtual SMTExpr CreateImpliesExpr(const SMTExpr& Antecedent, const SMTExpr& Consequent) override;
        virtual SMTExpr CreateIffExpr(const SMTExpr& Antecedent, const SMTExpr& Consequent) override;
        virtual SMTExpr CreateEQExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;
        virtual SMTExpr CreateNotExpr(const SMTExpr& Exp1) override;
        virtual SMTExpr CreateNegExpr(const SMTExpr& Exp1) override;
        virtual SMTExpr CreatePlusExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;
        virtual SMTExpr CreateMinusExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;
        virtual SMTExpr CreateDivExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;
        virtual SMTExpr CreateMulExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;
        virtual SMTExpr CreateTrueExpr() override;
        virtual SMTExpr CreateFalseExpr() override;
        virtual SMTExpr CreateITEExpr(const SMTExpr& Pred, const SMTExpr& IfExp, 
                                      const SMTExpr& ElseExp) override;
        virtual SMTExpr CreateLEExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;
        virtual SMTExpr CreateLTExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;
        virtual SMTExpr CreateGEExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;
        virtual SMTExpr CreateGTExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;

        // bit vector expression
        virtual SMTExpr CreateBVAndExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;
        virtual SMTExpr CreateBVOrExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;
        // Bitwise negation
        virtual SMTExpr CreateBVNotExpr(const SMTExpr& Exp1) override;

        // Added to support Jha's PLDI 2011 benchmarks
        // Bitwise ops
        virtual SMTExpr CreateBVXorExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;
        // Reduce OR
        virtual SMTExpr CreateBVRedOrExpr(const SMTExpr& Exp1) override;
        virtual SMTExpr CreateBVRedAndExpr(const SMTExpr& Exp1) override;

        // Arithmetic
        virtual SMTExpr CreateBVSubExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;
        virtual SMTExpr CreateBVAddExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;
        virtual SMTExpr CreateBVSDivExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;
        virtual SMTExpr CreateBVUSDivExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;
        virtual SMTExpr CreateBVSRemExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;
        virtual SMTExpr CreateBVUSRemExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;
        virtual SMTExpr CreateBVSModExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;
        virtual SMTExpr CreateBVMulExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;
        virtual SMTExpr CreateBVNegExpr(const SMTExpr& Exp1) override;

        // Shifts
        virtual SMTExpr CreateBVLShRExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;
        virtual SMTExpr CreateBVAShRExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;
        virtual SMTExpr CreateBVShLExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;

        // Comparison
        virtual SMTExpr CreateBVUSLEExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;
        virtual SMTExpr CreateBVSLEExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;
        virtual SMTExpr CreateBVUSGEExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;
        virtual SMTExpr CreateBVSGEExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;
        virtual SMTExpr CreateBVUSLTExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;
        virtual SMTExpr CreateBVSLTExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;
        virtual SMTExpr CreateBVUSGTExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;
        virtual SMTExpr CreateBVSGTExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;

        // conversion to boolean and int
        virtual SMTExpr CreateBVToBoolExpr(const SMTExpr& Exp1) override;
        virtual SMTExpr CreateBVToSIntExpr(const SMTExpr& Exp1) override;
        virtual SMTExpr CreateBVToUSIntExpr(const SMTExpr& Exp1) override;

        virtual SMTExpr CreateBVExtractExpr(const SMTExpr& Exp, 
                                            uint32 High, uint32 Low) override;
        virtual SMTExpr CreateBVConcatExpr(const SMTExpr& Exp1, const SMTExpr& Exp2) override;

        // end additions to support Jha's PLDI 2011 benchmarks

        // Sets and arrays
        virtual SMTExpr CreateEmptySetExpr(const SMTType& ElemType) override;
        virtual SMTExpr CreateFullSetExpr(const SMTType& ElemType) override;
        virtual SMTExpr CreateSetAddExpr(const SMTExpr& SetExpr, const SMTExpr& ElemExpr) override;
        virtual SMTExpr CreateSetDelExpr(const SMTExpr& SetExpr, const SMTExpr& ElemExpr) override;
        virtual SMTExpr CreateSetUnionExpr(const SMTExpr& SetExpr1, const SMTExpr& SetExpr2) override;
        virtual SMTExpr CreateSetInterExpr(const SMTExpr& SetExpr1, const SMTExpr& SetExpr2) override;
        virtual SMTExpr CreateSetDiffExpr(const SMTExpr& SetExpr1, const SMTExpr& SetExpr2) override;
        virtual SMTExpr CreateSetComplementExpr(const SMTExpr& SetExpr) override;
        virtual SMTExpr CreateSetIsMemberExpr(const SMTExpr& SetExpr, const SMTExpr& ElemExpr) override;
        virtual SMTExpr CreateSetIsSubsetExpr(const SMTExpr& SetExpr1, const SMTExpr& SetExpr2) override;

        virtual SMTExpr CreateStoreExpr(const SMTExpr& ArrayExpr, const SMTExpr& IndexExpr,
                                        const SMTExpr& ValueExpr) override;
        virtual SMTExpr CreateSelectExpr(const SMTExpr& ArrayExpr, const SMTExpr& IndexExpr) override;

        // Assertion methods
        virtual void AssertFormula(const SMTExpr& Exp) override;
        
        // Query methods
        virtual SolveStatus CheckValidity(const SMTExpr& QueryExpr) override;
        virtual SolveStatus CheckSatisfiability(const SMTExpr& QueryExpr) override;
        
        // Model generation
        virtual void GetConcreteModel(const set<string>& RelevantVars, 
                                      SMTModel& Model,
                                      ESolver* Solver) override;
        // ESolver specific model generation
        virtual void GetConcreteModel(const set<string>& RelevantVars,
                                      SMTModel& Model,
                                      SMTConcreteValueModel& ConcModel,
                                      ESolver* Solver) override;
        
        virtual void GetAllAssertions(vector<SMTExpr>& Assertions) override;

        // Simplification
        virtual SMTExpr Simplify(const SMTExpr& Exp) override;

        // Identification
        virtual string GetSMTSolverInUse() const override;

        // hash routines for exprs
        virtual uint64 GetHash(const SMTExpr& Exp) override;

        // Stringification routine
        virtual string SMTExprToString(const SMTExpr& Exp) override;
    };

} /* End namespace */

#endif /* __ESOLVER_THEOREM_PROVER_HPP */


// 
// Z3TheoremProver.hpp ends here
