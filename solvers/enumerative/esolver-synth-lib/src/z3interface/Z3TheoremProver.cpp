// Z3TheoremProver.cpp ---
//
// Filename: Z3TheoremProver.cpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:52:58 2014 (-0500)
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


#include "Z3TheoremProver.hpp"
#include "../exceptions/ESException.hpp"
#include "../solvers/ESolver.hpp"
#include "../descriptions/ESType.hpp"
#include <boost/functional/hash.hpp>
#include "Z3Objects.hpp"
#include "../external/spookyhash/SpookyHash.hpp"
#include <boost/lexical_cast.hpp>
#include "../descriptions/Operators.hpp"

namespace ESolver {

    // The Z3 error handler
    void Z3ErrorHandler(Z3_context TheContext, Z3_error_code Code)
    {
        switch(Code) {
        case Z3_MEMOUT_FAIL:
            throw OutOfMemoryException("Out of memory");
        case Z3_EXCEPTION:
            throw Z3Exception(Z3_get_error_msg_ex(TheContext, Code));
        default:
            cerr << "Weird error from Z3: " << Code << endl;
        }
    }

    // Z3Dispatcher implementation
    Z3TheoremProver::Z3TheoremProver(const SMTSolverParams& Params)
        : TheModel(), TheParams(Params)
    {
        Z3_config Config = Z3_mk_config();
        for(SMTSolverParams::const_iterator it = Params.begin();
            it != Params.end(); ++it) {
            Z3_set_param_value(Config, (it->first).c_str(), (it->second).c_str());
        }

        // Add model completion if not already done
        Z3_set_param_value(Config, "MODEL", "true");
        Z3_set_param_value(Config, "MODEL_COMPLETION", "true");

        TheContext = Z3_mk_context_rc(Config);
        Z3_del_config(Config);

        TheSolver = Z3_mk_solver(TheContext);
        Z3_solver_inc_ref(TheContext, TheSolver);

        // Register the error handler
        Z3_set_error_handler(TheContext, Z3ErrorHandler);

        BoolType = Z3Sort(TheContext, Z3_mk_bool_sort(TheContext));
        IntType = Z3Sort(TheContext, Z3_mk_int_sort(TheContext));
    }

    Z3TheoremProver::~Z3TheoremProver()
    {
        for (auto const& ConsFuncDecl : EnumConstructorToConsFuncMap) {
            Z3_dec_ref(TheContext, Z3_func_decl_to_ast(TheContext, ConsFuncDecl.second));
        }
        for (auto const& TestFuncDecl : EnumConstructorToTestFuncMap) {
            Z3_dec_ref(TheContext, Z3_func_decl_to_ast(TheContext, TestFuncDecl.second));
        }
        BoolType = SMTType();
        IntType = SMTType();
        TheModel = Z3Model();
        Z3_solver_dec_ref(TheContext, TheSolver);
        Z3_del_context(TheContext);
    }

    void Z3TheoremProver::Push()
    {
        Z3_solver_push(TheContext, TheSolver);
    }

    void Z3TheoremProver::Pop(uint32 NumContexts)
    {
        Z3_solver_pop(TheContext, TheSolver, NumContexts);
    }

    SMTType Z3TheoremProver::CreateEnumType(const string& TypeName,
                                            const vector<string>& Constructors)
    {
        // Qualify the constructors with the type name
        vector<string> QConstructors;
        for (auto const& Const : Constructors) {
            QConstructors.push_back(TypeName + "::" + Const);
        }
        // Create the symbol for the name
        Z3_symbol TypeNameSymbol = Z3_mk_string_symbol(TheContext, TypeName.c_str());
        const uint32 NumConstructors = QConstructors.size();
        // Create the symbols for the enum constructors
        Z3_symbol* EnumConstSymbols = (Z3_symbol*)calloc(NumConstructors, sizeof(Z3_symbol));
        for (uint32 i = 0; i < NumConstructors; ++i) {
            EnumConstSymbols[i] = Z3_mk_string_symbol(TheContext, QConstructors[i].c_str());
        }
        // Allocate space for the returned func_decls
        Z3_func_decl* EnumConsFuncDecls = (Z3_func_decl*)calloc(NumConstructors, sizeof(Z3_func_decl));
        Z3_func_decl* EnumTestFuncDecls = (Z3_func_decl*)calloc(NumConstructors, sizeof(Z3_func_decl));

        // Create the enum type
        Z3_sort EnumSortRaw = Z3_mk_enumeration_sort(TheContext, TypeNameSymbol,
                                                     NumConstructors, EnumConstSymbols,
                                                     EnumConsFuncDecls, EnumTestFuncDecls);

        // Increment the ref counts of the func decls immediately
        for (uint32 i = 0; i < NumConstructors; ++i) {
            Z3_inc_ref(TheContext, Z3_func_decl_to_ast(TheContext, EnumConsFuncDecls[i]));
            Z3_inc_ref(TheContext, Z3_func_decl_to_ast(TheContext, EnumTestFuncDecls[i]));
        }

        // Make the entries in the map
        for (uint32 i = 0; i < NumConstructors; ++i) {
            EnumConstructorToConsFuncMap[QConstructors[i]] = EnumConsFuncDecls[i];
            EnumConstructorToTestFuncMap[QConstructors[i]] = EnumTestFuncDecls[i];
        }

        Z3Sort Retval(TheContext, EnumSortRaw);
        // Free all allocated blocks before returning
        free(EnumConsFuncDecls);
        free(EnumTestFuncDecls);
        free(EnumConstSymbols);

        return Retval;
    }

    SMTType Z3TheoremProver::CreateSetType(const SMTType& ElementType)
    {
        return Z3Sort(TheContext, Z3_mk_set_sort(TheContext, ElementType.Sort));
    }

    SMTType Z3TheoremProver::CreateBVType(uint32 NumBits)
    {
        return Z3Sort(TheContext, Z3_mk_bv_sort(TheContext, NumBits));
    }

    SMTType Z3TheoremProver::CreateRealType()
    {
        return Z3Sort(TheContext, Z3_mk_real_sort(TheContext));
    }

    SMTType Z3TheoremProver::CreateArrayType(const SMTType& IndexType, const SMTType& ElementType)
    {
        return Z3Sort(TheContext, Z3_mk_array_sort(TheContext, IndexType.Sort, ElementType.Sort));
    }

    SMTType Z3TheoremProver::CreateIntType()
    {
        return IntType;
    }

    SMTType Z3TheoremProver::CreateBoolType()
    {
        return BoolType;
    }

    SMTExpr Z3TheoremProver::CreateIntConstant(int64 TheValue)
    {
        return Z3Expr(TheContext, Z3_mk_int64(TheContext, TheValue, IntType.Sort));
    }

    SMTExpr Z3TheoremProver::CreateIntConstant(const string& IntValue)
    {
        istringstream istr(IntValue);
        int64 TheValue = boost::lexical_cast<int64>(IntValue);
        return CreateIntConstant(TheValue);
    }

    SMTExpr Z3TheoremProver::CreateBVConstant(uint64 BVValue, uint32 BVSize)
    {
        ostringstream sstr;
        uint64 ActualValue;
        if (BVSize < 64) {
            ActualValue = (BVValue & (((uint64)1 << BVSize) - 1));
        } else {
            ActualValue = BVValue;
        }

        sstr << ActualValue;
        Z3_sort BVSort = Z3_mk_bv_sort(TheContext, BVSize);
        Z3_inc_ref(TheContext, Z3_sort_to_ast(TheContext, BVSort));
        SMTExpr Retval = Z3Expr(TheContext, Z3_mk_numeral(TheContext, sstr.str().c_str(), BVSort));
        Z3_dec_ref(TheContext, Z3_sort_to_ast(TheContext, BVSort));
        return Retval;
    }

    SMTExpr Z3TheoremProver::CreateBVConstant(const string& BVValue)
    {
        // Convert the bit vector value to a decimal string
        uint64 NumValue = 0;
        const uint32 NumBits = BVValue.length();

        for(uint32 i = 0; i < NumBits; ++i) {
            NumValue <<= 1;
            if(BVValue[i] == '0') {
                NumValue |= 0;
            } else if(BVValue[i] == '1') {
                NumValue |= 1;
            } else {
                throw ValueException((string)"Error: The value \"" + BVValue +
                                     "\" is not a valid bitvector");
            }
        }
        return CreateBVConstant(NumValue, NumBits);
    }

    // Assumption: The enumvalue is already qualified
    SMTExpr Z3TheoremProver::CreateEnumConstant(const string& EnumValue)
    {
        auto it = EnumConstructorToConsFuncMap.find(EnumValue);
        if (it == EnumConstructorToConsFuncMap.end()) {
            throw Z3Exception((string)"Z3: Could not find constructor for EnumValue \"" + EnumValue + "\"");
        }
        return Z3Expr(TheContext, Z3_mk_app(TheContext, it->second, 0, nullptr));
    }

    SMTExpr Z3TheoremProver::CreateRealConstant(int32 Numerator, int32 Denominator)
    {
        return Z3Expr(TheContext, Z3_mk_real(TheContext, Numerator, Denominator));
    }

    SMTExpr Z3TheoremProver::CreateRealConstant(const string& RealValue)
    {
        return Z3Expr(TheContext, Z3_mk_numeral(TheContext, RealValue.c_str(), Z3_mk_real_sort(TheContext)));
    }

    SMTExpr Z3TheoremProver::CreateRealConstant(double RealValue)
    {
        ostringstream sstr;
        sstr << RealValue;
        return Z3Expr(TheContext, Z3_mk_numeral(TheContext, sstr.str().c_str(), Z3_mk_real_sort(TheContext)));
    }

    SMTExpr Z3TheoremProver::CreateVarExpr(const string& VarName, const SMTType& VarType)
    {
        Z3_symbol VarSymbol = Z3_mk_string_symbol(TheContext, VarName.c_str());
        return Z3Expr(TheContext, Z3_mk_const(TheContext, VarSymbol, VarType.Sort));
    }

    SMTExpr Z3TheoremProver::CreateOrExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        vector<SMTExpr> Disjuncts;
        Disjuncts.push_back(Exp1);
        Disjuncts.push_back(Exp2);
        return CreateOrExpr(Disjuncts);
    }

    SMTExpr Z3TheoremProver::CreateOrExpr(const vector<SMTExpr>& Disjuncts)
    {
        Z3_ast* DisjunctArray;
        SMTExpr Retval;
        const uint32 NumDisjuncts = Disjuncts.size();
        if(NumDisjuncts == 1) {
            return Disjuncts[0];
        }
        DisjunctArray = (Z3_ast*)calloc(NumDisjuncts, sizeof(Z3_ast));
        if(DisjunctArray == NULL) {
            throw OutOfMemoryException("Out of Memory!");
        }
        for(uint32 i = 0; i < NumDisjuncts; ++i) {
            DisjunctArray[i] = Disjuncts[i].AST;
        }

        Retval = Z3Expr(TheContext, Z3_mk_or(TheContext, NumDisjuncts, DisjunctArray));
        free(DisjunctArray);
        return Retval;
    }

    SMTExpr Z3TheoremProver::CreateAndExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        vector<SMTExpr> Disjuncts;
        Disjuncts.push_back(Exp1);
        Disjuncts.push_back(Exp2);
        return CreateAndExpr(Disjuncts);
    }

    SMTExpr Z3TheoremProver::CreateAndExpr(const vector<SMTExpr>& Conjuncts)
    {
        Z3_ast* ConjunctArray;
        SMTExpr Retval;
        const uint32 NumConjuncts = Conjuncts.size();
        if(NumConjuncts == 1) {
            return Conjuncts[0];
        }
        ConjunctArray = (Z3_ast*)calloc(NumConjuncts, sizeof(Z3_ast));
        if(ConjunctArray == NULL) {
            throw OutOfMemoryException("Out of Memory!");
        }
        for(uint32 i = 0; i < NumConjuncts; ++i) {
            ConjunctArray[i] = Conjuncts[i].AST;
        }

        Retval = Z3Expr(TheContext, Z3_mk_and(TheContext, NumConjuncts, ConjunctArray));
        free(ConjunctArray);
        return Retval;
    }

    SMTExpr Z3TheoremProver::CreateImpliesExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        return Z3Expr(TheContext, Z3_mk_implies(TheContext, Exp1.AST, Exp2.AST));
    }

    SMTExpr Z3TheoremProver::CreateIffExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        return Z3Expr(TheContext, Z3_mk_iff(TheContext, Exp1.AST, Exp2.AST));
    }

    SMTExpr Z3TheoremProver::CreateEQExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        return Z3Expr(TheContext, Z3_mk_eq(TheContext, Exp1.AST, Exp2.AST));
    }

    SMTExpr Z3TheoremProver::CreateNotExpr(const SMTExpr& Exp1)
    {
        return Z3Expr(TheContext, Z3_mk_not(TheContext, Exp1.AST));
    }

    SMTExpr Z3TheoremProver::CreateNegExpr(const SMTExpr& Exp1)
    {
        return Z3Expr(TheContext, Z3_mk_unary_minus(TheContext, Exp1.AST));
    }

    SMTExpr Z3TheoremProver::CreatePlusExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        Z3_ast* Args;
        SMTExpr Retval;
        Args = (Z3_ast*)calloc(2, sizeof(Z3_ast));
        if(Args == NULL) {
            throw OutOfMemoryException("Out of Memory!");
        }
        Args[0] = Exp1.AST;
        Args[1] = Exp2.AST;

        Retval = Z3Expr(TheContext, Z3_mk_add(TheContext, 2, Args));
        free(Args);
        return Retval;
    }

    SMTExpr Z3TheoremProver::CreateMinusExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        Z3_ast* Args;
        SMTExpr Retval;
        Args = (Z3_ast*)calloc(2, sizeof(Z3_ast));
        if(Args == NULL) {
            throw OutOfMemoryException("Out of Memory!");
        }
        Args[0] = Exp1.AST;
        Args[1] = Exp2.AST;

        Retval = Z3Expr(TheContext, Z3_mk_sub(TheContext, 2, Args));
        free(Args);
        return Retval;
    }

    SMTExpr Z3TheoremProver::CreateMulExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        Z3_ast* Args;
        SMTExpr Retval;
        Args = (Z3_ast*)calloc(2, sizeof(Z3_ast));
        if(Args == NULL) {
            throw OutOfMemoryException("Out of Memory!");
        }
        Args[0] = Exp1.AST;
        Args[1] = Exp2.AST;
        Retval = Z3Expr(TheContext, Z3_mk_mul(TheContext, 2, Args));
        free(Args);
        return Retval;
    }

    SMTExpr Z3TheoremProver::CreateDivExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        SMTExpr Retval;
        return Z3Expr(TheContext, Z3_mk_div(TheContext, Exp1.AST, Exp2.AST));
    }

    SMTExpr Z3TheoremProver::CreateTrueExpr()
    {
        return Z3Expr(TheContext, Z3_mk_true(TheContext));
    }

    SMTExpr Z3TheoremProver::CreateFalseExpr()
    {
        return Z3Expr(TheContext, Z3_mk_false(TheContext));
    }

    SMTExpr Z3TheoremProver::CreateITEExpr(const SMTExpr& Pred,
                                        const SMTExpr& IfExp,
                                        const SMTExpr& ElseExp)
    {
        return Z3Expr(TheContext, Z3_mk_ite(TheContext, Pred.AST,
                                            IfExp.AST, ElseExp.AST));
    }

    SMTExpr Z3TheoremProver::CreateLEExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        return Z3Expr(TheContext, Z3_mk_le(TheContext, Exp1.AST, Exp2.AST));
    }

    SMTExpr Z3TheoremProver::CreateLTExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        return Z3Expr(TheContext, Z3_mk_lt(TheContext, Exp1.AST, Exp2.AST));
    }

    SMTExpr Z3TheoremProver::CreateGEExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        return Z3Expr(TheContext, Z3_mk_ge(TheContext, Exp1.AST, Exp2.AST));
    }

    SMTExpr Z3TheoremProver::CreateGTExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        return Z3Expr(TheContext, Z3_mk_gt(TheContext, Exp1.AST, Exp2.AST));
    }

    SMTExpr Z3TheoremProver::CreateBVAndExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        return Z3Expr(TheContext, Z3_mk_bvand(TheContext, Exp1.AST, Exp2.AST));
    }

    SMTExpr Z3TheoremProver::CreateBVOrExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        return Z3Expr(TheContext, Z3_mk_bvor(TheContext, Exp1.AST, Exp2.AST));
    }

    SMTExpr Z3TheoremProver::CreateBVNotExpr(const SMTExpr& Exp1)
    {
        return Z3Expr(TheContext, Z3_mk_bvnot(TheContext, Exp1.AST));
    }

    SMTExpr Z3TheoremProver::CreateBVXorExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        return Z3Expr(TheContext, Z3_mk_bvxor(TheContext, Exp1.AST, Exp2.AST));
    }

    SMTExpr Z3TheoremProver::CreateBVRedOrExpr(const SMTExpr& Exp1)
    {
        return CreateITEExpr(CreateEQExpr(Z3Expr(TheContext, Z3_mk_bvredor(TheContext, Exp1.AST)),
                                          CreateBVConstant(1, 1)), CreateTrueExpr(), CreateFalseExpr());
    }

    SMTExpr Z3TheoremProver::CreateBVRedAndExpr(const SMTExpr& Exp1)
    {
        return CreateITEExpr(CreateEQExpr(Z3Expr(TheContext, Z3_mk_bvredand(TheContext, Exp1.AST)),
                                          CreateBVConstant(1, 1)), CreateTrueExpr(), CreateFalseExpr());
    }

    SMTExpr Z3TheoremProver::CreateBVSubExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        return Z3Expr(TheContext, Z3_mk_bvsub(TheContext, Exp1.AST, Exp2.AST));
    }

    SMTExpr Z3TheoremProver::CreateBVAddExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        return Z3Expr(TheContext, Z3_mk_bvadd(TheContext, Exp1.AST, Exp2.AST));
    }

    SMTExpr Z3TheoremProver::CreateBVSDivExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        return Z3Expr(TheContext, Z3_mk_bvsdiv(TheContext, Exp1.AST, Exp2.AST));
    }

    SMTExpr Z3TheoremProver::CreateBVUSDivExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        return Z3Expr(TheContext, Z3_mk_bvudiv(TheContext, Exp1.AST, Exp2.AST));
    }

    SMTExpr Z3TheoremProver::CreateBVSRemExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        return Z3Expr(TheContext, Z3_mk_bvsrem(TheContext, Exp1.AST, Exp2.AST));
    }

    SMTExpr Z3TheoremProver::CreateBVUSRemExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        return Z3Expr(TheContext, Z3_mk_bvurem(TheContext, Exp1.AST, Exp2.AST));
    }

    SMTExpr Z3TheoremProver::CreateBVSModExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        return Z3Expr(TheContext, Z3_mk_bvsmod(TheContext, Exp1.AST, Exp2.AST));
    }

    SMTExpr Z3TheoremProver::CreateBVMulExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        return Z3Expr(TheContext, Z3_mk_bvmul(TheContext, Exp1.AST, Exp2.AST));
    }

    SMTExpr Z3TheoremProver::CreateBVNegExpr(const SMTExpr& Exp1)
    {
        return Z3Expr(TheContext, Z3_mk_bvneg(TheContext, Exp1.AST));
    }

    SMTExpr Z3TheoremProver::CreateBVLShRExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        return Z3Expr(TheContext, Z3_mk_bvlshr(TheContext, Exp1.AST, Exp2.AST));
    }

    SMTExpr Z3TheoremProver::CreateBVAShRExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        return Z3Expr(TheContext, Z3_mk_bvashr(TheContext, Exp1.AST, Exp2.AST));
    }

    SMTExpr Z3TheoremProver::CreateBVShLExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        return Z3Expr(TheContext, Z3_mk_bvshl(TheContext, Exp1.AST, Exp2.AST));
    }

    SMTExpr Z3TheoremProver::CreateBVUSLEExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        return Z3Expr(TheContext, Z3_mk_bvule(TheContext, Exp1.AST, Exp2.AST));
    }

    SMTExpr Z3TheoremProver::CreateBVSLEExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        return Z3Expr(TheContext, Z3_mk_bvsle(TheContext, Exp1.AST, Exp2.AST));
    }

    SMTExpr Z3TheoremProver::CreateBVUSGEExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        return Z3Expr(TheContext, Z3_mk_bvuge(TheContext, Exp1.AST, Exp2.AST));
    }

    SMTExpr Z3TheoremProver::CreateBVSGEExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        return Z3Expr(TheContext, Z3_mk_bvsge(TheContext, Exp1.AST, Exp2.AST));
    }

    SMTExpr Z3TheoremProver::CreateBVUSLTExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        return Z3Expr(TheContext, Z3_mk_bvult(TheContext, Exp1.AST, Exp2.AST));
    }

    SMTExpr Z3TheoremProver::CreateBVSLTExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        return Z3Expr(TheContext, Z3_mk_bvslt(TheContext, Exp1.AST, Exp2.AST));
    }

    SMTExpr Z3TheoremProver::CreateBVUSGTExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        return Z3Expr(TheContext, Z3_mk_bvugt(TheContext, Exp1.AST, Exp2.AST));
    }

    SMTExpr Z3TheoremProver::CreateBVSGTExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        return Z3Expr(TheContext, Z3_mk_bvsgt(TheContext, Exp1.AST, Exp2.AST));
    }

    SMTExpr Z3TheoremProver::CreateBVToBoolExpr(const SMTExpr& Exp1)
    {
        return CreateBVRedOrExpr(Exp1);
    }

    SMTExpr Z3TheoremProver::GenBVToIntExpr(const SMTExpr& Expr, uint32 BitNum)
    {
        if(BitNum == 0) {
            return CreateITEExpr(CreateEQExpr(CreateBVExtractExpr(Expr, BitNum, BitNum),
                                                       CreateBVConstant("1")),
                                 CreateIntConstant((int64)1),
                                 CreateIntConstant((int64)0));
        } else {
            SMTExpr Rest = GenBVToIntExpr(Expr, BitNum - 1);
            SMTExpr ThisBit = CreateITEExpr(CreateEQExpr(CreateBVExtractExpr(Expr, BitNum, BitNum),
                                                         CreateBVConstant("1")),
                                            CreateIntConstant(((int64)1 << BitNum)),
                                            CreateIntConstant((int64)0));

            return CreatePlusExpr(ThisBit, Rest);
        }
    }

    SMTExpr Z3TheoremProver::CreateBVToSIntExpr(const SMTExpr& Exp1)
    {
        uint32 NumBits = Z3_get_bv_sort_size(TheContext, Z3_get_sort(TheContext, Exp1.AST));
        SMTExpr NegVal = GenBVToIntExpr(CreateBVNegExpr(Exp1), NumBits - 1);
        SMTExpr PosVal = GenBVToIntExpr(Exp1, NumBits - 1);
        SMTExpr Retval = CreateITEExpr(CreateEQExpr(CreateBVExtractExpr(Exp1, NumBits - 1, NumBits - 1),
                                                    CreateBVConstant("1")),
                                       CreateNegExpr(NegVal), PosVal);
        return Retval;
    }

    SMTExpr Z3TheoremProver::CreateBVToUSIntExpr(const SMTExpr& Exp1)
    {
        uint32 NumBits = Z3_get_bv_sort_size(TheContext, Z3_get_sort(TheContext, Exp1.AST));
        return Z3Expr(GenBVToIntExpr(Exp1, NumBits - 1));
    }

    SMTExpr Z3TheoremProver::CreateBVExtractExpr(const SMTExpr& Exp,
                                                 uint32 High, uint32 Low)
    {
        return Z3Expr(TheContext, Z3_mk_extract(TheContext, High, Low, Exp.AST));
    }

    SMTExpr Z3TheoremProver::CreateBVConcatExpr(const SMTExpr& Exp1, const SMTExpr& Exp2)
    {
        return Z3Expr(TheContext, Z3_mk_concat(TheContext, Exp1.AST, Exp2.AST));
    }

    SMTExpr Z3TheoremProver::CreateEmptySetExpr(const SMTType& ElementType)
    {
        return Z3Expr(TheContext, Z3_mk_empty_set(TheContext, ElementType.Sort));
    }

    SMTExpr Z3TheoremProver::CreateFullSetExpr(const SMTType& ElementType)
    {
        return Z3Expr(TheContext, Z3_mk_full_set(TheContext, ElementType.Sort));
    }

    SMTExpr Z3TheoremProver::CreateSetAddExpr(const SMTExpr& SetExpr, const SMTExpr& ElemExpr)
    {
        return Z3Expr(TheContext, Z3_mk_set_add(TheContext, SetExpr.AST, ElemExpr.AST));
    }

    SMTExpr Z3TheoremProver::CreateSetDelExpr(const SMTExpr& SetExpr, const SMTExpr& ElemExpr)
    {
        return Z3Expr(TheContext, Z3_mk_set_del(TheContext, SetExpr.AST, ElemExpr.AST));
    }

    SMTExpr Z3TheoremProver::CreateSetUnionExpr(const SMTExpr& SetExpr1, const SMTExpr& SetExpr2)
    {
        Z3_ast Args[2];
        Args[0] = SetExpr1.AST;
        Args[1] = SetExpr2.AST;
        return Z3Expr(TheContext, Z3_mk_set_union(TheContext, 2, Args));
    }

    SMTExpr Z3TheoremProver::CreateSetInterExpr(const SMTExpr& SetExpr1, const SMTExpr& SetExpr2)
    {
        Z3_ast Args[2];
        Args[0] = SetExpr1.AST;
        Args[1] = SetExpr2.AST;
        return Z3Expr(TheContext, Z3_mk_set_intersect(TheContext, 2, Args));
    }

    SMTExpr Z3TheoremProver::CreateSetDiffExpr(const SMTExpr& SetExpr1, const SMTExpr& SetExpr2)
    {
        return Z3Expr(TheContext, Z3_mk_set_difference(TheContext, SetExpr1.AST, SetExpr2.AST));
    }

    SMTExpr Z3TheoremProver::CreateSetComplementExpr(const SMTExpr& SetExpr)
    {
        return Z3Expr(TheContext, Z3_mk_set_complement(TheContext, SetExpr.AST));
    }

    SMTExpr Z3TheoremProver::CreateSetIsMemberExpr(const SMTExpr& SetExpr, const SMTExpr& ElemExpr)
    {
        return Z3Expr(TheContext, Z3_mk_set_member(TheContext, SetExpr.AST, ElemExpr.AST));
    }

    SMTExpr Z3TheoremProver::CreateSetIsSubsetExpr(const SMTExpr& SetExpr1, const SMTExpr& SetExpr2)
    {
        return Z3Expr(TheContext, Z3_mk_set_subset(TheContext, SetExpr1.AST, SetExpr2.AST));
    }

    SMTExpr Z3TheoremProver::CreateStoreExpr(const SMTExpr& ArrayExpr,
                                             const SMTExpr& IndexExpr,
                                             const SMTExpr& ValueExpr)
    {
        return Z3Expr(TheContext, Z3_mk_store(TheContext, ArrayExpr.AST, IndexExpr.AST, ValueExpr.AST));
    }

    SMTExpr Z3TheoremProver::CreateSelectExpr(const SMTExpr& ArrayExpr, const SMTExpr& IndexExpr)
    {
        return Z3Expr(TheContext, Z3_mk_select(TheContext, ArrayExpr.AST, IndexExpr.AST));
    }

    void Z3TheoremProver::AssertFormula(const SMTExpr& Exp)
    {
        Z3_solver_assert(TheContext, TheSolver, Exp.AST);
    }

    SolveStatus Z3TheoremProver::CheckValidity(const SMTExpr& QueryExpr)
    {
        // Z3 is a satisfiability checker. So we check for
        // unsat of the negation of the formula
        // If unsat then the formula is valid

        // delete any existing model if present
        TheModel = Z3Model();
        SMTExpr NotQE = CreateNotExpr(QueryExpr);
        Z3_solver_push(TheContext, TheSolver);

        Z3_solver_assert(TheContext, TheSolver, NotQE.AST);

        Z3_lbool Result = Z3_solver_check(TheContext, TheSolver);

        if(Result == Z3_L_FALSE) {
            Z3_solver_pop(TheContext, TheSolver, 1);
            return SOLVE_VALID;
        } else if(Result == Z3_L_TRUE) {
            TheModel = Z3Model(TheContext, Z3_solver_get_model(TheContext, TheSolver));
            Z3_solver_pop(TheContext, TheSolver, 1);
            return SOLVE_INVALID;
        } else {
            Z3_solver_pop(TheContext, TheSolver, 1);
            return SOLVE_UNKNOWN;
        }
    }

    SolveStatus Z3TheoremProver::CheckSatisfiability(const SMTExpr& QueryExpr)
    {
        TheModel = Z3Model();
        Z3_solver_push(TheContext, TheSolver);
        Z3_solver_assert(TheContext, TheSolver, QueryExpr.AST);
        Z3_lbool Result = Z3_solver_check(TheContext, TheSolver);

        if(Result == Z3_L_FALSE) {
            // We're unsat
            Z3_solver_pop(TheContext, TheSolver, 1);
            return SOLVE_UNSATISFIABLE;
        } else if(Result == Z3_L_TRUE) {
            TheModel = Z3Model(TheContext, Z3_solver_get_model(TheContext, TheSolver));
            Z3_solver_pop(TheContext, TheSolver, 1);
            return SOLVE_SATISFIABLE;
        } else {
            Z3_solver_pop(TheContext, TheSolver, 1);
            return SOLVE_UNKNOWN;
        }
    }

    void Z3TheoremProver::GetConcreteModel(const set<string>& RelevantVars,
                                           SMTModel& Model,
                                           ESolver* Solver)
    {
        if(TheModel.Model == NULL) {
            throw ModelGenException("Error: Model generation called for, but unable to!");
        }

        set<string>::const_iterator RelevantVarsEnd = RelevantVars.end();

        for(set<string>::const_iterator it = RelevantVars.begin(); it != RelevantVarsEnd; ++it) {
            const OperatorBase* OpInfo = Solver->LookupOperator(*it);
            const VarOperatorBase* VarOp = OpInfo->As<VarOperatorBase>();
            auto AuxVarOp = OpInfo->As<AuxVarOperator>();
            if(VarOp == NULL && AuxVarOp == NULL) {
                throw ModelGenException((string)"Error: Expected operator \"" + *it +
                                        "\" to be a variable");
            }

            const ESFixedTypeBase* Type = OpInfo->GetEvalType();

            Z3_symbol CurrentVarSymbol = Z3_mk_string_symbol(TheContext, OpInfo->GetName().c_str());
            Z3_ast CurrentVarExpr = Z3_mk_const(TheContext, CurrentVarSymbol,
                                                Type->GetSMTType().Sort);
            Z3_inc_ref(TheContext, CurrentVarExpr);
            Z3_ast CurrentVarEval = CurrentVarExpr;
            if(!Z3_model_eval(TheContext, TheModel.Model,
                              CurrentVarExpr, Z3_TRUE,
                              &CurrentVarEval)) {
                throw ModelGenException((string)"Error: Could not find a valuation for \"" +
                                        OpInfo->GetName() + "\" in the concrete model");
            }
            Z3_inc_ref(TheContext, CurrentVarEval);
            Z3_dec_ref(TheContext, CurrentVarExpr);
            SMTExpr CurVarEvalExpr = Z3Expr(TheContext, CurrentVarEval);
            Z3_dec_ref(TheContext, CurrentVarEval);
            Model[OpInfo->GetName()] = CurVarEvalExpr;
        }
    }

    static inline string ParseZ3BVString(const string& BVString,
                                         const ESFixedTypeBase* Type)
    {
        string NumString;
        string NumBitsString;
        string WorkString = BVString.substr(2, BVString.length() - 2);
        ostringstream sstr;

        uint32 i = 0;

        while(WorkString[i] != '[') {
            NumString += WorkString[i];
            i++;
        }

        i++;
        while(WorkString[i] != ']') {
            NumBitsString += WorkString[i];
            i++;
        }

        uint32 NumBits = atoi(NumBitsString.c_str());

        assert(Type->As<ESBVType>()->GetSize() == NumBits);
        return NumString;
    }

    void Z3TheoremProver::GetConcreteModel(const set<string>& RelevantVars,
                                        SMTModel& Model,
                                        SMTConcreteValueModel& ConcModel,
                                        ESolver* Solver)
    {
        uint32 NumBits = 0, Shift = 0;
        int64 ModelValue = 0;
        GetConcreteModel(RelevantVars, Model, Solver);

        // Parse the concrete model into ConcreteValues
        SMTModel::iterator ModelEnd = Model.end();
        for(SMTModel::iterator it = Model.begin(); it != ModelEnd; ++it) {

            string ValueString;
            const OperatorBase* CurOp = Solver->LookupOperator(it->first);
            auto VarOp = CurOp->As<VarOperatorBase>();
            auto AuxVarOp = CurOp->As<AuxVarOperator>();

            if(VarOp == NULL && AuxVarOp == NULL) {
                throw ModelGenException((string)"Error: Expected operator \"" + it->first + "\" to be a variable");
            }

            const string& CurVarName = CurOp->GetName();
            const ESFixedTypeBase* Type = CurOp->GetEvalType();

            switch(Type->GetBaseType()) {
            case BaseTypeBool:
                ValueString = Z3_ast_to_string(TheContext, (it->second).AST);
                if(ValueString == "true") {
                    ConcModel[CurVarName] = Solver->CreateValue(Type, (int64)1);
                } else {
                    ConcModel[CurVarName] = Solver->CreateValue(Type, (int64)0);
                }
                break;

            case BaseTypeInt:
                ValueString = Z3_ast_to_string(TheContext, (it->second).AST);
                ConcModel[CurVarName] = Solver->CreateValue(Type, ValueString);
                break;

            case BaseTypeEnum:
                ValueString = Z3_ast_to_string(TheContext, (it->second).AST);
                ConcModel[CurVarName] = Solver->CreateValue(Type, ValueString);
                break;

            case BaseTypeBitVector:
                ValueString = Z3_ast_to_string(TheContext, (it->second).AST);
                ValueString = ParseZ3BVString(ValueString, Type);
                NumBits = Type->As<ESBVType>()->GetSize();
                Shift = 64 - NumBits;
                ModelValue = (int64)strtoll(ValueString.c_str(), NULL, 10);
                ModelValue = (ModelValue << Shift) >> Shift;
                ModelValue = ModelValue & (((uint64)1 << NumBits) - 1);
                ConcModel[CurVarName] = Solver->CreateValue(Type, ModelValue);
                break;

            default:
                throw InternalError((string)"Unhandled type in GetConcreteValue.\n" +
                                    "At: " + __FILE__ + ":" + to_string(__LINE__));
            }
        }
    }

    void Z3TheoremProver::GetAllAssertions(vector<SMTExpr>& Assertions)
    {
        Z3_ast_vector AssertionsASTVec = Z3_solver_get_assertions(TheContext, TheSolver);
        Z3_ast_vector_inc_ref(TheContext, AssertionsASTVec);
        const uint32 NumAssertions = Z3_ast_vector_size(TheContext, AssertionsASTVec);
        Assertions.clear();
        for(uint32 i = 0; i < NumAssertions; ++i) {
            Assertions.push_back(Z3Expr(TheContext, Z3_ast_vector_get(TheContext, AssertionsASTVec, i)));
        }
        return;
    }

    SMTExpr Z3TheoremProver::Simplify(const SMTExpr& Exp)
    {
        return Z3Expr(TheContext, Z3_simplify(TheContext, Exp.AST));
    }

    string Z3TheoremProver::GetSMTSolverInUse() const
    {
        return "Z3";
    }

    uint64 Z3TheoremProver::GetHash(const SMTExpr& Exp)
    {
        return Exp.Hash();
    }

    string Z3TheoremProver::SMTExprToString(const SMTExpr& Exp)
    {
        return Exp.ToString();
    }

} /* End namespace */


//
// Z3TheoremProver.cpp ends here
