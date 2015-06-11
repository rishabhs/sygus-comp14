// ESolverForwardDecls.hpp ---
//
// Filename: ESolverForwardDecls.hpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:52:43 2014 (-0500)
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


#if !defined __ESOLVER_FORWARD_DECLS_HPP
#define __ESOLVER_FORWARD_DECLS_HPP

#include "ESolverCommon.hpp"
#include "../external/sparsehash/dense_hash_map"
#include "../external/sparsehash/dense_hash_set"
#include "../external/sparsehash/sparse_hash_map"
#include "../external/sparsehash/sparse_hash_set"

#define UNDEFINED_HASH_VALUE ((uint64)0)
#define INVALID_TYPE_ID (-1)
#define INVALID_ENUM_VALUE_ID (-1)

namespace ESolver {

    // Smart Ptrs
    template<typename T> class ESSmartPtr;
    template<typename T> class ConstESSmartPtr;

    // Functors
    class ConcFunctorBase;
    class SymbFunctorBase;
    class CompConcreteFunctor;
    class OperatorFunctorBase;
    class CompSymbolicFunctor;
    class OperatorTree;

    // Exceptions
    class ESException;

    // Values
    class ConcreteValueBase;
    class ValueManager;
    class Signature;
    class ConstManager;

    class ConcreteValueBasePtrHasher;
    class ConcreteValueBasePtrEquals;

    class SignaturePtrEquals;
    class SignaturePtrDeepEquals;
    class SignaturePtrHasher;

    // Contexts and scoping
    class ESContext;
    class ESolverScope;
    class ScopeManager;

    // Solvers
    class ESolver;
    class CEGSolver;
    class SynthLib2ESolver;

    class ESolverOpts;


    // Types
    class ESTypeBase;
    class ESTemplateTypeBase;
    class ESFixedTypeBase;
    class ESIntType;
    class ESBoolType;
    class ESRealType;
    class ESSubrangeType;
    class ESEnumType;
    class ESBVTypeTemplate;
    class ESBVType;
    class ESArrayTypeTemplate;
    class ESArrayType;
    class ESSetTypeTemplate;
    class ESSetType;
    class ESFunctionTypeTemplate;
    class ESFunctionType;

    class TypePtrHasher;
    class TypePtrEquals;

    class TypeManager;

    // Operators and functions
    class OperatorBase;
    class VarOperatorBase;
    class UQVarOperator;
    class LetBoundVarOperator;
    class AuxVarOperator;
    class FormalParamOperator;
    class FuncOperatorBase;
    class ConstOperator;
    class UninterpretedFuncOperator;
    class InterpretedFuncOperator;
    class SynthFuncOperator;
    class MacroOperator;

    // Loggers
    class Logger;

    // UID Generators
    class UIDGenerator;

    // Expressions
    class UserExpressionBase;
    class UserVarExpressionBase;
    class UserUQVarExpression;
    class UserAuxVarExpression;
    class UserFormalParamExpression;
    class UserLetBoundVarExpression;
    class UserLetExpression;
    class UserFuncExpressionBase;
    class UserInterpretedFuncExpression;
    class UserConstExpression;
    class UserSynthFuncExpression;

    typedef ConstESSmartPtr<UserExpressionBase> Expression;

    class ExprManager;

    typedef map<Expression, Expression> LetExpBindingMap;

    class GenExpressionBase;
    class GenFPExpression;
    class GenLetVarExpression;
    class GenConstExpression;
    class GenLetExpression;
    class GenFuncExpression;

    // Visitors
    class ExpressionVisitorBase;
    class SpecCheckVisitor;
    class VarGatherer;
    class SpecRewriter;

    // Hashers and Equality
    class TypeHasher;
    class TypePtrHasher;
    class TypeEquals;
    class TypePtrEquals;
    class GNCostPairHasher;
    class GNCostPairPtrHasher;
    class GNCostPairEquals;
    class GNCostPairPtrEquals;
    class ExpressionHasher;
    class ExpressionEquals;

    // SMT solver wrappers
    class TheoremProver;
    class Z3Type;
    class Z3Expr;
    class Z3Object;
    class Z3Model;
    class Z3Sort;
    class Z3TheoremProver;

    // Logics;
    class ESolverLogic;
    class BVLogic;
    class LIALogic;

    // Evaluation
    class EvalRule;
    class ConcreteEvaluator;

    typedef map<string, SMTExpr> SMTModel;
    typedef map<string, const ConcreteValueBase*> SMTConcreteValueModel;


    template<typename T> class TLVec;

    // Typedefs for smart ptrs, etc.
    typedef unordered_set<Expression, ExpressionHasher, ExpressionEquals> ExpressionSet;

    typedef unordered_set<const ConcreteValueBase*, ConcreteValueBasePtrHasher,
                          ConcreteValueBasePtrEquals> ConcreteValueSet;

    typedef TLVec<const GenExpressionBase> GenExpTLVec;

    typedef unordered_set<Signature*, SignaturePtrHasher, SignaturePtrDeepEquals> SigSetType;

    // Grammar Related classes
    class Grammar;
    class GrammarNode;
    class GrammarNonTerminal;
    class GrammarVarBase;
    class GrammarFPVar;
    class GrammarLetVar;
    class GrammarConst;
    class GrammarExpansion;

    // Grammar enumerators
    class EnumeratorBase;
    class CFGEnumerator;

    // Pairs and tuples
    class GNCostPair;

    // Typedefs for IDs
    typedef uint64 EnumValueID;
    typedef uint64 TypeID;

    // Variable map
    typedef ConcreteValueBase const* const* VariableMap;
    typedef ConcreteValueBase const* const* EvalMap;
    typedef ConcreteValueBase const* const* LetBindingMap;
    typedef const uint32* ParameterMap;
    typedef const uint32* SubstMap;
    typedef GenExpressionBase const* const* ExpSubstMap;

    // Substitution maps for SMTfication
    typedef SMTExpr const* SubstitutionMap;

    // Solutions
    typedef vector<vector<pair<const SynthFuncOperator*, Expression>>> SolutionMap;

    // Indicates that an exception occurred during
    // concrete evaluation
    extern bool ConcreteException;
    // Indicates that an expression was partial
    // and could not be evaluated. This is for
    // distinguishability purposes. A partial
    // expression is by definition distinguishable
    // from everything else. Because we simply do not
    // know what kind of bindings it will be used with
    extern bool PartialExpression;

    extern bool TimeOut;
    extern bool MemOut;

    // Logger
    extern Logger TheLogger;

    /*
       This is the  the status returned by the
       Solver to the enumerator on each callback to the solver
       by the enumerator, i.e., for each expression enumerated by
       the enumerator
    */

    enum CallbackStatus {
        NONE_STATUS = 0,
        DELETE_EXPRESSION = 1,
        STOP_ENUMERATION = 2,
        RESTART_ENUMERATION = 4,
        // Padding to ensure that this is a 32 bit value
        INVALID_STATUS = (1 << 30)
    };

} /* End namespace */

#endif /* __ESOLVER_FORWARD_DECLS_HPP */


//
// ESolverForwardDecls.hpp ends here
