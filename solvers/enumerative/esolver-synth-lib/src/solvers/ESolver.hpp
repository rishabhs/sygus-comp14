// ESolver.hpp --- 
// 
// Filename: ESolver.hpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:50:38 2014 (-0500)
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


#if !defined __ESOLVER_ESOLVER_HPP
#define __ESOLVER_ESOLVER_HPP

#include "../common/ESolverOpts.hpp"
#include "../common/ESolverForwardDecls.hpp"
#include "../utils/UIDGenerator.hpp"
#include "../utils/TimeValue.hpp"
#include "../utils/MemStats.hpp"
#include "../utils/Logger.hpp"

namespace ESolver {

    /**
       This is the abstract base class for all
       solvers. It performs context management
       only, leaving the rest of the details
       abstract to be filled in by actual solvers
    */

    class ESolver
    {
    private:
        const ESFixedTypeBase* BoolType;
        const ESFixedTypeBase* IntType;
        UIDGenerator LetUIDGenerator;
        UIDGenerator FPUIDGenerator;
        vector<ESolverLogic*> LoadedLogics;
        BVLogic* LoadedBVLogic;
        
        // Utility methods
        inline void CheckOperatorRedeclaration(const string& OperatorName) const;
        inline void CheckOperatorRedeclaration(const string& OperatorName,
                                               const vector<const ESFixedTypeBase*>& TypeVector) const;
        // Perform common actions on creating a new type
        // create equality, ite, etc.
        inline void RegisterType(const ESFixedTypeBase* Type);

        // Builtin types and logic loader
        void AddBuiltins();

    protected:
        ESolverOpts Opts;
        TheoremProver* TP;
        
        // Managers
        ValueManager* ValMgr;
        ScopeManager* ScopeMgr;
        ExprManager* ExpMgr;
        ConstManager* ConstMgr;
        TypeManager* TypeMgr;

        const ConcreteValueBase* TrueValue;
        const ConcreteValueBase* FalseValue;
        TimeValue SolveStartTime;
        TimeValue SolveEndTime;
        MemStats SolveStartMemStats;
        MemStats SolveEndMemStats;
        
        Logger TheLogger;
        
    public:
        // Constructor
        ESolver(const ESolverOpts* Opts);
        // Destructor
        virtual ~ESolver();

        // Accessors
        TheoremProver* GetTP() const;

        // Context methods
        void Push();
        void Push(const string& ScopeName);
        void Pop();
        void DestroyScope(const string& ScopeName);
        void ReplaceScope(const string& ScopeName);

        // Type lookup and resolution
        const ESFixedTypeBase* LookupType(const string& TypeName) const;
        void BindType(const string& Name, const ESFixedTypeBase* Type);

        const OperatorBase* LookupOperatorNI(const string& Name) const;
        const FuncOperatorBase* LookupOperatorNI(const string& Name,
                                                 const vector<const ESFixedTypeBase*>& ArgTypes) const;

        const OperatorBase* LookupOperator(const string& Name) const;
        const FuncOperatorBase* LookupOperator(const string& Name,
                                               const vector<const ESFixedTypeBase*>& ArgTypes) const;

        // Type creation
        const ESFixedTypeBase* CreateBoolType() const;
        const ESFixedTypeBase* CreateIntType() const;

        const ESFixedTypeBase* CreateEnumType(const string& TypeName,
                                         const vector<string>& EnumConstructors);

        const ESFixedTypeBase* CreateBitVectorType(uint32 NumBits);

        // Value creation methods
        const ConcreteValueBase* CreateValue(const ESFixedTypeBase* Type, const string& ValueString);
        const ConcreteValueBase* CreateValue(const ESFixedTypeBase* Type, int64 TheValue);
        const ConcreteValueBase* CreateTrueValue();
        const ConcreteValueBase* CreateFalseValue();
        
        // Functions, variables and constant operators
        // Constant creation methods
        const ConstOperator* CreateConstant(const string& ConstantName,
                                            const ESFixedTypeBase* Type,
                                            const string& ConstantString);
        
        const ConstOperator* CreateConstant(const string& ConstantName,
                                            const ConcreteValueBase* ConstantValue);

        // Anonymous constants
        const ConstOperator* CreateConstant(const ConcreteValueBase* ConstantValue);

        // An interpreted function
        const InterpretedFuncOperator* CreateFunction(const string& FuncName,
                                                      const vector<const ESFixedTypeBase*>& DomainTypes,
                                                      const ESFixedTypeBase* RangeType,
                                                      SymbFunctorBase* SymbFunctor,
                                                      ConcFunctorBase* ConcFunctor,
                                                      bool Symmetric = false,
                                                      bool Builtin = false,
                                                      uint32 Cost = 1);

        // A macro
        const MacroOperator* CreateFunction(const string& FuncName,
                                            const vector<const ESFixedTypeBase*>& DomainTypes,
                                            const ESFixedTypeBase* RangeType,
                                            const Expression& MacroExpression,
                                            uint32 Cost = 1);

        // A function to be synthesized
        const SynthFuncOperator* CreateFunction(const string& FuncName,
                                                const vector<const ESFixedTypeBase*>& DomainTypes,
                                                const vector<string>& ParamNames,
                                                const ESFixedTypeBase* RangeType,
                                                Grammar* SynthGrammar);

        // Formal parameter ops for macros
        const FormalParamOperator* CreateFormalParamOperator(const string& ParamName,
                                                             const ESFixedTypeBase* Type,
                                                             uint32 Position);

        // Variable creation methods
        const UQVarOperator* CreateQuantifiedVariable(const string& VarName,
                                                      const ESFixedTypeBase* Type);
        
        // Let bound variable
        // WARNING: EACH call results in a new
        // variable being created, even if the same
        // Variable name is used!
        const LetBoundVarOperator* CreateLetBoundVariable(const string& Name,
                                                          const ESFixedTypeBase* Type);

        // For internal use ONLY!
        const AuxVarOperator* CreateAuxVariable(uint64 AuxID, const ESFixedTypeBase* Type);


        // Fresh let bound var expression
        Expression CreateFreshLetBoundVarExpression(const string& VarName,
                                                    const ESFixedTypeBase* Type);

        // Fresh formal param expresion
        Expression CreateFreshFormalParamExpression(const string& ParamName,
                                                    const ESFixedTypeBase* Type,
                                                    uint32 Position);

        Expression CreateAuxVarExpression(uint64 AuxID, const ESFixedTypeBase* Type);

        // Let expression
        Expression CreateLetExpression(const LetExpBindingMap& Bindings,
                                       Expression BoundInExpression);

        // Expression creation methods
        Expression CreateExpression(const OperatorBase* Op,
                                    const vector<Expression>& Children);

        Expression CreateExpression(const string& OperatorName,
                                    const vector<Expression>& Children);

        // Utilities for creating unary, binary and ternary expressions
        // We DO NOT want to use varargs, thus the specialization
        Expression CreateExpression(const string& OperatorName,
                                    const Expression& Exp1);
        Expression CreateExpression(const string& OperatorName,
                                    const Expression& Exp1, 
                                    const Expression& Exp2);
        Expression CreateExpression(const string& OperatorName,
                                    const Expression& Exp1, 
                                    const Expression& Exp2,
                                    const Expression& Exp3);

        // Constant expression creation
        Expression CreateExpression(const ConcreteValueBase* TheValue);
        Expression CreateExpression(const ESFixedTypeBase* Type,
                                    const string& ConstString);

        // Variable Expression creation methods
        Expression CreateExpression(const string& VariableName);
        Expression CreateExpression(const OperatorBase* OpInfo);

        Expression CreateTrueExpression();
        Expression CreateFalseExpression();


        // Builtin expression creation methods
        Expression CreateAndExpression(const Expression& Exp1, const Expression& Exp2);
        Expression CreateAndExpression(const vector<Expression>& Conjuncts);
        Expression CreateOrExpression(const Expression& Exp1, const Expression& Exp2);
        Expression CreateOrExpression(const vector<Expression>& Disjuncts);
        Expression CreateNotExpression(const Expression& Exp);
        Expression CreateImpliesExpression(const Expression& Antecedent,
                                                  const Expression& Consequent);
        Expression CreateIffExpression(const Expression& Exp1, const Expression& Exp2);

        // Callback for each enumerated expression.
        // Subclasses will need to implement this
        // special case for single function synthesis
        virtual CallbackStatus ExpressionCallBack(const GenExpressionBase* Exp, 
                                                  const ESFixedTypeBase* Type, 
                                                  uint32 ExpansionTypeID,
                                                  bool Complete,
                                                  uint32 EnumeratorIndex = 0) = 0;
        // For multifunction synthesis
        virtual CallbackStatus ExpressionCallBack(GenExpressionBase const* const* Exp,
                                                  ESFixedTypeBase const* const* Type, 
                                                  uint32 const* ExpansionTypeID) = 0;

        virtual SolutionMap Solve(const Expression& Constraint) = 0;
        void SetBudget(uint32 NewBudget);
        const ESolverOpts& GetOpts() const;
        Logger& GetLogger() const;

        // Clients are responsible for calling this function 
        // at reasonable interval to check for resource
        // limit expiration
        void CheckResourceLimits();
        // Clients should call this before a Solve
        void PreSolve();
        // Clients should call this after a Solve
        void PostSolve();

        // To be implemented by clients for abrupt end of solve
        virtual void EndSolve() = 0;
    };

} /* End namespace */

#endif /* __ESOLVER_ESOLVER_HPP */


// 
// ESolver.hpp ends here
