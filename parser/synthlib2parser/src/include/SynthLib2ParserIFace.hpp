/*
Copyright (c) 2013,
Abhishek Udupa,
Mukund Raghothaman,
The University of Pennsylvania

All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

1. Redistributions of source code must retain the above copyright
notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright
notice, this list of conditions and the following disclaimer in the
documentation and/or other materials provided with the distribution.

3. Neither the name of the copyright holder nor the names of its
contributors may be used to endorse or promote products derived from
this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/

#if !defined __SYNTH_LIB2_PARSER_IFACE_H
#define __SYNTH_LIB2_PARSER_IFACE_H

#include <string>
#include <utility>
#include <vector>
#include <functional>
#include "SynthLib2ParserCommon.hpp"
#include "SynthLib2ParserFwd.hpp"

namespace SynthLib2Parser {

    class SourceLocation
    {
    private:
        i32 LineNum;
        i32 ColNum;

    public:
        SourceLocation(i32 LineNum, i32 ColNum);
        ~SourceLocation();
        SourceLocation(const SourceLocation& Other);
        SourceLocation& operator = (const SourceLocation& Other);

        i32 GetLineNum() const;
        i32 GetColNum() const;

        string ToString() const;

        static SourceLocation None;
    };

    class ASTBase
    {
    protected:
        SourceLocation Location;

    public:
        ASTBase(const SourceLocation& Location);
        virtual ~ASTBase();

        // Accessors
        const SourceLocation& GetLocation() const;

        // Abstract methods
        virtual void Accept(ASTVisitorBase* Visitor) const = 0;
        virtual ASTBase* Clone() const = 0;
    };

    class ArgSortPair : public ASTBase
    {
    private:
        string Name;
        const SortExpr* Sort;

    public:
        ArgSortPair(const SourceLocation& Location,
                    const string& Name,
                    const SortExpr* Sort);
        virtual ~ArgSortPair();

        void Accept(ASTVisitorBase* Visitor) const override;
        ASTBase* Clone() const override;

        // Accessors
        const string& GetName() const;
        const SortExpr* GetSort() const;
    };

    // Commands
    class ASTCmd : public ASTBase
    {
    protected:
        ASTCmdKind CmdKind;

    public:
        ASTCmd(const SourceLocation& Location, ASTCmdKind CmdKind);
        virtual ~ASTCmd();

        // Accessors
        ASTCmdKind GetKind() const;
    };

    class CheckSynthCmd : public ASTCmd
    {
    public:
        CheckSynthCmd(const SourceLocation& Location);
        virtual ~CheckSynthCmd();

        virtual void Accept(ASTVisitorBase* Visitor) const override;
        virtual ASTBase* Clone() const override;
    };

    class SetLogicCmd : public ASTCmd
    {
    private:
        string LogicName;

    public:
        SetLogicCmd(const SourceLocation& Location,
                    const string& LogicName);
        virtual ~SetLogicCmd();

        virtual void Accept(ASTVisitorBase* Visitor) const override;
        virtual ASTBase* Clone() const override;

        // accessors
        const string& GetLogicName() const;
    };

    class FunDefCmd : public ASTCmd
    {
    private:
        string Symbol;
        ArgList Arguments;
        const SortExpr* Type;
        Term* Def;
        mutable SymbolTableScope* Scope;

    public:
        FunDefCmd(const SourceLocation& Location,
                  const string& FunSymbol,
                  const ArgList& FunArgs,
                  const SortExpr* FunType,
                  Term* FunDef,
                  SymbolTableScope* Scope);

        virtual ~FunDefCmd();
        virtual void Accept(ASTVisitorBase* Visitor) const override;
        virtual ASTBase* Clone() const override;

        // Accessors
        const string& GetFunName() const;
        const ArgList& GetArgs() const;
        const SortExpr* GetSort() const;
        Term* GetTerm() const;

        SymbolTableScope* GetScope() const;
        void SetScope(SymbolTableScope* Scope) const;
    };

    class FunDeclCmd : public ASTCmd
    {
    private:
        string Symbol;
        vector<const SortExpr*> ArgTypes;
        const SortExpr* Type;

    public:
        FunDeclCmd(const SourceLocation& Location,
                   const string& FunSymbol,
                   const vector<const SortExpr*>& ArgSorts,
                   const SortExpr* Sort);
        virtual ~FunDeclCmd();

        virtual void Accept(ASTVisitorBase* Visitor) const override;
        virtual ASTBase* Clone() const override;

        const string& GetFunName() const;
        const vector<const SortExpr*>& GetArgSorts() const;
        const SortExpr* GetSort() const;
    };

    class SynthFunCmd : public ASTCmd
    {
    private:
        string SynthFunName;
        ArgList Arguments;
        const SortExpr* FunType;
        vector<NTDef*> GrammarRules;
        mutable SymbolTableScope* Scope;

    public:
        SynthFunCmd(const SourceLocation& Location,
                    const string& Name,
                    const ArgList& Args,
                    const SortExpr* FunType,
                    const vector<NTDef*> GrammarRules,
                    SymbolTableScope* Scope);
        virtual ~SynthFunCmd();

        virtual void Accept(ASTVisitorBase* Visitor) const override;
        virtual ASTBase* Clone() const override;

        // accessors
        const string& GetFunName() const;
        const ArgList& GetArgs() const;
        const SortExpr* GetSort() const;
        const vector<NTDef*>& GetGrammarRules() const;
        void SetScope(SymbolTableScope* Scope) const;
        SymbolTableScope* GetScope() const;
    };

    class ConstraintCmd : public ASTCmd
    {
    private:
        Term* TheTerm;

    public:
        ConstraintCmd(const SourceLocation& Location,
                      Term* TheTerm);
        virtual ~ConstraintCmd();

        virtual void Accept(ASTVisitorBase* Visitor) const override;
        virtual ASTBase* Clone() const override;

        // accessors
        Term* GetTerm() const;
    };

    class SortDefCmd : public ASTCmd
    {
    private:
        string Symbol;
        const SortExpr* Expr;

    public:
        SortDefCmd(const SourceLocation& Location,
                   const string& Symbol,
                   const SortExpr* TheSortExpr);
        virtual ~SortDefCmd();

        virtual void Accept(ASTVisitorBase* Visitor) const override;
        virtual ASTBase* Clone() const override;

        // accessors
        const string& GetName() const;
        const SortExpr* GetSortExpr() const;
    };

    class SetOptsCmd : public ASTCmd
    {
    private:
        vector<pair<string, string> > Opts;

    public:
        SetOptsCmd(const SourceLocation& Location,
                   const vector<pair<string, string> >& Opts);
        virtual ~SetOptsCmd();

        virtual void Accept(ASTVisitorBase* Visitor) const override;
        virtual ASTBase* Clone() const override;

        // accessors
        const vector<pair<string, string> >& GetOpts() const;
    };

    class VarDeclCmd : public ASTCmd
    {
    private:
        string VarName;
        const SortExpr* VarType;

    public:
        VarDeclCmd(const SourceLocation& Location,
                   const string& VarName,
                   const SortExpr* VarType);
        virtual ~VarDeclCmd();

        virtual void Accept(ASTVisitorBase* Visitor) const override;
        virtual ASTBase* Clone() const override;

        // accessors
        const string& GetName() const;
        const SortExpr* GetSort() const;
    };

    class SortExpr : public ASTBase
    {
    private:
        SortKind Kind;

    public:
        SortExpr(const SourceLocation& Location,
                 SortKind Kind);

        virtual ~SortExpr();
        SortKind GetKind() const;

        virtual bool Equals(const SortExpr& Other) const = 0;
        virtual string ToMangleString() const = 0;
        virtual u32 Hash() const = 0;
    };

    class IntSortExpr : public SortExpr
    {
    public:
        IntSortExpr(const SourceLocation& Location);
        IntSortExpr();
        virtual ~IntSortExpr();

        virtual bool Equals(const SortExpr& Other) const override;
        virtual void Accept(ASTVisitorBase* Visitor) const override;
        virtual ASTBase* Clone() const override;
        virtual string ToMangleString() const override;
        virtual u32 Hash() const override;
    };

    class BVSortExpr : public SortExpr
    {
    private:
        u32 Size;
    public:
        BVSortExpr(const SourceLocation& Location,
                   u32 Size);
        BVSortExpr(u32 Size);
        virtual ~BVSortExpr();

        virtual bool Equals(const SortExpr& Other) const override;
        virtual void Accept(ASTVisitorBase* Visitor) const override;
        virtual ASTBase* Clone() const override;
        virtual string ToMangleString() const override;
        virtual u32 Hash() const override;
        // accessors
        u32 GetSize() const;
    };

    class NamedSortExpr : public SortExpr
    {
    private:
        string Name;

    public:
        NamedSortExpr(const SourceLocation& Location,
                      const string& Name);
        NamedSortExpr(const string& Name);
        virtual ~NamedSortExpr();
        virtual bool Equals(const SortExpr& Other) const override;
        virtual void Accept(ASTVisitorBase* Visitor) const override;
        virtual ASTBase* Clone() const override;
        virtual string ToMangleString() const override;
        const string& GetName() const;
        virtual u32 Hash() const override;
    };

    class ArraySortExpr : public SortExpr
    {
    private:
        const SortExpr* DomainSort;
        const SortExpr* RangeSort;

    public:
        ArraySortExpr(const SourceLocation& Location,
                      const SortExpr* DomainSort,
                      const SortExpr* RangeSort);
        ArraySortExpr(const SortExpr* DomainSort, const SortExpr* RangeSort);
        virtual ~ArraySortExpr();

        virtual bool Equals(const SortExpr& Other) const override;
        virtual void Accept(ASTVisitorBase* Visitor) const override;
        virtual ASTBase* Clone() const override;
        virtual string ToMangleString() const override;

        // accessors
        const SortExpr* GetDomainSort() const;
        const SortExpr* GetRangeSort() const;
        virtual u32 Hash() const override;
    };

    class RealSortExpr : public SortExpr
    {
    public:
        RealSortExpr(const SourceLocation& Location);
        RealSortExpr();
        virtual ~RealSortExpr();

        virtual bool Equals(const SortExpr& Other) const override;
        virtual void Accept(ASTVisitorBase* Visitor) const override;
        virtual ASTBase* Clone() const override;
        virtual string ToMangleString() const override;
        virtual u32 Hash() const override;
    };

    class FunSortExpr : public SortExpr
    {
    private:
        vector<const SortExpr*> ArgSorts;
        const SortExpr* RetSort;

    public:
        FunSortExpr(const SourceLocation& Location,
                    const vector<const SortExpr*>& ArgSorts,
                    const SortExpr* RetSort);
        FunSortExpr(const vector<const SortExpr*>& ArgSorts,
                    const SortExpr* RetSort);

        virtual ~FunSortExpr();

        virtual bool Equals(const SortExpr& Other) const override;
        virtual void Accept(ASTVisitorBase* Visitor) const override;
        virtual ASTBase* Clone() const override;
        virtual string ToMangleString() const override;

        // Accessors
        const vector<const SortExpr*>& GetArgSorts() const;
        const SortExpr* GetRetSort() const;
        virtual u32 Hash() const override;
    };

    class BoolSortExpr : public SortExpr
    {
    public:
        BoolSortExpr(const SourceLocation& Location);
        BoolSortExpr();
        virtual ~BoolSortExpr();

        virtual bool Equals(const SortExpr& Other) const override;
        virtual void Accept(ASTVisitorBase* Visitor) const override;
        virtual ASTBase* Clone() const override;
        virtual string ToMangleString() const override;
        virtual u32 Hash() const override;
    };

    class EnumSortExpr : public SortExpr
    {
    private:
        mutable string EnumSortName;
        const vector<string> EnumSortConstructorVec;
        const set<string> EnumSortConstructorSet;

    public:
        EnumSortExpr(const SourceLocation& Location,
                     const string& EnumSortName,
                     const vector<string>& EnumConstructors);
        EnumSortExpr(const SourceLocation& Location,
                     const vector<string>& EnumConstructors);
        virtual ~EnumSortExpr();

        virtual bool Equals(const SortExpr& Other) const override;
        virtual void Accept(ASTVisitorBase* Visitor) const override;
        virtual ASTBase* Clone() const override;
        virtual string ToMangleString() const override;
        virtual u32 Hash() const override;

        // accessors
        const vector<string>& GetConstructors() const;
        const string& GetEnumSortName() const;
        void SetEnumSortName(const string& Name) const;
        bool IsConstructorValid(const string& ConstructorName) const;
    };

    class Literal : public ASTBase
    {
    private:
        string LiteralString;
        SortExpr* LiteralSort;

    public:
        Literal(const SourceLocation& Location,
                const string& Constructor,
                SortExpr* Sort);

        virtual ~Literal();

        virtual void Accept(ASTVisitorBase* Visitor) const override;
        virtual ASTBase* Clone() const override;

        const SortExpr* GetSort(SymbolTable* SymTab) const;
        const string& GetLiteralString() const;
    };

    class Term : public ASTBase
    {
    private:
        TermKind Kind;

    public:
        Term(const SourceLocation& Location, TermKind Kind);

        virtual ~Term();

        TermKind GetKind() const;
        virtual const SortExpr* GetTermSort(SymbolTable* SymTab) const = 0;
    };

    class FunTerm : public Term
    {
    private:
        string FunName;
        vector<Term*> Args;

    public:
        FunTerm(const SourceLocation& Location,
                const string& FunName,
                const vector<Term*>& Args);
        virtual ~FunTerm();

        virtual void Accept(ASTVisitorBase* Visitor) const override;
        virtual ASTBase* Clone() const override;
        virtual const SortExpr* GetTermSort(SymbolTable* SymTab) const override;

        // accessors
        const string& GetFunName() const;
        const vector<Term*>& GetArgs() const;
    };

    class LiteralTerm : public Term
    {
    private:
        Literal* TheLiteral;

    public:
        LiteralTerm(const SourceLocation& Location,
                    Literal* TheLiteral);
        virtual ~LiteralTerm();

        virtual void Accept(ASTVisitorBase* Visitor) const override;
        virtual ASTBase* Clone() const override;
        virtual const SortExpr* GetTermSort(SymbolTable* SymTab) const override;

        // accessors
        Literal* GetLiteral() const;
    };

    class SymbolTerm : public Term
    {
    private:
        string TheSymbol;

    public:
        SymbolTerm(const SourceLocation& Location,
                   const string& TheSymbol);
        virtual ~SymbolTerm();

        virtual void Accept(ASTVisitorBase* Visitor) const override;
        virtual ASTBase* Clone() const override;
        virtual const SortExpr* GetTermSort(SymbolTable* SymTab) const override;

        const string& GetSymbol() const;
    };

    class LetBindingTerm : public ASTBase
    {
    private:
        const string VarName;
        const SortExpr* VarSort;
        Term* BoundToTerm;

    public:
        LetBindingTerm(const SourceLocation& Location,
                       const string& VarName,
                       const SortExpr* VarSort,
                       Term* BoundToTerm);
        virtual ~LetBindingTerm();

        void Accept(ASTVisitorBase* Visitor) const override;
        ASTBase* Clone() const override;

        // Accessors
        const string& GetVarName() const;
        const SortExpr* GetVarSort() const;
        Term* GetBoundToTerm() const;
    };

    class LetTerm : public Term
    {
    private:
        vector<LetBindingTerm*> Bindings;
        Term* BoundInTerm;
        mutable SymbolTableScope* Scope;

    public:
        LetTerm(const SourceLocation& Location,
                const vector<LetBindingTerm*>& Bindings,
                Term* BoundInTerm,
                SymbolTableScope* Scope);
        virtual ~LetTerm();

        virtual void Accept(ASTVisitorBase* Visitor) const override;
        virtual ASTBase* Clone() const override;
        virtual const SortExpr* GetTermSort(SymbolTable* SymTab) const override;

        // Accessors
        const vector<LetBindingTerm*>& GetBindings() const;
        Term* GetBoundInTerm() const;
        void SetScope(SymbolTableScope* Scope) const;
        SymbolTableScope* GetScope() const;
    };

    // TODO: uggh, this code is similar to Term, consider refactoring
    class GTerm : public ASTBase
    {
    private:
        GTermKind Kind;

    public:
        GTerm(const SourceLocation& Location,
              GTermKind Kind);
        virtual ~GTerm();

        GTermKind GetKind() const;
        virtual const SortExpr* GetTermSort(SymbolTable* SymTab) const = 0;
    };

    class SymbolGTerm : public GTerm
    {
    private:
        string TheSymbol;

    public:
        SymbolGTerm(const SourceLocation& Location,
                    const string& TheSymbol);
        virtual ~SymbolGTerm();

        virtual void Accept(ASTVisitorBase* Visitor) const override;
        virtual ASTBase* Clone() const override;
        virtual const SortExpr* GetTermSort(SymbolTable* SymTab) const override;

        // Accessors
        const string& GetSymbol() const;
    };

    class FunGTerm : public GTerm
    {
    private:
        string FunName;
        vector<GTerm*> Args;

    public:
        FunGTerm(const SourceLocation& Location,
                 const string& FunName,
                 const vector<GTerm*>& Args);
        virtual ~FunGTerm();

        virtual void Accept(ASTVisitorBase* Visitor) const override;
        virtual ASTBase* Clone() const override;
        virtual const SortExpr* GetTermSort(SymbolTable* SymTab) const override;

        // Accessors
        const string& GetName() const;
        const vector<GTerm*>& GetArgs() const;
    };

    class LiteralGTerm : public GTerm
    {
    private:
        Literal* TheLiteral;

    public:
        LiteralGTerm(const SourceLocation& Location,
                     Literal* TheLiteral);
        virtual ~LiteralGTerm();

        virtual void Accept(ASTVisitorBase* Visitor) const override;
        virtual ASTBase* Clone() const override;
        virtual const SortExpr* GetTermSort(SymbolTable* SymTab) const override;

        Literal* GetLiteral() const;
    };

    class ConstantGTerm : public GTerm
    {
    private:
        const SortExpr* ConstantSort;

    public:
        ConstantGTerm(const SourceLocation& Location,
                      const SortExpr* Sort);
        virtual ~ConstantGTerm();

        virtual void Accept(ASTVisitorBase* Visitor) const override;
        virtual ASTBase* Clone() const override;
        virtual const SortExpr* GetTermSort(SymbolTable* SymTab) const override;

        // accessor
        const SortExpr* GetSort() const;
    };

    class VariableGTerm : public GTerm
    {
    private:
        const SortExpr* VariableSort;
        VariableKind Kind;

    public:
        VariableGTerm(const SourceLocation& Location,
                      const SortExpr* VariableSort,
                      VariableKind Kind);
        virtual ~VariableGTerm();

        virtual void Accept(ASTVisitorBase* Visitor) const override;
        virtual ASTBase* Clone() const override;
        virtual const SortExpr* GetTermSort(SymbolTable* SymTab) const override;

        // accessors
        const SortExpr* GetSort() const;
        VariableKind GetKind() const;
    };

    class LetBindingGTerm : public ASTBase
    {
    private:
        string VarName;
        const SortExpr* VarSort;
        GTerm* BoundToTerm;

    public:
        LetBindingGTerm(const SourceLocation& Location,
                        const string& VarName,
                        const SortExpr* VarSort,
                        GTerm* BoundToTerm);
        virtual ~LetBindingGTerm();

        void Accept(ASTVisitorBase* Visitor) const override;
        ASTBase* Clone() const override;

        const string& GetVarName() const;
        GTerm* GetBoundToTerm() const;
        const SortExpr* GetVarSort() const;
    };

    class LetGTerm : public GTerm
    {
    private:
        vector<LetBindingGTerm*> Bindings;
        GTerm* BoundInTerm;
        mutable SymbolTableScope* Scope;

    public:
        LetGTerm(const SourceLocation& Location,
                 const vector<LetBindingGTerm*>& Bindings,
                 GTerm* BoundInTerm,
                 SymbolTableScope* Scope);

        virtual ~LetGTerm();

        virtual void Accept(ASTVisitorBase* Visitor) const override;
        virtual ASTBase* Clone() const override;
        virtual const SortExpr* GetTermSort(SymbolTable* SymTab) const override;

        // accessors
        const vector<LetBindingGTerm*>& GetBindings() const;
        GTerm* GetBoundInTerm() const;
        void SetScope(SymbolTableScope* Scope) const;
        SymbolTableScope* GetScope() const;
    };

    class NTDef : public ASTBase
    {
    private:
        string Symbol;
        const SortExpr* Sort;
        vector<GTerm*> Expansions;

    public:
        NTDef(const SourceLocation& Location,
              const string& Symbol,
              const SortExpr* Sort,
              const vector<GTerm*>& Expansions);
        virtual ~NTDef();

        virtual void Accept(ASTVisitorBase* Visitor) const override;
        virtual ASTBase* Clone() const override;

        // accessors
        const string& GetName() const;
        const SortExpr* GetSort() const;
        const vector<GTerm*>& GetExpansions() const;
    };

    class Program : public ASTBase
    {
    private:
        vector<ASTCmd*> Cmds;

    public:
        Program(const vector<ASTCmd*>& Cmds);
        virtual ~Program();

        virtual void Accept(ASTVisitorBase* Visitor) const override;
        virtual ASTBase* Clone() const override;

        // accessors
        const vector<ASTCmd*>& GetCmds() const;
    };

    class ASTVisitorBase
    {
    private:
        string Name;
    public:
        ASTVisitorBase(const string& Name);
        virtual ~ASTVisitorBase();

        // Visit methods
        virtual void VisitProgram(const Program* Prog);

        virtual void VisitFunDefCmd(const FunDefCmd* Cmd);
        virtual void VisitFunDeclCmd(const FunDeclCmd* Cmd);
        virtual void VisitSynthFunCmd(const SynthFunCmd* Cmd);
        virtual void VisitSortDefCmd(const SortDefCmd* Cmd);
        virtual void VisitSetOptsCmd(const SetOptsCmd* Cmd);
        virtual void VisitVarDeclCmd(const VarDeclCmd* Cmd);
        virtual void VisitConstraintCmd(const ConstraintCmd* Cmd);
        virtual void VisitSetLogicCmd(const SetLogicCmd* Cmd);
        virtual void VisitCheckSynthCmd(const CheckSynthCmd* Cmd);
        virtual void VisitArgSortPair(const ArgSortPair* ASPair);

        virtual void VisitIntSortExpr(const IntSortExpr* Sort);
        virtual void VisitBVSortExpr(const BVSortExpr* Sort);
        virtual void VisitNamedSortExpr(const NamedSortExpr* Sort);
        virtual void VisitArraySortExpr(const ArraySortExpr* Sort);
        virtual void VisitRealSortExpr(const RealSortExpr* Sort);
        virtual void VisitFunSortExpr(const FunSortExpr* Sort);
        virtual void VisitBoolSortExpr(const BoolSortExpr* Sort);
        virtual void VisitEnumSortExpr(const EnumSortExpr* Sort);

        virtual void VisitLetBindingTerm(const LetBindingTerm* Binding);

        virtual void VisitFunTerm(const FunTerm* TheTerm);
        virtual void VisitLiteralTerm(const LiteralTerm* TheTerm);
        virtual void VisitSymbolTerm(const SymbolTerm* TheTerm);
        virtual void VisitLetTerm(const LetTerm* TheTerm);

        virtual void VisitLetBindingGTerm(const LetBindingGTerm* Binding);

        virtual void VisitFunGTerm(const FunGTerm* TheTerm);
        virtual void VisitLiteralGTerm(const LiteralGTerm* TheTerm);
        virtual void VisitSymbolGTerm(const SymbolGTerm* TheTerm);
        virtual void VisitLetGTerm(const LetGTerm* TheTerm);
        virtual void VisitConstantGTerm(const ConstantGTerm* TheTerm);
        virtual void VisitVariableGTerm(const VariableGTerm* TheTerm);

        virtual void VisitNTDef(const NTDef* Def);
        virtual void VisitLiteral(const Literal* TheLiteral);

        const string& GetName() const;
    };


    // Class definition for the synthlib2 parser
    class SynthLib2Parser
    {
    private:
        Program* TheProgram;
        SymbolTable* TheSymbolTable;

        // type-state variable :-(
        bool ParseComplete;

    public:
        SynthLib2Parser();
        ~SynthLib2Parser();

        // The main parse action
        void operator () (const string& Filename, bool Pedantic = false);
        void operator () (FILE* Handle, bool Pedantic = false);

        // Accessors
        Program* GetProgram() const;
        SymbolTable* GetSymbolTable() const;
    };

    // General vector of AST cloner
    template<typename T>
    static inline vector<T> CloneVector(const vector<T>& Vec)
    {
        const u32 NumElems = Vec.size();
        vector<T> Retval(NumElems);

        for(u32 i = 0; i < NumElems; ++i) {
            Retval[i] = static_cast<T>(Vec[i]->Clone());
        }
        return Retval;
    }



} /* End namespace */

#endif /* __SYNTH_LIB2_PARSER_IFACE_H */
