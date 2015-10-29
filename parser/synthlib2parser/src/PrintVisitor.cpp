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

#include <PrintVisitor.hpp>

namespace SynthLib2Parser {

    PrintVisitor::PrintVisitor(ostream& Out)
        : ASTVisitorBase("PrintVisitor"), IndentLevel(0), Out(Out)
    {
        // Nothing here
    }

    PrintVisitor::~PrintVisitor()
    {
        Out.flush();
    }

    inline string PrintVisitor::GetIndent()
    {
        string Retval(IndentLevel * 4, ' ');
        return Retval;
    }

    void PrintVisitor::VisitProgram(const Program* Prog)
    {
        for(auto const& Cmd : Prog->GetCmds()) {
            Cmd->Accept(this);
        }
        Out.flush();
    }

    void PrintVisitor::VisitFunDefCmd(const FunDefCmd* Cmd)
    {
        Out << GetIndent() << "(define-fun " << Cmd->GetFunName() << " (";
        for(auto const& ASPair : Cmd->GetArgs()) {
            ASPair->Accept(this);
        }
        Out << ") ";
        Cmd->GetSort()->Accept(this);
        Out << endl;
        IndentLevel++;
        Out << GetIndent();
        Cmd->GetTerm()->Accept(this);
        Out << endl;
        IndentLevel--;
        Out << ")" << endl << endl;
    }

    void PrintVisitor::VisitFunDeclCmd(const FunDeclCmd* Cmd)
    {
        Out << GetIndent() << "(declare-fun " << Cmd->GetFunName() << " (";
        for(auto const& Sort : Cmd->GetArgSorts()) {
            Sort->Accept(this);
        }
        Out << ") ";
        Cmd->GetSort()->Accept(this);
        Out << ")" << endl << endl;
    }

    void PrintVisitor::VisitSynthFunCmd(const SynthFunCmd* Cmd)
    {
        Out << GetIndent() << "(synth-fun " << Cmd->GetFunName() << " (";
        for(auto const& ASPair : Cmd->GetArgs()) {
            ASPair->Accept(this);
        }
        Out << ") ";
        Cmd->GetSort()->Accept(this);
        Out << endl;
        IndentLevel++;
        Out << GetIndent() << "(";
        IndentLevel++;

        for(auto const& Rule : Cmd->GetGrammarRules()) {
            Rule->Accept(this);
            Out << endl;
        }
        IndentLevel--;
        Out << ")" << endl;
        IndentLevel--;
        Out << ")" << endl << endl;
    }

    void PrintVisitor::VisitSortDefCmd(const SortDefCmd* Cmd)
    {
        Out << GetIndent() << "(define-sort " << Cmd->GetName() << " ";
        Cmd->GetSortExpr()->Accept(this);
        Out << ")" << endl << endl;
    }

    void PrintVisitor::VisitSetOptsCmd(const SetOptsCmd* Cmd)
    {
        Out << GetIndent() << "(set-opts (";
        IndentLevel++;
        for(auto const& Opt : Cmd->GetOpts()) {
            Out << endl << GetIndent() << "(" << Opt.first << " \"" << Opt.second << "\")";
        }
        Out << endl;
        IndentLevel--;
        Out << GetIndent() << "))" << endl << endl;
    }

    void PrintVisitor::VisitVarDeclCmd(const VarDeclCmd* Cmd)
    {
        Out << GetIndent() << "(declare-var " << Cmd->GetName() << " ";
        Cmd->GetSort()->Accept(this);
        Out << ")" << endl << endl;
    }


    void PrintVisitor::VisitConstraintCmd(const ConstraintCmd* Cmd)
    {
        Out << "(constraint " << endl;
        IndentLevel++;
        Cmd->GetTerm()->Accept(this);
        IndentLevel--;
        Out << endl << GetIndent() << ")" << endl << endl;
    }

    void PrintVisitor::VisitSetLogicCmd(const SetLogicCmd* Cmd)
    {
        Out << GetIndent() << "(set-logic " << Cmd->GetLogicName() << ")" << endl << endl;
    }

    void PrintVisitor::VisitCheckSynthCmd(const CheckSynthCmd* Cmd)
    {
        Out << GetIndent() << "(check-synth)" << endl << endl;
    }

    void PrintVisitor::VisitArgSortPair(const ArgSortPair* ASPair)
    {
        Out << "(" << ASPair->GetName() << " ";
        ASPair->GetSort()->Accept(this);
        Out << ")";
    }

    void PrintVisitor::VisitIntSortExpr(const IntSortExpr* Sort)
    {
        Out << "Int";
    }

    void PrintVisitor::VisitBVSortExpr(const BVSortExpr* Sort)
    {
        Out << "(BitVec " << Sort->GetSize() << ")";
    }

    void PrintVisitor::VisitNamedSortExpr(const NamedSortExpr* Sort)
    {
        Out << Sort->GetName();
    }

    void PrintVisitor::VisitArraySortExpr(const ArraySortExpr* Sort)
    {
        Out << "(Array ";
        Sort->GetDomainSort()->Accept(this);
        Out << " ";
        Sort->GetRangeSort()->Accept(this);
        Out << ")";
    }

    void PrintVisitor::VisitRealSortExpr(const RealSortExpr* Sort)
    {
        Out << "Real";
    }

    void PrintVisitor::VisitFunSortExpr(const FunSortExpr* Sort)
    {
        // Do nothing!
    }

    void PrintVisitor::VisitBoolSortExpr(const BoolSortExpr* Sort)
    {
        Out << "Bool";
    }

    void PrintVisitor::VisitEnumSortExpr(const EnumSortExpr* Sort)
    {
        Out << "(Enum (";
        for(auto const& Con : Sort->GetConstructors()) {
            Out << Con << " ";
        }
        Out << "))";
    }

    void PrintVisitor::VisitLetBindingTerm(const LetBindingTerm* Binding)
    {
        Out << "(" << Binding->GetVarName() << " ";
        Binding->GetVarSort()->Accept(this);
        Out << " ";
        Binding->GetBoundToTerm()->Accept(this);
        Out << ")";
    }

    void PrintVisitor::VisitFunTerm(const FunTerm* TheTerm)
    {
        Out << "(" << TheTerm->GetFunName();
        for(auto const& Arg : TheTerm->GetArgs()) {
            Out << " ";
            Arg->Accept(this);
        }
        Out << ")";
    }

    void PrintVisitor::VisitLiteralTerm(const LiteralTerm* TheTerm)
    {
        TheTerm->GetLiteral()->Accept(this);
    }

    void PrintVisitor::VisitSymbolTerm(const SymbolTerm* TheTerm)
    {
        Out << TheTerm->GetSymbol();
    }

    void PrintVisitor::VisitLetTerm(const LetTerm* TheTerm)
    {
        Out << "(let (" << endl;
        IndentLevel++;
        for(auto const& Binding : TheTerm->GetBindings()) {
            Binding->Accept(this);
        }
        Out << ")" << endl;
        Out << GetIndent();
        TheTerm->GetBoundInTerm()->Accept(this);
        IndentLevel--;
        Out << endl << GetIndent() << ")";
    }

    void PrintVisitor::VisitLetBindingGTerm(const LetBindingGTerm* Binding)
    {
        Out << "(" << Binding->GetVarName() << " ";
        Binding->GetVarSort()->Accept(this);
        Out << " ";
        Binding->GetBoundToTerm()->Accept(this);
        Out << ")";
    }

    void PrintVisitor::VisitFunGTerm(const FunGTerm* TheTerm)
    {
        Out << "(" << TheTerm->GetName();
        for(auto const& Arg : TheTerm->GetArgs()) {
            Out << " ";
            Arg->Accept(this);
        }
        Out << ")" << endl;
    }

    void PrintVisitor::VisitLiteralGTerm(const LiteralGTerm* TheTerm)
    {
        TheTerm->GetLiteral()->Accept(this);
    }

    void PrintVisitor::VisitSymbolGTerm(const SymbolGTerm* TheTerm)
    {
        Out << TheTerm->GetSymbol();
    }

    void PrintVisitor::VisitLetGTerm(const LetGTerm* TheTerm)
    {
        Out << "(let (" << endl;
        IndentLevel++;
        for(auto const& Binding : TheTerm->GetBindings()) {
            Binding->Accept(this);
        }
        Out << ")" << endl;
        Out << GetIndent();
        TheTerm->GetBoundInTerm()->Accept(this);
        IndentLevel--;
        Out << endl << GetIndent() << ")";
    }

    void PrintVisitor::VisitConstantGTerm(const ConstantGTerm* TheTerm)
    {
        Out << "(Constant ";
        TheTerm->GetSort()->Accept(this);
        Out << ")";
    }

    void PrintVisitor::VisitVariableGTerm(const VariableGTerm* TheTerm)
    {
        switch (TheTerm->GetKind()) {
        case VARKIND_LOCAL:
            Out << "LocalVariable ";
            break;
        case VARKIND_INPUT:
            Out << "InputVariable ";
            break;
        case VARKIND_ANY:
            Out << "Variable ";
            break;
        }

        TheTerm->GetSort()->Accept(this);
        Out << ")";
    }

    void PrintVisitor::VisitNTDef(const NTDef* Def)
    {
        Out << "(" << Def->GetName() << " ";
        Def->GetSort()->Accept(this);
        Out << " (" << endl;
        IndentLevel++;
        for(auto const& Expansion : Def->GetExpansions()) {
            Out << GetIndent();
            Expansion->Accept(this);
        }
        IndentLevel--;
        Out << "))";
        Out << endl << GetIndent();
    }

    void PrintVisitor::VisitLiteral(const Literal* TheLiteral)
    {
        Out << TheLiteral->GetLiteralString();
    }

    // The << operator for AST bases
    ostream& operator << (ostream& Out, const ASTBase& AST)
    {
        PrintVisitor Printer(Out);
        AST.Accept(&Printer);
        return Out;
    }

    // The << operator for source locations
    ostream& operator << (ostream& Out, const SourceLocation& Location)
    {
        Out << Location.ToString();
        return Out;
    }

} /* end namespace */
