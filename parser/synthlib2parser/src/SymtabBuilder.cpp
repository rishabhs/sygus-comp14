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

#include <LogicSymbols.hpp>
#include <SymtabBuilder.hpp>

namespace SynthLib2Parser {

    SymtabBuilder::SymtabBuilder(SymbolTable* TheSymbolTable)
        : ASTVisitorBase("SymtabBuilder"), TheSymbolTable(TheSymbolTable)
    {
        // Nothing here
    }

    SymtabBuilder::~SymtabBuilder()
    {
        // Nothing here
    }

    void SymtabBuilder::VisitProgram(const Program* Prog)
    {
        // Delegate to base class
        ASTVisitorBase::VisitProgram(Prog);
    }

    void SymtabBuilder::VisitFunDefCmd(const FunDefCmd* Cmd)
    {
        // previsit. Push a new scope onto the symbol table
        TheSymbolTable->Push();
        // Check that the formals are okay.
        // And bind them in the new scope
        // also gather the argument sorts for later use
        vector<const SortExpr*> ArgSorts;
        for(auto const& ASPair : Cmd->GetArgs()) {
            ASPair->Accept(this);
            TheSymbolTable->BindFormal(ASPair->GetName(),
                                       static_cast<const SortExpr*>(ASPair->GetSort()->Clone()));
            ArgSorts.push_back(ASPair->GetSort());
        }

        // Check that the type of the term is the same as the one declared

        // Push the builder through the term to ensure that let-bound terms are
        // appropriately bound
        Cmd->GetTerm()->Accept(this);

        auto TermSort = Cmd->GetTerm()->GetTermSort(TheSymbolTable);
        auto ExpTermSort = Cmd->GetSort();
        if(!TheSymbolTable->ResolveSort(TermSort)->Equals(*(TheSymbolTable->ResolveSort(ExpTermSort)))) {
            throw SynthLib2ParserException((string)"Definition of function symbol \"" +
                                           Cmd->GetFunName() + "\" does not match expected sort\n" +
                                           Cmd->GetLocation().ToString());
        }

        Cmd->SetScope(TheSymbolTable->Pop());

        // Finally, we check that a function of the same name
        // is not already defined

        if (TheSymbolTable->LookupFun(Cmd->GetFunName(), ArgSorts) != NULL) {
            throw SynthLib2ParserException((string)"Function with name \"" +
                                           Cmd->GetFunName() + "\" has already been defined/declared.\n" +
                                           Cmd->GetLocation().ToString());
        }

        // All seems good.
        // Bind the def
        TheSymbolTable->BindUserFun(static_cast<FunDefCmd*>(Cmd->Clone()));
    }

    void SymtabBuilder::VisitFunDeclCmd(const FunDeclCmd* Cmd)
    {
        // Recurse to make sure all sorts are well formed
        ASTVisitorBase::VisitFunDeclCmd(Cmd);

        // Ensure that no other function symbol exists
        if (TheSymbolTable->LookupFun(Cmd->GetFunName(),
                                      Cmd->GetArgSorts()) != NULL) {
            throw SynthLib2ParserException((string)"Function with name \"" +
                                           Cmd->GetFunName() + "\" has already been defined/declared.\n" +
                                           Cmd->GetLocation().ToString());
        }

        // Bind this func decl
        TheSymbolTable->BindUninterpFun(Cmd->GetFunName(),
                                        CloneVector(Cmd->GetArgSorts()),
                                        static_cast<const SortExpr*>(Cmd->GetSort()));
    }

    void SymtabBuilder::VisitSynthFunCmd(const SynthFunCmd* Cmd)
    {
        // Push a new scope
        TheSymbolTable->Push();
        ASTVisitorBase::VisitSynthFunCmd(Cmd);
        // All is good
        Cmd->SetScope(TheSymbolTable->Pop());

        // Gather the arg sorts
        auto const& Args = Cmd->GetArgs();
        const u32 NumArgs = Args.size();
        vector<const SortExpr*> ArgSorts(NumArgs);
        for(u32 i = 0; i < NumArgs; ++i) {
            ArgSorts[i] = Args[i]->GetSort();
        }

        // Check that no function exists of the same name
        if (TheSymbolTable->LookupFun(Cmd->GetFunName(),
                                      ArgSorts) != NULL) {
            throw SynthLib2ParserException((string)"Function with name \"" +
                                           Cmd->GetFunName() + "\" has already been defined/declared.\n" +
                                           Cmd->GetLocation().ToString());
        }

        // Bind
        TheSymbolTable->BindSynthFun(Cmd->GetFunName(),
                                     CloneVector(ArgSorts),
                                     static_cast<SortExpr*>(Cmd->GetSort()->Clone()));
    }

    void SymtabBuilder::VisitSortDefCmd(const SortDefCmd* Cmd)
    {
        ASTVisitorBase::VisitSortDefCmd(Cmd);
        // Check for redeclaration
        vector<const SortExpr*> ArgSortDummy;
        if (TheSymbolTable->LookupSort(Cmd->GetName()) != NULL ||
            TheSymbolTable->LookupVariable(Cmd->GetName()) != NULL ||
            TheSymbolTable->LookupFun(Cmd->GetName(), ArgSortDummy) != NULL) {

            throw SynthLib2ParserException((string)"Identifier \"" + Cmd->GetName() + "\" has " +
                                           "already been declared/defined as a sort/variable/constant.\n" +
                                           Cmd->GetLocation().ToString());
        }
        // Bind
        TheSymbolTable->BindSort(Cmd->GetName(), static_cast<SortExpr*>(Cmd->GetSortExpr()->Clone()));
    }

    void SymtabBuilder::VisitSetOptsCmd(const SetOptsCmd* Cmd)
    {
        ASTVisitorBase::VisitSetOptsCmd(Cmd);
    }

    void SymtabBuilder::VisitVarDeclCmd(const VarDeclCmd* Cmd)
    {
        // Ensure that the sort is okay
        ASTVisitorBase::VisitVarDeclCmd(Cmd);

        // Check for redeclarations
        vector<const SortExpr*> ArgSortDummy;
        if (TheSymbolTable->LookupSort(Cmd->GetName()) != NULL ||
            TheSymbolTable->LookupVariable(Cmd->GetName()) != NULL ||
            TheSymbolTable->LookupFun(Cmd->GetName(), ArgSortDummy) != NULL) {

            throw SynthLib2ParserException((string)"Identifier \"" + Cmd->GetName() + "\" has " +
                                           "already been declared/defined as a sort/variable/constant.\n" +
                                           Cmd->GetLocation().ToString());
        }

        // Bind
        TheSymbolTable->BindVariable(Cmd->GetName(), static_cast<SortExpr*>(Cmd->GetSort()->Clone()));
    }

    void SymtabBuilder::VisitConstraintCmd(const ConstraintCmd* Cmd)
    {
        // Check that the type of the term is okay
        auto Sort = Cmd->GetTerm()->GetTermSort(TheSymbolTable);
        if (TheSymbolTable->ResolveSort(Sort)->GetKind() != SORTKIND_BOOL) {
            throw SynthLib2ParserException((string)"Constraint terms must be boolean typed.\n" +
                                           Cmd->GetLocation().ToString());
        }

        // Do nothing otherwise
        return;
    }

    void SymtabBuilder::VisitSetLogicCmd(const SetLogicCmd* Cmd)
    {
        ASTVisitorBase::VisitSetLogicCmd(Cmd);
    }

    void SymtabBuilder::VisitCheckSynthCmd(const CheckSynthCmd* Cmd)
    {
        ASTVisitorBase::VisitCheckSynthCmd(Cmd);
    }

    void SymtabBuilder::VisitArgSortPair(const ArgSortPair* ASPair)
    {
        // Just check that the sort is well formed
        ASTVisitorBase::VisitArgSortPair(ASPair);
    }

    void SymtabBuilder::VisitIntSortExpr(const IntSortExpr* Sort)
    {
        ASTVisitorBase::VisitIntSortExpr(Sort);
    }

    void SymtabBuilder::VisitBVSortExpr(const BVSortExpr* Sort)
    {
        ASTVisitorBase::VisitBVSortExpr(Sort);
        LogicSymbolLoader::RegisterSort(TheSymbolTable, Sort);
    }

    void SymtabBuilder::VisitNamedSortExpr(const NamedSortExpr* Sort)
    {
        // Check that the named sort actually resolves to something
        auto STE = TheSymbolTable->LookupSort(Sort->GetName());
        if(STE == NULL || STE->GetKind() != STENTRY_SORT) {
            throw SynthLib2ParserException((string)"Sort name \"" + Sort->GetName() + "\" could not " +
                                           "be resolved to anything meaningful.\n" +
                                           Sort->GetLocation().ToString());
        }
        auto SortE = STE->GetSort();
        if (TheSymbolTable->ResolveSort(SortE) == NULL) {
            throw SynthLib2ParserException((string)"Sort name \"" + Sort->GetName() + "\" could not " +
                                           "be resolved to anything meaningful.\n" +
                                           Sort->GetLocation().ToString());
        }
        // Do nothing otherwise
        return;
    }

    void SymtabBuilder::VisitArraySortExpr(const ArraySortExpr* Sort)
    {
        ASTVisitorBase::VisitArraySortExpr(Sort);
        LogicSymbolLoader::RegisterSort(TheSymbolTable, Sort);
    }

    void SymtabBuilder::VisitRealSortExpr(const RealSortExpr* Sort)
    {
        ASTVisitorBase::VisitRealSortExpr(Sort);
    }

    void SymtabBuilder::VisitFunSortExpr(const FunSortExpr* Sort)
    {
        ASTVisitorBase::VisitFunSortExpr(Sort);
    }

    void SymtabBuilder::VisitBoolSortExpr(const BoolSortExpr* Sort)
    {
        ASTVisitorBase::VisitBoolSortExpr(Sort);
    }

    void SymtabBuilder::VisitEnumSortExpr(const EnumSortExpr* Sort)
    {
        ASTVisitorBase::VisitEnumSortExpr(Sort);
        LogicSymbolLoader::RegisterSort(TheSymbolTable, Sort);
    }

    void SymtabBuilder::VisitLetBindingTerm(const LetBindingTerm* Binding)
    {
        // Check the sorts
        ASTVisitorBase::VisitLetBindingTerm(Binding);

        // Check that the sort of the term is what is expected
        auto TermSort = Binding->GetBoundToTerm()->GetTermSort(TheSymbolTable);
        auto ExpectedSort = Binding->GetVarSort();
        if (!TheSymbolTable->ResolveSort(TermSort)->Equals(*(TheSymbolTable->ResolveSort(ExpectedSort)))) {
            throw SynthLib2ParserException((string)"Let bound term \"" + Binding->GetVarName() +
                                           "\" does not match the expected sort.\n" +
                                           Binding->GetLocation().ToString());
        }
        // let bound terms can shadow anything
        TheSymbolTable->BindLetVariable(Binding->GetVarName(),
                                        static_cast<Term*>(Binding->GetBoundToTerm()->Clone()));
        return;
    }

    void SymtabBuilder::VisitFunTerm(const FunTerm* TheTerm)
    {
        ASTVisitorBase::VisitFunTerm(TheTerm);
    }

    void SymtabBuilder::VisitLiteralTerm(const LiteralTerm* TheTerm)
    {
        ASTVisitorBase::VisitLiteralTerm(TheTerm);
    }

    void SymtabBuilder::VisitSymbolTerm(const SymbolTerm* TheTerm)
    {
        ASTVisitorBase::VisitSymbolTerm(TheTerm);
    }

    void SymtabBuilder::VisitLetTerm(const LetTerm* TheTerm)
    {
        // Push a new scope
        TheSymbolTable->Push();
        // Visit the bindings to ensure that everything is in order
        // This process also creates the bindings in the current scope
        ASTVisitorBase::VisitLetTerm(TheTerm);
        // Push the scope to the let term
        TheTerm->SetScope(TheSymbolTable->Pop());
        return;
    }

    void SymtabBuilder::VisitLetBindingGTerm(const LetBindingGTerm* Binding)
    {
        // We don't handle this here.
        // except for checking the sort exprs
        ASTVisitorBase::VisitLetBindingGTerm(Binding);
    }

    void SymtabBuilder::VisitFunGTerm(const FunGTerm* TheTerm)
    {
        ASTVisitorBase::VisitFunGTerm(TheTerm);
    }

    void SymtabBuilder::VisitLiteralGTerm(const LiteralGTerm* TheTerm)
    {
        ASTVisitorBase::VisitLiteralGTerm(TheTerm);
    }

    void SymtabBuilder::VisitSymbolGTerm(const SymbolGTerm* TheTerm)
    {
        ASTVisitorBase::VisitSymbolGTerm(TheTerm);
    }

    void SymtabBuilder::VisitLetGTerm(const LetGTerm* TheTerm)
    {
        ASTVisitorBase::VisitLetGTerm(TheTerm);
    }

    void SymtabBuilder::VisitConstantGTerm(const ConstantGTerm* TheTerm)
    {
        ASTVisitorBase::VisitConstantGTerm(TheTerm);
    }

    void SymtabBuilder::VisitVariableGTerm(const VariableGTerm* TheTerm)
    {
        ASTVisitorBase::VisitVariableGTerm(TheTerm);
    }

    void SymtabBuilder::VisitNTDef(const NTDef* Def)
    {
        ASTVisitorBase::VisitNTDef(Def);
    }

    void SymtabBuilder::VisitLiteral(const Literal* TheLiteral)
    {
        ASTVisitorBase::VisitLiteral(TheLiteral);
    }

    void SymtabBuilder::Do(const Program* Prog, SymbolTable* TheSymbolTable)
    {
        SymtabBuilder Builder(TheSymbolTable);
        Prog->Accept(&Builder);
    }

} /* end namespace */
