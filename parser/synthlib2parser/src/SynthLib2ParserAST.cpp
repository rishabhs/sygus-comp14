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

#include <SynthLib2ParserIFace.hpp>
#include <SymbolTable.hpp>
#include <algorithm>
#include <boost/functional/hash.hpp>
#include <LogicSymbols.hpp>
#include <SymtabBuilder.hpp>
#include <boost/algorithm/string/split.hpp>
#include <boost/algorithm/string/classification.hpp>

namespace SynthLib2Bison {
    extern SynthLib2Parser::Program* TheProgram;
}

extern FILE* yyin;
extern int yyparse();

namespace SynthLib2Parser {

    SourceLocation SourceLocation::None(-1, -1);

    SourceLocation::SourceLocation(i32 LineNum, i32 ColNum)
        : LineNum(LineNum), ColNum(ColNum)
    {
        // Nothing here
    }

    SourceLocation::~SourceLocation()
    {
        // Nothing here
    }

    SourceLocation::SourceLocation(const SourceLocation& Other)
        : LineNum(Other.LineNum), ColNum(Other.ColNum)
    {
        // Nothing here
    }

    SourceLocation& SourceLocation::operator = (const SourceLocation& Other)
    {
        if (&Other == this) {
            return *this;
        }
        LineNum = Other.LineNum;
        ColNum = Other.ColNum;
        return *this;
    }

    i32 SourceLocation::GetLineNum() const
    {
        return LineNum;
    }

    i32 SourceLocation::GetColNum() const
    {
        return ColNum;
    }

    string SourceLocation::ToString() const
    {
        ostringstream sstr;
        sstr << "Line: " << LineNum << ", Col: " << ColNum;
        return sstr.str();
    }

    // ASTBase
    ASTBase::ASTBase(const SourceLocation& Location)
        : Location(Location)
    {
        // Nothing here
    }

    ASTBase::~ASTBase()
    {
        // Nothing here
    }

    const SourceLocation& ASTBase::GetLocation() const
    {
        return Location;
    }

    ArgSortPair::ArgSortPair(const SourceLocation& Location,
                             const string& Name,
                             const SortExpr* Sort)
        : ASTBase(Location), Name(Name), Sort(Sort)
    {
        // Nothing here
    }

    ArgSortPair::~ArgSortPair()
    {
        delete Sort;
    }

    void ArgSortPair::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitArgSortPair(this);
    }

    ASTBase* ArgSortPair::Clone() const
    {
        return new ArgSortPair(Location, Name, static_cast<const SortExpr*>(Sort->Clone()));
    }

    const string& ArgSortPair::GetName() const
    {
        return Name;
    }

    const SortExpr* ArgSortPair::GetSort() const
    {
        return Sort;
    }

    // ASTCmd
    ASTCmd::ASTCmd(const SourceLocation& Location, ASTCmdKind Kind)
        : ASTBase(Location), CmdKind(Kind)
    {
        // Nothing here
    }

    ASTCmd::~ASTCmd()
    {
        // Nothing here
    }

    ASTCmdKind ASTCmd::GetKind() const
    {
        return CmdKind;
    }

    CheckSynthCmd::CheckSynthCmd(const SourceLocation& Location)
        : ASTCmd(Location, CMD_CHECKSYNTH)
    {
        // Nothing here
    }

    CheckSynthCmd::~CheckSynthCmd()
    {
        // Nothing here
    }

    void CheckSynthCmd::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitCheckSynthCmd(this);
    }

    ASTBase* CheckSynthCmd::Clone() const
    {
        return new CheckSynthCmd(Location);
    }

    SetLogicCmd::SetLogicCmd(const SourceLocation& Location,
                             const string& LogicName)
        : ASTCmd(Location, CMD_SETLOGIC), LogicName(LogicName)
    {
        // Nothing here
    }

    SetLogicCmd::~SetLogicCmd()
    {
        // Nothing here
    }

    void SetLogicCmd::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitSetLogicCmd(this);
    }

    ASTBase* SetLogicCmd::Clone() const
    {
        return new SetLogicCmd(Location, LogicName);
    }

    const string& SetLogicCmd::GetLogicName() const
    {
        return LogicName;
    }

    FunDefCmd::FunDefCmd(const SourceLocation& Location,
                         const string& FunSymbol,
                         const ArgList& FunArgs,
                         const SortExpr* FunType,
                         Term* FunDef,
                         SymbolTableScope* Scope)
        : ASTCmd(Location, CMD_FUNDEF),
          Symbol(FunSymbol), Arguments(FunArgs),
          Type(FunType), Def(FunDef), Scope(Scope)
    {
        // Nothing here
    }

    FunDefCmd::~FunDefCmd()
    {
        for(auto const& ASPair : Arguments) {
            delete ASPair;
        }
        delete Type;
        delete Def;
        delete Scope;
    }

    void FunDefCmd::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitFunDefCmd(this);
    }

    ASTBase* FunDefCmd::Clone() const
    {
        return new FunDefCmd(Location, Symbol, CloneVector(Arguments),
                             static_cast<const SortExpr*>(Type->Clone()),
                             static_cast<Term*>(Def->Clone()),
                             Scope->Clone());
    }

    const string& FunDefCmd::GetFunName() const
    {
        return Symbol;
    }

    const ArgList& FunDefCmd::GetArgs() const
    {
        return Arguments;
    }

    const SortExpr* FunDefCmd::GetSort() const
    {
        return Type;
    }

    Term* FunDefCmd::GetTerm() const
    {
        return Def;
    }

    void FunDefCmd::SetScope(SymbolTableScope* Scope) const
    {
        this->Scope = Scope;
    }

    SymbolTableScope* FunDefCmd::GetScope() const
    {
        return Scope;
    }

    FunDeclCmd::FunDeclCmd(const SourceLocation& Location,
                           const string& FunSymbol,
                           const vector<const SortExpr*>& ArgTypes,
                           const SortExpr* Type)
        : ASTCmd(Location, CMD_FUNDECL),
          Symbol(FunSymbol), ArgTypes(ArgTypes), Type(Type)
    {
        // Nothing here
    }

    FunDeclCmd::~FunDeclCmd()
    {
        for (auto const& Arg : ArgTypes) {
            delete Arg;
        }
        delete Type;
    }

    void FunDeclCmd::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitFunDeclCmd(this);
    }

    ASTBase* FunDeclCmd::Clone() const
    {
        return new FunDeclCmd(Location, Symbol, CloneVector(ArgTypes),
                              static_cast<const SortExpr*>(Type->Clone()));
    }

    const string& FunDeclCmd::GetFunName() const
    {
        return Symbol;
    }

    const vector<const SortExpr*>& FunDeclCmd::GetArgSorts() const
    {
        return ArgTypes;
    }

    const SortExpr* FunDeclCmd::GetSort() const
    {
        return Type;
    }

    SynthFunCmd::SynthFunCmd(const SourceLocation& Location,
                             const string& Name,
                             const ArgList& Args,
                             const SortExpr* FunType,
                             const vector<NTDef*> GrammarRules,
                             SymbolTableScope* Scope)
        : ASTCmd(Location, CMD_SYNTHFUN), SynthFunName(Name),
          Arguments(Args), FunType(FunType), GrammarRules(GrammarRules),
          Scope(Scope)
    {
        // Nothing here
    }

    SynthFunCmd::~SynthFunCmd()
    {
        for(auto const& ASPair : Arguments) {
            delete ASPair;
        }

        delete FunType;
        for(auto const& NonTerm : GrammarRules) {
            delete NonTerm;
        }

        delete Scope;
    }

    void SynthFunCmd::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitSynthFunCmd(this);
    }

    ASTBase* SynthFunCmd::Clone() const
    {
        return new SynthFunCmd(Location, SynthFunName, CloneVector(Arguments),
                               static_cast<const SortExpr*>(FunType->Clone()),
                               CloneVector(GrammarRules), Scope->Clone());
    }

    const string& SynthFunCmd::GetFunName() const
    {
        return SynthFunName;
    }

    const ArgList& SynthFunCmd::GetArgs() const
    {
        return Arguments;
    }

    const SortExpr* SynthFunCmd::GetSort() const
    {
        return FunType;
    }

    const vector<NTDef*>& SynthFunCmd::GetGrammarRules() const
    {
        return GrammarRules;
    }

    void SynthFunCmd::SetScope(SymbolTableScope* Scope) const
    {
        this->Scope = Scope;
    }

    SymbolTableScope* SynthFunCmd::GetScope() const
    {
        return Scope;
    }

    ConstraintCmd::ConstraintCmd(const SourceLocation& Location, Term* TheTerm)
        : ASTCmd(Location, CMD_CONSTRAINT), TheTerm(TheTerm)
    {
        // Nothing here
    }

    ConstraintCmd::~ConstraintCmd()
    {
        delete TheTerm;
    }

    void ConstraintCmd::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitConstraintCmd(this);
    }

    ASTBase* ConstraintCmd::Clone() const
    {
        return new ConstraintCmd(Location, static_cast<Term*>(TheTerm->Clone()));
    }

    Term* ConstraintCmd::GetTerm() const
    {
        return TheTerm;
    }

    SortDefCmd::SortDefCmd(const SourceLocation& Location,
                           const string& Symbol, const SortExpr* Expr)
        : ASTCmd(Location, CMD_SORTDEF), Symbol(Symbol), Expr(Expr)
    {
        // Nothing here
    }

    SortDefCmd::~SortDefCmd()
    {
        delete Expr;
    }

    void SortDefCmd::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitSortDefCmd(this);
    }

    ASTBase* SortDefCmd::Clone() const
    {
        return new SortDefCmd(Location, Symbol, static_cast<SortExpr*>(Expr->Clone()));
    }

    const string& SortDefCmd::GetName() const
    {
        return Symbol;
    }

    const SortExpr* SortDefCmd::GetSortExpr() const
    {
        return Expr;
    }

    SetOptsCmd::SetOptsCmd(const SourceLocation& Location,
                           const vector<pair<string, string> >& Opts)
        : ASTCmd(Location, CMD_SETOPTS), Opts(Opts)
    {
        // Nothing here
    }

    SetOptsCmd::~SetOptsCmd()
    {
        // Nothing here
    }

    void SetOptsCmd::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitSetOptsCmd(this);
    }

    ASTBase* SetOptsCmd::Clone() const
    {
        return new SetOptsCmd(Location, Opts);
    }

    const vector<pair<string, string> >& SetOptsCmd::GetOpts() const
    {
        return Opts;
    }

    VarDeclCmd::VarDeclCmd(const SourceLocation& Location,
                           const string& VarName,
                           const SortExpr* VarType)
        : ASTCmd(Location, CMD_VARDECL), VarName(VarName),
          VarType(VarType)
    {
        // Nothing here
    }

    VarDeclCmd::~VarDeclCmd()
    {
        delete VarType;
    }

    void VarDeclCmd::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitVarDeclCmd(this);
    }

    ASTBase* VarDeclCmd::Clone() const
    {
        return new VarDeclCmd(Location, VarName, static_cast<const SortExpr*>(VarType->Clone()));
    }

    const string& VarDeclCmd::GetName() const
    {
        return VarName;
    }

    const SortExpr* VarDeclCmd::GetSort() const
    {
        return VarType;
    }

    SortExpr::SortExpr(const SourceLocation& Location,
                       SortKind Kind)
        : ASTBase(Location), Kind(Kind)
    {
        // Nothing here
    }

    SortExpr::~SortExpr()
    {
        // Nothing here
    }

    SortKind SortExpr::GetKind() const
    {
        return Kind;
    }

    IntSortExpr::IntSortExpr(const SourceLocation& Location)
        : SortExpr(Location, SORTKIND_INT)
    {
        // Nothing here
    }

    IntSortExpr::IntSortExpr()
        : SortExpr(SourceLocation::None, SORTKIND_INT)
    {
        // Nothing here
    }

    IntSortExpr::~IntSortExpr()
    {
        // Nothing here
    }

    bool IntSortExpr::Equals(const SortExpr& Other) const
    {
        auto OtherPtr = dynamic_cast<const IntSortExpr*>(&Other);
        if(OtherPtr == NULL) {
            return false;
        } else {
            return true;
        }
    }

    u32 IntSortExpr::Hash() const
    {
        return boost::hash_value((u32)GetKind());
    }

    void IntSortExpr::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitIntSortExpr(this);
    }

    ASTBase* IntSortExpr::Clone() const
    {
        return new IntSortExpr(Location);
    }

    string IntSortExpr::ToMangleString() const
    {
        return "Int";
    }

    BVSortExpr::BVSortExpr(const SourceLocation& Location,
                           u32 Size)
        : SortExpr(Location, SORTKIND_BV), Size(Size)
    {
        // Nothing here
    }

    BVSortExpr::BVSortExpr(u32 Size)
        : SortExpr(SourceLocation::None, SORTKIND_BV), Size(Size)
    {
        // Nothing here
    }

    BVSortExpr::~BVSortExpr()
    {
        // Nothing here
    }

    bool BVSortExpr::Equals(const SortExpr& Other) const
    {
        auto OtherPtr = dynamic_cast<const BVSortExpr*>(&Other);
        if(OtherPtr == NULL) {
            return false;
        } else {
            return OtherPtr->Size == Size;
        }
    }

    u32 BVSortExpr::Hash() const
    {
        u64 Retval = 0;
        boost::hash_combine(Retval, (u64)GetKind());
        boost::hash_combine(Retval, Size);
        return (u32)Retval;
    }

    void BVSortExpr::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitBVSortExpr(this);
    }

    ASTBase* BVSortExpr::Clone() const
    {
        return new BVSortExpr(Location, Size);
    }

    string BVSortExpr::ToMangleString() const
    {
        return ((string)"BV" + to_string(Size));
    }

    u32 BVSortExpr::GetSize() const
    {
        return Size;
    }

    NamedSortExpr::NamedSortExpr(const SourceLocation& Location,
                                 const string& Name)
        : SortExpr(Location, SORTKIND_NAMED), Name(Name)
    {
        // Nothing here
    }

    NamedSortExpr::NamedSortExpr(const string& Name)
        : SortExpr(SourceLocation::None, SORTKIND_NAMED), Name(Name)
    {
        // Nothing here
    }

    NamedSortExpr::~NamedSortExpr()
    {
        // Nothing here
    }

    bool NamedSortExpr::Equals(const SortExpr& Other) const
    {
        auto OtherPtr = dynamic_cast<const NamedSortExpr*>(&Other);
        if (OtherPtr == NULL) {
            return false;
        } else {
            return (OtherPtr->Name == Name);
        }
    }

    void NamedSortExpr::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitNamedSortExpr(this);
    }

    ASTBase* NamedSortExpr::Clone() const
    {
        return new NamedSortExpr(Location, Name);
    }

    u32 NamedSortExpr::Hash() const
    {
        return boost::hash_value(Name);
    }

    string NamedSortExpr::ToMangleString() const
    {
        throw SynthLib2ParserException("Internal: Tried to call NamedSortExpr::ToMangleString()");
    }

    const string& NamedSortExpr::GetName() const
    {
        return Name;
    }

    ArraySortExpr::ArraySortExpr(const SourceLocation& Location,
                                 const SortExpr* DomainSort,
                                 const SortExpr* RangeSort)
        : SortExpr(Location, SORTKIND_ARRAY), DomainSort(DomainSort), RangeSort(RangeSort)
    {
        // Nothing here
    }

    ArraySortExpr::ArraySortExpr(const SortExpr* DomainSort,
                                 const SortExpr* RangeSort)
        : SortExpr(SourceLocation::None, SORTKIND_ARRAY),
          DomainSort(DomainSort), RangeSort(RangeSort)
    {
        // Nothing here
    }

    ArraySortExpr::~ArraySortExpr()
    {
        delete RangeSort;
        delete DomainSort;
    }

    bool ArraySortExpr::Equals(const SortExpr& Other) const
    {
        auto OtherPtr = dynamic_cast<const ArraySortExpr*>(&Other);
        if(OtherPtr == NULL) {
            return false;
        }
        return (DomainSort->Equals(*(OtherPtr->DomainSort)) &&
                RangeSort->Equals(*(OtherPtr->RangeSort)));
    }

    void ArraySortExpr::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitArraySortExpr(this);
    }

    u32 ArraySortExpr::Hash() const
    {
        u64 Retval = 0;
        boost::hash_combine(Retval, (u64)GetKind());
        boost::hash_combine(Retval, DomainSort->Hash());
        boost::hash_combine(Retval, RangeSort->Hash());
        return (u32)Retval;
    }

    ASTBase* ArraySortExpr::Clone() const
    {
        return new ArraySortExpr(Location, static_cast<const SortExpr*>(DomainSort->Clone()),
                                 static_cast<const SortExpr*>(RangeSort->Clone()));
    }

    string ArraySortExpr::ToMangleString() const
    {
        return ((string)"Array_" + RangeSort->ToMangleString() +
                "_of_" + DomainSort->ToMangleString());
    }

    const SortExpr* ArraySortExpr::GetDomainSort() const
    {
        return DomainSort;
    }

    const SortExpr* ArraySortExpr::GetRangeSort() const
    {
        return RangeSort;
    }

    RealSortExpr::RealSortExpr(const SourceLocation& Location)
        : SortExpr(Location, SORTKIND_REAL)
    {
        // Nothing here
    }

    RealSortExpr::RealSortExpr()
        : SortExpr(SourceLocation::None, SORTKIND_REAL)
    {
        // Nothing here
    }

    RealSortExpr::~RealSortExpr()
    {
        // Nothing here
    }

    bool RealSortExpr::Equals(const SortExpr& Other) const
    {
        return (dynamic_cast<const RealSortExpr*>(&Other) != NULL);
    }

    u32 RealSortExpr::Hash() const
    {
        return boost::hash_value((u32)GetKind());
    }

    void RealSortExpr::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitRealSortExpr(this);
    }

    ASTBase* RealSortExpr::Clone() const
    {
        return new RealSortExpr(Location);
    }

    string RealSortExpr::ToMangleString() const
    {
        return "Real";
    }

    FunSortExpr::FunSortExpr(const SourceLocation& Location,
                             const vector<const SortExpr*>& ArgSorts,
                             const SortExpr* RetSort)
        : SortExpr(Location, SORTKIND_FUN), ArgSorts(ArgSorts),
          RetSort(RetSort)
    {
        // Nothing here
    }

    FunSortExpr::FunSortExpr(const vector<const SortExpr*>& ArgSorts,
                             const SortExpr* RetSort)
        : SortExpr(SourceLocation::None, SORTKIND_FUN),
          ArgSorts(ArgSorts), RetSort(RetSort)
    {
        // Nothing here
    }

    FunSortExpr::~FunSortExpr()
    {
        for(auto const& ArgSort : ArgSorts) {
            delete ArgSort;
        }
        delete RetSort;
    }

    bool FunSortExpr::Equals(const SortExpr& Other) const
    {
        auto OtherPtr = dynamic_cast<const FunSortExpr*>(&Other);
        if(OtherPtr == NULL) {
            return false;
        }
        const u32 NumArgs = ArgSorts.size();
        if(OtherPtr->ArgSorts.size() != NumArgs) {
            return false;
        }
        for(u32 i = 0; i < NumArgs; ++i) {
            if(!ArgSorts[i]->Equals(*(OtherPtr->ArgSorts[i]))) {
                return false;
            }
        }

        return (RetSort->Equals(*(OtherPtr->RetSort)));
    }

    u32 FunSortExpr::Hash() const
    {
        u64 Retval = 0;
        boost::hash_combine(Retval, (u64)GetKind());
        for(auto const& ArgSort : ArgSorts) {
            boost::hash_combine(Retval, ArgSort->Hash());
        }
        boost::hash_combine(Retval, RetSort->Hash());
    return (u32)Retval;
    }

    void FunSortExpr::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitFunSortExpr(this);
    }

    ASTBase* FunSortExpr::Clone() const
    {
        return new FunSortExpr(Location, CloneVector(ArgSorts),
                               static_cast<SortExpr*>(RetSort->Clone()));
    }

    string FunSortExpr::ToMangleString() const
    {
        string Retval;
        for(auto const& ArgSort : ArgSorts) {
            Retval += ArgSort->ToMangleString() + "->";
        }
        Retval += RetSort->ToMangleString();
        return Retval;
    }

    const vector<const SortExpr*>& FunSortExpr::GetArgSorts() const
    {
        return ArgSorts;
    }

    const SortExpr* FunSortExpr::GetRetSort() const
    {
        return RetSort;
    }

    BoolSortExpr::BoolSortExpr(const SourceLocation& Location)
        : SortExpr(Location, SORTKIND_BOOL)
    {
        // Nothing here
    }

    BoolSortExpr::BoolSortExpr()
        : SortExpr(SourceLocation::None, SORTKIND_BOOL)
    {
        // Nothing here
    }

    BoolSortExpr::~BoolSortExpr()
    {
        // Nothing here
    }

    void BoolSortExpr::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitBoolSortExpr(this);
    }

    ASTBase* BoolSortExpr::Clone() const
    {
        return new BoolSortExpr(Location);
    }

    u32 BoolSortExpr::Hash() const
    {
        return boost::hash_value((u32)GetKind());
    }

    bool BoolSortExpr::Equals(const SortExpr& Other) const
    {
        return (dynamic_cast<const BoolSortExpr*>(&Other) != NULL);
    }

    string BoolSortExpr::ToMangleString() const
    {
        return "Bool";
    }

    EnumSortExpr::EnumSortExpr(const SourceLocation& Location,
                               const string& EnumSortName,
                               const vector<string>& EnumConstructors)
        : SortExpr(Location, SORTKIND_ENUM),
          EnumSortName(EnumSortName), EnumSortConstructorVec(EnumConstructors),
          EnumSortConstructorSet(EnumConstructors.begin(), EnumConstructors.end())
    {
        // Nothing here
    }

    EnumSortExpr::EnumSortExpr(const SourceLocation& Location,
                               const vector<string>& EnumConstructors)
        : SortExpr(Location, SORTKIND_ENUM),
          EnumSortConstructorVec(EnumConstructors),
          EnumSortConstructorSet(EnumConstructors.begin(), EnumConstructors.end())
    {
        // Nothing here
    }

    EnumSortExpr::~EnumSortExpr()
    {
        // Nothing here
    }

    bool EnumSortExpr::Equals(const SortExpr& Other) const
    {
        auto OtherPtr = dynamic_cast<const EnumSortExpr*>(&Other);
        if(OtherPtr == NULL) {
            return false;
        }

        return (EnumSortName == OtherPtr->EnumSortName &&
                includes(EnumSortConstructorSet.begin(), EnumSortConstructorSet.end(),
                         OtherPtr->EnumSortConstructorSet.begin(),
                         OtherPtr->EnumSortConstructorSet.end()) &&
                includes(OtherPtr->EnumSortConstructorSet.begin(),
                         OtherPtr->EnumSortConstructorSet.end(),
                         EnumSortConstructorSet.begin(), EnumSortConstructorSet.end()));
    }

    void EnumSortExpr::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitEnumSortExpr(this);
    }

    u32 EnumSortExpr::Hash() const
    {
        u64 Retval = 0;
        boost::hash_combine(Retval, (u64)GetKind());
        for(auto const& Constructor : EnumSortConstructorVec) {
            boost::hash_combine(Retval, Constructor);
        }
        boost::hash_combine(Retval, EnumSortName);
        return (u32)Retval;
    }

    ASTBase* EnumSortExpr::Clone() const
    {
        return new EnumSortExpr(Location, EnumSortName, EnumSortConstructorVec);
    }

    string EnumSortExpr::ToMangleString() const
    {
        return ("EnumSort_" + EnumSortName);
    }

    const vector<string>& EnumSortExpr::GetConstructors() const
    {
        return EnumSortConstructorVec;
    }

    const string& EnumSortExpr::GetEnumSortName() const
    {
        return EnumSortName;
    }

    void EnumSortExpr::SetEnumSortName(const string& Name) const
    {
        EnumSortName = Name;
    }

    bool EnumSortExpr::IsConstructorValid(const string& ConstructorName) const
    {
        // Works only for unqualified constructors
        return (EnumSortConstructorSet.find(ConstructorName) !=
                EnumSortConstructorSet.end());
    }

    // Literals and terms
    Literal::Literal(const SourceLocation& Location,
                     const string& Constructor,
                     SortExpr* Sort)
    : ASTBase(Location), LiteralString(Constructor),
          LiteralSort(Sort)
    {
        // Nothing here
    }

    Literal::~Literal()
    {
        delete LiteralSort;
    }

    void Literal::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitLiteral(this);
    }

    ASTBase* Literal::Clone() const
    {
        return new Literal(Location, LiteralString, static_cast<SortExpr*>(LiteralSort->Clone()));
    }

    const SortExpr* Literal::GetSort(SymbolTable* SymTab) const
    {
        if (LiteralSort != NULL) {
            return LiteralSort;
        } else {
            // This must be an enum constant
            // lookup the type of the enumerated type in the symbol table
            vector<string> SplitVec;
            boost::algorithm::split(SplitVec, LiteralString,
                                    boost::algorithm::is_any_of(":"),
                                    boost::algorithm::token_compress_on);
            if (SplitVec.size() != 2) {
                throw SynthLib2ParserException("Internal: Expected a well-formed enum literal");
            }
            auto const& EnumTypeName = SplitVec[0];
            auto const& EnumConsName = SplitVec[1];

            // Lookup the type in the symbol table
            auto STE = SymTab->LookupSort(EnumTypeName);
            if(STE == NULL || STE->GetKind() != STENTRY_SORT) {
                throw SynthLib2ParserException((string)"Identifier \"" + EnumTypeName + "\" does not " +
                                               "refer to an enumeration sort\n" +
                                               Location.ToString());
            }
            // Resolve this sort
            auto Sort = SymTab->ResolveSort(STE->GetSort());
            if (Sort == NULL || Sort->GetKind() != SORTKIND_ENUM) {
                throw SynthLib2ParserException((string)"Identifier \"" + EnumTypeName + "\" does not " +
                                               "refer to an enumeration sort\n" +
                                               Location.ToString());
            }
            // Check that the constructor is valid for the sort

            if(!(dynamic_cast<const EnumSortExpr*>(Sort)->IsConstructorValid(EnumConsName))) {
                throw SynthLib2ParserException((string)"Constructor \"" + EnumConsName + "\" is not " +
                                               "a valid constructor for enumeration type \"" +
                                               EnumTypeName + "\"" +
                                               Location.ToString());
            }
            // return the enumeration sort
            return Sort;
        }
    }

    const string& Literal::GetLiteralString() const
    {
        return LiteralString;
    }

    Term::Term(const SourceLocation& Location,
               TermKind Kind)
        : ASTBase(Location), Kind(Kind)
    {
        // Nothing here
    }

    Term::~Term()
    {
        // Nothing here
    }

    TermKind Term::GetKind() const
    {
        return Kind;
    }

    FunTerm::FunTerm(const SourceLocation& Location,
                     const string& FunName,
                     const vector<Term*>& Args)
        : Term(Location, TERMKIND_FUN), FunName(FunName), Args(Args)
    {
        // Nothing here
    }

    FunTerm::~FunTerm()
    {
        for(auto const& Arg : Args) {
            delete Arg;
        }
    }

    void FunTerm::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitFunTerm(this);
    }

    ASTBase* FunTerm::Clone() const
    {
        return new FunTerm(Location, FunName, CloneVector(Args));
    }

    const SortExpr* FunTerm::GetTermSort(SymbolTable* SymTab) const
    {
        ostringstream SS;

        // determine this function's sort from the symbol table
        const u32 NumArgs = Args.size();
        vector<const SortExpr*> ArgSorts(NumArgs);

        for(u32 i = 0; i < NumArgs; ++i) {
            ArgSorts[i] = Args[i]->GetTermSort(SymTab);
        }

        auto Entry = SymTab->LookupFun(FunName, ArgSorts);
        if(Entry == NULL) {
            SS.str("");
            SS << "Could not determine type of term: "
               << *this << endl;
            SS << "This could be due to an undeclared function or "
               << "mismatched arguments to function" << endl;
            SS << Location;
            throw SynthLib2ParserException(SS.str());
        }

        auto FunSort = dynamic_cast<const FunSortExpr*>(Entry->GetSort());
        if(FunSort == NULL) {
            throw SynthLib2ParserException("Identifier \"" + FunName + "\" does " +
                                           "not refer to an function, but used as one");
        }
        return FunSort->GetRetSort();
    }

    const string& FunTerm::GetFunName() const
    {
        return FunName;
    }

    const vector<Term*>& FunTerm::GetArgs() const
    {
        return Args;
    }

    LiteralTerm::LiteralTerm(const SourceLocation& Location,
                             Literal* TheLiteral)
        : Term(Location, TERMKIND_LITERAL), TheLiteral(TheLiteral)
    {
        // Nothing here
    }

    LiteralTerm::~LiteralTerm()
    {
        delete TheLiteral;
    }

    void LiteralTerm::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitLiteralTerm(this);
    }

    ASTBase* LiteralTerm::Clone() const
    {
        return new LiteralTerm(Location, static_cast<Literal*>(TheLiteral->Clone()));
    }

    const SortExpr* LiteralTerm::GetTermSort(SymbolTable* SymTab) const
    {
        return TheLiteral->GetSort(SymTab);
    }

    Literal* LiteralTerm::GetLiteral() const
    {
        return TheLiteral;
    }

    SymbolTerm::SymbolTerm(const SourceLocation& Location,
                           const string& TheSymbol)
        : Term(Location, TERMKIND_SYMBOL), TheSymbol(TheSymbol)
    {
        // Nothing here
    }

    SymbolTerm::~SymbolTerm()
    {
        // Nothing here
    }

    void SymbolTerm::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitSymbolTerm(this);
    }

    ASTBase* SymbolTerm::Clone() const
    {
        return new SymbolTerm(Location, TheSymbol);
    }

    const SortExpr* SymbolTerm::GetTermSort(SymbolTable* SymTab) const
    {
        auto Entry = SymTab->Lookup(TheSymbol);
        if(Entry == NULL) {
            throw SynthLib2ParserException("Could not resolve identifier \"" +
                                           TheSymbol + "\"");
        }

        auto const SymSort = Entry->GetSort();
        if(Entry->GetKind() == STENTRY_USER_FUNCTION ||
           Entry->GetKind() == STENTRY_SYNTH_FUNCTION ||
           Entry->GetKind() == STENTRY_THEORY_FUNCTION ||
           Entry->GetKind() == STENTRY_UNINTERP_FUNCTION) {
            auto SymFunSort = dynamic_cast<const FunSortExpr*>(SymSort);
            return SymFunSort->GetRetSort();
        } else {
            return SymSort;
        }
    }

    const string& SymbolTerm::GetSymbol() const
    {
        return TheSymbol;
    }

    LetBindingTerm::LetBindingTerm(const SourceLocation& Location,
                                   const string& VarName,
                                   const SortExpr* VarSort,
                                   Term* BoundToTerm)
        : ASTBase(Location), VarName(VarName), VarSort(VarSort),
          BoundToTerm(BoundToTerm)
    {
        // Nothing here
    }

    LetBindingTerm::~LetBindingTerm()
    {
        delete VarSort;
        delete BoundToTerm;
    }

    void LetBindingTerm::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitLetBindingTerm(this);
    }

    ASTBase* LetBindingTerm::Clone() const
    {
        return new LetBindingTerm(Location, VarName,
                                  static_cast<const SortExpr*>(VarSort->Clone()),
                                  static_cast<Term*>(BoundToTerm->Clone()));
    }

    const string& LetBindingTerm::GetVarName() const
    {
        return VarName;
    }

    Term* LetBindingTerm::GetBoundToTerm() const
    {
        return BoundToTerm;
    }

    const SortExpr* LetBindingTerm::GetVarSort() const
    {
        return VarSort;
    }

    LetTerm::LetTerm(const SourceLocation& Location,
                     const vector<LetBindingTerm*>& Bindings,
                     Term* BoundInTerm,
                     SymbolTableScope* Scope)
        : Term(Location, TERMKIND_LET),
          Bindings(Bindings),
          BoundInTerm(BoundInTerm),
          Scope(Scope)
    {
        // Nothing here
    }

    LetTerm::~LetTerm()
    {
        for(auto const& Binding : Bindings) {
            delete Binding;
        }

        delete BoundInTerm;
        delete Scope;
    }

    void LetTerm::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitLetTerm(this);
    }

    ASTBase* LetTerm::Clone() const
    {
        return new LetTerm(Location, CloneVector(Bindings),
                           static_cast<Term*>(BoundInTerm->Clone()),
                           Scope->Clone());
    }

    const SortExpr* LetTerm::GetTermSort(SymbolTable* SymTab) const
    {
        // push the scope onto the symbol table
        SymTab->Push(Scope);
        auto Retval = BoundInTerm->GetTermSort(SymTab);
        SymTab->Pop();
        return Retval;
    }

    const vector<LetBindingTerm*>& LetTerm::GetBindings() const
    {
        return Bindings;
    }

    Term* LetTerm::GetBoundInTerm() const
    {
        return BoundInTerm;
    }

    void LetTerm::SetScope(SymbolTableScope* Scope) const
    {
        this->Scope = Scope;
    }

    SymbolTableScope* LetTerm::GetScope() const
    {
        return Scope;
    }

    GTerm::GTerm(const SourceLocation& Location,
                 GTermKind Kind)
        : ASTBase(Location), Kind(Kind)
    {
        // Nothing here
    }

    GTerm::~GTerm()
    {
        // Nothing here
    }

    GTermKind GTerm::GetKind() const
    {
        return Kind;
    }

    SymbolGTerm::SymbolGTerm(const SourceLocation& Location,
                             const string& TheSymbol)
        : GTerm(Location, GTERMKIND_SYMBOL),
          TheSymbol(TheSymbol)
    {
        // Nothing here
    }

    SymbolGTerm::~SymbolGTerm()
    {
        // Nothing here
    }

    void SymbolGTerm::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitSymbolGTerm(this);
    }

    ASTBase* SymbolGTerm::Clone() const
    {
        return new SymbolGTerm(Location, TheSymbol);
    }

    const SortExpr* SymbolGTerm::GetTermSort(SymbolTable* SymTab) const
    {
        auto Entry = SymTab->Lookup(TheSymbol);
        auto SymSort = Entry->GetSort();
        if(Entry->GetKind() == STENTRY_THEORY_FUNCTION ||
           Entry->GetKind() == STENTRY_SYNTH_FUNCTION ||
           Entry->GetKind() == STENTRY_USER_FUNCTION ||
           Entry->GetKind() == STENTRY_UNINTERP_FUNCTION) {

            auto SymFunSort = dynamic_cast<const FunSortExpr*>(SymSort);
            return SymFunSort->GetRetSort();
        } else {
            return SymSort;
        }
    }

    const string& SymbolGTerm::GetSymbol() const
    {
        return TheSymbol;
    }

    FunGTerm::FunGTerm(const SourceLocation& Location,
                       const string& FunName,
                       const vector<GTerm*>& Args)
        : GTerm(Location, GTERMKIND_FUN),
          FunName(FunName), Args(Args)
    {
        // Nothing here
    }

    FunGTerm::~FunGTerm()
    {
        for(auto const& Arg : Args) {
            delete Arg;
        }
    }

    void FunGTerm::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitFunGTerm(this);
    }

    ASTBase* FunGTerm::Clone() const
    {
        return new FunGTerm(Location, FunName,
                            CloneVector(Args));
    }

    const SortExpr* FunGTerm::GetTermSort(SymbolTable* SymTab) const
    {
        const u32 NumArgs = Args.size();
        vector<const SortExpr*> ArgSorts(NumArgs);

        for(u32 i = 0; i < NumArgs; ++i) {
            ArgSorts[i] = Args[i]->GetTermSort(SymTab);
        }


        auto Entry = SymTab->LookupFun(FunName, ArgSorts);
        if(Entry == NULL) {
            throw SynthLib2ParserException("Could not resolve identifier \"" +
                                           FunName + "\"");
        }
        auto EntrySort = Entry->GetSort();
        auto EntryFunSort = dynamic_cast<const FunSortExpr*>(EntrySort);
        if(EntryFunSort == NULL) {
            throw SynthLib2ParserException("Identifier \"" + FunName + "\" does not " +
                                           "refer to a function, but is used as one");
        }
        return EntryFunSort->GetRetSort();
    }

    const string& FunGTerm::GetName() const
    {
        return FunName;
    }

    const vector<GTerm*>& FunGTerm::GetArgs() const
    {
        return Args;
    }

    LiteralGTerm::LiteralGTerm(const SourceLocation& Location,
                               Literal* TheLiteral)
        : GTerm(Location, GTERMKIND_LITERAL), TheLiteral(TheLiteral)
    {
        // Nothing here
    }

    LiteralGTerm::~LiteralGTerm()
    {
        delete TheLiteral;
    }

    void LiteralGTerm::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitLiteralGTerm(this);
    }

    ASTBase* LiteralGTerm::Clone() const
    {
        return new LiteralGTerm(Location,
                                static_cast<Literal*>(TheLiteral->Clone()));
    }

    const SortExpr* LiteralGTerm::GetTermSort(SymbolTable* SymTab) const
    {
        return TheLiteral->GetSort(SymTab);
    }

    Literal* LiteralGTerm::GetLiteral() const
    {
        return TheLiteral;
    }

    ConstantGTerm::ConstantGTerm(const SourceLocation& Location,
                                 const SortExpr* Sort)
        : GTerm(Location, GTERMKIND_CONSTANT), ConstantSort(Sort)
    {
        // Nothing here
    }

    ConstantGTerm::~ConstantGTerm()
    {
        delete ConstantSort;
    }

    void ConstantGTerm::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitConstantGTerm(this);
    }

    ASTBase* ConstantGTerm::Clone() const
    {
        return new ConstantGTerm(Location,
                                 static_cast<const SortExpr*>(ConstantSort->Clone()));
    }

    const SortExpr* ConstantGTerm::GetTermSort(SymbolTable* SymTab) const
    {
        return ConstantSort;
    }

    const SortExpr* ConstantGTerm::GetSort() const
    {
        return ConstantSort;
    }

    VariableGTerm::VariableGTerm(const SourceLocation& Location,
                                 const SortExpr* VariableSort,
                                 VariableKind Kind)
        : GTerm(Location, GTERMKIND_VARIABLE), VariableSort(VariableSort),
          Kind(Kind)
    {
        // Nothing here
    }

    VariableGTerm::~VariableGTerm()
    {
        delete VariableSort;
    }

    void VariableGTerm::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitVariableGTerm(this);
    }

    ASTBase* VariableGTerm::Clone() const
    {
        return new VariableGTerm(Location, static_cast<const SortExpr*>(VariableSort->Clone()),
                                 Kind);
    }

    const SortExpr* VariableGTerm::GetTermSort(SymbolTable* SymTab) const
    {
        return VariableSort;
    }

    const SortExpr* VariableGTerm::GetSort() const
    {
        return VariableSort;
    }

    VariableKind VariableGTerm::GetKind() const
    {
        return Kind;
    }

    LetBindingGTerm::LetBindingGTerm(const SourceLocation& Location,
                                     const string& VarName,
                                     const SortExpr* VarSort,
                                     GTerm* BoundToTerm)
        : ASTBase(Location), VarName(VarName),
          VarSort(VarSort), BoundToTerm(BoundToTerm)
    {
        // Nothing here
    }

    LetBindingGTerm::~LetBindingGTerm()
    {
        delete VarSort;
        delete BoundToTerm;
    }

    void LetBindingGTerm::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitLetBindingGTerm(this);
    }

    ASTBase* LetBindingGTerm::Clone() const
    {
        return new LetBindingGTerm(Location, VarName,
                                   static_cast<const SortExpr*>(VarSort->Clone()),
                                   static_cast<GTerm*>(BoundToTerm->Clone()));
    }

    const string& LetBindingGTerm::GetVarName() const
    {
        return VarName;
    }

    GTerm* LetBindingGTerm::GetBoundToTerm() const
    {
        return BoundToTerm;
    }

    const SortExpr* LetBindingGTerm::GetVarSort() const
    {
        return VarSort;
    }

    LetGTerm::LetGTerm(const SourceLocation& Location,
                       const vector<LetBindingGTerm*>& Bindings,
                       GTerm* BoundInTerm,
                       SymbolTableScope* Scope)
        : GTerm(Location, GTERMKIND_LET),
          Bindings(Bindings),
          BoundInTerm(BoundInTerm),
          Scope(Scope)
    {
        // Nothing here
    }

    LetGTerm::~LetGTerm()
    {
        for(auto const& Binding : Bindings) {
            delete Binding;
        }

        delete BoundInTerm;
        delete Scope;
    }

    void LetGTerm::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitLetGTerm(this);
    }

    ASTBase* LetGTerm::Clone() const
    {
        return new LetGTerm(Location, CloneVector(Bindings),
                            static_cast<GTerm*>(BoundInTerm->Clone()),
                            Scope->Clone());
    }

    const SortExpr* LetGTerm::GetTermSort(SymbolTable* SymTab) const
    {
        SymTab->Push(Scope);
        auto Retval = BoundInTerm->GetTermSort(SymTab);
        SymTab->Pop();
        return Retval;
    }

    const vector<LetBindingGTerm*>& LetGTerm::GetBindings() const
    {
        return Bindings;
    }

    GTerm* LetGTerm::GetBoundInTerm() const
    {
        return BoundInTerm;
    }

    SymbolTableScope* LetGTerm::GetScope() const
    {
        return Scope;
    }

    NTDef::NTDef(const SourceLocation& Location,
                 const string& Symbol,
                 const SortExpr* Sort,
                 const vector<GTerm*>& Expansions)
        : ASTBase(Location),
          Symbol(Symbol),
          Sort(Sort), Expansions(Expansions)
    {
        // Nothing here
    }

    NTDef::~NTDef()
    {
        delete Sort;
        for(auto const& Expansion : Expansions) {
            delete Expansion;
        }
    }

    void NTDef::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitNTDef(this);
    }

    ASTBase* NTDef::Clone() const
    {
        return new NTDef(Location, Symbol, static_cast<const SortExpr*>(Sort->Clone()),
                         CloneVector(Expansions));
    }

    const string& NTDef::GetName() const
    {
        return Symbol;
    }

    const SortExpr* NTDef::GetSort() const
    {
        return Sort;
    }

    const vector<GTerm*>& NTDef::GetExpansions() const
    {
        return Expansions;
    }

    Program::Program(const vector<ASTCmd*>& Cmds)
        : ASTBase(SourceLocation::None),
          Cmds(Cmds)
    {
        // Nothing here
    }

    Program::~Program()
    {
        for(auto const& Cmd : Cmds) {
            delete Cmd;
        }
    }

    void Program::Accept(ASTVisitorBase* Visitor) const
    {
        Visitor->VisitProgram(this);
    }

    ASTBase* Program::Clone() const
    {
        return new Program(CloneVector(Cmds));
    }

    const vector<ASTCmd*>& Program::GetCmds() const
    {
        return Cmds;
    }

    ASTVisitorBase::ASTVisitorBase(const string& Name)
        : Name(Name)
    {
        // Nothing here
    }

    ASTVisitorBase::~ASTVisitorBase()
    {
        // Nothing here
    }

    void ASTVisitorBase::VisitProgram(const Program* Prog)
    {
        auto const& Cmds = Prog->GetCmds();
        for(auto const& Cmd : Cmds) {
            Cmd->Accept(this);
        }
    }

    void ASTVisitorBase::VisitArgSortPair(const ArgSortPair* ASPair)
    {
        ASPair->GetSort()->Accept(this);
    }

    void ASTVisitorBase::VisitFunDefCmd(const FunDefCmd* Cmd)
    {
        // Visit the args
        auto const& Args = Cmd->GetArgs();
        for(auto const& ASPair : Args) {
            ASPair->Accept(this);
        }

        // Visit the return sort
        Cmd->GetSort()->Accept(this);
        // Visit the term
        Cmd->GetTerm()->Accept(this);
    }

    void ASTVisitorBase::VisitFunDeclCmd(const FunDeclCmd* Cmd)
    {
        // Visit the arg sorts
        auto const& ArgTypes = Cmd->GetArgSorts();
        for(auto const& ArgType : ArgTypes) {
            ArgType->Accept(this);
        }

        // Visit the return sort
        Cmd->GetSort()->Accept(this);
    }

    void ASTVisitorBase::VisitSynthFunCmd(const SynthFunCmd* Cmd)
    {
        auto const& ArgSorts = Cmd->GetArgs();
        for(auto const& Arg : ArgSorts) {
            Arg->Accept(this);
        }

        // Visit the return type
        Cmd->GetSort()->Accept(this);
        // Visit the Grammar rules
        auto const& Rules = Cmd->GetGrammarRules();
        for(auto const& Rule : Rules) {
            Rule->Accept(this);
        }
    }

    void ASTVisitorBase::VisitSortDefCmd(const SortDefCmd* Cmd)
    {
        // Just visit the sort expression
        Cmd->GetSortExpr()->Accept(this);
    }

    void ASTVisitorBase::VisitSetOptsCmd(const SetOptsCmd* Cmd)
    {
        // Nothing to do really.
    }

    void ASTVisitorBase::VisitVarDeclCmd(const VarDeclCmd* Cmd)
    {
        // Visit the sort expression
        Cmd->GetSort()->Accept(this);
    }

    void ASTVisitorBase::VisitConstraintCmd(const ConstraintCmd* Cmd)
    {
        // Visit the constraint term
        Cmd->GetTerm()->Accept(this);
    }

    void ASTVisitorBase::VisitSetLogicCmd(const SetLogicCmd* Cmd)
    {
        // Nothing to do really
    }

    void ASTVisitorBase::VisitCheckSynthCmd(const CheckSynthCmd* Cmd)
    {
        // Nothing to do really
    }

    void ASTVisitorBase::VisitIntSortExpr(const IntSortExpr* Sort)
    {
        // Nothing to do really
    }

    void ASTVisitorBase::VisitBVSortExpr(const BVSortExpr* Sort)
    {
        // Nothing to do really
    }

    void ASTVisitorBase::VisitNamedSortExpr(const NamedSortExpr* Sort)
    {
        // Nothing to do really
    }

    void ASTVisitorBase::VisitArraySortExpr(const ArraySortExpr* Sort)
    {
        Sort->GetDomainSort()->Accept(this);
        Sort->GetRangeSort()->Accept(this);
    }

    void ASTVisitorBase::VisitRealSortExpr(const RealSortExpr* Sort)
    {
        // Nothing to do really
    }

    void ASTVisitorBase::VisitFunSortExpr(const FunSortExpr* Sort)
    {
        auto const& ArgSorts = Sort->GetArgSorts();
        for(auto const& ArgSort : ArgSorts) {
            ArgSort->Accept(this);
        }
        Sort->GetRetSort()->Accept(this);
    }

    void ASTVisitorBase::VisitBoolSortExpr(const BoolSortExpr* Sort)
    {
        // Nothing to do really
    }

    void ASTVisitorBase::VisitEnumSortExpr(const EnumSortExpr* Sort)
    {
        // Nothing to do really
    }

    void ASTVisitorBase::VisitFunTerm(const FunTerm* TheTerm)
    {
        auto const& Args = TheTerm->GetArgs();
        for(auto const& Arg : Args) {
            Arg->Accept(this);
        }
    }

    void ASTVisitorBase::VisitLiteralTerm(const LiteralTerm* TheTerm)
    {
        TheTerm->GetLiteral()->Accept(this);
    }

    void ASTVisitorBase::VisitSymbolTerm(const SymbolTerm* TheTerm)
    {
        // Nothing to do really
    }

    void ASTVisitorBase::VisitLetTerm(const LetTerm* TheTerm)
    {
        auto const& Bindings = TheTerm->GetBindings();
        for(auto const& Binding : Bindings) {
            Binding->Accept(this);
        }
        TheTerm->GetBoundInTerm()->Accept(this);
    }

    void ASTVisitorBase::VisitFunGTerm(const FunGTerm* TheTerm)
    {
        auto const& Args = TheTerm->GetArgs();
        for(auto const Arg : Args) {
            Arg->Accept(this);
        }
    }

    void ASTVisitorBase::VisitLiteralGTerm(const LiteralGTerm* TheTerm)
    {
        TheTerm->GetLiteral()->Accept(this);
    }

    void ASTVisitorBase::VisitSymbolGTerm(const SymbolGTerm* TheTerm)
    {
        // Nothing to do really
    }

    void ASTVisitorBase::VisitLetGTerm(const LetGTerm* TheTerm)
    {
        auto const& Bindings = TheTerm->GetBindings();

        for(auto const& Binding : Bindings) {
            Binding->Accept(this);
        }

        TheTerm->GetBoundInTerm()->Accept(this);
    }

    void ASTVisitorBase::VisitConstantGTerm(const ConstantGTerm* TheTerm)
    {
        TheTerm->GetSort()->Accept(this);
    }

    void ASTVisitorBase::VisitVariableGTerm(const VariableGTerm* TheTerm)
    {
        TheTerm->GetSort()->Accept(this);
    }

    void ASTVisitorBase::VisitNTDef(const NTDef* Def)
    {
        Def->GetSort()->Accept(this);
        auto const& Expansions = Def->GetExpansions();
        for(auto const& Expansion : Expansions) {
            Expansion->Accept(this);
        }
    }

    void ASTVisitorBase::VisitLiteral(const Literal* TheLiteral)
    {
        // Nothing to do here really
    }

    void ASTVisitorBase::VisitLetBindingTerm(const LetBindingTerm* Binding)
    {
        Binding->GetVarSort()->Accept(this);
        Binding->GetBoundToTerm()->Accept(this);
    }

    void ASTVisitorBase::VisitLetBindingGTerm(const LetBindingGTerm* Binding)
    {
        Binding->GetVarSort()->Accept(this);
        Binding->GetBoundToTerm()->Accept(this);
    }

    SynthLib2Parser::SynthLib2Parser()
        : TheProgram(NULL), TheSymbolTable(NULL),
          ParseComplete(false)
    {
        // Nothing here
    }

    SynthLib2Parser::~SynthLib2Parser()
    {
        if(TheProgram != NULL) {
            delete TheProgram;
            TheProgram = NULL;
        }
        if(TheSymbolTable != NULL) {
            delete TheSymbolTable;
            TheSymbolTable = NULL;
        }
    }

    void SynthLib2Parser::operator () (const string& FileName,
                                       bool Pedantic)
    {
        if(TheProgram != NULL) {
            delete TheProgram;
            TheProgram = NULL;
        }
        if(TheSymbolTable != NULL) {
            delete TheSymbolTable;
            TheSymbolTable = NULL;
        }


        yyin = fopen(FileName.c_str(), "r");
        if (yyin == NULL) {
            throw SynthLib2ParserException("Could not open input file \"" + FileName + "\"");
        }
        if(yyparse() != 0) {
            throw SynthLib2ParserException("Error parsing input file \"" + FileName + "\"");
        }

        fclose(yyin);

        TheProgram = SynthLib2Bison::TheProgram;
        TheSymbolTable = new SymbolTable();

        LogicSymbolLoader::LoadAll(TheSymbolTable);
        SymtabBuilder::Do(TheProgram, TheSymbolTable);
        LogicSymbolLoader::Reset();

        SynthLib2Bison::TheProgram = NULL;
    }

    void SynthLib2Parser::operator () (FILE* Handle,
                                       bool Pedantic)
    {
        if (Handle == NULL) {
            throw SynthLib2ParserException("Cannot parse NULL handle");
        }

        if(TheProgram != NULL) {
            delete TheProgram;
            TheProgram = NULL;
        }
        if(TheSymbolTable != NULL) {
            delete TheSymbolTable;
            TheSymbolTable = NULL;
        }

        yyin = Handle;

        if(yyparse() != 0) {
            throw SynthLib2ParserException("Error parsing input file via handle");
        }

        // Not ours to close;

        TheProgram = SynthLib2Bison::TheProgram;
        TheSymbolTable = new SymbolTable();

        LogicSymbolLoader::LoadAll(TheSymbolTable);
        SymtabBuilder::Do(TheProgram, TheSymbolTable);
        LogicSymbolLoader::Reset();

        SynthLib2Bison::TheProgram = NULL;
    }

    Program* SynthLib2Parser::GetProgram() const
    {
        if(TheProgram == NULL) {
            throw SynthLib2ParserException((string)"SynthLib2Parser: No program parsed yet!" +
                                           " But SynthLib2Parser::GetProgram() called");
        }
        return TheProgram;
    }

    SymbolTable* SynthLib2Parser::GetSymbolTable() const
    {
        if(TheSymbolTable == NULL) {
            throw SynthLib2ParserException((string)"SynthLib2Parser: No program parsed yet!" +
                                           " But SynthLib2Parser::GetSymbolTable() called");
        }
        return TheSymbolTable;
    }

} /* end namespace */
