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

%{
    #include <SynthLib2ParserIFace.hpp>
    #include <SymbolTable.hpp>
    #include <iostream>
    #include <string.h>
    #include <boost/lexical_cast.hpp>
    #include <LogicSymbols.hpp>

    using namespace std;
    using namespace Sygus2Parser;

    namespace Sygus2Bison {
        Program* the_program = NULL;
        string* file_name = NULL;
    }

    long yylinenum = 1;
    long yycolnum = 0;
    extern char* yytext;

    extern int yylex(void);
    int yyerror(char* s)
    {
        cerr << "Parse error: Last token read was: " << yytext
             << " at line: " << yylinenum << ", column: "
             << yycolnum - strlen(yytext) << endl;
        cerr.flush();
        exit(1);
    }

    #define GET_CURRENT_LOCATION()                                                                 \
        SourceLocation(@$.first_line, @$.first_column, @$.last_line, @$.last_column,               \
                       file_name == nullptr ? "", *file_name)

%}

%union {
    // yyunion fields
    string* lexer_string;
    Command* the_command;
    Grammar* the_grammar;
    vector<SortedSymbol*>* sorted_symbol_vector;
}

%token TK_DEFINE_SORT TK_DEFINE_FUN TK_DECLARE_FUN TK_SET_OPTION TK_SET_FEATURE
%token TK_CHECK_SYNTH TK_SYNTH_FUN TK_DECLARE_VAR TK_INV_CONSTRAINT TK_SYNTH_INV
%token TK_LPAREN TK_RPAREN TK_SET_LOGIC TK_BV
%token TK_BOOL TK_ENUM TK_CONSTRAINT
%token TK_CONSTANT TK_VARIABLE TK_LOCAL_VARIABLE TK_INPUT_VARIABLE
%token TK_ERROR TK_DOUBLECOLON TK_COLON
%token TK_LET TK_ARRAY TK_REAL TK_EXISTS TK_FORALL
%token TK_DECLARE_DATATYPE TK_DECLARE_DATATYPES TK_DECLARE_SORT

%token<LexerString> TK_NUMERAL TK_DECIMAL TK_BOOL_CONST TK_HEX_CONST TK_BIN_CONST
%token<LexerString> TK_ENUM_LITERAL TK_BV_LITERAL TK_SYMBOL

%type<lexer_string> Symbol BoolConst
%type<sorted_symbol_vector> SortedSymbolStar
%type<the_grammar> OptGrammarDef


/* %type<TheSortExpr> SortExpr */
/* %type<TheCmd> SortDefCmd FunDefCmd FunDeclCmd SetOptionCmd SetFeatureCmd SynthFunCmd */
/* %type<TheCmd> CheckSynthCmd VarDeclCmd ConstraintCmd SetLogicCmd Cmd DatatypeDeclCmd */
/* %type<TheCmd> DatatypesDeclCmd InvConstraintCmd SortDeclCmd */
/* %type<CmdList> CmdStar */
/* %type<LexerString> IntConst */
/* %type<LexerString> BoolConst */
/* %type<LexerString> BVConst */
/* %type<LexerString> EnumConst */
/* %type<LexerString> RealConst; */
/* %type<SymbolVector> ECList */
/* %type<SymbolVector> SymbolPlus */
/* %type<LexerString> Symbol */
/* %type<SymbolSortVector> ArgList */
/* %type<SymbolSortVector> SymbolSortPairStar */
/* %type<SymbolSortPair> SymbolSortPair */
/* %type<TheTerm> Term LetTerm */
/* %type<TermVector> TermStar */
/* %type<TheLiteral> Literal */
/* %type<NTDefVector> NTDefPlus */
/* %type<TheNTDef> NTDef */
/* %type<GTermVector> GTermPlus */
/* %type<TheGTerm> GTerm LetGTerm */
/* %type<GTermVector> GTermStar */
/* %type<TheProgram> Prog */
/* %type<STPair> LetBindingTerm */
/* %type<STPairVector> LetBindingTermPlus */
/* %type<SGPair> LetBindingGTerm */
/* %type<SGPairVector> LetBindingGTermPlus */
/* %type<SortVector> SortStar */

%%

start : Prog
      { SynthLib2Bison::TheProgram = $1; }

Prog : CommandStar
     {
         $$ = new Program(GET_CURRENT_LOCATION(), *$1);
         delete $1;
     }

CommandStar : CommandStar Command
            {
                $1->push_back($2);
                $$ = $1;
            }
            | /* empty */
            {
                $$ = new vector<ASTCmd*>();
            }

Command : CheckSynthCommand
        | ConstraintCommand
        | VarDeclCommand
        | InvConstraintCommand
        | SetFeatureCommand
        | SynthFunCommand
        | SynthInvCommand
        | SmtCommand

SmtCommand : SortDeclCommand
           | FunDefCommand
           | SortDefCommand
           | SetLogicCommand
           | SetOptionCommand

CheckSynthCommand : TK_LPAREN TK_CHECK_SYNTH TK_RPAREN
                  {
                      $$ = new CheckSynthCommand(GET_CURRENT_LOCATION());
                  }

ConstraintCommand : TK_LPAREN TK_CONSTRAINT Term TK_RPAREN
                  {
                      $$ = new ConstraintCommand(GET_CURRENT_LOCATION(), $3);
                  }

VarDeclCommand : TK_LPAREN TK_DECLARE_VAR Symbol SortExpr TK_RPAREN
           {
               $$ = new VarDeclCmd(GET_CURRENT_LOCATION(), *$3, $4);
               delete $3;
           }

InvConstraintCommand : TK_LPAREN TK_INV_CONSTRAINT Symbol Symbol Symbol Symbol TK_RPAREN
                 {
                     $$ = new InvConstraintCmd(GET_CURRENT_LOCATION(), *$3, *$4, *$5, *$6);
                     delete $3;
                     delete $4;
                     delete $5;
                     delete $6;
                 }

SetFeatureCommand : TK_LPAREN TK_SET_FEATURE TK_COLON Symbol BoolConst TK_RPAREN
              {
                  bool value;
                  if (*$5 == "true") {
                      value = true;
                  } else if (*$5 == "false") {
                      value = false;
                  } else {
                      cout << "Error parsing a boolean value: " << value << endl;
                      throw Exception();
                  }
                  $$ = new SetFeatureCmd(GetCurrentLocation(), *$4, value);
                  delete $4;
                  delete $5;
              }

SynthFunCmd : TK_LPAREN TK_SYNTH_FUN Symbol SortedSymbolStar SortExpr OptGrammarDef TK_RPAREN
            {
                $$ = new SynthFunCmd(GetCurrentLocation(), *$3, *$4, $5, $6);


                delete $3;
                delete $4;
                delete $7;
            }

SynthInvCommand : TK_LPAREN TK_SYNTH_INV Symbol SortedSymbolStar OptGrammarDef TK_RPAREN
            {
                $$ = new SynthInvCommand(GET_CURRENT_LOCATION(), *$3, *$4, $5);
                delete $3;
                delete $4;
            }
SortDeclCommand : TK_LPAREN TK_DECLARE_SORT Symbol TK_NUMERAL TK_RPAREN
                {
                    istringstream istr(*$4);
                    u32 value;
                    istr >> value;
                    $$ = new DeclareSortCommand(GET_CURRENT_LOCATION(), *$3, value);
                    delete $3;
                }


FunDefCommand : TK_LPAREN TK_DEFINE_FUN Symbol SortedSymbolStar SortExpr Term TK_RPAREN
          {
              $$ = new DefineFunCommand(GET_CURRENT_LOCATION(), *$3, *$4, $5, $6, NULL);
              delete $3;
              delete $4;
          }

SortDefCommand : TK_LPAREN TK_DEFINE_SORT Symbol SortExpr TK_RPAREN
           {
               $$ = new DefineSortCommand(GET_CURRENT_LOCATION(), *$3, $4);
               delete $3;
           }

SetLogicCommand : TK_LPAREN TK_SET_LOGIC Symbol TK_RPAREN
            {
                $$ = new SetLogicCommand(GET_CURRENT_LOCATION(), *$3);
                delete $3;
            }

SetOptionCommand : TK_LPAREN TK_SET_OPTION TK_COLON Symbol Literal TK_RPAREN
           {
               $$ = new SetOptionCommand(GET_CURRENT_LOCATION(), *$4, $5);
               delete $4;
           }

SortExpr : Identifier
         {
             $$ = new SortExpr(GET_CURRENT_LOCATION(), *$1);
             delete $1;
         }
         | TK_LPAREN Identifier SortExprPlus TK_RPAREN
         {
             $$ = new SortExpr(GET_CURRENT_LOCATION(), *$1, *$2);
             delete $1;
             delete $2;
         }

SortExprPlus : SortExprPlus SortExpr
             {
                 $$ = $1;
                 $$->push_back($2);
             }
             | SortExpr
             {
                 $$ = new vector<SortExpr*>();
                 $$->push_back($1)
             }

Identifier : Symbol
           {
               $$ = new Identifier(GET_CURRENT_LOCATION(), *$1);
               delete $1;
           }
           | TK_LPAREN UNDERSCORE Symbol IndexPlus TK_RPAREN
           {
               $$ = new Identifier(GET_CURRENT_LOCATION(), *$3, *$4);
               delete $3;
               delete $4;
           }

Symbol : TK_SYMBOL
       {
           $$ = $1;
       }

IndexPlus : IndexPlus Index
          {
              $$ = $1;
              $$->push_back($2);
          }
          | Index
          {
              $$ = new vector<Index*>();
              $$->push_back($1)
          }

Index : TK_NUMERAL
      {
          istringstream istr(*$1);
          int value;
          istr >> value;
          $$ = new Index(GET_CURRENT_LOCATION(), value);
          delete $1;
      }
      | Symbol
      {
          $$ = new Index(GET_CURRENT_LOCATION(), *$1);
          delete $1;
      }

Term : Identifier
     {
         $$ = new IdentifierTerm(GET_CURRENT_LOCATION(), $1);
     }
     | Literal
     {
         $$ = new LiteralTerm(GET_CURRENT_LOCATION(), $1);
     }
     | TK_LPAREN Identifier TermPlus TK_RPAREN
     {
         $$ = new FunctionApplicationTerm(GET_CURRENT_LOCATION(), $2, *$3);
         delete $3;
     }
     | TK_LPAREN TK_EXISTS SortedSymbolPlus Term TK_RPAREN
     {
         $$ = new QuantifiedTerm(GET_CURRENT_LOCATION(), QuantifierKind::Exists, *$3, $4);
         delete $3;
     }
     | TK_LPAREN TK_FORALL SortedSymbolPlus Term TK_RPAREN
     {
         $$ = new QuantifiedTerm(GET_CURRENT_LOCATION(), QuantifierKind::Forall, *$3, $4);
         delete $3;
     }
     | TK_LPAREN TK_LET BindingPlus Term TK_RPAREN
     {
         $$ = new LetTerm(GET_CURRENT_LOCATION(), *$3, $4);
         delete $3;
     }

SortedSymbolPlus : SortedSymbolPlus SortedSymbol
                 {
                     $$ = $1;
                     $$->push_back($2);
                 }
                 | SortedSymbol
                 {
                     $$ = new vector<SortedSymbol*>();
                     $$->push_back($1)
                 }

SortedSymbolStar : SortedSymbolStar SortedSymbol
                 {
                     $$ = $1;
                     $$->push_back($2);
                 }
                 | /* empty */
                 {
                     $$ = new vector<SortedSymbol*>();
                 }

SortedSymbol : TK_LPAREN Symbol SortExpr TK_RPAREN
             {
                 $$ = new SortedSymbol(GET_CURRENT_LOCATION(), *$2, $3);
                 delete $2;
             }

BindingPlus : BindingPlus Binding
            {
                $$ = $1;
                $$->push_back($2)
            }
            | Binding
            {
                $$ = new vector<VariableBinding*>();
                $$->push_back($1);
            }

Binding : TK_LPAREN Symbol Term TK_RPAREN
        {
            $$ = new VariableBinding(GET_CURRENT_LOCATION(), $2, $3);
            delete $2;
        }

Literal : TK_NUMERAL
        {
            $$ = new Literal(GET_CURRENT_LOCATION(), *$1 LiteralKind::Numeral);
            delete $1;
        }
        | TK_BOOL_CONST
        {
            $$ = new Literal(GET_CURRENT_LOCATION(), *$1, LiteralKind::Boolean);
            delete $1;
        }
        | TK_DECIMAL
        {
            $$ = new Literal(GET_CURRENT_LOCATION(), *$1, LiteralKind::Decimal);
            delete $1;
        }
        | TK_HEX_CONST
        {
            $$ = new Literal(GET_CURRENT_LOCATION(), *$1, LiteralKind::Hexadecimal);
            delete $1;
        }
        | TK_BIN_CONST
        {
            $$ = new Literal(GET_CURRENT_LOCATION(), *$1, LiteralKind::Binary);
            delete $1;
        }
        | TK_STRING_LITERAL
        {
            $$ = new Literal(GET_CURRENT_LOCATION(), *$1, LiteralKind::String);
            delete $1;
        }

OptGrammarDef : GrammarDef
              {
                  $$ = $1;
              }
              | /* empty */
              {
                  $$ = nullptr;
              }

GrammarDef : TK_LPAREN SortedSymbolPlus TK_RPAREN TK_LPAREN GroupedRuleListPlus TK_RPAREN

GroupedRuleListPlus : GroupedRuleListPlus : GroupedRuleList
                    | GroupedRuleList

GroupedRuleList : TK_LPAREN Symbol SortExpr TK_LPAREN GTermPlus TK_RPAREN TK_RPAREN

GTermPlus : GTermPlus GTerm
          | GTerm

GTerm : TK_LPAREN TK_CONSTANT SortExpr TK_RPAREN
      | TK_LPAREN TK_VARIABLE SortExpr TK_RPAREN
      | BFTerm

BFTerm : IdentifierTerm
       | LiteralTerm
       | TK_LPAREN Identifier BFTermPlus TK_RPAREN

BFTermPlus : BFTermPlus BFTerm
           | BFTerm
