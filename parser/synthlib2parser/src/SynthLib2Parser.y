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
    using namespace SynthLib2Parser;

    namespace SynthLib2Bison {
        Program* TheProgram = NULL;
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

    static inline SourceLocation GetCurrentLocation()
    {
        return SourceLocation(yylinenum, yycolnum);
    }
%}

%union {
    // yyunion fields
    string* LexerString;
    pair<string, string>* EnumConstant;
    const SortExpr* TheSortExpr;
    Literal* TheLiteral;
    vector<string>* SymbolVector;
    ArgSortPair* SymbolSortPair;
    vector<const SortExpr*>* SortVector;
    vector<ArgSortPair*>* SymbolSortVector;
    pair<string, string>* SymbolSymbolPair;
    vector<pair<string, string> >* SymbolSymbolVector;
    Term* TheTerm;
    vector<Term*>* TermVector;
    LetBindingTerm* STPair;
    vector<LetBindingTerm*>* STPairVector;
    vector<NTDef*>* NTDefVector;
    NTDef* TheNTDef;
    GTerm* TheGTerm;
    vector<GTerm*>* GTermVector;
    LetBindingGTerm* SGPair;
    vector<LetBindingGTerm*>* SGPairVector;
    Program* TheProgram;
    ASTCmd* TheCmd;
    vector<ASTCmd*>* CmdList;
}

%token TK_DEFINE_SORT TK_DEFINE_FUN TK_DECLARE_FUN TK_SET_OPTIONS
%token TK_CHECK_SYNTH TK_SYNTH_FUN TK_DECLARE_VAR
%token TK_LPAREN TK_RPAREN TK_SET_LOGIC TK_BV
%token TK_INT TK_BOOL TK_ENUM TK_CONSTRAINT
%token TK_CONSTANT TK_VARIABLE TK_LOCAL_VARIABLE TK_INPUT_VARIABLE
%token TK_ERROR TK_DOUBLECOLON
%token TK_LET TK_ARRAY TK_REAL

%token<LexerString> TK_INT_LITERAL TK_REAL_LITERAL TK_BOOL_LITERAL
%token<LexerString> TK_ENUM_LITERAL TK_BV_LITERAL TK_SYMBOL
%token<LexerString> TK_QUOTED_LITERAL

%type<TheSortExpr> SortExpr
%type<TheCmd> SortDefCmd FunDefCmd FunDeclCmd SetOptsCmd SynthFunCmd
%type<TheCmd> CheckSynthCmd VarDeclCmd SetLogicCmd ConstraintCmd Cmd
%type<CmdList> CmdPlus
%type<LexerString> IntConst
%type<LexerString> BoolConst
%type<LexerString> BVConst
%type<LexerString> EnumConst
%type<LexerString> RealConst;
%type<SymbolVector> ECList
%type<SymbolVector> SymbolPlus
%type<LexerString> Symbol
%type<SymbolSymbolVector> OptList
%type<SymbolSymbolVector> SymbolPairPlus
%type<SymbolSymbolPair> SymbolPair
%type<SymbolSortVector> ArgList
%type<SymbolSortVector> SymbolSortPairStar
%type<SymbolSortPair> SymbolSortPair
%type<TheTerm> Term LetTerm
%type<TermVector> TermStar
%type<TheLiteral> Literal
%type<NTDefVector> NTDefPlus
%type<TheNTDef> NTDef
%type<GTermVector> GTermPlus
%type<TheGTerm> GTerm LetGTerm
%type<GTermVector> GTermStar
%type<TheProgram> Prog
%type<STPair> LetBindingTerm
%type<STPairVector> LetBindingTermPlus
%type<SGPair> LetBindingGTerm
%type<SGPairVector> LetBindingGTermPlus
%type<SortVector> SortStar

%%

start : Prog
      { SynthLib2Bison::TheProgram = $1; }
      | /* epsilon */
      {
          vector<ASTCmd*> Dummy;
          SynthLib2Bison::TheProgram = new Program(Dummy);
      }

Prog : SetLogicCmd CmdPlus
     {
         vector<ASTCmd*> AllCmds;
         AllCmds.push_back($1);
         AllCmds.insert(AllCmds.end(), $2->begin(), $2->end());
         delete $2;
         $$ = new Program(AllCmds);
     }
     | CmdPlus
     {
         $$ = new Program(*$1);
         delete $1;
     }

Symbol : TK_SYMBOL
       {
           $$ = $1;
       }

SetLogicCmd : TK_LPAREN TK_SET_LOGIC Symbol TK_RPAREN
            {
                if(*$3 != "LIA" && *$3 != "Reals" && *$3 != "Arrays" && *$3 != "BV") {
                    throw SynthLib2ParserException("Invalid logic in set logic command");
                }
                $$ = new SetLogicCmd(GetCurrentLocation(), *$3);
                delete $3;
            }

CmdPlus : CmdPlus Cmd
        {
            $$ = $1;
            $$->push_back($2);
        }
        | Cmd
        {
            $$ = new vector<ASTCmd*>();
            $$->push_back($1);
        }

Cmd : FunDefCmd
    | FunDeclCmd
    | SynthFunCmd
    | CheckSynthCmd
    | ConstraintCmd
    | SortDefCmd
    | SetOptsCmd
    | VarDeclCmd

VarDeclCmd : TK_LPAREN TK_DECLARE_VAR Symbol SortExpr TK_RPAREN
           {
               $$ = new VarDeclCmd(GetCurrentLocation(),
                                   *$3, $4);
               delete $3;
           }

SortDefCmd : TK_LPAREN TK_DEFINE_SORT Symbol SortExpr TK_RPAREN
           {
               $$ = new SortDefCmd(GetCurrentLocation(),
                                   *$3, $4);
               if ($4->GetKind() == SORTKIND_ENUM) {
                   auto SortExprAsEnum = dynamic_cast<const EnumSortExpr*>($4);
                   SortExprAsEnum->SetEnumSortName(*$3);
               }
               delete $3;
           }

SortExpr : TK_LPAREN TK_BV IntConst TK_RPAREN
         {
             if (boost::lexical_cast<u32>(*$3) == 0) {
                 throw SynthLib2ParserException("Zero-length bitvectors not supported.\n" +
                                                GetCurrentLocation().ToString());
             }
             $$ = new BVSortExpr(GetCurrentLocation(),
                                 boost::lexical_cast<u32>(*$3));
             delete $3;
         }
         | TK_INT
         {
             $$ = new IntSortExpr(GetCurrentLocation());
         }
         | TK_BOOL
         {
             $$ = new BoolSortExpr(GetCurrentLocation());
         }
         | TK_REAL
         {
             $$ = new RealSortExpr(GetCurrentLocation());
         }
         | TK_LPAREN TK_ENUM ECList TK_RPAREN
         {
             $$ = new EnumSortExpr(GetCurrentLocation(), *$3);
             delete $3;
         }
         | TK_LPAREN TK_ARRAY SortExpr SortExpr TK_RPAREN
         {
             $$ = new ArraySortExpr(GetCurrentLocation(),
                                    $3, $4);
         }
         | Symbol
         {
             $$ = new NamedSortExpr(GetCurrentLocation(), *$1);
             delete $1;
         }

IntConst : TK_INT_LITERAL
         {
             $$ = $1;
         }

BoolConst : TK_BOOL_LITERAL
          {
              $$ = $1;
          }

BVConst : TK_BV_LITERAL
        {
            $$ = $1;
        }

EnumConst : Symbol TK_DOUBLECOLON Symbol
          {
              auto ConCat = new string(*$1 + "::" + *$3);
              delete $1;
              delete $3;
              $$ = ConCat;
          }

RealConst : TK_REAL_LITERAL
          {
              $$ = $1;
          }

ECList : TK_LPAREN SymbolPlus TK_RPAREN
       {
           $$ = $2;
       }

SymbolPlus : SymbolPlus Symbol
           {
               $$ = $1;
               $$->push_back(*$2);
               delete $2;
           }
           | Symbol
           {
               $$ = new vector<string>();
               $$->push_back(*$1);
               delete $1;
           }

SetOptsCmd : TK_LPAREN TK_SET_OPTIONS OptList TK_RPAREN
           {
               $$ = new SetOptsCmd(GetCurrentLocation(), *$3);
               delete $3;
           }

OptList : TK_LPAREN SymbolPairPlus TK_RPAREN
        {
            $$ = $2;
        }

SymbolPairPlus : SymbolPairPlus SymbolPair
               {
                   $$ = $1;
                   $$->push_back(*$2);
                   delete $2;
               }
               | SymbolPair
               {
                   $$ = new vector<pair<string, string> >();
                   $$->push_back(*$1);
                   delete $1;
               }

SymbolPair : TK_LPAREN Symbol TK_QUOTED_LITERAL TK_RPAREN
           {
               $$ = new pair<string, string>(*$2, $3->substr(1, $3->length() - 2));
               delete $2;
               delete $3;
           }

FunDefCmd : TK_LPAREN TK_DEFINE_FUN Symbol ArgList SortExpr Term TK_RPAREN
          {
              $$ = new FunDefCmd(GetCurrentLocation(),
                                 *$3, *$4, $5, $6, NULL);

              delete $3;
              delete $4;
          }

FunDeclCmd : TK_LPAREN TK_DECLARE_FUN Symbol TK_LPAREN SortStar TK_RPAREN SortExpr TK_RPAREN
           {
               $$ = new FunDeclCmd(GetCurrentLocation(),
                                   *$3, *$5, $7);
               delete $3;
               delete $5;
           }

SortStar : SortStar SortExpr
         { $$ = $1; $$->push_back($2); }
         | /* empty */
         { $$ = new vector<const SortExpr*>(); }

ArgList : TK_LPAREN SymbolSortPairStar TK_RPAREN
        {
            $$ = $2;
        }

SymbolSortPairStar : SymbolSortPairStar SymbolSortPair
                   {
                       $$ = $1;
                       $$->push_back($2);
                   }
                   | /* epsilon */
                   {
                       $$ = new vector<ArgSortPair*>();
                   }


SymbolSortPair : TK_LPAREN Symbol SortExpr TK_RPAREN
               {
                   $$ = new ArgSortPair(GetCurrentLocation(), *$2, $3);
                   delete $2;
               }

Term : TK_LPAREN Symbol TermStar TK_RPAREN
     {
         $$ = new FunTerm(GetCurrentLocation(), *$2, *$3);
         delete $2;
         delete $3;
     }
     | Literal
     {
         $$ = new LiteralTerm(GetCurrentLocation(), $1);
     }
     | Symbol
     {
         $$ = new SymbolTerm(GetCurrentLocation(), *$1);
         delete $1;
     }
     | LetTerm
     {
         $$ = $1;
     }

LetTerm : TK_LPAREN TK_LET TK_LPAREN LetBindingTermPlus TK_RPAREN Term TK_RPAREN
        {
            $$ = new LetTerm(GetCurrentLocation(), *$4, $6, NULL);
            delete $4;
        }

LetBindingTermPlus : LetBindingTermPlus LetBindingTerm
                   {
                       $$ = $1;
                       $$->push_back($2);
                   }
                   | LetBindingTerm
                   {
                       $$ = new vector<LetBindingTerm*>();
                       $$->push_back($1);
                   }

LetBindingTerm : TK_LPAREN Symbol SortExpr Term TK_RPAREN
               {
                   $$ = new LetBindingTerm(GetCurrentLocation(),
                                           *$2, $3, $4);
                   delete $2;
               }

TermStar : TermStar Term
         {
             $$ = $1;
             $$->push_back($2);
         }
         | /* epsilon */
         {
             $$ = new vector<Term*>();
         }

Literal : IntConst
        {
            $$ = new Literal(GetCurrentLocation(), *$1, new IntSortExpr(SourceLocation::None));
            delete $1;
        }
        | BoolConst
        {
            $$ = new Literal(GetCurrentLocation(), *$1, new BoolSortExpr(SourceLocation::None));
            delete $1;
        }
        | BVConst
        {
            if ((*$1)[1] == 'x') {
                $$ = new Literal(GetCurrentLocation(), *$1, new BVSortExpr(SourceLocation::None, ($1->length() - 2) * 4));
            } else {
                $$ = new Literal(GetCurrentLocation(), *$1, new BVSortExpr(SourceLocation::None, ($1->length() - 2)));
            }
            delete $1;
        }
        | EnumConst
        {
            // Lookup the type of the enumeration
            auto ConstString = *$1;
            vector<string> Tokens;
            boost::algorithm::split(Tokens, ConstString, boost::algorithm::is_any_of(": "),
                                    boost::algorithm::token_compress_on);
            auto SortString = Tokens[0];
            SortExpr* Sort = new NamedSortExpr(SourceLocation::None, SortString);
            $$ = new Literal(GetCurrentLocation(), *$1, Sort);
            delete $1;
        }
        | RealConst
        {
            $$ = new Literal(GetCurrentLocation(), *$1, new RealSortExpr(SourceLocation::None));
            delete $1;
        }

NTDefPlus : NTDefPlus NTDef
          {
              $$ = $1;
              $$->push_back($2);
          }
          | NTDef
          {
              $$ = new vector<NTDef*>();
              $$->push_back($1);
          }

NTDef : TK_LPAREN Symbol SortExpr TK_LPAREN GTermPlus TK_RPAREN TK_RPAREN
      {
          $$ = new NTDef(GetCurrentLocation(),
                         *$2, $3, *$5);
          delete $2;
          delete $5;
      }

GTermPlus : GTermPlus GTerm
          {
              $$ = $1;
              $$->push_back($2);
          }
          | GTerm
          {
              $$ = new vector<GTerm*>();
              $$->push_back($1);
          }

CheckSynthCmd : TK_LPAREN TK_CHECK_SYNTH TK_RPAREN
              {
                  $$ = new CheckSynthCmd(GetCurrentLocation());
              }

ConstraintCmd : TK_LPAREN TK_CONSTRAINT Term TK_RPAREN
              {
                  $$ = new ConstraintCmd(GetCurrentLocation(), $3);
              }

SynthFunCmd : TK_LPAREN TK_SYNTH_FUN Symbol ArgList SortExpr
              TK_LPAREN NTDefPlus TK_RPAREN TK_RPAREN
            {
                $$ = new SynthFunCmd(GetCurrentLocation(), *$3,
                                     *$4, $5, *$7, new SymbolTableScope());


                delete $3;
                delete $4;
                delete $7;
            }

GTerm : Symbol
      {
          $$ = new SymbolGTerm(GetCurrentLocation(), *$1);
          delete $1;
      }
      | Literal
      {
          $$ = new LiteralGTerm(GetCurrentLocation(), $1);
      }
      | TK_LPAREN Symbol GTermStar TK_RPAREN
      {
          $$ = new FunGTerm(GetCurrentLocation(), *$2, *$3);
          delete $2;
          delete $3;
      }
      | TK_LPAREN TK_CONSTANT SortExpr TK_RPAREN
      {
          $$ = new ConstantGTerm(GetCurrentLocation(), $3);
      }
      | TK_LPAREN TK_VARIABLE SortExpr TK_RPAREN
      {
          $$ = new VariableGTerm(GetCurrentLocation(), $3, VARKIND_ANY);
      }
      | TK_LPAREN TK_INPUT_VARIABLE SortExpr TK_RPAREN
      {
          $$ = new VariableGTerm(GetCurrentLocation(), $3, VARKIND_INPUT);
      }
      | TK_LPAREN TK_LOCAL_VARIABLE SortExpr TK_RPAREN
      {
          $$ = new VariableGTerm(GetCurrentLocation(), $3, VARKIND_LOCAL);
      }
      | LetGTerm
      {
          $$ = $1;
      }

LetGTerm : TK_LPAREN TK_LET TK_LPAREN LetBindingGTermPlus TK_RPAREN GTerm TK_RPAREN
         {
             $$ = new LetGTerm(GetCurrentLocation(), *$4, $6, new SymbolTableScope());
             delete $4;
         }

LetBindingGTermPlus : LetBindingGTermPlus LetBindingGTerm
                    {
                        $$ = $1;
                        $$->push_back($2);
                    }
                    | LetBindingGTerm
                    {
                        $$ = new vector<LetBindingGTerm*>();
                        $$->push_back($1);
                    }

LetBindingGTerm : TK_LPAREN Symbol SortExpr GTerm TK_RPAREN
                {
                    $$ = new LetBindingGTerm(GetCurrentLocation(),
                                             *$2, $3, $4);
                    delete $2;
                }

GTermStar : GTermStar GTerm
          {
              $$ = $1;
              $$->push_back($2);
          }
          | /* epsilon */
          {
              $$ = new vector<GTerm*>();
          }
