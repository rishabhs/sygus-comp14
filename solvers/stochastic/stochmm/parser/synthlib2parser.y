%{
    #include "parser/iface.h"
    #include <iostream>
    #include <string.h>

    using namespace std;
    using namespace SynthLib2Parser;

    namespace SynthLib2Parser {
        class SynthLib2Parser;
        // The parser needs to set this before
        // calling yyparse()
        const SynthLib2Parser* TheParser = NULL;
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

    static inline void PopulateLocation(ASTBase* Obj)
    {
        Obj->LineNum = yylinenum;
        Obj->ColNum = yycolnum;
    }
    // Includes, C decls, etc
%}

%union {
    // yyunion fields
    string* LexerString;
    SortExpr* TheSortExpr;
    Literal* TheLiteral;
    vector<string>* SymbolVector;
    pair<string, SortExpr*>* SymbolSortPair;
    vector<pair<string, SortExpr*> >* SymbolSortVector;
    pair<string, string>* SymbolSymbolPair;
    vector<pair<string, string> >* SymbolSymbolVector;
    Term* TheTerm;
    vector<Term*>* TermVector;
    vector<NTDef*>* NTDefVector;
    NTDef* TheNTDef;
    GTerm* TheGTerm;
    vector<GTerm*>* GTermVector;
    long IntVal;
    bool BoolVal;
}

%token TK_DEFINE_SORT TK_DEFINE_FUN TK_SET_OPTIONS
%token TK_CHECK_SYNTH TK_SYNTH_FUN TK_DECLARE_VAR
%token TK_LPAREN TK_RPAREN TK_SET_LOGIC TK_BV
%token TK_INT TK_BOOL TK_ENUM TK_CONSTRAINT
%token TK_CONSTANT TK_VARIABLE TK_ERROR

%token<IntVal> TK_INT_LITERAL
%token<BoolVal> TK_BOOL_LITERAL
%token<LexerString> TK_ENUM_LITERAL
%token<LexerString> TK_BV_LITERAL
%token<LexerString> TK_SYMBOL
%token<LexerString> TK_QUOTED_LITERAL

%type<TheSortExpr> SortExpr
%type<IntVal> IntConst
%type<BoolVal> BoolConst
%type<LexerString> BVConst
%type<LexerString> EnumConst
%type<SymbolVector> ECList
%type<SymbolVector> SymbolPlus
%type<LexerString> Symbol
%type<SymbolSymbolVector> OptList
%type<SymbolSymbolVector> SymbolPairPlus
%type<SymbolSymbolPair> SymbolPair
%type<SymbolSortVector> ArgList
%type<SymbolSortVector> SymbolSortPairStar
%type<SymbolSortPair> SymbolSortPair
%type<TheTerm> Term
%type<TermVector> TermStar
%type<TheLiteral> Literal
%type<NTDefVector> NTDefPlus
%type<TheNTDef> NTDef
%type<GTermVector> GTermPlus
%type<TheGTerm> GTerm
%type<GTermVector> GTermStar

%%

start : Prog
      | /* epsilon */

Prog : SetLogicCmd CmdPlus
     | CmdPlus

Symbol : TK_SYMBOL
       {
           $$ = $1;
       }

SetLogicCmd : TK_LPAREN TK_SET_LOGIC Symbol TK_RPAREN
            {
                auto Cmd = new SetLogicCmd();
                PopulateLocation(Cmd);
                Cmd->LogicName = *$3;
                delete $3;
                // Do the callbacks
                TheParser->DoSetLogicCallbacks(Cmd);
                DestroySetLogicCmd(Cmd);
            }

CmdPlus : CmdPlus Cmd
        | Cmd

Cmd : FunDefCmd
    | SynthFunCmd
    | CheckSynthCmd
    | ConstraintCmd
    | SortDefCmd
    | SetOptsCmd
    | VarDeclCmd

VarDeclCmd : TK_LPAREN TK_DECLARE_VAR Symbol SortExpr TK_RPAREN
           {
               auto Cmd = new VarDeclCmd();
               PopulateLocation(Cmd);
               Cmd->VarName = *$3;
               delete $3;
               Cmd->VarType = $4;
               TheParser->DoVarDeclCallbacks(Cmd);
               DestroyVarDeclCmd(Cmd);
           }

SortDefCmd : TK_LPAREN TK_DEFINE_SORT Symbol SortExpr TK_RPAREN
           {
               auto Cmd = new SortDefCmd();
               PopulateLocation(Cmd);
               Cmd->Symbol = *$3;
               delete $3;
               Cmd->Expr = $4;
               TheParser->DoSortDefCallbacks(Cmd);
               DestroySortDefCmd(Cmd);
           }

SortExpr : TK_LPAREN TK_BV IntConst TK_RPAREN
         {
             auto Retval = new SortExpr();
             PopulateLocation(Retval);
             Retval->BSort = SORT_BV;
             Retval->BVSize = $3;
             $$ = Retval;
         }
         | TK_INT
         {
             auto Retval = new SortExpr();
             PopulateLocation(Retval);
             Retval->BSort = SORT_INT;
             $$ = Retval;
         }
         | TK_BOOL
         {
             auto Retval = new SortExpr();
             PopulateLocation(Retval);
             Retval->BSort = SORT_BOOL;
             $$ = Retval;
         }
         | TK_LPAREN TK_ENUM ECList TK_RPAREN
         {
             auto Retval = new SortExpr();
             PopulateLocation(Retval);
             Retval->BSort = SORT_ENUM;
             Retval->EnumConstructors = *$3;
             delete $3;
             $$ = Retval;
         }
         | Symbol
         {
             auto Retval = new SortExpr();
             PopulateLocation(Retval);
             Retval->BSort = SORT_SYMBOL;
             Retval->Symbol = *$1;
             delete $1;
             $$ = Retval;
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

EnumConst : TK_ENUM_LITERAL
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
               $1->push_back(*$2);
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
               auto Cmd = new SetOptsCmd();
               PopulateLocation(Cmd);
               Cmd->Opts = *$3;
               delete $3;
               TheParser->DoSetOptsCallbacks(Cmd);
               DestroySetOptsCmd(Cmd);
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
               $$ = new pair<string, string>(*$2, *$3);
               delete $2;
               delete $3;
           }

FunDefCmd : TK_LPAREN TK_DEFINE_FUN Symbol ArgList SortExpr Term TK_RPAREN
          {
              auto Cmd = new FunDefCmd();
              PopulateLocation(Cmd);
              Cmd->Symbol = *$3;
              delete $3;
              Cmd->Arguments = *$4;
              delete $4;
              Cmd->Type = $5;
              Cmd->Def = $6;
              TheParser->DoFunDefCallbacks(Cmd);
              DestroyFunDefCmd(Cmd);
          }

ArgList : TK_LPAREN SymbolSortPairStar TK_RPAREN
        {
            $$ = $2;
        }

SymbolSortPairStar : SymbolSortPairStar SymbolSortPair
                   {
                       $$ = $1;
                       $$->push_back(*$2);
                       delete $2;
                   }
                   | /* epsilon */
                   {
                       $$ = new vector<pair<string, SortExpr*> >();
                   }


SymbolSortPair : TK_LPAREN Symbol SortExpr TK_RPAREN
               {
                   $$ = new pair<string, SortExpr*>(*$2, $3);
                   delete $2;
               }

Term : TK_LPAREN Symbol TermStar TK_RPAREN
     {
         $$ = new Term();
         PopulateLocation($$);
         $$->TType = TERMTYPE_FUNC;
         $$->Symbol = *$2;
         delete $2;
         $$->Children = *$3;
         delete $3;
     }
     | Literal
     {
         $$ = new Term();
         PopulateLocation($$);
         $$->TType = TERMTYPE_LITERAL;
         $$->TheLiteral = $1;
     }
     | Symbol
     {
         $$ = new Term();
         PopulateLocation($$);
         $$->TType = TERMTYPE_SYMBOL;
         $$->Symbol = *$1;
         delete $1;
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
            $$ = new Literal();
            PopulateLocation($$);
            $$->LType = LITERALTYPE_INT;
            $$->IntValue = $1;
        }
        | BoolConst
        {
            $$ = new Literal();
            PopulateLocation($$);
            $$->LType = LITERALTYPE_BOOL;
            $$->BoolValue = $1;
        }
        | BVConst
        {
            $$ = new Literal();
            PopulateLocation($$);
            $$->LType = LITERALTYPE_BV;
            $$->LiteralString = *$1;
            delete $1;
        }
        | EnumConst
        {
            $$ = new Literal();
            PopulateLocation($$);
            $$->LType = LITERALTYPE_ENUM;
            $$->LiteralString = *$1;
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
          $$ = new NTDef();
          PopulateLocation($$);
          $$->Symbol = *$2;
          delete $2;
          $$->Sort = $3;
          $$->Expansions = *$5;
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
                  TheParser->DoCheckSynthCallbacks();
              }

ConstraintCmd : TK_LPAREN TK_CONSTRAINT Term TK_RPAREN
              {
                  auto Cmd = new ConstraintCmd();
                  PopulateLocation(Cmd);
                  Cmd->TheTerm = $3;
                  TheParser->DoConstraintCallbacks(Cmd);
                  DestroyConstraintCmd(Cmd);
              }

SynthFunCmd : TK_LPAREN TK_SYNTH_FUN Symbol ArgList SortExpr
              TK_LPAREN NTDefPlus TK_RPAREN TK_RPAREN
            {
                auto Cmd = new SynthFunCmd();
                PopulateLocation(Cmd);
                Cmd->SynthFunName = *$3;
                delete $3;
                Cmd->Arguments = *$4;
                delete $4;
                Cmd->FunType = $5;
                Cmd->GrammarRules = *$7;
                delete $7;
                TheParser->DoSynthFunCallbacks(Cmd);
                DestroySynthFunCmd(Cmd);
            }

GTerm : Symbol
      {
          $$ = new GTerm();
          PopulateLocation($$);
          $$->GTType = GTERMTYPE_SYMBOL;
          $$->Symbol = *$1;
          delete $1;
      }
      | Literal
      {
          $$ = new GTerm();
          PopulateLocation($$);
          $$->GTType = GTERMTYPE_LITERAL;
          $$->TheLiteral = $1;
      }
      | TK_LPAREN Symbol GTermStar TK_RPAREN
      {
          $$ = new GTerm();
          PopulateLocation($$);
          $$->GTType = GTERMTYPE_FUNC;
          $$->Symbol = *$2;
          delete $2;
          $$->Children = *$3;
          delete $3;
      }
      | TK_LPAREN TK_CONSTANT SortExpr TK_RPAREN
      {
          $$ = new GTerm();
          PopulateLocation($$);
          $$->GTType = GTERMTYPE_CONSTANT;
          $$->TermSort = $3;
      }
      | TK_LPAREN TK_VARIABLE SortExpr TK_RPAREN
      {
          $$ = new GTerm();
          PopulateLocation($$);
          $$->GTType = GTERMTYPE_VARIABLE;
          $$->TermSort = $3;
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
