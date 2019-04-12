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
    #include "include/Sygus2ParserIFace.hpp"
    #include "include/Sygus2ParserExceptions.hpp"
    // #include "include/SymbolTable.hpp"
    // #include "include/LogicSymbols.hpp"
    #include <iostream>
    #include <string.h>

    using namespace std;
    using namespace Sygus2Parser;

    namespace Sygus2Bison {
        Program* the_program = NULL;
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
        SourceLocation(yylinenum, yycolnum)

%}

%union {
    // yyunion fields
    Program* the_program;
    string* lexer_string;

    vector<string>* symbol_list;

    Command* the_command;
    vector<CommandSPtr>* command_list;

    SortedSymbol* the_sorted_symbol;
    vector<SortedSymbolSPtr>* sorted_symbol_list;

    Identifier* the_identifier;

    SortExpr* the_sort_expr;
    vector<SortExprSPtr>* sort_expr_list;

    SortNameAndArity* sort_name_and_arity;
    vector<SortNameAndAritySPtr>* sort_name_and_arity_list;

    DatatypeConstructor* datatype_constructor;
    vector<DatatypeConstructorSPtr>* datatype_constructor_list;

    DatatypeConstructorList* datatype_constructors;
    vector<DatatypeConstructorListSPtr>* datatype_constructors_list;

    Index* the_index;
    vector<IndexSPtr>* index_list;

    Term* the_term;
    vector<TermSPtr>* term_list;

    VariableBinding* the_binding;
    vector<VariableBindingSPtr>* binding_list;

    GroupedRuleList* the_grouped_rule_list;
    vector<GroupedRuleListSPtr>* grouped_rule_list_list;

    Grammar* the_grammar;

    GrammarTerm* the_grammar_term;
    vector<GrammarTermSPtr>* grammar_term_list;

    Literal* the_literal;
}

%token TK_DEFINE_SORT TK_DEFINE_FUN TK_SET_OPTION TK_SET_FEATURE
%token TK_CHECK_SYNTH TK_SYNTH_FUN TK_DECLARE_VAR TK_INV_CONSTRAINT TK_SYNTH_INV
%token TK_LPAREN TK_RPAREN TK_SET_LOGIC TK_PAR
%token TK_CONSTRAINT TK_DECLARE_DATATYPE TK_DECLARE_DATATYPES
%token TK_CONSTANT TK_VARIABLE
%token TK_ERROR TK_COLON TK_UNDERSCORE
%token TK_LET TK_EXISTS TK_FORALL
%token TK_DECLARE_SORT

%token<lexer_string> TK_SYMBOL TK_BOOL_CONST TK_NUMERAL TK_DECIMAL
%token<lexer_string> TK_HEX_CONST TK_BIN_CONST TK_STRING_LITERAL


%type<the_program> Program

%type<command_list> CommandStar

%type<the_command> Command CheckSynthCommand ConstraintCommand VarDeclCommand InvConstraintCommand
%type<the_command> SetFeatureCommand SynthFunCommand SynthInvCommand SmtCommand
%type<the_command> SortDeclCommand FunDefCommand SortDefCommand SetLogicCommand SetOptionCommand
%type<the_command> DeclareDatatypeCommand DeclareDatatypesCommand

%type<the_sorted_symbol> SortedSymbol
%type<sorted_symbol_list> SortedSymbolStar SortedSymbolPlus

%type<the_sort_expr> SortExpr
%type<sort_expr_list> SortExprPlus

%type<sort_name_and_arity> SortNameAndArity
%type<sort_name_and_arity_list> SortNameAndArityPlus

%type<datatype_constructor> ConstructorDefinition
%type<datatype_constructor_list> ConstructorDefinitionPlus

%type<datatype_constructors> DatatypeConstructorList SimpleDatatypeConstructorList
%type<datatype_constructors> ParameterizedDatatypeConstructorList
%type<datatype_constructors_list> DatatypeConstructorListPlus

%type<the_identifier> Identifier

%type<lexer_string> Symbol
%type<symbol_list> SymbolPlus

%type<the_literal> Literal

%type<the_term> Term
%type<term_list> TermPlus

%type<the_index> Index
%type<index_list> IndexPlus

%type<the_binding> Binding
%type<binding_list> BindingPlus

%type<the_grammar> OptGrammarDef GrammarDef

%type<the_grouped_rule_list> GroupedRuleList
%type<grouped_rule_list_list> GroupedRuleListPlus

%type<the_grammar_term> GTerm
%type<grammar_term_list> GTermPlus

%type<the_term> BFTerm
%type<term_list> BFTermPlus

%%

start : Program
      { Sygus2Bison::the_program = $1; }

Program : CommandStar
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
                $$ = new vector<CommandSPtr>();
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
           | DeclareDatatypeCommand
           | DeclareDatatypesCommand

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
               $$ = new DeclareVarCommand(GET_CURRENT_LOCATION(), *$3, $4);
               delete $3;
           }

InvConstraintCommand : TK_LPAREN TK_INV_CONSTRAINT Symbol Symbol Symbol Symbol TK_RPAREN
                 {
                     $$ = new InvConstraintCommand(GET_CURRENT_LOCATION(), *$3, *$4, *$5, *$6);
                     delete $3;
                     delete $4;
                     delete $5;
                     delete $6;
                 }

SetFeatureCommand : TK_LPAREN TK_SET_FEATURE TK_COLON Symbol TK_BOOL_CONST TK_RPAREN
              {
                  bool value;
                  if (*$5 == "true") {
                      value = true;
                  } else if (*$5 == "false") {
                      value = false;
                  } else {
                      cout << "Error parsing a boolean value: " << *$5 << endl;
                      throw MalformedLiteralException("Error parsing boolean value: " + *$5, "");
                  }
                  $$ = new SetFeatureCommand(GET_CURRENT_LOCATION(), *$4, value);
                  delete $4;
                  delete $5;
              }

SynthFunCommand : TK_LPAREN TK_SYNTH_FUN Symbol TK_LPAREN SortedSymbolStar TK_RPAREN SortExpr OptGrammarDef TK_RPAREN
                {
                    $$ = new SynthFunCommand(GET_CURRENT_LOCATION(), *$3, *$5, $7, $8);
                    delete $3;
                    delete $5;
                }

SynthInvCommand : TK_LPAREN TK_SYNTH_INV Symbol TK_LPAREN SortedSymbolStar TK_RPAREN OptGrammarDef TK_RPAREN
            {
                $$ = new SynthInvCommand(GET_CURRENT_LOCATION(), *$3, *$5, $7);
                delete $3;
                delete $5;
            }

SortDeclCommand : TK_LPAREN TK_DECLARE_SORT Symbol TK_NUMERAL TK_RPAREN
                {
                    istringstream istr(*$4);
                    u32 value;
                    istr >> value;
                    $$ = new DeclareSortCommand(GET_CURRENT_LOCATION(), *$3, value);
                    delete $3;
                }


FunDefCommand : TK_LPAREN TK_DEFINE_FUN Symbol TK_LPAREN SortedSymbolStar TK_RPAREN SortExpr Term TK_RPAREN
          {
              $$ = new DefineFunCommand(GET_CURRENT_LOCATION(), *$3, *$5, $7, $8);
              delete $3;
              delete $5;
          }

SortDefCommand : TK_LPAREN TK_DEFINE_SORT Symbol SymbolPlus SortExpr TK_RPAREN
               {
                   $$ = new DefineSortCommand(GET_CURRENT_LOCATION(), *$3, *$4, $5);
                   delete $3;
                   delete $4;
               }
               | TK_LPAREN TK_DEFINE_SORT Symbol SortExpr TK_RPAREN
               {
                   vector<string> empty_string_vector;
                   $$ = new DefineSortCommand(GET_CURRENT_LOCATION(), *$3, empty_string_vector, $4);
                   delete $3;
               }

DeclareDatatypesCommand : TK_LPAREN TK_DECLARE_DATATYPES TK_LPAREN SortNameAndArityPlus TK_RPAREN
                          TK_LPAREN DatatypeConstructorListPlus TK_RPAREN
                        {
                            $$ = new DeclareDatatypesCommand(GET_CURRENT_LOCATION(), *$4, *$7);
                            delete $4;
                            delete $7;
                        }

DeclareDatatypeCommand : TK_LPAREN TK_DECLARE_DATATYPE Symbol DatatypeConstructorList TK_RPAREN
                       {
                           $$ = new DeclareDatatypeCommand(GET_CURRENT_LOCATION(), *$3, $4);
                           delete $3;
                       }

SortNameAndArityPlus : SortNameAndArityPlus SortNameAndArity
                     {
                         $$ = $1;
                         $$->push_back($2);
                     }
                     | SortNameAndArity
                     {
                         $$ = new vector<SortNameAndAritySPtr>();
                         $$->push_back($1);
                     }

SortNameAndArity : TK_LPAREN Symbol TK_NUMERAL TK_RPAREN
                 {
                     istringstream istr(*$3);
                     u32 value;
                     istr >> value;
                     $$ = new SortNameAndArity(GET_CURRENT_LOCATION(), *$2, value);
                     delete $2;
                     delete $3;
                 }

DatatypeConstructorListPlus : DatatypeConstructorListPlus DatatypeConstructorList
                            {
                                $$ = $1;
                                $$->push_back($2);
                            }
                            | DatatypeConstructorList
                            {
                                $$ = new vector<DatatypeConstructorListSPtr>();
                                $$->push_back($1);
                            }

DatatypeConstructorList : ParameterizedDatatypeConstructorList
                        { $$ = $1; }
                        | SimpleDatatypeConstructorList
                        { $$ = $1; }

SimpleDatatypeConstructorList : TK_LPAREN ConstructorDefinitionPlus TK_RPAREN
                              {
                                  vector<string> empty_sort_parameter_names;
                                  $$ = new DatatypeConstructorList(GET_CURRENT_LOCATION(),
                                                                   empty_sort_parameter_names,
                                                                   *$2);
                                  delete $2;
                              }

ParameterizedDatatypeConstructorList : TK_LPAREN TK_PAR SymbolPlus
                                       TK_LPAREN ConstructorDefinitionPlus TK_RPAREN TK_RPAREN
                                     {
                                         $$ = new DatatypeConstructorList(GET_CURRENT_LOCATION(),
                                                                          *$3, *$5);
                                         delete $3;
                                         delete $5;
                                     }

ConstructorDefinitionPlus : ConstructorDefinitionPlus ConstructorDefinition
                          {
                              $$ = $1;
                              $$->push_back($2);
                          }
                          | ConstructorDefinition
                          {
                              $$ = new vector<DatatypeConstructorSPtr>();
                              $$->push_back($1);
                          }

ConstructorDefinition : TK_LPAREN Symbol SortedSymbolStar TK_RPAREN
                      {
                          $$ = new DatatypeConstructor(GET_CURRENT_LOCATION(), *$2, *$3);
                          delete $2;
                          delete $3;
                      }

SymbolPlus : TK_LPAREN SymbolPlus Symbol TK_RPAREN
           {
               $$ = $2;
               $$->push_back(*$3);
               delete $3;
           }
           | TK_LPAREN Symbol TK_RPAREN
           {
               $$ = new vector<string>();
               $$->push_back(*$2);
               delete $2;
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
             $$ = new SortExpr(GET_CURRENT_LOCATION(), $1);
         }
         | TK_LPAREN Identifier SortExprPlus TK_RPAREN
         {
             $$ = new SortExpr(GET_CURRENT_LOCATION(), $2, *$3);
             delete $3;
         }

Identifier : Symbol
           {
               $$ = new Identifier(GET_CURRENT_LOCATION(), *$1);
               delete $1;
           }
           | TK_LPAREN TK_UNDERSCORE Symbol IndexPlus TK_RPAREN
           {
               $$ = new Identifier(GET_CURRENT_LOCATION(), *$3, *$4);
               delete $3;
               delete $4;
           }

SortExprPlus : SortExprPlus SortExpr
             {
                 $$ = $1;
                 $$->push_back($2);
             }
             | SortExpr
             {
                 $$ = new vector<SortExprSPtr>();
                 $$->push_back($1);
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
              $$ = new vector<IndexSPtr>();
              $$->push_back($1);
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
     | TK_LPAREN TK_EXISTS TK_LPAREN SortedSymbolPlus TK_RPAREN Term TK_RPAREN
     {
         $$ = new QuantifiedTerm(GET_CURRENT_LOCATION(), QuantifierKind::Exists, *$4, $6);
         delete $4;
     }
     | TK_LPAREN TK_FORALL TK_LPAREN SortedSymbolPlus TK_RPAREN Term TK_RPAREN
     {
         $$ = new QuantifiedTerm(GET_CURRENT_LOCATION(), QuantifierKind::Forall, *$4, $6);
         delete $4;
     }
     | TK_LPAREN TK_LET TK_LPAREN BindingPlus TK_RPAREN Term TK_RPAREN
     {
         $$ = new LetTerm(GET_CURRENT_LOCATION(), *$4, $6);
         delete $4;
     }

TermPlus : TermPlus Term
         {
             $$ = $1;
             $$->push_back($2);
         }
         | Term
         {
             $$ = new vector<TermSPtr>();
             $$->push_back($1);
         }

SortedSymbolPlus : SortedSymbolPlus SortedSymbol
                 {
                     $$ = $1;
                     $$->push_back($2);
                 }
                 | SortedSymbol
                 {
                     $$ = new vector<SortedSymbolSPtr>();
                     $$->push_back($1);
                 }

SortedSymbolStar : SortedSymbolStar SortedSymbol
                 {
                     $$ = $1;
                     $$->push_back($2);
                 }
                 | /* empty */
                 {
                     $$ = new vector<SortedSymbolSPtr>();
                 }

SortedSymbol : TK_LPAREN Symbol SortExpr TK_RPAREN
             {
                 $$ = new SortedSymbol(GET_CURRENT_LOCATION(), *$2, $3);
                 delete $2;
             }

BindingPlus : BindingPlus Binding
            {
                $$ = $1;
                $$->push_back($2);
            }
            | Binding
            {
                $$ = new vector<VariableBindingSPtr>();
                $$->push_back($1);
            }

Binding : TK_LPAREN Symbol Term TK_RPAREN
        {
            $$ = new VariableBinding(GET_CURRENT_LOCATION(), *$2, $3);
            delete $2;
        }

Literal : TK_NUMERAL
        {
            $$ = new Literal(GET_CURRENT_LOCATION(), *$1, LiteralKind::Numeral);
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
           {
               $$ = new Grammar(GET_CURRENT_LOCATION(), *$2, *$5);
               delete $2;
               delete $5;
           }

GroupedRuleListPlus : GroupedRuleListPlus GroupedRuleList
                    {
                        $$ = $1;
                        $$->push_back($2);
                    }
                    | GroupedRuleList
                    {
                        $$ = new vector<GroupedRuleListSPtr>();
                        $$->push_back($1);
                    }

GroupedRuleList : TK_LPAREN Symbol SortExpr TK_LPAREN GTermPlus TK_RPAREN TK_RPAREN
                {
                    $$ = new GroupedRuleList(GET_CURRENT_LOCATION(), *$2, $3, *$5);
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
              $$ = new vector<GrammarTermSPtr>();
              $$->push_back($1);
          }

GTerm : TK_LPAREN TK_CONSTANT SortExpr TK_RPAREN
      {
          $$ = new ConstantGrammarTerm(GET_CURRENT_LOCATION(), $3);
      }
      | TK_LPAREN TK_VARIABLE SortExpr TK_RPAREN
      {
          $$ = new VariableGrammarTerm(GET_CURRENT_LOCATION(), $3);
      }
      | BFTerm
      {
          $$ = new BinderFreeGrammarTerm(GET_CURRENT_LOCATION(), $1);
      }

BFTerm : Identifier
       {
           $$ = new IdentifierTerm(GET_CURRENT_LOCATION(), $1);
       }
       | Literal
       {
           $$ = new LiteralTerm(GET_CURRENT_LOCATION(), $1);
       }
       | TK_LPAREN Identifier BFTermPlus TK_RPAREN
       {
           $$ = new FunctionApplicationTerm(GET_CURRENT_LOCATION(), $2, *$3);
           delete $3;
       }

BFTermPlus : BFTermPlus BFTerm
           {
               $$ = $1;
               $$->push_back($2);
           }
           | BFTerm
           {
               $$ = new vector<TermSPtr>();
           }
