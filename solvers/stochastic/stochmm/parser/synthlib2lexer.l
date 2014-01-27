%{
    #include <utility>
    #include <vector>
    #include "parser/iface.h"
    using namespace std;
    using namespace SynthLib2Parser;

    #include "synthlib2parser.tab.hpp"
    /* C includes, etc */
    extern long yylinenum;
    extern long yycolnum;
%}

%option noyywrap

%x                      linecomment
WS                      [ \t\f]
LETTER                  [a-zA-Z_]
DIGIT                   [0-9]
HEXDIGIT                {DIGIT}|[a-f]|[A-F]
BIT                     "0"|"1"
ID                      ({LETTER}({LETTER}|{DIGIT})*)
INTEGER                 (-?{DIGIT}+)
INTCONST                {INTEGER}
BVCONST                 "#x"{HEXDIGIT}+|"#b"{BIT}+
DOUBLECOLON             "::"
ENUMCONST               {ID}DOUBLECOLON{ID}
SYMBOLCC                [a-z]|[A-Z]|"_"|"+"|"-"|"*"|"&"|"|"|"!"|"~"|"<"|">"|"="|"/"|"%"|"?"|"."|"$"|"^"
SYMBOL                  {SYMBOLCC}({SYMBOLCC}|{DIGIT})*
QUOTEDLIT               "\""([a-z]|[A-Z]|{DIGIT}|".")+"\""

%%

{WS}                    { yycolnum++; }
[\n]                    { yylinenum++; yycolnum = 0; }
";"                     { BEGIN linecomment; yycolnum += 1; }
<linecomment>\n         { BEGIN INITIAL; yylinenum++; yycolnum = 0; }
<linecomment>.          { yycolnum++; }
"define-sort"           { yycolnum += strlen(yytext); return TK_DEFINE_SORT; }
"define-fun"            { yycolnum += strlen(yytext); return TK_DEFINE_FUN; }
"set-options"           { yycolnum += strlen(yytext); return TK_SET_OPTIONS;}
"check-synth"           { yycolnum += strlen(yytext); return TK_CHECK_SYNTH; }
"declare-var"           { yycolnum += strlen(yytext); return TK_DECLARE_VAR; }
"synth-fun"             { yycolnum += strlen(yytext); return TK_SYNTH_FUN; }
"set-logic"             { yycolnum += strlen(yytext); return TK_SET_LOGIC; }
"constraint"            { yycolnum += strlen(yytext); return TK_CONSTRAINT; }
"("                     { yycolnum += strlen(yytext); return TK_LPAREN; }
")"                     { yycolnum += strlen(yytext); return TK_RPAREN; }
"BitVec"                { yycolnum += strlen(yytext); return TK_BV; }
"Int"                   { yycolnum += strlen(yytext); return TK_INT; }
"Bool"                  { yycolnum += strlen(yytext); return TK_BOOL; }
"Enum"                  { yycolnum += strlen(yytext); return TK_ENUM; }
"Constant"              { yycolnum += strlen(yytext); return TK_CONSTANT; }
"Variable"              { yycolnum += strlen(yytext); return TK_VARIABLE; }
"true"                  { yylval.BoolVal = true; yycolnum += strlen(yytext); return TK_BOOL_LITERAL; }
"false"                 { yylval.BoolVal = false; yycolnum += strlen(yytext); return TK_BOOL_LITERAL; }
{INTCONST}              {
                            yycolnum += strlen(yytext);
                            yylval.IntVal = atol(yytext);
                            return TK_INT_LITERAL;
                        }
{ENUMCONST}             {
                            yycolnum += strlen(yytext);
                            yylval.LexerString = new string(yytext);
                            return TK_ENUM_LITERAL;
                        }
{BVCONST}               {
                            yycolnum += strlen(yytext);
                            yylval.LexerString = new string(yytext);
                            return TK_BV_LITERAL;
                        }
{SYMBOL}                {
                            yycolnum += strlen(yytext);
                            string *SymbolVal = new string(yytext);
                            yylval.LexerString = SymbolVal;
                            return TK_SYMBOL;
                        }
{QUOTEDLIT}             {
                            yycolnum += strlen(yytext);
                            string* SymbolVal = new string(yytext);
                            yylval.LexerString = SymbolVal;
                            return TK_QUOTED_LITERAL;
                        }
.                       { return TK_ERROR; }

