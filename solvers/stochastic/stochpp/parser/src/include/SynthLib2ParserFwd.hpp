#if !defined __SYNTHLIB2_PARSER_FWD_HPP
#define __SYNTHLIB2_PARSER_FWD_HPP

#include "SynthLib2ParserCommon.hpp"

namespace SynthLib2Parser {

    // class representing the location
    class SourceLocation;

    // Base class for all AST nodes
    class ASTBase;
    // Base class for all commands
    class ASTCmd;
    // enum for command kinds
    enum ASTCmdKind {
        CMD_FUNDEF,
        CMD_SYNTHFUN,
        CMD_FUNDECL,
        CMD_SORTDEF,
        CMD_SETOPTS,
        CMD_VARDECL,
        CMD_CONSTRAINT,
        CMD_SETLOGIC,
        CMD_CHECKSYNTH
    };
    
    // Commands
    class SetLogicCmd;
    class FunDefCmd;
    class SynthFunCmd;
    class SortDefCmd;
    class SetOptsCmd;
    class VarDeclCmd;
    class ConstraintCmd;
    class CheckSynthCmd;

    // Base class for all sort exprs
    class SortExpr;
    // enum for sort kinds
    enum SortKind {
        SORTKIND_INT,
        SORTKIND_BV,
        SORTKIND_ARRAY, 
        SORTKIND_REAL,
        SORTKIND_BOOL,
        SORTKIND_FUN,
        SORTKIND_ENUM,
        SORTKIND_NAMED
    };

    class IntSortExpr;
    class BVSortExpr;
    class NamedSortExpr;
    class ArraySortExpr;
    class RealSortExpr;
    class FunSortExpr;
    class BoolSortExpr;
    
    // Terms and such
    // Base class for all terms
    class Term;

    enum TermKind {
        TERMKIND_FUN,
        TERMKIND_LITERAL,
        TERMKIND_SYMBOL,
        TERMKIND_LET
    };
    
    class FunTerm;
    class LiteralTerm;
    class SymbolTerm;
    class LetTerm;

    // Base class for all GTerms
    class GTerm;

    enum VariableKind {
        VARKIND_LOCAL,
        VARKIND_INPUT,
        VARKIND_ANY
    };

    enum GTermKind {
        GTERMKIND_SYMBOL,
        GTERMKIND_FUN,
        GTERMKIND_LITERAL,
        GTERMKIND_CONSTANT,
        GTERMKIND_VARIABLE,
        GTERMKIND_LET
    };

    class SymbolGTerm;
    class FunGTerm;
    class LiteralGTerm;
    class ConstantGTerm;
    class VariableGTerm;
    class LetGTerm;

    class NTDef;
    
    // Literals
    class Literal;

    // Arg sort pair
    class ArgSortPair;
    
    typedef vector<ArgSortPair*> ArgList;

    // Visitors
    class ASTVisitorBase;
    
    // Symbol tables
    class SymbolTable;
    class SymbolTableScope;
    class SymbolTableEntry;

    // printing
    extern ostream& operator << (ostream& Out, const ASTBase& AST);
    extern ostream& operator << (ostream& Out, const SourceLocation& Location);

} /* end namespace */

#endif /* __SYNTHLIB2PARSER_FWD_HPP */

