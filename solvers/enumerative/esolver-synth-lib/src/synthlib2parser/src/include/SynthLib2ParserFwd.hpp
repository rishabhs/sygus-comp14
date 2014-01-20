// SynthLib2ParserFwd.hpp --- 
// 
// Filename: SynthLib2ParserFwd.hpp
// Author: Abhishek Udupa
// Created: Sat Jan 18 16:42:17 2014 (-0500)
// 
// 
// Copyright (c) 2013, Abhishek Udupa, University of Pennsylvania
// All rights reserved.
// 
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in the
//    documentation and/or other materials provided with the distribution.
// 3. All advertising materials mentioning features or use of this software
//    must display the following acknowledgement:
//    This product includes software developed by The University of Pennsylvania
// 4. Neither the name of the University of Pennsylvania nor the
//    names of its contributors may be used to endorse or promote products
//    derived from this software without specific prior written permission.
// 
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER ''AS IS'' AND ANY
// EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
// WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
// DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
// DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
// (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
// LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
// ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
// SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
// 
// 

// Code:


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
    

    // printing
    extern ostream& operator << (ostream& Out, const ASTBase& AST);
    extern ostream& operator << (ostream& Out, const SourceLocation& Location);

} /* end namespace */

#endif /* __SYNTHLIB2PARSER_FWD_HPP */


// 
// SynthLib2ParserFwd.hpp ends here
