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

#if !defined __SYGUS2_PARSER_FWD_HPP
#define __SYGUS2_PARSER_FWD_HPP

#include "Sygus2ParserCommon.hpp"

namespace Sygus2Parser {

// class representing the location
class SourceLocation;

// Base class for all AST nodes
class ASTBase;

// Base class for all commands
class ASTCmd;

// Commands
class CheckSynthCmd;
class ConstraintCmd;
class DeclareVarCmd;
class InvConstraintCmd;
class SetFeatureCmd;
class SynthFunCmd;
class SynthInvCmd;
class DeclareDatatypeCmd;
class DeclareDatatypesCmd;
class DeclareSortCmd;
class DefineFunCmd;
class SetLogicCmd;
class SetOptionCmd;

// Base class for all sort exprs
class SortExpr;

// Identifiers
class Identifier;

// Indices
class Index;

// Base class for all terms
class Term;

class FunTerm;
class LiteralTerm;
class SymbolTerm;
class LetTerm;
class QuantifiedTerm;

// Sorted symbol
class SortedSymbol;
class VariableBinding;

// Base class for all GTerms
class GTerm;

class ConstantGTerm;
class VariableGTerm;
class BFGTerm;

class GrammarRule;
class Grammar;

// Literals
class Literal;

// Visitors
class ASTVisitorBase;

// Symbol tables
class SymbolTable;
class SymbolTableScope;
class SymbolTableEntry;

// printing
extern ostream& operator << (ostream& out, const ASTBase& ast);
extern ostream& operator << (ostream& out, const SourceLocation& location);

} /* end namespace */

#endif /* __SYNTHLIB2PARSER_FWD_HPP */