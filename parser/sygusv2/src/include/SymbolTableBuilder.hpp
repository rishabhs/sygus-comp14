#if !defined __SYGUS2_PARSER_SYMBOL_TABLE_BUILDER_HPP
#define __SYGUS2_PARSER_SYMBOL_TABLE_BUILDER_HPP

#include "Sygus2ParserIFace.hpp"

namespace Sygus2Parser {

class SymbolTableBuilder : public ASTVisitorBase
{
private:
    SymbolTable* symbol_table;

public:
};

} /* end namespace Sygus2Parser */

#endif /* __SYGUS2_PARSER_SYMBOL_TABLE_BUILDER_HPP */
