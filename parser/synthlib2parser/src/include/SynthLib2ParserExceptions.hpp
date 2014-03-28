#if !defined __SYNTH_LIB2_PARSER_EXCEPTIONS_HPP
#define __SYNTH_LIB2_PARSER_EXCEPTIONS_HPP

#include <exception>
#include <string>
#include <iostream>
#include <sstream>

using namespace std;

namespace SynthLib2Parser {

    class SynthLib2ParserException : public exception
    {
    protected:
        string ExceptionInfo;

    public:
        SynthLib2ParserException();
        SynthLib2ParserException(const string& ExceptionInfo);
        virtual ~SynthLib2ParserException() noexcept (true);
        virtual const char* what() const throw() override;
        const string& GetExceptionInfo() const;
    };

    class SymbolTableException : public SynthLib2ParserException
    {
    public:
        SymbolTableException(const string& ExceptionInfo);
        virtual ~SymbolTableException() noexcept (true);
    };

    class MalformedLiteralException : public SynthLib2ParserException
    {
    public:
        MalformedLiteralException(const string& LiteralString, const string& Suffix);
        virtual ~MalformedLiteralException() noexcept (true);
    };

    extern ostream& operator << (ostream& str, const SynthLib2ParserException& Exc);

} /* End namespace */

#endif /* __SYNTH_LIB2_PARSER_EXCEPTIONS_H */
