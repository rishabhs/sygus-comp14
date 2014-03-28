#include <SynthLib2ParserExceptions.hpp>

namespace SynthLib2Parser {

    SynthLib2ParserException::SynthLib2ParserException()
        : ExceptionInfo("Unspecified")
    {
        // Nothing here
    }

    SynthLib2ParserException::SynthLib2ParserException(const string& ExceptionInfo)
        : ExceptionInfo(ExceptionInfo)
    {
        // Nothing here
    }

    SynthLib2ParserException::~SynthLib2ParserException() noexcept (true)
    {
        // Nothing here
    }

    const char* SynthLib2ParserException::what() const throw()
    {
        return ExceptionInfo.c_str();
    }

    SymbolTableException::SymbolTableException(const string& ExceptionInfo)
        : SynthLib2ParserException(ExceptionInfo)
    {
        // Nothing here
    }

    SymbolTableException::~SymbolTableException() noexcept (true)
    {
        // Nothing here
    }

    MalformedLiteralException::MalformedLiteralException(const string& LiteralString,
                                                         const string& Suffix)
    {
        ostringstream sstr;
        sstr << "The literal \"" << LiteralString << "\" is malformed" << endl;
        sstr << "Details: " << Suffix;
        ExceptionInfo = sstr.str();
    }
    
    MalformedLiteralException::~MalformedLiteralException() noexcept (true)
    {
        // Nothing here
    }

    ostream& operator << (ostream& str, const SynthLib2ParserException& Exc)
    {
        str << Exc.what();
        return str;
    }

} /* End namespace */

