#include "parser/exceptions.h"

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

    ostream& operator << (ostream& str, const SynthLib2ParserException& Exc)
    {
        str << Exc.what();
        return str;
    }

} /* End namespace */

