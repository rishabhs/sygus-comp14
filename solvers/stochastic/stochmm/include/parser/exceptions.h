#if !defined __SYNTH_LIB2_PARSER_EXCEPTIONS_H
#define __SYNTH_LIB2_PARSER_EXCEPTIONS_H

#include <exception>
#include <string>
#include <iostream>

using namespace std;

namespace SynthLib2Parser {

    class SynthLib2ParserException : public exception
    {
    private:
        string ExceptionInfo;

    public:
        SynthLib2ParserException();
        SynthLib2ParserException(const string& ExceptionInfo);
        virtual ~SynthLib2ParserException() noexcept (true);
        virtual const char* what() const throw();
    };

    extern ostream& operator << (ostream& str, const SynthLib2ParserException& Exc);

} /* End namespace */

#endif /* __SYNTH_LIB2_PARSER_EXCEPTIONS_H */
