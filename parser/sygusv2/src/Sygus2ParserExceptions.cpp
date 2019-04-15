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

#include "include/Sygus2ParserExceptions.hpp"
#include "include/Sygus2ParserIFace.hpp"

namespace Sygus2Parser {

Sygus2ParserException::Sygus2ParserException()
    : exception_info("Unspecified"), location(SourceLocation::none)
{
    // Nothing here
}

Sygus2ParserException::Sygus2ParserException(const string& exception_info)
    : exception_info(exception_info), location(SourceLocation::none)
{
    // Nothing here
}

Sygus2ParserException::Sygus2ParserException(const string& exception_info,
                                             const SourceLocation& location)
    : exception_info(exception_info), location(location)
{
    // Nothing here
}

Sygus2ParserException::~Sygus2ParserException() noexcept (true)
{
    // Nothing here
}

const SourceLocation& Sygus2ParserException::get_location() const
{
    return location;
}

const char* Sygus2ParserException::what() const throw()
{
    return exception_info.c_str();
}

SymbolTableException::SymbolTableException(const string& exception_info)
    : Sygus2ParserException(exception_info)
{
    // Nothing here
}

SymbolTableException::SymbolTableException(const string& exception_info,
                                           const SourceLocation& location)
    : Sygus2ParserException(exception_info, location)
{
    // Nothing here
}

SymbolTableException::~SymbolTableException() noexcept (true)
{
    // Nothing here
}

MalformedLiteralException::MalformedLiteralException(const string& literal_string,
                                                     const string& suffix)
{
    ostringstream sstr;
    sstr << "The literal \"" << literal_string << "\" is malformed" << endl;
    sstr << "Details: " << suffix;
    exception_info = sstr.str();
}

MalformedLiteralException::MalformedLiteralException(const string& literal_string,
                                                     const string& suffix,
                                                     const SourceLocation& location)
{
    ostringstream sstr;
    sstr << "The literal \"" << literal_string << "\" is malformed" << endl;
    sstr << "Details: " << suffix;
    exception_info = sstr.str();
    this->location = location;
}

MalformedLiteralException::~MalformedLiteralException() noexcept (true)
{
    // Nothing here
}

UnsupportedFeatureException::UnsupportedFeatureException(const string& exception_info)
    : Sygus2ParserException(exception_info)
{
    // Nothing here
}

UnsupportedFeatureException::UnsupportedFeatureException(const string& exception_info,
                                                         const SourceLocation& location)
    : Sygus2ParserException(exception_info, location)
{
    // Nothing here
}

UnsupportedFeatureException::~UnsupportedFeatureException()
{
    // Nothing here
}

ostream& operator << (ostream& str, const Sygus2ParserException& exc)
{
    str << exc.what();
    auto const& location = exc.get_location();
    if (location != SourceLocation::none) {
        str << endl;
        str << "At: " << location.to_string();
    }
    return str;
}

} /* End namespace */
