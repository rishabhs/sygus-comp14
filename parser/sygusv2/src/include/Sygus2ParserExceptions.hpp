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

#if !defined __SYGUS2_PARSER_EXCEPTIONS_HPP
#define __SYGUS2_PARSER_EXCEPTIONS_HPP

#include <exception>
#include <string>
#include <iostream>
#include <sstream>

using namespace std;

namespace Sygus2Parser {

class Sygus2ParserException : public exception
{
protected:
    string exception_info;

public:
    Sygus2ParserException();
    Sygus2ParserException(const string& exception_info);
    virtual ~Sygus2ParserException() noexcept (true);
    virtual const char* what() const throw() override;
    const string& get_exception_info() const;
};

class SymbolTableException : public Sygus2ParserException
{
public:
    SymbolTableException(const string& exception_info);
    virtual ~SymbolTableException() noexcept (true);
};

class MalformedLiteralException : public Sygus2ParserException
{
public:
    MalformedLiteralException(const string& literal_string, const string& suffix);
    virtual ~MalformedLiteralException() noexcept (true);
};

class UnsupportedFeatureException : public Sygus2ParserException
{
public:
    UnsupportedFeatureException(const string& exception_info);
    virtual ~UnsupportedFeatureException() noexcept (true);
};

extern ostream& operator << (ostream& str, const Sygus2ParserException& exc);

} /* End namespace */

#endif /* __SYGUS2_PARSER_EXCEPTIONS_H */
