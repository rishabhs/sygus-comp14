// ESException.cpp --- 
// 
// Filename: ESException.cpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:55:55 2014 (-0500)
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


#include "ESException.hpp"

namespace ESolver {

    ESException::ESException() throw() 
        : exception(), ExceptionInformation("")
    {
        // Nothing here
    }

    ESException::ESException(const string& ExceptionInfo) throw()
        : exception(), ExceptionInformation(ExceptionInfo) 
    {
        // Nothing here
    }

    ESException::ESException(const ESException& Other) throw()
        : exception(Other), ExceptionInformation(Other.ExceptionInformation)
    {
        // Nothing here
    }

    ESException::~ESException() throw()
    {
        // Nothing here
    }
    
    ESException& ESException::operator = (const ESException& Other) throw()
    {
        if(this == &Other) {
            return *this;
        }
        exception::operator =(Other);
        ExceptionInformation = Other.ExceptionInformation;
        return *this;
    }

    const char* ESException::what() const throw()
    {
        return ExceptionInformation.c_str();
    }

    const string& ESException::GetExceptionInfo() const throw()
    {
        return ExceptionInformation;
    }
    
    UnexpectedNullException::UnexpectedNullException(const string& ExceptionInfo)
        : ESException(ExceptionInfo)
    {
        // Nothing here
    }

    TypeException::TypeException(const string& ExceptionInfo) : ESException(ExceptionInfo)
    {
        // Nothing here
    }

    IdentifierException::IdentifierException(const string& ExceptionInfo)
        : ESException(ExceptionInfo)
    {
        // Nothing here
    }

    ContextException::ContextException(const string& ExceptionInfo) 
        : ESException(ExceptionInfo)
    {
        // Nothing here
    }

    ValueException::ValueException(const string& ExceptionInfo)
        : ESException(ExceptionInfo)
    {
        // Nothing here
    }

    UndefinedVarException::UndefinedVarException(const string& ExceptionInfo)
        : ESException(ExceptionInfo)
    {
        // Nothing here
    }

    MonotonicityException::MonotonicityException(const string& ExceptionInfo)
        : ESException(ExceptionInfo)
    {
        // Nothing here
    }

    OptionException::OptionException(const string& ExceptionInfo)
        : ESException(ExceptionInfo)
    {
        // Nothing here
    }

    ExampleException::ExampleException(const string& ExceptionInfo)
        : ESException(ExceptionInfo)
    {
        // Nothing here
    }

    InternalError::InternalError(const string& ExceptionInfo)
        :ESException(ExceptionInfo)
    {
        // Nothing here
    }

    UnimplementedException::UnimplementedException(const string& ExceptionInfo)
        : ESException(ExceptionInfo)
    {
        // Nothing here
    }

    InvalidExampleException::InvalidExampleException(const string& ExceptionInfo)
        : ESException(ExceptionInfo)
    {
        // Nothing here
    }

    ModelGenException::ModelGenException(const string& ExceptionInfo)
        : ESException(ExceptionInfo)
    {
        // Nothing here
    }

    OutOfMemoryException::OutOfMemoryException(const string& ExceptionInfo)
        : ESException(ExceptionInfo)
    {
        // Nothing here
    }

    OutOfTimeException::OutOfTimeException(const string& ExceptionInfo)
        : ESException(ExceptionInfo)
    {
        // Nothing here
    }

    Z3Exception::Z3Exception(const string& ExceptionInfo)
        : ESException(ExceptionInfo)
    {
        // Nothing here
    }

    GrammarException::GrammarException(const string& ExceptionInfo)
        : ESException(ExceptionInfo)
    {
        // Nothing here
    }

    UndefinedBehaviorException::UndefinedBehaviorException(const string& ExceptionInfo)
        : ESException(ExceptionInfo)
    {
        // Nothing here
    }

    EnumeratorException::EnumeratorException(const string& ExceptionInfo)
        : ESException(ExceptionInfo)
    {
        // Nothing here
    }

    TLVecException::TLVecException(const string& ExceptionInfo)
        : ESException(ExceptionInfo)
    {
        // Nothing here
    }

    ManagedVecException::ManagedVecException(const string& ExceptionInfo)
        : ESException(ExceptionInfo)
    {
        // Nothing here
    }

    ManagedVecOOBException::ManagedVecOOBException(const string& ExceptionInfo,
                                                   uint32 Index, uint32 MaxIndex)
        : ManagedVecException(ExceptionInfo), Index(Index), MaxIndex(MaxIndex)
    {
        // Nothing here
    }

    ManagedVecOOBException::ManagedVecOOBException(uint32 Index, uint32 MaxIndex)
        : ManagedVecException("Error: OOBException"), Index(Index), MaxIndex(MaxIndex)
    {
        // Nothing here
    }

    const char* ManagedVecOOBException::what() const throw()
    {
        ostringstream sstr;
        sstr << " Index " << Index << " out of bounds for Managed vector with size " << MaxIndex;
        ExceptionInformation = ExceptionInformation + sstr.str();
        return ExceptionInformation.c_str();
    }

    SpecException::SpecException(const string& ExceptionInfo)
        : ESException(ExceptionInfo)
    {
        // Nothing here
    }

    SynthLib2Exception::SynthLib2Exception(uint32 LineNum, 
                                           uint32 ColNum, 
                                           const string& ExceptionInfo)
        : ESException(ExceptionInfo), LineNum(LineNum), ColNum(ColNum)
    {
        ostringstream sstr;
        sstr << ExceptionInfo << endl;
        sstr << "At Line: " << LineNum << ", Column: " << ColNum;
        this->ExceptionInformation = sstr.str();
    }

    ostream& operator << (ostream& out, const ESException& TheException)
    {
        out << TheException.what() << endl;
        return out;
    }

} /* End namespace */


// 
// ESException.cpp ends here
