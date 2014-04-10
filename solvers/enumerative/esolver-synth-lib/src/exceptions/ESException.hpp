// ESException.hpp --- 
// 
// Filename: ESException.hpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:51:44 2014 (-0500)
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


#if !defined __ESOLVER_ES_EXCEPTION_HPP
#define __ESOLVER_ES_EXCEPTION_HPP

#include "../common/ESolverCommon.hpp"

namespace ESolver {

    /**
       This is the base class for all ESolver exceptions
    */
    class ESException : public exception
    {
    protected:
        mutable string ExceptionInformation;
    public:
        ESException() throw();
        ESException(const string& ExceptionInfo) throw();
        ESException(const ESException& Other) throw();
        virtual ~ESException() throw();
        ESException& operator = (const ESException& Other) throw();
        virtual const char* what() const throw();
        const string& GetExceptionInfo() const throw();
    };

    class UnexpectedNullException : public ESException
    {
    public:
        UnexpectedNullException(const string& ExceptionInfo);
    };

    class TypeException : public ESException
    {
    public:
        TypeException(const string& ExceptionInfo);
    };

    class IdentifierException : public ESException
    {
    public:
        IdentifierException(const string& ExceptionInfo);
    };

    class ContextException : public ESException
    {
    public:
        ContextException(const string& ExceptionInfo);
    };

    class ValueException : public ESException
    {
    public:
        ValueException(const string& ExceptionInfo);
    };

    class UndefinedVarException : public ESException
    {
    public:
        UndefinedVarException(const string& ExceptionInfo);
    };

    class MonotonicityException : public ESException
    {
    public:
        MonotonicityException(const string& ExceptionInfo);
    };

    class OptionException : public ESException
    {
    public:
        OptionException(const string& ExceptionInfo);
    };

    class ExampleException : public ESException
    {
    public:
        ExampleException(const string& ExceptionInfo);
    };

    class InternalError : public ESException
    {
    public:
        InternalError(const string& ExceptionInfo);
    };

    class UnimplementedException : public ESException
    {
    public:
        UnimplementedException(const string& ExceptionInfo);
    };

    class InvalidExampleException : public ESException
    {
    public:
        InvalidExampleException(const string& ExceptionInfo);
    };

    class ModelGenException : public ESException
    {
    public:
        ModelGenException(const string& ExceptionInfo);
    };

    class OutOfMemoryException : public ESException
    {
    public:
        OutOfMemoryException(const string& ExceptionInfo);
    };

    class OutOfTimeException : public ESException
    {
    public:
        OutOfTimeException(const string& ExceptionInfo);
    };

    class Z3Exception : public ESException
    {
    public:
        Z3Exception(const string& ExceptionInfo);
    };

    class GrammarException : public ESException
    {
    public:
        GrammarException(const string& ExceptionInfo);
    };

    class UndefinedBehaviorException : public ESException
    {
    public:
        UndefinedBehaviorException(const string& ExceptionInfo);
    };

    class EnumeratorException : public ESException
    {
    public:
        EnumeratorException(const string& ExceptionInfo);
    };

    class ManagedVecException : public ESException
    {
    public:
        ManagedVecException(const string& ExceptionInfo);
    };

    class ManagedVecOOBException : public ManagedVecException
    {
    private:
        uint32 Index;
        uint32 MaxIndex;

    public:
        ManagedVecOOBException(const string& ExceptionInfo, uint32 Index, uint32 MaxIndex);
        ManagedVecOOBException(uint32 Index, uint32 MaxIndex);
        virtual const char* what() const throw() override;
    };

    class TLVecException : public ESException
    {
    public:
        TLVecException(const string& ExceptionInfo);
    };

    class SpecException : public ESException
    {
    public:
        SpecException(const string& ExceptionInfo);
    };

    class SynthLib2Exception : public ESException
    {
    private:
        uint32 LineNum;
        uint32 ColNum;

    public:
        SynthLib2Exception(uint32 LineNum, uint32 ColNum, const string& ExceptionInfo);
    };

    extern ostream& operator << (ostream& out, const ESException& TheException);

} /* End namespace */

#endif /* __ESOLVER_ES_EXCEPTION_HPP */


// 
// ESException.hpp ends here
