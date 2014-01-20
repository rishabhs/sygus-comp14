// Logger.hpp --- 
// 
// Filename: Logger.hpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:49:22 2014 (-0500)
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


#if !defined __ESOLVER_LOGGER_HPP
#define __ESOLVER_LOGGER_HPP

#include "../common/ESolverCommon.hpp"

namespace ESolver {

    class Logger
    {
    private:
        ostream& LogStream;
        uint32 ActualLogLevel;
        bool LogStreamIsCout;

    public:
        Logger(uint32 ActualLogLevel);
        Logger(const string& LogFileName, uint32 ActualLogLevel);
        ~Logger();
        void Flush();

        template<typename T> Logger& Log(const T& Obj, uint32 Level);
        template<typename T> Logger& Log(const T& Obj);
        template<typename T> Logger& Log0(const T& Obj);
        template<typename T> Logger& Log1(const T& Obj);
        template<typename T> Logger& Log2(const T& Obj);
        template<typename T> Logger& Log3(const T& Obj);
        template<typename T> Logger& Log4(const T& Obj);
        template<typename T> Logger& Log5(const T& Obj);
        template<typename T> Logger& Log6(const T& Obj);
        template<typename T> Logger& Log7(const T& Obj);
        template<typename T> Logger& Log8(const T& Obj);
        template<typename T> Logger& Log9(const T& Obj);
        template<typename T> Logger& Log10(const T& Obj);
        
    };
    
    template<typename T> Logger& Logger::Log(const T& Obj, uint32 Level)
    {
        if(ActualLogLevel >= Level) {
            LogStream << Obj; LogStream.flush();
        }
        return *this;
    }

    template<typename T> Logger& Logger::Log(const T& Obj)
    {
        return Log(Obj, 0);
    }

    template<typename T> Logger& Logger::Log0(const T& Obj)
    {
        return Log(Obj, 0);
    }

    template<typename T> Logger& Logger::Log1(const T& Obj)
    {
        return Log(Obj, 1);
    }

    template<typename T> Logger& Logger::Log2(const T& Obj)
    {
        return Log(Obj, 2);
    }

    template<typename T> Logger& Logger::Log3(const T& Obj)
    {
        return Log(Obj, 3);
    }

    template<typename T> Logger& Logger::Log4(const T& Obj)
    {
        return Log(Obj, 4);
    }

    template<typename T> Logger& Logger::Log5(const T& Obj)
    {
        return Log(Obj, 5);
    }

    template<typename T> Logger& Logger::Log6(const T& Obj)
    {
        return Log(Obj, 6);
    }

    template<typename T> Logger& Logger::Log7(const T& Obj)
    {
        return Log(Obj, 7);
    }

    template<typename T> Logger& Logger::Log8(const T& Obj)
    {
        return Log(Obj, 8);
    }

    template<typename T> Logger& Logger::Log9(const T& Obj)
    {
        return Log(Obj, 9);
    }

    template<typename T> Logger& Logger::Log10(const T& Obj)
    {
        return Log(Obj, 10);
    }

} /* End namespace */

#endif /* __ESOLVER_LOGGER_HPP */


// 
// Logger.hpp ends here
