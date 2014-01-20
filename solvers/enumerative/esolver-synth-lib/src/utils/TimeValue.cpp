// TimeValue.cpp --- 
// 
// Filename: TimeValue.cpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:53:54 2014 (-0500)
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


#include "TimeValue.hpp"

namespace ESolver {

    void TimeValue::Initialize(const TimeValue& Other)
    {
        Value = Other.Value;
    }

    TimeValue::TimeValue(struct timeval Value)
        : Value(Value)
    {
        // Nothing here
    }

    TimeValue::TimeValue(time_t sec, suseconds_t usec)
    {
        Value.tv_sec = sec;
        Value.tv_usec = usec;
    }

    TimeValue::TimeValue()
    {
        Value.tv_sec = 0;
        Value.tv_usec = 0;
    }

    TimeValue& TimeValue::operator = (const TimeValue& Other)
    {
        if(&Other == this) {
            return *this;
        }
        Initialize(Other);
        return *this;
    }

    TimeValue TimeValue::operator - (const TimeValue& Other) const
    {
        time_t sec;
        suseconds_t usec;
        struct timeval tv = Value;

        if (tv.tv_usec < Other.Value.tv_usec) {
            tv.tv_usec += 1000000;
            tv.tv_sec--;
        }

        usec = tv.tv_usec - Other.Value.tv_usec;
        sec = tv.tv_sec - Other.Value.tv_sec;

        return TimeValue(sec, usec);
    }

    TimeValue TimeValue::operator + (const TimeValue& Other) const
    {
        time_t sec;
        suseconds_t usec;

        sec = 0;
        usec = 0;
        
        usec = this->Value.tv_usec + Other.Value.tv_usec;
        if(usec > 1000000) {
            usec -= 1000000;
            sec += 1;
        }
        sec += (this->Value.tv_sec + Other.Value.tv_sec);
        return TimeValue(sec, usec);
    }

    TimeValue TimeValue::operator += (const TimeValue& Other)
    {
        this->Value.tv_usec += Other.Value.tv_usec;
        if(this->Value.tv_usec > 1000000) {
            this->Value.tv_usec -= 1000000;
            this->Value.tv_sec += 1;
        }
        this->Value.tv_sec += Other.Value.tv_sec;
        return *this;
    }

    uint64 TimeValue::InMicroSeconds() const
    {
        return ((uint64)Value.tv_sec * (uint64)1000000 + (uint64)Value.tv_usec);
    }

    string TimeValue::ToString() const
    {
        ostringstream sstr;
        sstr << ((double)Value.tv_sec + ((double)Value.tv_usec / 1000000.0));
        return sstr.str();
    }

    TimeValue TimeValue::GetTimeValue()
    {
        struct timeval tv;
        gettimeofday(&tv, NULL);
        return TimeValue(tv);
    }

    ostream& operator << (ostream& str, const TimeValue& TV)
    {
        str << TV.ToString();
        return str;
    }

} /* End namespace */


// 
// TimeValue.cpp ends here
