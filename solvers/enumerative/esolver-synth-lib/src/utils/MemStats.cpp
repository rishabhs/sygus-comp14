// MemStats.cpp --- 
// 
// Filename: MemStats.cpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:53:47 2014 (-0500)
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


#include "MemStats.hpp"
#include "Humanification.hpp"

namespace ESolver {

    void MemStats::Initialize(const MemStats& Other)
    {
        ProgramSize = Other.ProgramSize;
        ResidentSize = Other.ResidentSize;
        SharedSize = Other.SharedSize;        
        TextSize = Other.TextSize;
        LibSize = Other.LibSize;
        DataSize = Other.DataSize;
    }

    MemStats::MemStats(uint64 ProgramSize, uint64 ResidentSize,
                       uint64 SharedSize, uint64 TextSize,
                       uint64 LibSize, uint64 DataSize)
        : ProgramSize(ProgramSize), ResidentSize(ResidentSize),
          SharedSize(SharedSize), TextSize(TextSize),
          LibSize(LibSize), DataSize(DataSize)
    {
        // nothing here;
    }
    

    MemStats::MemStats()
    {
        ProgramSize = ResidentSize = SharedSize = TextSize = LibSize = DataSize = 0;
    }

    MemStats::MemStats(const MemStats& Other)
    {
        Initialize(Other);
    }

    MemStats& MemStats::operator = (const MemStats& Other)
    {
        if(&Other == this) {
            // Self assignment
            return *this;
        }
        Initialize(Other);
        return *this;
    }

    MemStats MemStats::operator - (const MemStats& Other) const
    {
        return MemStats((ProgramSize - Other.ProgramSize),
                        (ResidentSize - Other.ResidentSize),
                        (SharedSize - Other.SharedSize),
                        (TextSize - Other.TextSize),
                        (LibSize - Other.LibSize),
                        (DataSize - Other.DataSize));
    }

    uint64 MemStats::Aggregate() const
    {
        return ProgramSize;
    }

    string MemStats::ToAggregateString() const
    {
        return HumanifyNumberC(Aggregate());
    }

    string MemStats::ToString() const
    {
        ostringstream sstr;
        
        sstr << "Program Size  : " << HumanifyNumberC(ProgramSize) << endl;
        sstr << "Resident Size : " << HumanifyNumberC(ResidentSize) << endl;
        sstr << "Shared Size   : " << HumanifyNumberC(SharedSize) << endl;
        sstr << "Text Size     : " << HumanifyNumberC(TextSize) << endl;
        sstr << "Lib Size      : " << HumanifyNumberC(LibSize) << endl;
        sstr << "Data Size     : " << HumanifyNumberC(DataSize) << endl;
        return sstr.str();
    }

    MemStats MemStats::GetMemStats()
    {
        ostringstream MemFileNameBuilder;
        uint32 PageSize = getpagesize();

        MemFileNameBuilder << "/proc/" << getpid() << "/statm";
        ifstream istr(MemFileNameBuilder.str().c_str());
        
        istr.setf(ios::skipws);

        uint64 ProgramSize, ResidentSize, SharedSize, TextSize, LibSize, DataSize;
        istr >> ProgramSize;
        istr >> ResidentSize;
        istr >> SharedSize;
        istr >> TextSize;
        istr >> LibSize;
        istr >> DataSize;

        ProgramSize *= PageSize;
        ResidentSize *= PageSize;
        SharedSize *= PageSize;
        TextSize *= TextSize;
        LibSize *= LibSize;
        DataSize *= DataSize;

        return MemStats(ProgramSize, ResidentSize, SharedSize, TextSize, LibSize, DataSize);
    }

    ostream& operator << (ostream& str, const MemStats& Stats)
    {
        str << Stats.ToString();
        return str;
    }

} /* End namespace */



// 
// MemStats.cpp ends here
