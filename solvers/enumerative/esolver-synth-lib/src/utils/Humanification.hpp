// Humanification.hpp --- 
// 
// Filename: Humanification.hpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:49:13 2014 (-0500)
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


#if !defined __ESOLVER_HUMANIFICATION_HPP
#define __ESOLVER_HUMANIFICATION_HPP

#include "../common/ESolverForwardDecls.hpp"

namespace ESolver {

    static inline string HumanifyNumber(uint64 Num)
    {
        ostringstream sstr;
        if(Num >= 1000000000000000ULL) {
            sstr << ((double)Num / 1000000000000000.0) << " P";
        }
        else if(Num >= 1000000000000ULL) {
            sstr << ((double)Num / 1000000000000.0) << " T";
        } else if(Num >= 1000000000UL) {
            sstr << ((double)Num / 1000000000.0) << " B";
        } else if(Num >= 1000000UL) {
            sstr << ((double)Num / 1000000.0) << " M";
        } else if(Num >= 1000UL) {
            sstr << ((double)Num / 1000.0) << " K";
        } else {
            sstr << Num;
        }

        return sstr.str();
    }

    static inline string HumanifyNumberC(uint64 Num)
    {
        ostringstream sstr;
        if(Num >= (1ULL << 50)) {
            sstr << ((double)Num / (1ULL << 50)) << " P";
        } else if(Num >= (1ULL << 40)) {
            sstr << ((double)Num / (1ULL << 40)) << " T";
        } else if(Num >= (1ULL << 30)) {
            sstr << ((double)Num / (1ULL << 30)) << " G";
        } else if(Num >= (1ULL << 20)) {
            sstr << ((double)Num / (1ULL << 20)) << " M";
        } else if(Num >= (1ULL << 10)) {
            sstr << ((double)Num / (1ULL << 10)) << " K";
        } else {
            sstr << Num;
        }
        return sstr.str();
    }

} /* End namespace */

#endif /* __ESOLVER_HUMANIFICATION_HPP */


// 
// Humanification.hpp ends here
