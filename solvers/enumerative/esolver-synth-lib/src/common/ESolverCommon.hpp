// ESolverCommon.hpp --- 
// 
// Filename: ESolverCommon.hpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:52:38 2014 (-0500)
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


#if !defined __ESOLVER_COMMON_HPP
#define __ESOLVER_COMMON_HPP

#include <cstdio>
#include <cstdlib>
#include <inttypes.h>
#include <cstdint>
#include <cstddef>
#include <limits.h>
#include <iostream>
#include <string>
#include <unistd.h>
#include <sstream>
#include <fstream>
#include <iomanip>
#include <assert.h>
#include <z3.h>
#include <string.h>
#include <vector>
#include <set>
#include <unordered_set>
#include <map>
#include <list>
#include <deque>
#include <unordered_map>
#include <sys/time.h>
#include <stdarg.h>

using namespace std;

// definition of prefix for bitvector type names
#define ESOLVER_BITVEC_PREFIX ((string)"BV")
#define ESOLVER_MAX_BV_SIZE (64)

typedef uint32_t uint32;
typedef int32_t int32;

#if !(__APPLE__ & __MACH__)
typedef uint64_t uint64;
typedef int64_t int64;
#else
typedef size_t uint64;
typedef size_t int64;
#endif

typedef uint16_t uint16;
typedef int16_t int16;
typedef int8_t int8;
typedef uint8_t uint8;

namespace ESolver {

    class Z3Expr;
    class Z3Sort;

    typedef Z3Expr SMTExpr;
    typedef Z3Sort SMTType;
    typedef map<string, string> SMTSolverParams;

} /* End namespace */

// Some macros for branch prediction
#if defined __GNUG__ && !defined DISABLE_STATIC_BP
#define UNLIKELY(__Condition) __builtin_expect(__Condition, 0)
#define LIKELY(__Condition) __builtin_expect(__Condition, 1)
#else /* !__GNUG__ || DISABLE_STATIC_BP */
#define UNLIKELY(__Condition) __Condition
#define LIKELY(__Condition) __Condition
#endif /* __GNUG__ */

#endif /* __ESOLVER_COMMON_HPP */


// 
// ESolverCommon.hpp ends here
