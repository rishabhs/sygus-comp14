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

#if !defined __SYNTHLIB2_PARSER_LOGIC_SYMBOLS_HPP
#define __SYNTHLIB2_PARSER_LOGIC_SYMBOLS_HPP

#include "SynthLib2ParserFwd.hpp"
#include <boost/functional/hash.hpp>
#include <unordered_set>


// Change this to support larger bitvectors
#define SYNTHLIB2PARSER_MAX_BV_LEN (64)

namespace SynthLib2Parser {

    class SortExprPtrEquals
    {
    public:
        bool operator () (const SortExpr* SortPtr1, const SortExpr* SortPtr2) const;
    };

    class SortExprPtrHash
    {
    public:
        u32 operator () (const SortExpr* SortPtr) const;
    };

    typedef unordered_set<const SortExpr*, SortExprPtrHash, SortExprPtrEquals> SortExprPtrSet;

    class LogicSymbolLoader
    {
    private:
        static SortExprPtrSet RegisteredTypes;
        static bool BVLoaded;

    public:
        static void LoadLIA(SymbolTable* SymTab);
        static void LoadBV(SymbolTable* SymTab, u32 Size);
        static void LoadReal(SymbolTable* SymTab);
        static void LoadArrays(SymbolTable* SymTab, const ArraySortExpr* Sort);
        static void LoadCore(SymbolTable* SymTab);

        static void LoadAll(SymbolTable* SymTab);

        // Callback whenever a new type is registered
        // Should be called only for array types
        static void RegisterSort(SymbolTable* SymTab,
                                 const SortExpr* NewSort);
        static void Reset();
    };

} /* end namespace */

#endif /* __SYNTHLIB2_PARSER_LOGIC_SYMBOLS_HPP */
