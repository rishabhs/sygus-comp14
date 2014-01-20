// CrossProductGenerator.cpp --- 
// 
// Filename: CrossProductGenerator.cpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:54:55 2014 (-0500)
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


#include "CrossProductGenerator.hpp"

namespace ESolver {

    CrossProductGenerator::CrossProductGenerator(const vector<GenExpTLVec::ConstIterator>& Begins,
                                                 const vector<GenExpTLVec::ConstIterator>& Ends,
                                                 boost::pool<>* Pool)
        : Begins(Begins), Ends(Ends), Currents(Begins), Done(false),
          Size(Begins.size()), First(true), ElemSize(Begins.size()), Pool(Pool)
    {
        // Check if any of the iterators are empty
        for(uint32 i = 0; i < Size; ++i) {
            if(Begins[i] == Ends[i]) {
                CurrentElems = NULL;
                Done = true;
                return;
            }
        }
        CurrentElems = (GenExpressionBase const**)Pool->malloc();
        if(CurrentElems == NULL) {
            throw OutOfMemoryException("Out of Memory!");
        }
        FixCurrentElems();
    }

    inline void CrossProductGenerator::FixCurrentElems()
    {
        if(Done) {
            return;
        }
        // Check if any iterator is empty
        for(uint32 i = 0; i < Size; ++i) {
            CurrentElems[i] = *(Currents[i]);
        }
    }

    CrossProductGenerator::~CrossProductGenerator()
    {
        if(CurrentElems != NULL) {
            Pool->free(CurrentElems);
        }
    }

    GenExpressionBase const** CrossProductGenerator::GetNext()
    {
        if(Done) {
            return NULL;
        }
        if(First) {
            First = false;
            return CurrentElems;
        }

        bool Found = false;
        for(uint32 i = 0; i < Size; i++) {
            if(++(Currents[i]) == Ends[i]) {
                Currents[i] = Begins[i];
            } else {
                Found = true;
                break;
            }
        }
        
        if(Found) {
            FixCurrentElems();
        } else {
            Done = true;
            Pool->free(CurrentElems);
            CurrentElems = NULL;
        }

        return CurrentElems;
    }

    void CrossProductGenerator::Reset()
    {
        Done = false;
        for(uint32 i = 0; i < Size; ++i) {
            Currents[i] = Begins[i];
        }
        First = true;
    }

    void CrossProductGenerator::RelinquishOwnerShip()
    {
        // We're supposed to assume that we've lost the
        // CurrentElems we have allocated. Reallocate
        CurrentElems = (GenExpressionBase const**)Pool->malloc();
        if(CurrentElems == NULL) {
            throw OutOfMemoryException("Out of Memory!");
        }
    }

} /* End namespace */


// 
// CrossProductGenerator.cpp ends here
