// SymPartitionGenerator.cpp --- 
// 
// Filename: SymPartitionGenerator.cpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:55:02 2014 (-0500)
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


#include "SymPartitionGenerator.hpp"

namespace ESolver {

    SymPartitionGenerator::SymPartitionGenerator(uint32 N)
        : PartitionGenerator(N, 2)
    {
        if(N < 2) {
            Done = true;
        } else {
            Initialize();
        }
    }
    
    SymPartitionGenerator::~SymPartitionGenerator()
    {
        // Nothing here
    }

    void SymPartitionGenerator::Initialize()
    {
        // TODO:
        // The cleaner solution here would be to
        // have an ABC for a partition generator and
        // have it not populate the Partition vector
        // and let SymPartitionGenerator inherit from
        // that class rather than have the constructor
        // populate the partition vector and then clean it 
        // up here!

        PartitionVectors.clear();

        uint32 Left = 1;
        uint32 Right = N - 1;
        while(Left <= Right) {
            vector<uint32> CurrentPartition;
            CurrentPartition.push_back(Left);
            CurrentPartition.push_back(Right);
            PartitionVectors.push_back(CurrentPartition);
            Left++;
            Right--;
        }
    }

} /* End namespace */


// 
// SymPartitionGenerator.cpp ends here
