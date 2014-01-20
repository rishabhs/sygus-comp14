// PartitionGenerator.cpp --- 
// 
// Filename: PartitionGenerator.cpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:54:59 2014 (-0500)
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


#include "PartitionGenerator.hpp"

namespace ESolver {

    void PartitionGenerator::Initialize() 
    {
        uint32 *Cuts = new uint32[K + 1];
        Cuts[0] = 0;
        Cuts[1] = N - K + 1;
        for(uint32 i = 2; i < K + 1; ++i) {
            Cuts[i] = N - K + i;
        }
        bool BuildDone = false;
        while (!BuildDone) {
            vector<uint32> CurrentPartition;
            for(uint32 i = 1; i < K + 1; ++i) {
                CurrentPartition.push_back(Cuts[i] - Cuts[i-1]);
            }
            PartitionVectors.push_back(CurrentPartition);
            uint32 RightMost = 0;
            for(uint32 i = 1; i < K; ++i) {
                if(Cuts[i] - Cuts[i - 1] > 1) {
                    RightMost = i;
                    Cuts[i]--;
                    break;
                }
            }
            if(RightMost == 0) {
                BuildDone = true;
            } else {
                uint32 Accum = 1;
                for(uint32 i = RightMost - 1; i > 0; --i) {
                    Cuts[i] = Cuts[RightMost] - Accum;
                    Accum++;
                }
            }
        }

        delete[] Cuts;
    }

    PartitionGenerator::PartitionGenerator(uint32 N, uint32 K)
        : N(N), K(K), CurrentPosition(0), SeedPosition(0), Done(false)
    {
        Initialize();
    }
    
    PartitionGenerator::~PartitionGenerator()
    {
        // Nothing here
    }

    const vector<uint32>& PartitionGenerator::Next()
    {
        if(Done) {
            return ZeroVector;
        }
        const vector<uint32>& Retval = PartitionVectors[CurrentPosition];
        CurrentPosition = (CurrentPosition + 1) % PartitionVectors.size();
        if(CurrentPosition == SeedPosition) {
            Done = true;
        }
        return Retval;
    }

    void PartitionGenerator::Reset()
    {
        Done = false;
        CurrentPosition = SeedPosition;
    }

    uint32 PartitionGenerator::Size() const
    {
        return PartitionVectors.size();
    }

    uint32 PartitionGenerator::GetN() const
    {
        return N;
    }

    uint32 PartitionGenerator::GetK() const
    {
        return K;
    }

    const vector<uint32>& PartitionGenerator::operator [] (uint32 Index) const
    {
        if(Index >= PartitionVectors.size()) {
            return ZeroVector;
        }
        return PartitionVectors[Index];
    }

} /* End namespace */


// 
// PartitionGenerator.cpp ends here
