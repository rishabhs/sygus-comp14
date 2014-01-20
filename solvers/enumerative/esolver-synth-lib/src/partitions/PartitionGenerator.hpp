// PartitionGenerator.hpp --- 
// 
// Filename: PartitionGenerator.hpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:50:54 2014 (-0500)
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


#if !defined __ESOLVER_PARTITION_GENERATOR_HPP
#define __ESOLVER_PARTITION_GENERATOR_HPP

#include "../common/ESolverForwardDecls.hpp"

namespace ESolver {

    class PartitionGenerator
    {
    protected:
        uint32 N;
        uint32 K;
        uint32 CurrentPosition;
        uint32 SeedPosition;
        bool Done;
        vector<vector<uint32> > PartitionVectors;
        vector<uint32> ZeroVector;

    private:

        void Initialize();
        
    public:
        PartitionGenerator(uint32 N, uint32 K);
        virtual ~PartitionGenerator();
        const vector<uint32>& Next();
        void Reset();
        // Accessors
        uint32 Size() const;
        uint32 GetN() const;
        uint32 GetK() const;
        const vector<uint32>& operator [] (uint32 Index) const;
    };

    static inline string PVToString(const vector<uint32>& PV)
    {
        ostringstream sstr;
        sstr << "<";
        for (auto const& Part : PV) {
            sstr << " " << Part;
        }
        sstr << " >";
        return sstr.str();
    }

} /* End namespace */

#endif /* __ESOLVER_PARTITION_GENERATOR_HPP */



// 
// PartitionGenerator.hpp ends here
