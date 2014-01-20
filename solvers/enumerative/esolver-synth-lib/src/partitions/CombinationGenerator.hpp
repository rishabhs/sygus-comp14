// CombinationGenerator.hpp --- 
// 
// Filename: CombinationGenerator.hpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:50:49 2014 (-0500)
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


#if !defined __ESOLVER_COMBINATION_GENERATOR_HPP
#define __ESOLVER_COMBINATION_GENERATOR_HPP

#include "../common/ESolverForwardDecls.hpp"

namespace ESolver {

    /**
       Generates combinations of "things"
    */

    template<typename T>
    class CombinationGenerator
    {
    private:
        vector<vector<T> > CombinationVectors;
        vector<T> ActualElements;
        
        void Initialize();

    public:
        CombinationGenerator(const vector<T>& ActualElements);
        ~CombinationGenerator();
        inline const vector<T>& operator [] (uint32 Index) const;
        inline const vector<T>& At(uint32 Index) const;
        inline uint32 Size() const;
    };

    // Implementation

    template<typename T>
    inline void CombinationGenerator<T>::Initialize()
    {
        const uint32 NumElements = ActualElements.size();
        uint32 Mask = 1;
        uint32 Limit = (1 << NumElements);
        while(Mask < Limit) {
            CombinationVectors.push_back(vector<T>());
            for(uint32 i = 0; i < NumElements; ++i) {
                if((Mask & (1 << i)) != 0) {
                    CombinationVectors.back().push_back(ActualElements[i]);
                }
            }
            Mask++;
        }
    }

    template<typename T>
    CombinationGenerator<T>::CombinationGenerator(const vector<T>& ActualElements)
        : ActualElements(ActualElements)
    {
        Initialize();
    }

    template<typename T>
    CombinationGenerator<T>::~CombinationGenerator()
    {
        CombinationVectors.clear();
    }

    template<typename T>
    inline const vector<T>& CombinationGenerator<T>::operator [] (uint32 Index) const
    {
        return CombinationVectors[Index];
    }

    template<typename T>
    inline const vector<T>& CombinationGenerator<T>::At(uint32 Index) const
    {
        return CombinationVectors[Index];
    }

    template<typename T>
    inline uint32 CombinationGenerator<T>::Size() const
    {
        return CombinationVectors.size();
    }

} /* End namespace */

#endif /* __ESOLVER_COMBINATION_GENERATOR_HPP */


// 
// CombinationGenerator.hpp ends here
