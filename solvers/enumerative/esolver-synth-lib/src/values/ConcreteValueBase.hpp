// ConcreteValueBase.hpp --- 
// 
// Filename: ConcreteValueBase.hpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:48:49 2014 (-0500)
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


#if !defined __ESOLVER_CONCRETE_VALUE_BASE_HPP
#define __ESOLVER_CONCRETE_VALUE_BASE_HPP

#include "../common/ESolverForwardDecls.hpp"
#include <boost/functional/hash.hpp>


namespace ESolver {
    
    /**
       A class representing and efficiently implementing  the most commonly 
       used types of values. Additional classes may be extended from this 
       as required to handle aadditional types as they might be added
       
       We simply use a uint64 to represent ALL values.
       Ints - No explanation needed
       Bools - 1 for true, 0 for false
       Subranges - Just the integer value
       Sets - Sets of upto 64 elements are represented as bitvectors
       EnumTypes - The value encodes a distinct enum constructor, which
       may be looked up in an auxiliary lookup structure
    */

    class ConcreteValueBase
    {
    private:
        int64 TheValue;
        const ESFixedTypeBase* Type;
        mutable uint64 HashValue;

        // Utility functions
        inline string IntToString(bool Simple = false) const;
        inline string BoolToString(bool Simple = false) const;
        inline string EnumTypeToString(bool Simple = false) const;
        inline string BVToString(bool Simple = false) const;

        inline SMTExpr IntToSMT(TheoremProver* TP) const;
        inline SMTExpr BoolToSMT(TheoremProver* TP) const;
        inline SMTExpr EnumTypeToSMT(TheoremProver* TP) const;
        inline SMTExpr BVToSMT(TheoremProver* TP) const;

    protected:
        void ComputeHashValue() const;
        
    public:
        // Default constructor
        ConcreteValueBase();
        // Constructor
        ConcreteValueBase(const ESFixedTypeBase* Type, int64 TheValue);
        // Copy constructor
        ConcreteValueBase(const ConcreteValueBase& Other);
        // Destructor
        ~ConcreteValueBase();
        // Equality check
        bool Equals(const ConcreteValueBase& Other) const;
        string ToString() const;
        string ToSimpleString() const;
        int64 GetValue() const;
        SMTExpr ToSMT(TheoremProver* TP) const;

        bool operator == (const ConcreteValueBase& Other) const;
        bool operator != (const ConcreteValueBase& Other) const;
        const ESFixedTypeBase* GetType() const;
        uint64 Hash() const;

        // Additional methods for stack allocated objects
        void Set(const ESFixedTypeBase* Type, int64 TheValue);
    };

} /* End namespace */

#endif /* __ESOLVER_CONCRETE_VALUE_BASE_HPP */


// 
// ConcreteValueBase.hpp ends here
