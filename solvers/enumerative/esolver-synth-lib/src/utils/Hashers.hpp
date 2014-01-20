// Hashers.hpp --- 
// 
// Filename: Hashers.hpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:49:09 2014 (-0500)
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


#if !defined __ESOLVER_HASHERS_HPP
#define __ESOLVER_HASHERS_HPP

#include "../common/ESolverCommon.hpp"
#include "../common/ESolverForwardDecls.hpp"
#include "../descriptions/Operators.hpp"
#include "../descriptions/ESType.hpp"
#include "../utils/GNCostPair.hpp"
#include "../values/ConcreteValueBase.hpp"
#include "../expressions/UserExpression.hpp"
#include "../containers/ESSmartPtr.hpp"
#include "../descriptions/GrammarNodes.hpp"
#include "../values/Signature.hpp"

namespace ESolver {

    class ExpressionHasher
    {
    public:
        inline uint64 operator () (const Expression& Exp) const
        {
            return Exp->Hash();
        }
    };

    class ExpressionEquals
    {
    public:
        inline bool operator () (const Expression& Exp1, const Expression& Exp2) const
        {
            return Exp1->Equals(*Exp2);
        }
    };

    class TypeHasher
    {
    public:
        inline uint64 operator () (const ESTypeBase& Type) const
        {
            return Type.Hash();
        }
    };

    class TypeEquals
    {
    public:
        inline bool operator () (const ESTypeBase& Type1, const ESTypeBase& Type2) const
        {
            return Type1.Equals(Type2);
        }
    };

    class TypePtrHasher
    {
    public:
        inline uint64 operator () (const ESTypeBase* Type) const
        {
            return Type->Hash();
        }
    };
    
    class TypePtrEquals
    {
    public:
        inline bool operator () (const ESTypeBase* Type1, const ESTypeBase* Type2) const
        {
            return Type1->Equals(*Type2);
        }
    };

    class GNCostPairHasher
    {
    public:
        inline uint64 operator () (const GNCostPair& Pair) const
        {
            return Pair.Hash();
        }
    };

    class GNCostPairPtrHasher
    {
    public:
        inline uint64 operator () (const GNCostPair* PairPtr) const
        {
            return PairPtr->Hash();
        }
    };

    class GNCostPairEquals
    {
    public:
        inline bool operator () (const GNCostPair& Pair1, const GNCostPair& Pair2) const
        {
            return (Pair1 == Pair2);
        }
    };
    
    class GNCostPairPtrEquals
    {
    public:
        inline bool operator () (const GNCostPair* PairPtr1, const GNCostPair* PairPtr2) const
        {
            return (*PairPtr1 == *PairPtr2);
        }
    };

    // hashers for concrete values
    class ConcreteValueBasePtrHasher
    {
    public:
        inline uint64 operator () (const ConcreteValueBase* Ptr1) const
        {
            if (Ptr1 == nullptr) {
                return 0;
            }
            return Ptr1->Hash();
        }
    };

    class ConcreteValueBasePtrEquals
    {
    public:
        inline bool operator () (const ConcreteValueBase* Ptr1, const ConcreteValueBase* Ptr2) const
        {
            if (Ptr1 == nullptr && Ptr2 == nullptr) {
                return true;
            } else if (Ptr1 == nullptr || Ptr2 == nullptr) {
                return false;
            }
            return Ptr1->Equals(*Ptr2);
        }
    };

    class GrammarNodePtrHasher
    {
    public:
        inline uint64 operator () (const GrammarNode* Ptr) const
        {
            return Ptr->Hash();
        }
    };

    class GrammarNodePtrEquals
    {
    public:
        inline bool operator () (const GrammarNode* Ptr1, const GrammarNode* Ptr2) const
        {
            return ((*Ptr1) == (*Ptr2));
        }
    };

    class SignaturePtrHasher
    {
    public:
        inline uint64 operator () (const Signature* Ptr) const
        {
            if (Ptr == nullptr) {
                return 0;
            }
            return Ptr->Hash();
        }
    };

    class SignaturePtrEquals
    {
    public:
        inline bool operator () (const Signature* Ptr1, const Signature* Ptr2) const
        {
            // if (Ptr1 == nullptr && Ptr2 == nullptr) {
            //     return true;
            // } else if (Ptr1 == nullptr || Ptr2 == nullptr) {
            //     return false;
            // }
            return Ptr1->Equals(*Ptr2);
        }
    };

    class SignaturePtrDeepEquals
    {
    public:
        inline bool operator () (const Signature* Ptr1, const Signature* Ptr2) const
        {
            if (Ptr1 == nullptr && Ptr2 == nullptr) {
                return true;
            } else if (Ptr1 == nullptr || Ptr2 == nullptr) {
                return false;
            }
            return Ptr1->DeepEquals(*Ptr2);
        }
    };


} /* End namespace */

#endif /* __ESOLVER_HASHERS_HPP */


// 
// Hashers.hpp ends here
