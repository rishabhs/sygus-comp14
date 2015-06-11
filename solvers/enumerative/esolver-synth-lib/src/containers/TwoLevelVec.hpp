// TwoLevelVec.hpp ---
//
// Filename: TwoLevelVec.hpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:52:34 2014 (-0500)
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


#if !defined __ESOLVER_TWO_LEVEL_VEC_HPP
#define __ESOLVER_TWO_LEVEL_VEC_HPP

#include "../common/ESolverForwardDecls.hpp"
#include "../containers/ESRefCountable.hpp"
#include "../containers/ESSmartPtr.hpp"
#include "../exceptions/ESException.hpp"

namespace ESolver {

    // Forward decls
    template<typename T> class TLVecConstIterator;
    template<typename T> class TLVec;


    /*
       A two level managed vector class
    */

    template<typename T>
    class TLVec
    {
    private:
        template<typename U>
        class TLVecConstIterator
        {
        private:
            typedef const TLVec<U>* ContainerType;
            ContainerType Container;
            int64 L1;
            int64 L2;
            bool Done;

        public:
            TLVecConstIterator()
                : Container(nullptr), L1(-1), L2(-1), Done(false) {}

            TLVecConstIterator(const TLVecConstIterator<U>& Other)
                : Container(Other.Container), L1(Other.L1), L2(Other.L2), Done(Other.Done) {}

            TLVecConstIterator(ContainerType Container, int64 L1, int64 L2, bool Done = false)
                : Container(Container), L1(L1), L2(L2), Done(Done) {}
            ~TLVecConstIterator()
            {
                Container = nullptr;
                L1 = L2 = -1;
                Done = false;
            }

            // assignment
            inline TLVecConstIterator<U>& operator = (const TLVecConstIterator<U>& Other)
            {
                if(&Other == this) {
                    return *this;
                } else {
                    Container = Other.Container;
                    L1 = Other.L1;
                    L2 = Other.L2;
                    Done = Other.Done;
                    return *this;
                }
            }


            // Equality
            inline bool operator == (const TLVecConstIterator<U>& Other) const
            {
                return (Container != nullptr && Other.Container != nullptr &&
                        Container == Other.Container && L1 == Other.L1 &&
                        L2 == Other.L2 && Done == Other.Done);
            }

            inline bool operator != (const TLVecConstIterator<U>& Other) const
            {
                return (!(*this == Other));
            }

            // Increment
            inline TLVecConstIterator<U> operator ++ (int Dummy)
            {
                if(Done) {
                    return *this;
                }
                auto Retval = *this;
                if(UNLIKELY(++L2 == (int64)Container->TheTLVec[L1]->size())) {
                    if(UNLIKELY(++L1 == (int64)Container->TheTLVec.size())) {
                        Done = true;
                        return Retval;
                    } else {
                        L2 = 0;
                        return Retval;
                    }
                } else {
                    return Retval;
                }
            }

            inline TLVecConstIterator<U>& operator ++ ()
            {
                if(Done) {
                    return *this;
                }
                if(UNLIKELY(++L2 == (int64)Container->TheTLVec[L1]->size())) {
                    if(UNLIKELY(++L1 == (int64)Container->TheTLVec.size())) {
                        Done = true;
                        return *this;
                    } else {
                        L2 = 0;
                        return *this;
                    }
                } else {
                    return *this;
                }
            }

            // Deref
            inline const U* operator * () const
            {
                return (Container->TheTLVec[L1])->at(L2);
            }
        };

        template<typename U>
        class RefCountedVector : public ESRefCountable
        {
        private:
            vector<U>* VecPtr;

        public:
            RefCountedVector() { VecPtr = new vector<U>(); }
            virtual ~RefCountedVector() { delete VecPtr; }

            inline size_t size() const { return VecPtr->size(); }
            U& at(size_t Index) { return VecPtr->at(Index); }
            const U& at(size_t Index) const { return VecPtr->at(Index); }
            void shrink_to_fit() { VecPtr->shrink_to_fit(); }
            void push_back(const U& Elem) { VecPtr->push_back(Elem); }
        };

        vector<ESSmartPtr<RefCountedVector<T*>>> TheTLVec;
        uint64 NumElems;

    public:
        // typedefs
        typedef TLVecConstIterator<T> ConstIterator;

        // Default constructor
        TLVec();
        // Copy constructor
        TLVec(const TLVec& Other);

        // Destructor
        ~TLVec();

        // Insertion
        inline void PushBack(const T* Elem);
        inline void Merge(const TLVec<T>& Other);

        // Indexing
        inline T& operator [] (uint32 Index);
        inline const T& operator [] (uint32 Index) const;
        inline const T& At(uint32 Index) const;

        // Size
        uint64 Size() const;

        // Freezing
        inline void Freeze();

        // Iterators
        inline ConstIterator Begin() const;
        inline ConstIterator End() const;
    };

    // Two level vector implementation
    template<typename T>
    TLVec<T>::TLVec()
        : TheTLVec(), NumElems(0)
    {
        // Nothing here
    }

    template<typename T>
    TLVec<T>::TLVec(const TLVec<T>& Other)
        : TheTLVec(Other.TheTLVec), NumElems(Other.NumElems)
    {
        if(NumElems == 0) {
            TheTLVec.clear();
        }
    }

    template<typename T>
    TLVec<T>::~TLVec()
    {
        TheTLVec.clear();
    }

    template<typename T>
    inline void TLVec<T>::PushBack(const T* Elem)
    {
        if(UNLIKELY(NumElems == 0)) {
            TheTLVec.push_back(new RefCountedVector<T*>());
        }
        TheTLVec.back()->push_back(Elem);
        NumElems++;
    }

    template<typename T>
    inline void TLVec<T>::Merge(const TLVec<T>& Other)
    {
        if(Other.NumElems == 0) {
            return;
        }
        for(auto const& MVec : Other.TheTLVec) {
            if(MVec->size() > 0) {
                TheTLVec.push_back(MVec);
                NumElems += MVec->size();
            }
        }
    }

    template<typename T>
    inline T& TLVec<T>::operator [] (uint32 Index)
    {
        for(auto const& MVec : TheTLVec) {
            if(Index < MVec->size()) {
                return (*MVec)[Index];
            } else {
                Index -= MVec->size();
            }
        }

        throw TLVecException("Out of bounds access on two level vector");
    }

    template<typename T>
    inline const T& TLVec<T>::operator [] (uint32 Index) const
    {
        for(auto const& MVec : TheTLVec) {
            if(Index < MVec->size()) {
                return MVec->At(Index);
            } else {
                Index -= MVec->size();
            }
        }

        throw TLVecException("Out of bounds access on two level vector");
    }

    template<typename T>
    inline const T& TLVec<T>::At(uint32 Index) const
    {
        return (*this)[Index];
    }

    template<typename T>
    inline uint64 TLVec<T>::Size() const
    {
        return NumElems;
    }

    template<typename T>
    inline void TLVec<T>::Freeze()
    {
        for (auto it = TheTLVec.begin(); it != TheTLVec.end(); ++it) {
            auto& MVec = *it;
            MVec->shrink_to_fit();
        }
    }

    template<typename T>
    inline typename TLVec<T>::ConstIterator TLVec<T>::Begin() const
    {
        return typename TLVec<T>::ConstIterator(this, 0, 0, (NumElems == 0));
    }

    template<typename T>
    inline typename TLVec<T>::ConstIterator TLVec<T>::End() const
    {
        if(NumElems == 0) {
            return typename TLVec<T>::ConstIterator(this, 0, 0, true);
        } else {
            return typename TLVec<T>::ConstIterator(this, TheTLVec.size(), TheTLVec.back()->size(), true);
        }
    }

} /* End namespace */

#endif /* __ESOLVER_TWO_LEVEL_VEC_HPP */


//
// TwoLevelVec.hpp ends here
