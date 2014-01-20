// ESSmartPtr.hpp --- 
// 
// Filename: ESSmartPtr.hpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:52:30 2014 (-0500)
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


#if !defined __ESOLVER_ES_SMART_PTR_HPP
#define __ESOLVER_ES_SMART_PTR_HPP

#include "../common/ESolverCommon.hpp"

namespace ESolver {

    template<typename T> class ESSmartPtr
    {
    private:
        mutable T* __Ptr;

        inline void __Assign(T* Ptr)
        {
            if(Ptr != NULL) {
                Ptr->__IncRefCount();
            }
            T* OldPtr = this->__Ptr;
            this->__Ptr = Ptr;
            if(OldPtr != NULL) {
                OldPtr->__DecRefCount();
            }
        }

        inline void __Free()
        {
            if(__Ptr != NULL) {
                __Ptr->__DecRefCount();
            }
            __Ptr = NULL;
        }

        inline int64 __Compare(const T* Other) const
        {
            return (__Ptr - Other);
        }

        inline int64 __Compare(const ESSmartPtr& Other) const
        {
            return (__Ptr - Other.__Ptr); 
        }
        
    public:
        static const ESSmartPtr<T> NullObject;
        
        inline ESSmartPtr()
        {
            __Ptr = NULL;
        }
        
        inline ESSmartPtr(T* Ptr)
        {
            this->__Ptr = NULL;
            __Assign(Ptr);
        }

        inline ESSmartPtr(const ESSmartPtr& Other)
        {
            this->__Ptr = NULL;
            __Assign(Other.__Ptr);
        }

        ~ESSmartPtr()
        {
            __Free();
        }

        inline T* GetPtr() const
        {
            return __Ptr;
        }

        inline ESSmartPtr& operator = (const ESSmartPtr& Other)
        {
            __Assign(Other.__Ptr);
            return (*this);
        }

        inline ESSmartPtr& operator = (T* __Ptr)
        {
            __Assign(__Ptr);
            return (*this);
        }

        inline T* operator -> ()
        {
            return __Ptr;
        }

        inline const T* operator -> () const
        {
            return __Ptr;
        }

        inline operator T* () const
        {
            return __Ptr;
        }

        inline bool operator == (const ESSmartPtr& Other) const
        {
            return (__Compare(Other) == 0);
        }

        inline bool operator != (const ESSmartPtr& Other) const
        {
            return (__Compare(Other) != 0);
        }

        inline bool operator > (const ESSmartPtr& Other) const
        {
            return (__Compare(Other) > 0);
        }

        inline bool operator >= (const ESSmartPtr& Other) const
        {
            return (__Compare(Other) >= 0);
        }

        inline bool operator < (const ESSmartPtr& Other) const
        {
            return (__Compare(Other) < 0);
        }

        inline bool operator <= (const ESSmartPtr& Other) const
        {
            return (__Compare(Other) <= 0);
        }

        inline bool operator == (const T* Other) const
        {
            return (__Compare(Other) == 0);
        }

        inline bool operator != (const T* Other) const
        {
            return (__Compare(Other) != 0);
        }

        inline bool operator > (T* Other) const
        {
            return (__Compare(Other) > 0);
        }

        inline bool operator >= (T* Other) const
        {
            return (__Compare(Other) >= 0);
        }

        inline bool operator < (T* Other) const
        {
            return (__Compare(Other) < 0);
        }

        inline bool operator <= (T* Other) const
        {
            return (__Compare(Other) <= 0);
        }

        inline bool IsNull() const
        {
            return (__Ptr == NULL);
        }
    };

    template<typename T> class ConstESSmartPtr
    {
    private:
        const T* __Ptr;

        inline void __Assign(const T* Ptr)
        {
            if(Ptr != NULL) {
                (const_cast<T*>(Ptr))->__IncRefCount();
            }
            T* OldPtr = const_cast<T*>(this->__Ptr);
            this->__Ptr = Ptr;
            if(OldPtr != NULL) {
                OldPtr->__DecRefCount();
            }
        }

        inline void __Free()
        {
            if(__Ptr != NULL) {
                (const_cast<T*>(__Ptr))->__DecRefCount();
            }
            __Ptr = NULL;
        }

        inline int64 __Compare(const T* Other) const
        {
            return (__Ptr - Other);
        }

        inline int64 __Compare(const ConstESSmartPtr& Other) const
        {
            return (__Ptr - Other.__Ptr); 
        }
        
    public:
        static const ConstESSmartPtr<T> NullObject;

        inline ConstESSmartPtr()
        {
            __Ptr = NULL;
        }
        
        inline ConstESSmartPtr(T* __Ptr)
        {
            this->__Ptr = NULL;
            __Assign(__Ptr);
        }

        inline ConstESSmartPtr(const T* __Ptr)
        {
            this->__Ptr = NULL;
            __Assign(__Ptr);
        }

        inline ConstESSmartPtr(const ESSmartPtr<T>& Other)
        {
            __Ptr = NULL;
            __Assign(Other.__Ptr);
        }

        inline ConstESSmartPtr(const ConstESSmartPtr& Other)
        {
            __Ptr = NULL;
            __Assign(Other.__Ptr);
        }


        ~ConstESSmartPtr()
        {
            __Free();
        }

        inline const T* GetPtr() const
        {
            return __Ptr;
        }

        inline ConstESSmartPtr<T>& operator = (const ConstESSmartPtr<T>& Other)
        {
            __Assign(Other.__Ptr);
            return (*this);
        }

        inline ConstESSmartPtr& operator = (T* __Ptr)
        {
            __Assign(__Ptr);
            return (*this);
        }
        
        inline ConstESSmartPtr& operator = (const T* __Ptr)
        {
            __Assign(__Ptr);
            return (*this);
        }

        inline ConstESSmartPtr& operator = (const ESSmartPtr<T>& Other)
        {
            __Assign(Other.__Ptr);
            return (*this);
        }

        inline const T* operator -> () const
        {
            return __Ptr;
        }

        inline operator const T* () const
        {
            return __Ptr;
        }

        inline bool operator == (const ESSmartPtr<T>& Other) const
        {
            return (__Compare(Other) == 0);
        }

        inline bool operator != (const ESSmartPtr<T>& Other) const
        {
            return (__Compare(Other) != 0);
        }

        inline bool operator > (const ESSmartPtr<T>& Other) const
        {
            return (__Compare(Other) > 0);
        }

        inline bool operator >= (const ESSmartPtr<T>& Other) const
        {
            return (__Compare(Other) >= 0);
        }

        inline bool operator < (const ESSmartPtr<T>& Other) const
        {
            return (__Compare(Other) < 0);
        }

        inline bool operator <= (const ESSmartPtr<T>& Other) const
        {
            return (__Compare(Other) <= 0);
        }

        inline bool operator == (const T* Other) const
        {
            return (__Compare(Other) == 0);
        }

        inline bool operator != (const T* Other) const
        {
            return (__Compare(Other) != 0);
        }

        inline bool operator > (const T* Other) const
        {
            return (__Compare(Other) > 0);
        }

        inline bool operator >= (const T* Other) const
        {
            return (__Compare(Other) >= 0);
        }

        inline bool operator < (const T* Other) const
        {
            return (__Compare(Other) < 0);
        }

        inline bool operator <= (const T* Other) const
        {
            return (__Compare(Other) <= 0);
        }

        inline bool IsNull() const
        {
            return (__Ptr == NULL);
        }
    };

    template<typename T>
    const ESSmartPtr<T> ESSmartPtr<T>::NullObject;

    template<typename T>
    const ConstESSmartPtr<T> ConstESSmartPtr<T>::NullObject;


} /* End namespace */

#endif /* __ESOLVER_ES_SMART_PTR_HPP */


// 
// ESSmartPtr.hpp ends here
