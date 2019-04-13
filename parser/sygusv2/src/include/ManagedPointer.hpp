// ManagedPointer.hpp ---
//
// Filename: ManagedPointer.hpp
// Author: Abhishek Udupa
// Created: Sun Jun 29 14:10:50 2014 (-0400)
//
//
// Copyright (c) 2015, Abhishek Udupa, University of Pennsylvania
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

#if !defined __SYGUS2_PARSER_MANAGED_POINTER_HPP
#define __SYGUS2_PARSER_MANAGED_POINTER_HPP

#include <type_traits>
#include <utility>

#include "RefCountable.hpp"

namespace Sygus2Parser {
namespace detail_ {

// base class for managed pointers (for type traits)
class ManagedPointerEBC
{
    // Nothing here
};

template <typename T, bool CONSTPOINTER>
class ManagedPointerBase : private ManagedPointerEBC
{
public:
    typedef typename std::conditional<CONSTPOINTER, const T*, T*>::type RawPointerType;
    typedef typename std::conditional<CONSTPOINTER, const T&, T&>::type ReferenceType;

    static const T* const pointer_sentinel;

private:
    RawPointerType m_ptr;

    template <typename U, bool OTHERCONSTPOINTER>
    inline i64 compare_(const ManagedPointerBase<U, OTHERCONSTPOINTER>& other_managed_ptr) const;

    template <typename U>
    inline i64 compare_(const U* other_raw_ptr) const;

public:
    static const ManagedPointerBase null_pointer;

    // Default constructor
    inline ManagedPointerBase();

    // Copy constructor
    inline ManagedPointerBase(const ManagedPointerBase& other_managed_ptr);

    template <bool OTHERCONSTPOINTER>
    inline ManagedPointerBase(const ManagedPointerBase<T, OTHERCONSTPOINTER>& other_managed_ptr);

    // Move constructor
    inline ManagedPointerBase(ManagedPointerBase&& other_managed_ptr);

    template <bool OTHERCONSTPOINTER>
    inline ManagedPointerBase(ManagedPointerBase<T, OTHERCONSTPOINTER>&& other_managed_ptr);

    // From raw pointer
    inline ManagedPointerBase(RawPointerType raw_pointer);

    // Destructor
    inline ~ManagedPointerBase();

    // get the raw pointer
    inline RawPointerType get_raw_pointer() const;

    // cast to raw pointer
    inline operator RawPointerType () const;

    // Assignment operator
    inline ManagedPointerBase& operator = (const ManagedPointerBase& other_managed_ptr);

    template <bool OTHERCONSTPOINTER>
    inline ManagedPointerBase& operator = (const ManagedPointerBase<T, OTHERCONSTPOINTER>& other_managed_ptr);

    // Move assignment operator
    inline ManagedPointerBase& operator = (ManagedPointerBase&& other_managed_ptr);

    template <bool OTHERCONSTPOINTER>
    inline ManagedPointerBase& operator = (ManagedPointerBase<T, OTHERCONSTPOINTER>&& other);

    // Assignment to raw pointer
    inline ManagedPointerBase& operator = (RawPointerType raw_pointer);

    inline RawPointerType operator -> () const;
    inline ReferenceType operator * () const;

    template <typename U, bool OTHERCONSTPOINTER>
    inline bool
    operator == (const ManagedPointerBase<U, OTHERCONSTPOINTER>& other_managed_ptr) const;

    template <typename U, bool OTHERCONSTPOINTER>
    inline bool
    operator != (const ManagedPointerBase<U, OTHERCONSTPOINTER>& other_managed_ptr) const;

    template <typename U, bool OTHERCONSTPOINTER>
    inline bool
    operator < (const ManagedPointerBase<U, OTHERCONSTPOINTER>& other_managed_ptr) const;

    template <typename U, bool OTHERCONSTPOINTER>
    inline bool
    operator <= (const ManagedPointerBase<U, OTHERCONSTPOINTER>& other_managed_ptr) const;

    template <typename U, bool OTHERCONSTPOINTER>
    inline bool
    operator > (const ManagedPointerBase<U, OTHERCONSTPOINTER>& other_managed_ptr) const;

    template <typename U, bool OTHERCONSTPOINTER>
    inline bool
    operator >= (const ManagedPointerBase<U, OTHERCONSTPOINTER>& other_managed_ptr) const;


    inline bool operator == (const T* other_pointer) const;
    inline bool operator != (const T* other_pointer) const;
    inline bool operator < (const T* other_pointer) const;
    inline bool operator <= (const T* other_pointer) const;
    inline bool operator > (const T* other_pointer) const;
    inline bool operator >= (const T* other_pointer) const;

    inline bool operator ! () const;
    inline bool is_null() const;
    inline operator bool () const;
};

// Implementation of ManagedPointerBase
template <typename T, bool CONSTPOINTER>
const ManagedPointerBase<T, CONSTPOINTER> ManagedPointerBase<T, CONSTPOINTER>::null_pointer;

// Anything below this address is considered not a valid pointer
template <typename T, bool CONSTPOINTER>
const T* const
ManagedPointerBase<T, CONSTPOINTER>::pointer_sentinel = (T*)0x1000;

template <typename T, bool CONSTPOINTER>
template <typename U, bool OTHERCONSTPOINTER>
inline i64
ManagedPointerBase<T, CONSTPOINTER>::compare_
(const ManagedPointerBase<U, OTHERCONSTPOINTER>& other_managed_ptr) const
{
    return (i64)(reinterpret_cast<const char*>(m_ptr) -
                 reinterpret_cast<const char*>(other_managed_ptr.get_raw_pointer()));
}

template <typename T, bool CONSTPOINTER>
template <typename U>
inline i64 ManagedPointerBase<T, CONSTPOINTER>::compare_(const U* other_raw_ptr) const
{
    return (i64)(reinterpret_cast<const char*>(m_ptr) -
                 reinterpret_cast<const char*>(other_raw_ptr));
}

template <typename T, bool CONSTPOINTER>
inline ManagedPointerBase<T, CONSTPOINTER>::ManagedPointerBase()
    : m_ptr(nullptr)
{
    // Nothing here
}

template <typename T, bool CONSTPOINTER>
inline ManagedPointerBase<T, CONSTPOINTER>::ManagedPointerBase(const ManagedPointerBase& other_managed_ptr)
    : m_ptr(nullptr)
{
    m_ptr = other_managed_ptr.get_raw_pointer();
    if (m_ptr >= pointer_sentinel) {
        m_ptr->inc_ref_();
    }
}

template <typename T, bool CONSTPOINTER>
template <bool OTHERCONSTPOINTER>
inline
ManagedPointerBase<T, CONSTPOINTER>::ManagedPointerBase
(const ManagedPointerBase<T, OTHERCONSTPOINTER>& other_managed_ptr)
    : m_ptr(nullptr)
{
    static_assert((!OTHERCONSTPOINTER || CONSTPOINTER),
                  "Cannot convert a const managed pointer into a non-const "
                  "managed pointer");

    m_ptr = other_managed_ptr.get_raw_pointer();
    if (m_ptr >= pointer_sentinel) {
        m_ptr->inc_ref_();
    }
}

template <typename T, bool CONSTPOINTER>
inline ManagedPointerBase<T, CONSTPOINTER>::ManagedPointerBase(ManagedPointerBase&&
                                                               other_managed_ptr)
    : m_ptr(other_managed_ptr.get_raw_pointer())
{
    if (m_ptr >= pointer_sentinel) {
        m_ptr->inc_ref_();
    }
}

template <typename T, bool CONSTPOINTER>
template <bool OTHERCONSTPOINTER>
inline
ManagedPointerBase<T, CONSTPOINTER>::ManagedPointerBase
(ManagedPointerBase<T, OTHERCONSTPOINTER>&& other_managed_ptr)
    : ManagedPointerBase<T, CONSTPOINTER>()
{
    static_assert((!OTHERCONSTPOINTER || CONSTPOINTER),
                  "Cannot convert a const managed pointer into a non-const "
                  "managed pointer");

    m_ptr = other_managed_ptr.get_raw_pointer();
    if (m_ptr >= pointer_sentinel) {
        m_ptr->inc_ref_();
    }
}

template <typename T, bool CONSTPOINTER>
inline ManagedPointerBase<T, CONSTPOINTER>::ManagedPointerBase(RawPointerType raw_pointer)
    : m_ptr(raw_pointer)
{
    if (m_ptr >= pointer_sentinel) {
        m_ptr->inc_ref_();
    }
}

template <typename T, bool CONSTPOINTER>
inline ManagedPointerBase<T, CONSTPOINTER>::~ManagedPointerBase()
{
    if (m_ptr >= pointer_sentinel) {
        m_ptr->dec_ref_();
    }
    m_ptr = nullptr;
}

template <typename T, bool CONSTPOINTER>
inline typename ManagedPointerBase<T, CONSTPOINTER>::RawPointerType
ManagedPointerBase<T, CONSTPOINTER>::get_raw_pointer() const
{
    return m_ptr;
}

template <typename T, bool CONSTPOINTER>
inline ManagedPointerBase<T, CONSTPOINTER>::operator RawPointerType () const
{
    return m_ptr;
}

template <typename T, bool CONSTPOINTER>
inline ManagedPointerBase<T, CONSTPOINTER>&
ManagedPointerBase<T, CONSTPOINTER>::operator = (const ManagedPointerBase& other_managed_ptr)
{
    if (&other_managed_ptr == this) {
        return *this;
    }
    if (m_ptr >= pointer_sentinel) {
        m_ptr->dec_ref_();
        m_ptr = nullptr;
    }

    m_ptr = other_managed_ptr.get_raw_pointer();
    m_ptr->inc_ref_();
    return *this;
}

template <typename T, bool CONSTPOINTER>
template <bool OTHERCONSTPOINTER>
inline ManagedPointerBase<T, CONSTPOINTER>&
ManagedPointerBase<T, CONSTPOINTER>::operator =
(const ManagedPointerBase<T, OTHERCONSTPOINTER>& other_managed_ptr)
{
    static_assert((!OTHERCONSTPOINTER || CONSTPOINTER),
                  "Cannot convert a const managed pointer into a non-const "
                  "managed pointer");

    if ((decltype(this))(&other_managed_ptr) == this) {
        return *this;
    }
    if (m_ptr >= pointer_sentinel) {
        m_ptr->dec_ref_();
        m_ptr = nullptr;
    }
    m_ptr = other_managed_ptr.get_raw_pointer();
    m_ptr->inc_ref_();
    return *this;
}

template <typename T, bool CONSTPOINTER>
inline ManagedPointerBase<T, CONSTPOINTER>&
ManagedPointerBase<T, CONSTPOINTER>::operator = (ManagedPointerBase&& other_managed_ptr)
{
    if (&other_managed_ptr == this) {
        return *this;
    }
    if (m_ptr >= pointer_sentinel) {
        m_ptr->dec_ref_();
        m_ptr = nullptr;
    }
    m_ptr = other_managed_ptr.get_raw_pointer();
    m_ptr->inc_ref_();
    return *this;
}

template <typename T, bool CONSTPOINTER>
template <bool OTHERCONSTPOINTER>
inline ManagedPointerBase<T, CONSTPOINTER>&
ManagedPointerBase<T, CONSTPOINTER>::operator =
(ManagedPointerBase<T, OTHERCONSTPOINTER>&& other_managed_ptr)
{
    static_assert((!OTHERCONSTPOINTER || CONSTPOINTER),
                  "Cannot convert a const managed pointer into a non-const "
                  "managed pointer");

    if (&other_managed_ptr == this) {
        return *this;
    }
    m_ptr->dec_ref_();
    m_ptr = other_managed_ptr.get_raw_pointer();
    m_ptr->inc_ref_();
    return *this;
}

template <typename T, bool CONSTPOINTER>
inline ManagedPointerBase<T, CONSTPOINTER>&
ManagedPointerBase<T, CONSTPOINTER>::operator =
(RawPointerType raw_pointer)
{
    if (m_ptr >= pointer_sentinel) {
        m_ptr->dec_ref_();
    }
    m_ptr = raw_pointer;
    if (m_ptr >= pointer_sentinel) {
        m_ptr->inc_ref_();
    }
    return (*this);
}

template <typename T, bool CONSTPOINTER>
inline typename ManagedPointerBase<T, CONSTPOINTER>::RawPointerType
ManagedPointerBase<T, CONSTPOINTER>::operator -> () const
{
    return m_ptr;
}

template <typename T, bool CONSTPOINTER>
inline typename ManagedPointerBase<T, CONSTPOINTER>::ReferenceType
ManagedPointerBase<T, CONSTPOINTER>::operator * () const
{
    return (*m_ptr);
}

template <typename T, bool CONSTPOINTER>
template <typename U, bool OTHERCONSTPOINTER>
inline bool
ManagedPointerBase<T, CONSTPOINTER>::operator ==
(const ManagedPointerBase<U, OTHERCONSTPOINTER>& other_managed_ptr) const
{
    return (compare_(other_managed_ptr) == 0);
}

template <typename T, bool CONSTPOINTER>
template <typename U, bool OTHERCONSTPOINTER>
inline bool
ManagedPointerBase<T, CONSTPOINTER>::operator !=
(const ManagedPointerBase<U, OTHERCONSTPOINTER>& other_managed_ptr) const
{
    return (compare_(other_managed_ptr) != 0);
}

template <typename T, bool CONSTPOINTER>
template <typename U, bool OTHERCONSTPOINTER>
inline bool
ManagedPointerBase<T, CONSTPOINTER>::operator <
(const ManagedPointerBase<U, OTHERCONSTPOINTER>& other_managed_ptr) const
{
    return (compare_(other_managed_ptr) < 0);
}

template <typename T, bool CONSTPOINTER>
template <typename U, bool OTHERCONSTPOINTER>
inline bool
ManagedPointerBase<T, CONSTPOINTER>::operator <=
(const ManagedPointerBase<U, OTHERCONSTPOINTER>& other_managed_ptr) const
{
    return (compare_(other_managed_ptr) <= 0);
}

template <typename T, bool CONSTPOINTER>
template <typename U, bool OTHERCONSTPOINTER>
inline bool
ManagedPointerBase<T, CONSTPOINTER>::operator >
(const ManagedPointerBase<U, OTHERCONSTPOINTER>& other_managed_ptr) const
{
    return (compare_(other_managed_ptr) > 0);
}

template <typename T, bool CONSTPOINTER>
template <typename U, bool OTHERCONSTPOINTER>
inline bool
ManagedPointerBase<T, CONSTPOINTER>::operator >=
(const ManagedPointerBase<U, OTHERCONSTPOINTER>& other_managed_ptr) const
{
    return (compare_(other_managed_ptr) >= 0);
}

template <typename T, bool CONSTPOINTER>
inline bool ManagedPointerBase<T, CONSTPOINTER>::operator ==
(const T* other_pointer) const
{
    return (compare_(other_pointer) == 0);
}

template <typename T, bool CONSTPOINTER>
inline bool ManagedPointerBase<T, CONSTPOINTER>::operator !=
(const T* other_pointer) const
{
    return (compare_(other_pointer) != 0);
}

template <typename T, bool CONSTPOINTER>
inline bool ManagedPointerBase<T, CONSTPOINTER>::operator <
(const T* other_pointer) const
{
    return (compare_(other_pointer) < 0);
}

template <typename T, bool CONSTPOINTER>
inline bool ManagedPointerBase<T, CONSTPOINTER>::operator <=
(const T* other_pointer) const
{
    return (compare_(other_pointer) <= 0);
}

template <typename T, bool CONSTPOINTER>
inline bool ManagedPointerBase<T, CONSTPOINTER>::operator >
(const T* other_pointer) const
{
    return (compare_(other_pointer) > 0);
}

template <typename T, bool CONSTPOINTER>
inline bool ManagedPointerBase<T, CONSTPOINTER>::operator >=
(const T* other_pointer) const
{
    return (compare_(other_pointer) >= 0);
}

template <typename T, bool CONSTPOINTER>
inline bool ManagedPointerBase<T, CONSTPOINTER>::is_null() const
{
    return (m_ptr == nullptr);
}

template <typename T, bool CONSTPOINTER>
inline bool ManagedPointerBase<T, CONSTPOINTER>::operator !() const
{
    return (is_null());
}

template <typename T, bool CONSTPOINTER>
inline ManagedPointerBase<T, CONSTPOINTER>::operator bool () const
{
    return (m_ptr != nullptr);
}

} /* end namespace detail_ */

template <typename T, bool CONSTPOINTER>
static inline detail_::ManagedPointerBase<T, false>
discard_const(const detail_::ManagedPointerBase<T, CONSTPOINTER>& managed_pointer)
{
    if (!CONSTPOINTER) {
        return managed_pointer;
    } else {
        auto non_const_raw_ptr = const_cast<T*>(managed_pointer->get_raw_pointer());
        return detail_::ManagedPointerBase<T, false>(non_const_raw_ptr);
    }
}

// typedefs for commonly used managed pointer types
template <typename T>
using ManagedPointer = detail_::ManagedPointerBase<T, false>;

template <typename T>
using ManagedConstPointer = detail_::ManagedPointerBase<T, true>;

template <typename T, bool CONSTPOINTER>
static inline std::ostream& operator << (std::ostream& out_stream,
                                         const detail_::ManagedPointerBase<T, CONSTPOINTER>&
                                         managed_ptr)
{
    out_stream << managed_ptr.get_raw_pointer();
    return out_stream;
}

} /* end namespace Sygus2Parser */

#endif /* __SYGUS2_PARSER_MANAGED_POINTER_HPP */

//
// ManagedPointer.hpp ends here
