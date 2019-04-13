/*
Copyright (c) 2013,
Abhishek Udupa,
Mukund Raghothaman,
The University of Pennsylvania

All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

1. Redistributions of source code must retain the above copyright
notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright
notice, this list of conditions and the following disclaimer in the
documentation and/or other materials provided with the distribution.

3. Neither the name of the copyright holder nor the names of its
contributors may be used to endorse or promote products derived from
this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/

#if !defined __SYGUS2_PARSER_BASE_TYPES_HPP
#define __SYGUS2_PARSER_BASE_TYPES_HPP

#include <type_traits>

#include "Sygus2ParserCommon.hpp"

namespace Sygus2Parser {
namespace detail_ {

// Empty base class for equatables
class EquatableEBC {};

// Empty base class for hashables
class HashableEBC {};

} /* end namespace __detail */

template<typename TDerived>
class Equatable : public detail_::EquatableEBC
{
public:
    inline bool operator == (const TDerived& other) const
    {
        if (&other == this) {
            return true;
        }
        auto this_as_derived = static_cast<const TDerived*>(this);
        return this_as_derived->equals_(other);
    }

    inline bool operator != (const TDerived& other) const
    {
        return !(*this == other);
    }
};

template<typename TDerived>
class Hashable : public detail_::HashableEBC
{
private:
    mutable bool hash_valid_;
    mutable u64 hash_value_;

public:
    inline u64 get_hash() const
    {
        if (!hash_valid_) {
            auto this_as_derived = static_cast<const TDerived*>(this);
            hash_value_ = this_as_derived->compute_hash_();
            hash_valid_ = true;
        }

        return hash_value_;
    }
};

template<typename TDerived>
class Downcastable
{
public:
    template <typename T>
    T* as()
    {
        static_assert(std::is_base_of<TDerived, T>::value, "");
        return dynamic_cast<T*>(static_cast<TDerived*>(this));
    }

    template <typename T>
    const T* as() const
    {
        static_assert(std::is_base_of<TDerived, T>::value, "");
        return dynamic_cast<const T*>(static_cast<const TDerived*>(this));
    }

    template <typename T>
    T* static_as()
    {
        static_assert(std::is_base_of<TDerived, T>::value, "");
        return static_cast<T*>(static_cast<TDerived*>(this));
    }

    template <typename T>
    const T* static_as() const
    {
        static_assert(std::is_base_of<TDerived, T>::value, "");
        return static_cast<const T*>(static_cast<const TDerived*>(this));
    }

    template <typename T>
    T& as_ref()
    {
        static_assert(std::is_base_of<TDerived, T>::value, "");
        return dynamic_cast<T&>(static_cast<TDerived&>(*this));
    }

    template <typename T>
    const T& as_ref() const
    {
        static_assert(std::is_base_of<TDerived, T>::value, "");
        return dynamic_cast<const T&>(static_cast<const TDerived&>(*this));
    }

    template <typename T>
    T& static_as_ref()
    {
        static_assert(std::is_base_of<TDerived, T>::value, "");
        return static_cast<T&>(static_cast<TDerived&>(*this));
    }

    template <typename T>
    const T& static_as_ref() const
    {
        static_assert(std::is_base_of<TDerived, T>::value, "");
        return static_cast<const T&>(static_cast<const TDerived&>(*this));
    }

    template <typename T>
    bool is() const
    {
        static_assert(std::is_base_of<TDerived, T>::value, "");
        return (dynamic_cast<const T*>(static_cast<const TDerived*>(this)) != nullptr);
    }
};

// Hash and equality classes
template<typename T>
class Hasher
{
    static_assert(std::is_base_of<detail_::HashableEBC, T>::value,
                  "Hasher can only be instantiated with classes extending Hashable.");
public:
    inline u64 operator () (const T& obj) const
    {
        return obj.get_hash();
    }
};

template<typename T>
class Equals
{
    static_assert(std::is_base_of<detail_::EquatableEBC, T>::value,
                  "Equals can only be instantiated with classes extending Equatable.");
public:
    inline bool operator () (const T& obj1, const T& obj2) const
    {
        return obj1 == obj2;;
    }
};

} /* end namespace Sygus2Parser */

#endif /* __SYGUS2_PARSER_BASE_TYPES_HPP */
