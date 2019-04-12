// RefCountable.hpp ---
//
// Filename: RefCountable.hpp
// Author: Abhishek Udupa
// Created: Sun Jun 29 13:47:16 2014 (-0400)
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

// Basic ref countable type

#if !defined __SYGUS2_PARSER_REF_COUNTABLE_HPP
#define __SYGUS2_PARSER_REF_COUNTABLE_HPP

#include <type_traits>
#include "Sygus2ParserCommon.hpp"

namespace Sygus2Parser {

namespace detail_ {

class RefCountableEBC
{
    // Empty base class
};

} /* end namespace detail_ */

template <typename DerivedClass>
class RefCountable : public detail_::RefCountableEBC
{
private:
    mutable i64 m_ref_count_;

public:
    inline RefCountable()
        : m_ref_count_((i64)0)
    {
        // Nothing here
    }

    virtual inline ~RefCountable()
    {
        // Nothing here
    }

    inline void inc_ref_() const
    {
        m_ref_count_++;
    }

    inline void dec_ref_() const
    {
        m_ref_count_--;
        if (m_ref_count_ <= 0) {
            auto this_as_derived = static_cast<const DerivedClass*>(this);
            delete this_as_derived;
        }
    }

    inline i64 get_ref_count_() const
    {
        return m_ref_count_;
    }
};

} /* end namespace Sygus2Parser */

#endif /* __SYGUS2_PARSER_REF_COUNTABLE_HPP_REF */

//
// RefCountable.hpp ends here
