// TextUtils.hpp ---
//
// Filename: TextUtils.hpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:49:42 2014 (-0500)
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


#if !defined __ESOLVER_TEXT_UTILS_HPP
#define __ESOLVER_TEXT_UTILS_HPP

#include <sstream>
#include "../descriptions/ESType.hpp"
#include "../exceptions/ESException.hpp"
#include <boost/algorithm/string/trim.hpp>
#include <boost/algorithm/string/split.hpp>
#include <boost/algorithm/string/classification.hpp>
#include <boost/algorithm/string/predicate.hpp>
#include <ctype.h>

namespace ESolver {

    static inline int64 ParseIntString(const string& ValueString)
    {
        string LocalValueString = boost::algorithm::trim_copy(ValueString);
        if(LocalValueString[0] == '(') {
            LocalValueString =
                boost::algorithm::trim_copy(LocalValueString.substr(1, LocalValueString.length() - 2));
            if(LocalValueString[0] == '-' && LocalValueString[1] == ' ') {
                LocalValueString = (string)"-" + LocalValueString.substr(2, LocalValueString.length() - 2);
            }
        }
        for(uint32 i = 0; i < LocalValueString.length(); ++i) {
            if(!isdigit(LocalValueString[i])) {
                if(i == 0 && LocalValueString[i] == '-') {
                    continue;
                } else {
                    throw ValueException((string)"Value \"" + ValueString +
                                         "\" is a malformed integer");
                }
            }
        }
        istringstream istr(LocalValueString);
        int64 Retval;
        istr >> Retval;
        return Retval;
    }

    static inline int64 ParseBoolString(const string& ValueString)
    {
        if(ValueString != "true" && ValueString != "false") {
            throw ValueException((string)"Value \"" + ValueString +
                                 "\" is a malformed boolean value");
        }
        return (ValueString == "true" ? 1 : 0);
    }

    static inline int64 ParseEnumString(const string& ValueString,
                                        const ESFixedTypeBase* Type)
    {
        auto TypeAsEnum = Type->As<ESEnumType>();
        if (TypeAsEnum == nullptr) {
            throw ValueException((string)"Value \"" + ValueString + "\" is not a valid " +
                                 " constructor for type with ID: " + to_string(Type->GetID()));

        }
        // Is this a qualified value?
        vector<string> SplitConstructors;
        boost::algorithm::split(SplitConstructors, ValueString,
                                boost::algorithm::is_any_of(":"),
                                boost::algorithm::token_compress_on);
        if (SplitConstructors.size() > 1) {
            string QueryString = SplitConstructors[1];
            if (!TypeAsEnum->IsValidEnumConstructor(QueryString)) {
                throw ValueException((string)"Value \"" + ValueString + "\" is not a valid " +
                                     " constructor for enumerated type " + TypeAsEnum->GetName());
            }
            return TypeAsEnum->GetEnumValueIDForName(QueryString);
        }

        string QueryString = ValueString;
        if(!TypeAsEnum->IsValidEnumConstructor(QueryString)) {
            throw ValueException((string)"Value \"" + ValueString + "\" is not a valid " +
                                 " constructor for enumerated type " + TypeAsEnum->GetName());
        }

        return Type->As<ESEnumType>()->GetEnumValueIDForName(QueryString);
    }

    static inline int64 ParseBVString(const string& ValueString, uint32 NumBits)
    {
        string ValString = ValueString;
        int64 Retval;

        boost::algorithm::trim(ValString);


        if(boost::algorithm::istarts_with(ValString, "0x") ||
           boost::algorithm::istarts_with(ValString, "#x")) {

            if (boost::algorithm::istarts_with(ValString, "#x")) {
                ValString[0] = '0';
            }

            if (ValString.length() != (NumBits / 4) + 2) {
                throw ValueException((string)"Value \"" + ValString + "\" is not a " +
                                     to_string(NumBits) + " bit bitvector value");
            }

            istringstream istr(ValString);

            istr >> hex >> Retval;
        } else if(boost::algorithm::istarts_with(ValString, "0b") ||
                  boost::algorithm::istarts_with(ValString, "#b")) {
            if (ValString.length() != NumBits + 2) {
                throw ValueException((string)"Value \"" + ValString + "\" is not a " +
                                     to_string(NumBits) + " bit bitvector value");
            }

            Retval = 0;
            for(uint32 i = 2; i < ValString.length(); ++i) {
                Retval <<= 1;
                if(ValString[i] == '1') {
                    Retval |= 1;
                } else if(ValString[i] == '0') {
                    Retval |= 0;
                } else {
                    throw ValueException((string)"Value \"" + ValString + "\" is not a valid value");
                }
            }
        } else {
            throw ValueException("Malformed Bitvector literal");
        }
        return Retval;
    }


    static inline string GetStringForBitVector(const uint64 TheValue,
                                               uint32 SetSize)
    {
        ostringstream sstr;
        for(int32 i = SetSize - 1; i >= 0; --i) {
            sstr << ((TheValue & (1 << i)) == 0 ? "0" : "1");
        }
        return sstr.str();
    }

    static inline pair<int64, const ESFixedTypeBase*> ParseEnumStringSynthLib(const string& ValueString,
                                                                              const ESolver* Solver)
    {
        // split the type name and the constructor name
        string LocalValueString = ValueString;
        boost::algorithm::trim(LocalValueString);
        vector<string> Parts;
        boost::algorithm::split(Parts, LocalValueString, boost::algorithm::is_any_of(":"),
                                boost::algorithm::token_compress_on);
        auto Type = Solver->LookupType(Parts[0]);
        if(Type == nullptr || Type->As<ESEnumType>() == nullptr) {
            throw TypeException((string)"Enumerated Type \"" + Parts[0] + "\" not defined");
        }
        if(!Type->As<ESEnumType>()->IsValidEnumConstructor(Parts[1])) {
            throw TypeException((string)"Constructor \"" + Parts[1] + "\" is not valid for enum type " +
                                "\"" + Parts[0] + "\"");
        }
        auto Val = Type->As<ESEnumType>()->GetEnumValueIDForName(Parts[1]);
        return pair<int64, const ESFixedTypeBase*>(Val, Type);
    }

    static inline pair<int64, const ESFixedTypeBase*> ParseBVStringSynthLib(const string& ValueString,
                                                                            ESolver* Solver)
    {
        string ValString = ValueString;
        int64 Retval;
        uint32 NumBits = 0;

        boost::algorithm::trim(ValString);

        // Convert to a standard notation first
        if(boost::algorithm::istarts_with(ValString, "#x")) {
            ValString = "0x" + ValString.substr(2, ValString.length() - 2);
        } else if(boost::algorithm::istarts_with(ValString, "#b")) {
            ValString = "0b" + ValString.substr(2, ValString.length() - 2);
        }

        if(boost::algorithm::istarts_with(ValString, "0x")) {
            istringstream istr(ValString);
            istr >> hex >> Retval;
            // 4 bits per hex value
            NumBits = (ValString.length() - 2) * 4;
        } else if(boost::algorithm::istarts_with(ValString, "0b")) {
            Retval = 0;
            for(uint32 i = 2; i < ValString.length(); ++i) {
                NumBits++;
                Retval <<= 1;
                if(ValString[i] == '1') {
                    Retval |= 1;
                } else if(ValString[i] == '0') {
                    Retval |= 0;
                } else {
                    throw ValueException((string)"Value \"" + ValString + "\" is not a valid value");
                }
            }
        }

        return pair<int64, const ESFixedTypeBase*>(Retval, Solver->CreateBitVectorType(NumBits));
    }


} /* End namespace */

#endif /* __ESOLVER_TEXT_UTILS_HPP */


//
// TextUtils.hpp ends here
