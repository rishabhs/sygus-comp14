// TypeManager.hpp --- 
// 
// Filename: TypeManager.hpp
// Author: Abhishek Udupa
// Created: Wed Jan  1 20:43:13 2014 (-0500)
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
//    This product includes software developed by the University of Pennsylvania.
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

#if !defined __ESOLVER_TYPE_MANAGER_HPP
#define __ESOLVER_TYPE_MANAGER_HPP

#include "../common/ESolverForwardDecls.hpp"
#include "../utils/Hashers.hpp"

namespace ESolver {

    // A type manager. Responsible for ensuring that only a 
    // canonical representation of a type is available in the
    // system. All requests for new types need to come from here
    
    class TypeManager
    {
    private:
        typedef unordered_set<ESFixedTypeBase*, TypePtrHasher, TypePtrEquals> TypeSet;
        typedef unordered_map<string, ESFixedTypeBase*> TypeMap;
        
        TypeSet TheTypeSet;
        TypeMap TheTypeMap;
        TheoremProver* TP;

        // helper 
        // something tells me that some day I'm going to regret 
        // this evil template hackery. But until that day, 
        // it's less code to write :-)

        template<typename T, typename... ArgTypes>
        T* GetCachedOrInsert(ArgTypes&&... Args)
        {
            T Type(forward<ArgTypes>(Args)...);
            TypeSet::iterator it;
            if ((it = TheTypeSet.find(&Type)) == TheTypeSet.end()) {
                it = (TheTypeSet.insert(new T(TP, forward<ArgTypes>(Args)...))).first;
            }
            return static_cast<T*>(*it);
        }

    public:
        TypeManager(TheoremProver* TP);
        ~TypeManager();

        template<typename T, typename... ArgTypes>
        const T* CreateType(ArgTypes&&... Args)
        {
            return GetCachedOrInsert<T>(forward<ArgTypes>(Args)...);
        }

        // For type lookups and bindings
        void BindType(const string& TypeName, const ESFixedTypeBase* Type);
        const ESFixedTypeBase* LookupType(const string& TypeName) const;

        template<typename T>
        const T* LookupType(const string& TypeName) const
        {
            return dynamic_cast<const T*>(LookupType(TypeName));
        }
    };

} /* end namespace */

#endif /* __ESOLVER_TYPE_MANAGER_HPP */


// 
// TypeManager.hpp ends here
