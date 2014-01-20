// Z3Objects.hpp --- 
// 
// Filename: Z3Objects.hpp
// Author: Abhishek Udupa
// Created: Wed Jan  8 14:16:54 2014 (-0500)
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


#if !defined __ESOLVER_Z3_OBJECTS_HPP
#define __ESOLVER_Z3_OBJECTS_HPP

#include <z3.h>
#include "../exceptions/ESException.hpp"

namespace ESolver {

    // Abstract Base class for all Z3 ref counted objects
    class Z3Object
    {
        friend class Z3TheoremProver;

    protected:
        Z3_context Ctx;
        mutable bool HashValid;
        mutable uint64 HashValue;
        
        virtual void ComputeHashValue() const = 0;
        
    public:
        Z3Object(Z3_context Ctx);
        Z3Object(const Z3Object& Other);
        Z3Object();
        virtual ~Z3Object();

        uint64 Hash() const;

        // and also an equality operator
        virtual bool operator == (const Z3Object& Other) const = 0;
        virtual string ToString() const = 0;
    };

    // This is a wrapper around the Z3_sort type
    class Z3Sort : public Z3Object
    {
        friend class Z3TheoremProver;

    private:
        Z3_sort Sort;

    protected:
        virtual void ComputeHashValue() const override;

    public:
        Z3Sort();
        Z3Sort(Z3_context Ctx, Z3_sort Sort);
        Z3Sort(const Z3Sort& Other);
        virtual ~Z3Sort();

        Z3Sort& operator = (const Z3Sort& Other);
        virtual bool operator == (const Z3Object& Other) const override;
        virtual string ToString() const override;
    };

    // A wrapper around Z3_ast
    class Z3Expr : public Z3Object
    {
        friend class Z3TheoremProver;

    private:
        Z3_ast AST;

    protected:
        virtual void ComputeHashValue() const override;
        
    public:
        Z3Expr();
        Z3Expr(Z3_context Ctx, Z3_ast AST);
        Z3Expr(const Z3Expr& Other);
        virtual ~Z3Expr();

        Z3Expr& operator = (const Z3Expr& Other);
        Z3Sort GetSort() const;
        virtual bool operator == (const Z3Object& Other) const override;
        virtual string ToString() const override;
    };
    
    // A wrapper around Z3_model
    class Z3Model : public Z3Object
    {
        friend class Z3TheoremProver;

    private:
        Z3_model Model;

    protected:
        virtual void ComputeHashValue() const override;

    public:
        Z3Model();
        Z3Model(Z3_context Ctx, Z3_model Model);
        Z3Model(const Z3Model& Other);
        virtual ~Z3Model();

        Z3Model& operator = (const Z3Model& Model);
        virtual bool operator == (const Z3Object& Other) const override;
        virtual string ToString() const override;
    };

} /* End namespace */

#endif /* __ESOLVER_Z3_OBJECTS_HPP */


// 
// Z3Objects.hpp ends here
