// Z3Objects.cpp --- 
// 
// Filename: Z3Objects.cpp
// Author: Abhishek Udupa
// Created: Wed Jan  8 14:17:03 2014 (-0500)
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


#include "Z3Objects.hpp"
#include "../external/spookyhash/SpookyHash.hpp"

namespace ESolver {
    
    // Z3Object implementation
    Z3Object::Z3Object()
        : Ctx(nullptr), HashValid(false), HashValue((uint64)0)
    {
        // Nothing here
    }

    Z3Object::Z3Object(Z3_context Ctx)
        : Ctx(Ctx), HashValid(false), HashValue((uint64)0)
    {
        // Nothing here
    }

    Z3Object::Z3Object(const Z3Object& Other)
        : Ctx(Other.Ctx), HashValid(Other.HashValid), HashValue(Other.HashValue)
    {
        // Nothing here
    }

    Z3Object::~Z3Object()
    {
        // Nothing here
    }

    uint64 Z3Object::Hash() const
    {
        if (!HashValid) {
            ComputeHashValue();
            HashValid = true;
        }
        return HashValue;
    }

    // Z3Sort implementation
    Z3Sort::Z3Sort()
        : Z3Object(), Sort(nullptr)
    {
        // Nothing here
    }

    Z3Sort::Z3Sort(Z3_context Ctx, Z3_sort Sort)
        : Z3Object(Ctx), Sort(Sort)
    {
        if (Ctx == nullptr || Sort == nullptr) {
            throw InternalError((string)"Error: Attempted to call Z3Sort::Z3Sort(Z3_context, Z3_sort " + 
                                "with one or more nullptrs");
        }
        Z3_inc_ref(Ctx, Z3_sort_to_ast(Ctx, Sort));
    }

    Z3Sort::Z3Sort(const Z3Sort& Other)
        : Z3Object(Other.Ctx), Sort(Other.Sort)
    {
        if (Ctx != nullptr && Sort != nullptr) {
            Z3_inc_ref(Ctx, Z3_sort_to_ast(Ctx, Sort));
        }
    }

    Z3Sort::~Z3Sort()
    {
        if (Ctx != nullptr && Sort != nullptr) {
            Z3_dec_ref(Ctx, Z3_sort_to_ast(Ctx, Sort));
        }
    }

    void Z3Sort::ComputeHashValue() const
    {
        if (Ctx != nullptr && Sort != nullptr) {
            auto&& SortAsString = ToString();
            HashValue = SpookyHash::SpookyHash::Hash64(SortAsString.c_str(), SortAsString.length(), (uint64)0);
        } else {
            throw InternalError((string)"Error ComputeHashValue() called on null Z3Sort object");
        }
    }
    
    Z3Sort& Z3Sort::operator = (const Z3Sort& Other)
    {
        if(&Other == this) {
            return *this;
        }
        
        if (Ctx != nullptr && Sort != nullptr) {
            Z3_dec_ref(Ctx, Z3_sort_to_ast(Ctx, Sort));
        }
        Ctx = Other.Ctx;
        Sort = Other.Sort;
        if (Ctx != nullptr && Sort != nullptr) {
            Z3_inc_ref(Ctx, Z3_sort_to_ast(Ctx, Sort));
        }
        return *this;
    }

    bool Z3Sort::operator == (const Z3Object& Other) const
    {
        auto AsZ3Sort = dynamic_cast<const Z3Sort*>(&Other);
        if (AsZ3Sort == nullptr) {
            return false;
        }
        if (Ctx == nullptr || Sort == nullptr) {
            return (AsZ3Sort->Ctx == Ctx && AsZ3Sort->Sort == Sort);
        } else {
            return (Ctx == AsZ3Sort->Ctx && Z3_is_eq_sort(Ctx, Sort, AsZ3Sort->Sort));
        }
    }

    string Z3Sort::ToString() const
    {
        if (Ctx != nullptr && Sort != nullptr) {
            string Retval = Z3_sort_to_string(Ctx, Sort);
            return Retval;
        } else {
            throw InternalError((string)"Error ToString() called on null Z3Sort object");
        }
    }

    // Z3Expr implementation

    Z3Expr::Z3Expr()
        : Z3Object(), AST(nullptr)
    {
        // Nothing here
    }

    Z3Expr::Z3Expr(Z3_context Ctx, Z3_ast AST)
        : Z3Object(Ctx), AST(AST)
    {
        if (AST == nullptr || Ctx == nullptr) {
            throw InternalError((string)"Error: Attempted to call Z3Expr::Z3Expr(Z3_context, Z3_ast) with " +
                                "one or more nullptrs");
        }
        Z3_inc_ref(Ctx, AST);
    }

    Z3Expr::Z3Expr(const Z3Expr& Other)
        : Z3Object(Other.Ctx), AST(Other.AST)
    {
        if(AST != nullptr && Ctx != nullptr) {
            Z3_inc_ref(Ctx, AST);
        }
    }

    Z3Expr::~Z3Expr()
    {
        if(AST != nullptr && Ctx != nullptr) {
            Z3_dec_ref(Ctx, AST);
        }
    }

    void Z3Expr::ComputeHashValue() const
    {
        if (Ctx == nullptr || AST == nullptr) {
            throw InternalError((string)"ComputeHashValue() called on a null Z3Expr object");
        }
        auto&& ASTAsString = ToString();
        HashValue = SpookyHash::SpookyHash::Hash64(ASTAsString.c_str(), ASTAsString.length(), (uint64)0);
    }

    Z3Expr& Z3Expr::operator = (const Z3Expr& Other)
    {
        if(&Other == this) {
            return *this;
        }

        // Do the destructor
        if(AST != nullptr && Ctx != nullptr) {
            Z3_dec_ref(Ctx, AST);
        }

        // Assign
        Ctx = Other.Ctx;
        AST = Other.AST;

        if(AST != nullptr && Ctx != nullptr) {
            Z3_inc_ref(Ctx, AST);
        }
        return *this;
    }

    Z3Sort Z3Expr::GetSort() const
    {
        if (Ctx == nullptr || AST == nullptr) {
            return Z3Sort();
        } else {
            return Z3Sort(Ctx, Z3_get_sort(Ctx, AST));
        }
    }

    bool Z3Expr::operator == (const Z3Object& Other) const
    {
        auto AsZ3Expr = dynamic_cast<const Z3Expr*>(&Other);
        if (AsZ3Expr == nullptr) {
            return false;
        }
        if (Ctx == nullptr || AST == nullptr) {
            return (Ctx == AsZ3Expr->Ctx && AST == AsZ3Expr->AST);
        } else {
            return (Ctx == AsZ3Expr->Ctx && Z3_is_eq_ast(Ctx, AST, AsZ3Expr->AST));
        }
    }

    string Z3Expr::ToString() const
    {
        if (Ctx != nullptr && AST != nullptr) {
            return string(Z3_ast_to_string(Ctx, AST));
        } else {
            throw InternalError((string)"ToString() called on null Z3Expr object");
        }
    }

    // Z3Model implementation
    Z3Model::Z3Model()
        : Z3Object(), Model(NULL)
    {
        // Nothing here
    }

    Z3Model::Z3Model(Z3_context Ctx, Z3_model Model)
        : Z3Object(Ctx), Model(Model)
    {
        if (Ctx == nullptr || Model == nullptr) {
            throw InternalError((string)"Error: Z3Model::Z3Model(Z3_context, Z3_model) called with " + 
                                "one or more nullptrs");
        }
        Z3_model_inc_ref(Ctx, Model);
    }

    Z3Model::Z3Model(const Z3Model& Other)
        : Z3Object(Other.Ctx), Model(Other.Model)
    {
        if(Model != nullptr && Ctx != nullptr) {
            Z3_model_inc_ref(Ctx, Model);
        }
    }

    Z3Model::~Z3Model()
    {
        if(Model != nullptr && Ctx != nullptr) {
            Z3_model_dec_ref(Ctx, Model);
        }
    }

    Z3Model& Z3Model::operator = (const Z3Model& Other)
    {
        if(&Other == this) {
            return *this;
        }

        // Do the destructor
        if(Model != nullptr && Ctx != nullptr) {
            Z3_model_dec_ref(Ctx, Model);
        }

        // Assign
        Ctx = Other.Ctx;
        Model = Other.Model;

        if(Model != nullptr && Ctx != nullptr) {
            Z3_model_inc_ref(Ctx, Model);
        }
        return *this;
    }

    void Z3Model::ComputeHashValue() const
    {
        if (Ctx == nullptr || Model == nullptr) {
            throw InternalError((string)"ComputeHashValue() called on a null Z3Model object");
        }
        auto&& AsString = ToString();
        HashValue = SpookyHash::SpookyHash::Hash64(AsString.c_str(), AsString.length(), (uint64)0);
    }

    string Z3Model::ToString() const
    {
        if (Ctx == nullptr || Model == nullptr) {
            throw InternalError((string)"ToString() called on a null Z3Model object");
        }
        return string(Z3_model_to_string(Ctx, Model));
    }
            
    bool Z3Model::operator == (const Z3Object& Other) const
    {
        auto AsZ3Model = dynamic_cast<const Z3Model*>(&Other);
        if (AsZ3Model == nullptr) {
            return false;
        }
        return (Ctx == AsZ3Model->Ctx && AsZ3Model->Model == Model);
    }

} /* End namespace */


// 
// Z3Objects.cpp ends here
