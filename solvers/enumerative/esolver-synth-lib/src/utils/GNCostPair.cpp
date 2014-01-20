// GNCostPair.cpp --- 
// 
// Filename: GNCostPair.cpp
// Author: Abhishek Udupa
// Created: Sun Jan 12 22:52:23 2014 (-0500)
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


#include "GNCostPair.hpp"
#include "../descriptions/GrammarNodes.hpp"
#include <boost/functional/hash.hpp>

namespace ESolver {

    // For empty key in dense hash map
    const GNCostPair NullGNCostPair;

    GNCostPair::GNCostPair(const GrammarNode* Node, uint32 Cost)
        : Node(Node), Cost(Cost)
    {
        // Nothing here
    }

    GNCostPair::GNCostPair()
        : Node(NULL), Cost(0)
    {
        // Nothing here
    }

    GNCostPair::GNCostPair(const GNCostPair& Other)
        : Node(Other.Node), Cost(Other.Cost)
    {
        // Nothing here
    }

    GNCostPair::~GNCostPair()
    {
        // Nothing here
    }

    const GrammarNode* GNCostPair::GetNode() const
    {
        return Node;
    }

    uint32 GNCostPair::GetCost() const
    {
        return Cost;
    }

    bool GNCostPair::operator == (const GNCostPair& Other) const
    {
        return ((Node == Other.Node) && (Cost == Other.Cost));
    }

    GNCostPair& GNCostPair::operator = (const GNCostPair& Other)
    {
        if(&Other == this) {
            return *this;
        }
        Node = Other.Node;
        Cost = Other.Cost;
        return *this;
    }

    string GNCostPair::ToString() const
    {
        ostringstream sstr;
        sstr << "<" << Node->ToString() << ", " << Cost << ">";
        return sstr.str();
    }

    uint64 GNCostPair::Hash() const
    {
        uint64 Retval = 0;
        boost::hash_combine(Retval, Cost);
        boost::hash_combine(Retval, Node->Hash());
        return Retval;
    }
    
} /* End namespace */


// 
// GNCostPair.cpp ends here
