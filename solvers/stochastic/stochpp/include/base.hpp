#ifndef __BASE_HPP_
#define __BASE_HPP_

#include "nonstd.hpp"

namespace stoch {

struct id
{
    id() : v(0) {};
    id(size_t v) : v(v) {};
    size_t v;
};

bool operator<(const id& x, const id& y)
{
    return x.v < y.v;
}

template <typename U> struct expr;
typedef expr <z_class> aexpr;
typedef expr <bool> bexpr;
typedef expr <bv> bvexpr;

typedef shared_ptr <const aexpr> aexpr_p;
typedef shared_ptr <const bexpr> bexpr_p;
typedef shared_ptr <const bvexpr> bvexpr_p;

template <typename U> struct fexpr;
typedef fexpr <z_class> afexpr;
typedef fexpr <bool> bfexpr;
typedef fexpr <bv> bvfexpr;

typedef shared_ptr <const afexpr> afexpr_p;
typedef shared_ptr <const bfexpr> bfexpr_p;
typedef shared_ptr <const bvfexpr> bvfexpr_p;

// Typedefs to evaluate expressions given concrete valuations of its free variables
typedef map <id, z_class> aval_t;
typedef map <id, bool> bval_t;
typedef map <id, bv> bvval_t;
typedef tuple <aval_t, bval_t, bvval_t> val_t;

// Typedefs to substitute expressions
typedef map <id, aexpr_p> asubst_t;
typedef map <id, bexpr_p> bsubst_t;
typedef map <id, bvexpr_p> bvsubst_t;
typedef tuple <asubst_t, bsubst_t, bvsubst_t> subst_t;

size_t subst_size(const subst_t& subst)
{
    return std::get <0> (subst).size() + std::get <1> (subst).size() + std::get <2> (subst).size();
}

// Typedefs to substitute fexprs
typedef map <id, afexpr_p> afsubst_t;
typedef map <id, bfexpr_p> bfsubst_t;
typedef map <id, bvfexpr_p> bvfsubst_t;
typedef tuple <afsubst_t, bfsubst_t, bvfsubst_t> fsubst_t;

size_t fsubst_size(const fsubst_t& fsubst)
{
    return std::get <0> (fsubst).size() + std::get <1> (fsubst).size() + std::get <2> (fsubst).size();
}

// Evaluating fexprs. Memoization space for common subexpression elimination
struct memo_t
{
    map <size_t, z_class> zmemo;
    map <size_t, bool> bmemo;
    map <size_t, bv> bvmemo;
};

struct cs_elim_args_t
{
    fsubst_t fsubst;

    mutable map <string, size_t> amemo;
    mutable map <string, size_t> bmemo;
    mutable map <string, size_t> bvmemo;
};

// Grammars
template <typename U> struct gsymb_t : public id
{
    gsymb_t(id v, size_t len) : id(v), len(len)
    {
        bool is_bv = std::is_same <U, bv>::value;
        assert((is_bv && len > 0) || (!is_bv && len == 0));
    }

    gsymb_t() : gsymb_t(0, 0) {}
    gsymb_t(id v) : gsymb_t(v, 0) {}

    size_t len;
};

template <typename U>
bool operator<(const gsymb_t <U>& s1, const gsymb_t <U>& s2)
{
    bool is_bv = std::is_same <U, bv>::value;
    if (!is_bv) {
        return s1.v < s2.v;
    } else {
        return s1.v < s2.v || (s1.v == s2.v && s1.len < s2.len);
    }
}

typedef gsymb_t <z_class> agsymb_t;
typedef gsymb_t <bool> bgsymb_t;
typedef gsymb_t <bv> bvgsymb_t;

template <typename U> struct prod_rule;
typedef prod_rule <z_class> aprod_rule;
typedef prod_rule <bool> bprod_rule;
typedef prod_rule <bv> bvprod_rule;

typedef shared_ptr <aprod_rule> aprod_rule_p;
typedef shared_ptr <bprod_rule> bprod_rule_p;
typedef shared_ptr <bvprod_rule> bvprod_rule_p;

template <typename U> struct production;
typedef production <z_class> aprodn;
typedef production <bool> bprodn;
typedef production <bv> bvprodn;

typedef shared_ptr <const aprodn> aprodn_p;
typedef shared_ptr <const bprodn> bprodn_p;
typedef shared_ptr <const bvprodn> bvprodn_p;

// Typedefs to unroll grammars

typedef set <id> set_id;
typedef tuple <set_id, set_id, set_id> var_set;

var_set var_set_union(const var_set& vs1, const var_set& vs2)
{
    set_id as = nonstd::set_union(std::get <0> (vs1), std::get <0> (vs2));
    set_id bs = nonstd::set_union(std::get <1> (vs1), std::get <1> (vs2));
    set_id bvs = nonstd::set_union(std::get <2> (vs1), std::get <2> (vs2));
    return var_set(as, bs, bvs);
}

var_set var_set_intersection(const var_set& vs1, const var_set& vs2)
{
    set_id as = nonstd::set_intersection(std::get <0> (vs1), std::get <0> (vs2));
    set_id bs = nonstd::set_intersection(std::get <1> (vs1), std::get <1> (vs2));
    set_id bvs = nonstd::set_intersection(std::get <2> (vs1), std::get <2> (vs2));
    return var_set(as, bs, bvs);
}

var_set var_set_intersection(const var_set& vs1, const var_set& vs2, const var_set& vs3)
{
    var_set vs23 = var_set_intersection(vs2, vs3);
    return var_set_intersection(vs1, vs23);
}

bool var_set_subset(const var_set& vs1, const var_set& vs2)
{
    return nonstd::subset(std::get <0> (vs1), std::get <0> (vs2)) &&
        nonstd::subset(std::get <1> (vs1), std::get <2> (vs2)) &&
        nonstd::subset(std::get <1> (vs1), std::get <2> (vs2));
}

ostream& operator<<(ostream& out, const set_id& s)
{
    out << "{ ";
    for (auto& x : s) {
        out << x.v << ", ";
    }
    return out << "}";
}

ostream& operator<<(ostream& out, const var_set& vs)
{
    return out << "(" << std::get <0> (vs) << ", " << std::get <1> (vs) << ", "
        << std::get <2> (vs) << ")";
}

} // namespace stoch

#endif // __BASE_HPP_

