#ifndef __PARSER_IFACE_DYN_HPP_
#define __PARSER_IFACE_DYN_HPP_

#include "parser_iface.hpp"

namespace stoch {
namespace parser {

template <typename T1, typename T2, typename T3>
bool dyn_check(const sort& s, const variant <T1, T2, T3>& v)
{
    switch (s.type) {
        case sort::type_t::INT: {
            return boost::get <T1> (&v);
        } case sort::type_t::BOOL: {
            return boost::get <T2> (&v);
        } case sort::type_t::BV: {
            return boost::get <T3> (&v);
        } default: {
            assert (false);
        }
    }
}

struct dyn_expr;
struct dyn_fexpr;

struct dyn_expr
{
    dyn_expr(const sort& s, const variant <aexpr_p, bexpr_p, bvexpr_p>& e)
    : s(s), e(e)
    {
        assert (dyn_check(s, e));
    }

    dyn_expr(const sort&& s, const variant <aexpr_p, bexpr_p, bvexpr_p>&& e)
    : dyn_expr(s, e) {}

    dyn_expr() : dyn_expr(sort::type_t::INT, aexpr_p(new cz(0))) {}

    dyn_expr subst(const subst_t& subst) const
    {
        switch (s.type) {
            case sort::type_t::INT: {
                return dyn_expr(s, boost::get <aexpr_p> (e) -> subst(subst));
            } case sort::type_t::BOOL: {
                return dyn_expr(s, boost::get <bexpr_p> (e) -> subst(subst));
            } case sort::type_t::BV: {
                return dyn_expr(s, boost::get <bvexpr_p> (e) -> subst(subst));
            } default: {
                assert (false);
            }
        }
    }

    dyn_expr bind(const subst_t& subst) const
    {
        switch (s.type) {
            case sort::type_t::INT: {
                const aexpr_p& ep = boost::get <aexpr_p> (e);
                return dyn_expr(s, aexpr_p(new zlet(subst, ep)));
            } case sort::type_t::BOOL: {
                const bexpr_p& ep = boost::get <bexpr_p> (e);
                return dyn_expr(s, bexpr_p(new blet(subst, ep)));
            } case sort::type_t::BV: {
                const bvexpr_p& ep = boost::get <bvexpr_p> (e);
                return dyn_expr(s, bvexpr_p(new bvlet(subst, ep)));
            } default: {
                assert (false);
            }
        }
    }

    dyn_expr make_macro(const string& name, const subst_t& args) const
    {
        switch (s.type) {
            case sort::type_t::INT: {
                const aexpr_p& ep = boost::get <aexpr_p> (e);
                return dyn_expr(s, aexpr_p(new zmacro(name, ep, args)));
            } case sort::type_t::BOOL: {
                const bexpr_p& ep = boost::get <bexpr_p> (e);
                return dyn_expr(s, bexpr_p(new bmacro(name, ep, args)));
            } case sort::type_t::BV: {
                const bvexpr_p& ep = boost::get <bvexpr_p> (e);
                return dyn_expr(s, bvexpr_p(new bvmacro(name, ep, args)));
            } default: {
                assert (false);
            }
        }
    }

    sort s;
    variant <aexpr_p, bexpr_p, bvexpr_p> e;
};

ostream& operator<<(ostream& out, const dyn_expr& de)
{
    switch (de.s.type) {
        case sort::type_t::INT: {
            return out << "(Int, " << *boost::get <aexpr_p> (de.e) << ")";
        } case sort::type_t::BOOL: {
            return out << "(Bool, " << *boost::get <bexpr_p> (de.e) << ")";
        } case sort::type_t::BV: {
            return out << "(BV" << de.s.len << ", " << *boost::get <bvexpr_p> (de.e) << ")";
        } default: {
            assert (false);
        }
    }
}

struct dyn_fexpr
{
    dyn_fexpr(const sort& s, const variant <afexpr_p, bfexpr_p, bvfexpr_p>& e)
    : s(s), e(e)
    {
        assert (dyn_check(s, e));
    }

    dyn_fexpr(const sort&& s, const variant <afexpr_p, bfexpr_p, bvfexpr_p>&& e)
    : dyn_fexpr(s, e) {}

    dyn_fexpr(const dyn_expr& de)
    {
        s = de.s;

        switch (de.s.type) {
            case sort::type_t::INT: {
                e = boost::get <aexpr_p> (de.e) -> f_lift();
                break;
            } case sort::type_t::BOOL: {
                e = boost::get <bexpr_p> (de.e) -> f_lift();
                break;
            } case sort::type_t::BV: {
                e = boost::get <bvexpr_p> (de.e) -> f_lift();
                break;
            } default: {
                assert (false);
            }
        }

        assert (dyn_check(s, e));
    }

    dyn_fexpr() : dyn_fexpr(sort::type_t::INT, afexpr_p(new fcz(0))) {}

    dyn_fexpr subst(const fsubst_t& subst) const
    {
        switch (s.type) {
            case sort::type_t::INT: {
                return dyn_fexpr(s, boost::get <afexpr_p> (e) -> subst(subst));
            } case sort::type_t::BOOL: {
                return dyn_fexpr(s, boost::get <bfexpr_p> (e) -> subst(subst));
            } case sort::type_t::BV: {
                return dyn_fexpr(s, boost::get <bvfexpr_p> (e) -> subst(subst));
            } default: {
                assert (false);
            }
        }
    }

    dyn_fexpr bind(const fsubst_t& subst) const
    {
        switch (s.type) {
            case sort::type_t::INT: {
                const afexpr_p& ep = boost::get <afexpr_p> (e);
                return dyn_fexpr(s, afexpr_p(new aflet(subst, ep)));
            } case sort::type_t::BOOL: {
                const bfexpr_p& ep = boost::get <bfexpr_p> (e);
                return dyn_fexpr(s, bfexpr_p(new bflet(subst, ep)));
            } case sort::type_t::BV: {
                const bvfexpr_p& ep = boost::get <bvfexpr_p> (e);
                return dyn_fexpr(s, bvfexpr_p(new bvflet(subst, ep)));
            } default: {
                assert (false);
            }
        }
    }

    sort s;
    variant <afexpr_p, bfexpr_p, bvfexpr_p> e;
};

ostream& operator<<(ostream& out, const dyn_fexpr& dfe)
{
    switch (dfe.s.type) {
        case sort::type_t::INT: {
            return out << "(Int, " << *boost::get <afexpr_p> (dfe.e) << ")";
        } case sort::type_t::BOOL: {
            return out << "(Bool, " << *boost::get <bfexpr_p> (dfe.e) << ")";
        } case sort::type_t::BV: {
            return out << "(BV" << dfe.s.len << ", " << *boost::get <bvfexpr_p> (dfe.e) << ")";
        } default: {
            assert (false);
        }
    }
}

struct dyn_grammar
{
    dyn_grammar(const sort& s, const grammar& g)
    : s(s), g(g)
    {
        assert (dyn_check(s, g.start));
    }

    dyn_grammar(const sort&& s, const grammar&& g)
    : dyn_grammar(s, g) {}

    dyn_grammar() {}

    sort s;
    grammar g;
};

} // namespace parser
} // namespace stoch

#endif // __PARSER_IFACE_DYN_HPP_

