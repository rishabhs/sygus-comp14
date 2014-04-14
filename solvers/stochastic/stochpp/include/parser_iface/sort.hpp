#ifndef __PARSER_IFACE_SORT_HPP_
#define __PARSER_IFACE_SORT_HPP_

#include "parser_iface.hpp"

namespace stoch {
namespace parser {

struct sort
{
    enum class type_t { INT, BOOL, BV };

    sort() : type(type_t::INT), len(1) { }

    sort(type_t type) : type(type), len(1)
    {
        assert(type != type_t::BV);
    }

    sort(type_t type, size_t len) : type(type), len(len)
    {
        assert(type == type_t::BV && 0 < len && len <= bv::digits);
    }

    bool operator==(const sort& s) const
    {
        return type == s.type && (type != type_t::BV || len == s.len);
    }

    bool operator!=(const sort& s) const
    {
        return !(*this == s);
    }

    ostream& operator<<(ostream& out) const
    {
        switch (type) {
            case type_t::INT: {
                return out << "Int";
            } case type_t::BOOL: {
                return out << "Bool";
            } case type_t::BV: {
                return out << "BV" << len;
            } default: {
                assert (false);
            }
        }
    }

    string get_string() const
    {
        switch (type) {
            case type_t::INT: {
                return "Int";
            } case type_t::BOOL: {
                return "Bool";
            } case type_t::BV: {
                return string("(BitVec ") + lexical_cast <string> (len)
                    + lexical_cast <string> (")");
            } default: {
                assert (false);
            }
        }
    }

    type_t type;
    size_t len;
};

bool operator<(const sort& s1, const sort& s2)
{
    return s1.type < s2.type || (s1.type == s2.type && s1.len < s2.len);
}

} // namespace parser
} // namespace stoch

#endif // __PARSER_IFACE_SORT_HPP_

