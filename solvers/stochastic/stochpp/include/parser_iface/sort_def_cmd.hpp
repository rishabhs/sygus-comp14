#ifndef __PARSER_IFACE_SORT_DEF_CMD_HPP_
#define __PARSER_IFACE_SORT_DEF_CMD_HPP_

#include "parser_iface.hpp"

namespace stoch {
namespace parser {

sort visitor_t::get_sort(const SortExpr *expr) const
{
    if (dynamic_cast <const IntSortExpr *> (expr)) {
        return sort(sort::type_t::INT);
    } else if (dynamic_cast <const BoolSortExpr *> (expr)) {
        return sort(sort::type_t::BOOL);
    } else if (dynamic_cast <const RealSortExpr *> (expr)) {
        *streams.err << __LOGSTR__ << location(expr) << "Real sorts unimplemented." << endl;
        exit(1);
    } else if (auto exprp = dynamic_cast <const BVSortExpr *> (expr)) {
        return sort(sort::type_t::BV, exprp -> GetSize());
    } else if (dynamic_cast <const EnumSortExpr *> (expr)) {
        *streams.err << __LOGSTR__ << location(expr) << "Enumerated sorts unimplemented." << endl;
        exit(1);
    } else if (dynamic_cast <const ArraySortExpr *> (expr)) {
        *streams.err << __LOGSTR__ << location(expr) << "Array sorts unimplemented." << endl;
        exit(1);
    } else if (auto exprp = dynamic_cast <const NamedSortExpr *> (expr)) {
        string sort_name = exprp -> GetName();
        if (sort_table.find(sort_name) == sort_table.end()) {
            *streams.err << __LOGSTR__ << location(expr) << "Sort " << sort_name
                << " undefined." << endl;
            exit(1);
        }
        return sort_table.at(sort_name);
    } else {
        assert (false);
    }
}

void visitor_t::VisitSortDefCmd(const SortDefCmd* Cmd)
{
    string sort_name = Cmd -> GetName();
    if (sort_table.find(sort_name) != sort_table.end()) {
        *streams.err << __LOGSTR__ << location(Cmd)
            << "Attempting to redefine sort " << sort_name << endl;
        exit(1);
    } else {
        sort_table[sort_name] = get_sort(Cmd -> GetSortExpr());
    }
}

} // namespace parser
} // namespace stoch

#endif // __PARSER_IFACE_SORT_DEF_CMD_HPP_

