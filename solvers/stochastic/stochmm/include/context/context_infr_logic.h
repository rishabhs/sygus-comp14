#ifndef __CONTEXT_INFR_LOGIC_H_
#define __CONTEXT_INFR_LOGIC_H_

#include <cstdlib>
#include <iostream>
#include <map>
#include <memory>
#include <utility>
#include <vector>

#include "context_infr.h"

namespace stoch
{
namespace context
{

template <typename U>
void set_logic_cmd(std::map <std::string, std::pair <std::shared_ptr <const expr <U>>, sort>>& symbol_table,
                   const std::string& symbol, std::shared_ptr <const expr <U>> e,
                   sort s, const sl2p::SetLogicCmd* cmd)
{
    typedef expr <U> eU;
    typedef std::shared_ptr <const eU> eU_p;

    if (symbol_table.find(symbol) != symbol_table.end())
    {
        std::cerr << __LOGSTR__ << parse_loc(cmd)
                  << "Error. Attempting to redefine symbol " << symbol
                  << ". Exiting." << std::endl;
        exit(EXIT_FAILURE);
    }

    symbol_table[symbol] = std::pair <eU_p, sort> (e, s);
}

void set_logic_lia(context& ctxt, const sl2p::SetLogicCmd *cmd)
{
    std::vector <sort> arg_types_z { sort(sort_class::Integer) };
    std::vector <sort> arg_types_b { sort(sort_class::Boolean) };
    std::vector <sort> arg_types_zz { sort(sort_class::Integer),
                                      sort(sort_class::Integer)
                                    };
    std::vector <sort> arg_types_bb { sort(sort_class::Boolean),
                                      sort(sort_class::Boolean)
                                    };
    std::vector <sort> arg_types_bzz { sort(sort_class::Boolean),
                                       sort(sort_class::Integer),
                                       sort(sort_class::Integer)
                                     };
    std::vector <sort> arg_types_bbb { sort(sort_class::Boolean),
                                       sort(sort_class::Boolean),
                                       sort(sort_class::Boolean)
                                     };

    aexpr_p x0(new zvar(0)), x1(new zvar(1));
    bexpr_p b0(new bvar(0)), b1(new bvar(1)), b2(new bvar(2));

    set_logic_cmd(ctxt.symbol_table_zfun[to_string(arg_types_z)], "-", -x0, sort_class::Integer, cmd);
    set_logic_cmd(ctxt.symbol_table_bfun[to_string(arg_types_b)], "not", !b0, sort_class::Boolean, cmd);

    set_logic_cmd(ctxt.symbol_table_zfun[to_string(arg_types_zz)], "+", x0 + x1, sort_class::Integer, cmd);
    set_logic_cmd(ctxt.symbol_table_zfun[to_string(arg_types_zz)], "-", x0 - x1, sort_class::Integer, cmd);
    set_logic_cmd(ctxt.symbol_table_zfun[to_string(arg_types_zz)], "*", x0 * x1, sort_class::Integer, cmd);

    set_logic_cmd(ctxt.symbol_table_bfun[to_string(arg_types_zz)], "=", x0 == x1, sort_class::Boolean, cmd);
    // TODO: SMT-Lib2 operator for [!=]?
    set_logic_cmd(ctxt.symbol_table_bfun[to_string(arg_types_zz)], ">", x0 > x1, sort_class::Boolean, cmd);
    set_logic_cmd(ctxt.symbol_table_bfun[to_string(arg_types_zz)], "<", x0 < x1, sort_class::Boolean, cmd);
    set_logic_cmd(ctxt.symbol_table_bfun[to_string(arg_types_zz)], ">=", x0 >= x1, sort_class::Boolean, cmd);
    set_logic_cmd(ctxt.symbol_table_bfun[to_string(arg_types_zz)], "<=", x0 <= x1, sort_class::Boolean, cmd);

    set_logic_cmd(ctxt.symbol_table_bfun[to_string(arg_types_bb)], "and", b0 && b1, sort_class::Boolean, cmd);
    set_logic_cmd(ctxt.symbol_table_bfun[to_string(arg_types_bb)], "or", b0 || b1, sort_class::Boolean, cmd);
    set_logic_cmd(ctxt.symbol_table_bfun[to_string(arg_types_bb)], "=", b0 == b1, sort_class::Boolean, cmd);

    set_logic_cmd(ctxt.symbol_table_zfun[to_string(arg_types_bzz)], "ite",
                  aexpr_p(new aite(b0, x0, x1)), sort_class::Integer, cmd);
    set_logic_cmd(ctxt.symbol_table_bfun[to_string(arg_types_bbb)], "ite",
                  bexpr_p(new bite(b0, b1, b2)), sort_class::Boolean, cmd);
    set_logic_cmd(ctxt.symbol_table_bfun[to_string(arg_types_bb)], "=>",
                  (!b0) || b1, sort_class::Boolean, cmd);
}

void set_logic_bv(context& ctxt, const sl2p::SetLogicCmd *cmd)
{
    sort sb(sort_class::Boolean);
    std::vector <sort> arg_types_b { sb };
    std::vector <sort> arg_types_bb { sb, sb };
    std::vector <sort> arg_types_bbb { sb, sb, sb };

    bexpr_p b0(new bvar(0)), b1(new bvar(1)), b2(new bvar(2));

    for (size_t len = 1; len <= 64; len++)
    {
        sort sv(sort_class::BV, len);
        std::vector <sort> arg_types_bv { sv };
        std::vector <sort> arg_types_bvbv { sv, sv };
        std::vector <sort> arg_types_bbvbv { sb, sv, sv };

        bvexpr_p v0(new bvvar(0, len)), v1(new bvvar(1, len));

        set_logic_cmd(ctxt.symbol_table_bvfun[to_string(arg_types_bvbv)], "bvand",
                      v0 & v1, sv, cmd);
        set_logic_cmd(ctxt.symbol_table_bvfun[to_string(arg_types_bvbv)], "bvor",
                      v0 | v1, sv, cmd);
        set_logic_cmd(ctxt.symbol_table_bvfun[to_string(arg_types_bv)], "bvnot",
                      ~v0, sv, cmd);
        set_logic_cmd(ctxt.symbol_table_bvfun[to_string(arg_types_bvbv)], "bvxor",
                      v0 ^ v1, sv, cmd);
        set_logic_cmd(ctxt.symbol_table_bvfun[to_string(arg_types_bv)], "bvneg",
                      -v0, sv, cmd);

        set_logic_cmd(ctxt.symbol_table_bvfun[to_string(arg_types_bvbv)], "bvshl",
                      bvexpr_p(new stoch::bv_shl(v0, v1)), sv, cmd);
        set_logic_cmd(ctxt.symbol_table_bvfun[to_string(arg_types_bvbv)], "bvashr",
                      bvexpr_p(new stoch::bv_ashr(v0, v1)), sv, cmd);
        set_logic_cmd(ctxt.symbol_table_bvfun[to_string(arg_types_bvbv)], "bvlshr",
                      bvexpr_p(new stoch::bv_lshr(v0, v1)), sv, cmd);

        set_logic_cmd(ctxt.symbol_table_bvfun[to_string(arg_types_bvbv)], "bvadd",
                      v0 + v1, sv, cmd);
        set_logic_cmd(ctxt.symbol_table_bvfun[to_string(arg_types_bvbv)], "bvsub",
                      v0 - v1, sv, cmd);
        set_logic_cmd(ctxt.symbol_table_bvfun[to_string(arg_types_bvbv)], "bvmul",
                      v0 * v1, sv, cmd);
        set_logic_cmd(ctxt.symbol_table_bvfun[to_string(arg_types_bvbv)], "bvudiv",
                      bvexpr_p(new bv_udiv(v0, v1)), sv, cmd);
        set_logic_cmd(ctxt.symbol_table_bvfun[to_string(arg_types_bvbv)], "bvurem",
                      bvexpr_p(new bv_urem(v0, v1)), sv, cmd);
        set_logic_cmd(ctxt.symbol_table_bvfun[to_string(arg_types_bvbv)], "bvsdiv",
                      bvexpr_p(new bv_sdiv(v0, v1)), sv, cmd);
        set_logic_cmd(ctxt.symbol_table_bvfun[to_string(arg_types_bvbv)], "bvsrem",
                      bvexpr_p(new bv_srem(v0, v1)), sv, cmd);

        set_logic_cmd(ctxt.symbol_table_bfun[to_string(arg_types_bvbv)], "bvult",
                      bexpr_p(new bv_ult(v0, v1)), sb, cmd);
        set_logic_cmd(ctxt.symbol_table_bfun[to_string(arg_types_bvbv)], "bvslt",
                      bexpr_p(new bv_slt(v0, v1)), sb, cmd);
        set_logic_cmd(ctxt.symbol_table_bfun[to_string(arg_types_bvbv)], "bvule",
                      bexpr_p(new bv_ule(v0, v1)), sb, cmd);
        set_logic_cmd(ctxt.symbol_table_bfun[to_string(arg_types_bvbv)], "bvsle",
                      bexpr_p(new bv_sle(v0, v1)), sb, cmd);
        set_logic_cmd(ctxt.symbol_table_bfun[to_string(arg_types_bvbv)], "=",
                      bexpr_p(new bv_eq(v0, v1)), sb, cmd);
        set_logic_cmd(ctxt.symbol_table_bfun[to_string(arg_types_bvbv)], "bvuge",
                      bexpr_p(new bv_uge(v0, v1)), sb, cmd);
        set_logic_cmd(ctxt.symbol_table_bfun[to_string(arg_types_bvbv)], "bvsge",
                      bexpr_p(new bv_sge(v0, v1)), sb, cmd);
        set_logic_cmd(ctxt.symbol_table_bfun[to_string(arg_types_bvbv)], "bvugt",
                      bexpr_p(new bv_ugt(v0, v1)), sb, cmd);
        set_logic_cmd(ctxt.symbol_table_bfun[to_string(arg_types_bvbv)], "bvsgt",
                      bexpr_p(new bv_sgt(v0, v1)), sb, cmd);

        set_logic_cmd(ctxt.symbol_table_bfun[to_string(arg_types_bv)], "bvredor",
                      bexpr_p(new logical_not(v0 == bvexpr_p(new cbv(bv(len, 0))))), sb, cmd);
        set_logic_cmd(ctxt.symbol_table_bvfun[to_string(arg_types_bbvbv)], "ite",
                      bvexpr_p(new bvite(b0, v0, v1)), sort_class::Integer, cmd);
    }

    set_logic_cmd(ctxt.symbol_table_bfun[to_string(arg_types_b)], "not", !b0, sb, cmd);
    set_logic_cmd(ctxt.symbol_table_bfun[to_string(arg_types_bb)], "and", b0 && b1, sb, cmd);
    set_logic_cmd(ctxt.symbol_table_bfun[to_string(arg_types_bb)], "or", b0 || b1, sb, cmd);
    set_logic_cmd(ctxt.symbol_table_bfun[to_string(arg_types_bb)], "=", b0 == b1, sb, cmd);
    set_logic_cmd(ctxt.symbol_table_bfun[to_string(arg_types_bb)], "xor", !(b0 == b1), sb, cmd);
    set_logic_cmd(ctxt.symbol_table_bfun[to_string(arg_types_bbb)], "ite",
                  bexpr_p(new bite(b0, b1, b2)), sb, cmd);
    set_logic_cmd(ctxt.symbol_table_bfun[to_string(arg_types_bb)], "=>", (!b0) || b1, sb, cmd);
}

} // namespace context
} // namespace stoch

#endif // __CONTEXT_INFR_LOGIC_H_

