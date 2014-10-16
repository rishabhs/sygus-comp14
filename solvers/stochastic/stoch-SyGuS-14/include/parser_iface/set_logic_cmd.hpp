#ifndef __PARSER_IFACE_SET_LOGIC_CMD_HPP_
#define __PARSER_IFACE_SET_LOGIC_CMD_HPP_

#include "parser_iface.hpp"

namespace stoch {
namespace parser {

map <tuple <vector <sort>, string>, dyn_expr> define_core();
map <tuple <vector <sort>, string>, dyn_expr> define_lia();
map <tuple <vector <sort>, string>, dyn_expr> define_bv();
map <tuple <vector <sort>, string>, dyn_expr> define_bv(size_t len);

void visitor_t::VisitSetLogicCmd(const SetLogicCmd* Cmd)
{
    string logic = Cmd -> GetLogicName();
    if (logic == "LIA" || logic == "BV") {
        auto lia_macros = define_lia();
        auto bv_macros = define_bv();
        macros.insert(lia_macros.begin(), lia_macros.end());
        macros.insert(bv_macros.begin(), bv_macros.end());
    } else if (logic == "Reals" || logic == "Arrays") {
        *streams.err << __LOGSTR__ << location(Cmd) << "Logic " << logic
            << " unimplemented" << endl;
        assert(false);
    } else {
        *streams.err << __LOGSTR__ << location(Cmd) << "Unrecognized logic "
            << logic << endl;
        exit(1);
    }
}

map <tuple <vector <sort>, string>, dyn_expr> define_core()
{
    map <tuple <vector <sort>, string>, dyn_expr> macros;

    sort sort_bool(sort::type_t::BOOL);
    vector <sort> b { sort_bool };
    vector <sort> bb { sort_bool, sort_bool };
    vector <sort> bbb { sort_bool, sort_bool, sort_bool };
    bexpr_p bv0(new bvar(0)), bv1(new bvar(1)), bv2(new bvar(2));

    macros[make_tuple(bb, string("and"))] = dyn_expr(sort_bool, bv0 && bv1);
    macros[make_tuple(bb, string("or"))] = dyn_expr(sort_bool, bv0 || bv1);
    macros[make_tuple(bb, string("=>"))] = dyn_expr(sort_bool, !bv0 || bv1);
    macros[make_tuple(b, string("not"))] = dyn_expr(sort_bool, !bv0);

    macros[make_tuple(bb, string("xor"))] = dyn_expr(sort_bool, !(bv0 == bv1));
    macros[make_tuple(bb, string("xnor"))] = dyn_expr(sort_bool, bv0 == bv1);
    macros[make_tuple(bb, string("nand"))] = dyn_expr(sort_bool, !(bv0 && bv1));
    macros[make_tuple(bb, string("nor"))] = dyn_expr(sort_bool, !(bv0 || bv1));
    macros[make_tuple(bb, string("iff"))] = dyn_expr(sort_bool, bv0 == bv1);
    macros[make_tuple(bb, string("="))] = dyn_expr(sort_bool, bv0 == bv1);

    macros[make_tuple(bbb, string("ite"))] = dyn_expr(sort_bool, bexpr_p(new bite(bv0, bv1, bv2)));

    return macros;
}

map <tuple <vector <sort>, string>, dyn_expr> define_lia()
{
    auto macros = define_core();

    sort sort_int(sort::type_t::INT), sort_bool(sort::type_t::BOOL);
    vector <sort> a { sort_int };
    vector <sort> aa { sort_int, sort_int };
    vector <sort> baa { sort_bool, sort_int, sort_int };

    aexpr_p ac0(new cz(0));
    aexpr_p av0(new zvar(0)), av1(new zvar(1)), av2(new zvar(2));
    bexpr_p bv0(new bvar(0));

    macros[make_tuple(aa, string("+"))] = dyn_expr(sort_int, av0 + av1);
    macros[make_tuple(aa, string("-"))] = dyn_expr(sort_int, av0 - av1);
    macros[make_tuple(aa, string("*"))] = dyn_expr(sort_int, av0 * av1);
    macros[make_tuple(aa, string("/"))] = dyn_expr(sort_int, aexpr_p(new aite(av1 != ac0, av0 / av1, ac0)));
    macros[make_tuple(a, string("abs"))] = dyn_expr(sort_int, aexpr_p(new aite(av0 >= ac0, av0, -av0)));
    macros[make_tuple(a, string("-"))] = dyn_expr(sort_int, aexpr_p(-av0));

    macros[make_tuple(aa, string("<"))] = dyn_expr(sort_bool, av0 < av1);
    macros[make_tuple(aa, string("<="))] = dyn_expr(sort_bool, av0 <= av1);
    macros[make_tuple(aa, string(">"))] = dyn_expr(sort_bool, av0 > av1);
    macros[make_tuple(aa, string(">="))] = dyn_expr(sort_bool, av0 >= av1);
    macros[make_tuple(aa, string("="))] = dyn_expr(sort_bool, av0 == av1);

    macros[make_tuple(baa, string("ite"))] = dyn_expr(sort_int, aexpr_p(new aite(bv0, av1, av2)));

    return macros;
}

map <tuple <vector <sort>, string>, dyn_expr> define_bv()
{
    auto macros = define_core();

    assert(typeid(bv) == typeid(small_bv));
    for (size_t len = 1; len < bv::digits; len++) {
        auto lm = define_bv(len);
        macros.insert(lm.begin(), lm.end());
    }

    return macros;
}

map <tuple <vector <sort>, string>, dyn_expr> define_bv(size_t len)
{
    auto macros = define_core();

    sort sort_bool(sort::type_t::BOOL), sort_bv(sort::type_t::BV, len);
    vector <sort> v { sort_bv };
    vector <sort> vv { sort_bv, sort_bv };
    vector <sort> bvv { sort_bool, sort_bv, sort_bv };

    bexpr_p bv0(new bvar(0));
    bvexpr_p bvv0(new bvvar(0, len)), bvv1(new bvvar(1, len));

    macros[make_tuple(bvv, string("ite"))] = dyn_expr(sort_bv, bvexpr_p(new bvite(bv0, bvv0, bvv1)));

    macros[make_tuple(vv, string("bvult"))] = dyn_expr(sort_bool, bexpr_p(new bv_ult(bvv0, bvv1)));
    macros[make_tuple(vv, string("bvslt"))] = dyn_expr(sort_bool, bexpr_p(new bv_slt(bvv0, bvv1)));
    macros[make_tuple(vv, string("bvule"))] = dyn_expr(sort_bool, bexpr_p(new bv_ule(bvv0, bvv1)));
    macros[make_tuple(vv, string("bvsle"))] = dyn_expr(sort_bool, bexpr_p(new bv_sle(bvv0, bvv1)));
    macros[make_tuple(vv, string("bveq"))] = dyn_expr(sort_bool, bexpr_p(new bv_eq(bvv0, bvv1)));
    macros[make_tuple(vv, string("="))] = dyn_expr(sort_bool, bexpr_p(new bv_eq(bvv0, bvv1)));
    macros[make_tuple(vv, string("bvuge"))] = dyn_expr(sort_bool, bexpr_p(new bv_uge(bvv0, bvv1)));
    macros[make_tuple(vv, string("bvsge"))] = dyn_expr(sort_bool, bexpr_p(new bv_sge(bvv0, bvv1)));
    macros[make_tuple(vv, string("bvugt"))] = dyn_expr(sort_bool, bexpr_p(new bv_ugt(bvv0, bvv1)));
    macros[make_tuple(vv, string("bvsgt"))] = dyn_expr(sort_bool, bexpr_p(new bv_sgt(bvv0, bvv1)));

    macros[make_tuple(vv, string("bvand"))] = dyn_expr(sort_bv, bvv0 & bvv1);
    macros[make_tuple(vv, string("bvor"))] = dyn_expr(sort_bv, bvv0 | bvv1);
    macros[make_tuple(vv, string("bvxor"))] = dyn_expr(sort_bv, bvv0 ^ bvv1);
    macros[make_tuple(vv, string("bvxnor"))] = dyn_expr(sort_bv, ~(bvv0 ^ bvv1));
    macros[make_tuple(vv, string("bvnand"))] = dyn_expr(sort_bv, ~(bvv0 & bvv1));

    macros[make_tuple(vv, string("bvadd"))] = dyn_expr(sort_bv, bvv0 + bvv1);
    macros[make_tuple(vv, string("bvsub"))] = dyn_expr(sort_bv, bvv0 - bvv1);
    macros[make_tuple(vv, string("bvmul"))] = dyn_expr(sort_bv, bvv0 * bvv1);
    macros[make_tuple(vv, string("bvudiv"))] = dyn_expr(sort_bv, bvexpr_p(new bv_udiv(bvv0, bvv1)));
    macros[make_tuple(vv, string("bvurem"))] = dyn_expr(sort_bv, bvexpr_p(new bv_urem(bvv0, bvv1)));
    macros[make_tuple(vv, string("bvsdiv"))] = dyn_expr(sort_bv, bvexpr_p(new bv_sdiv(bvv0, bvv1)));
    macros[make_tuple(vv, string("bvsrem"))] = dyn_expr(sort_bv, bvexpr_p(new bv_srem(bvv0, bvv1)));

    macros[make_tuple(vv, string("bvshl"))] = dyn_expr(sort_bv, bvexpr_p(new bv_shl(bvv0, bvv1)));
    macros[make_tuple(vv, string("bvlshr"))] = dyn_expr(sort_bv, bvexpr_p(new bv_lshr(bvv0, bvv1)));
    macros[make_tuple(vv, string("bvashr"))] = dyn_expr(sort_bv, bvexpr_p(new bv_ashr(bvv0, bvv1)));

    macros[make_tuple(v, string("bvneg"))] = dyn_expr(sort_bv, -bvv0);
    macros[make_tuple(v, string("bvnot"))] = dyn_expr(sort_bv, ~bvv0);

    return macros;
}

} // namespace parser
} // namespace stoch

#endif // __PARSER_IFACE_SET_LOGIC_CMD_HPP_

