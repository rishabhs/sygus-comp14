#ifndef __SEARCH_INFR_HPP_
#define __SEARCH_INFR_HPP_

#include "search.hpp"

namespace stoch {

optional <val_t> smt_check(bfexpr_p spec, const subst_t& subst,
    const set <id>& zfree, const set <id>& bfree,
    const set <tuple <id, size_t>>& bvfree)
{
    z3::context ctxt;
    z3::solver slvr(ctxt);

    slvr.add(!spec -> subst(subst) -> smt(ctxt));
    optional <val_t> ans = boost::none;

    if (slvr.check() != z3::check_result::unsat) {
        z3::model model = slvr.get_model();

        val_t cex;

        for (auto& zid : zfree) {
            z3::expr ex = zvar(zid).smt(ctxt);
            auto vx_s = Z3_get_numeral_string(ctxt, model.eval(ex, true));
            z_class vx = lexical_cast <z_class> (vx_s);
            std::get <0> (cex)[zid] = vx;
        }

        for (auto& bid : bfree) {
            z3::expr eb = bvar(bid).smt(ctxt);
            bool vb = (Z3_get_bool_value(ctxt, model.eval(eb, true)) == Z3_L_TRUE);
            std::get <1> (cex)[bid] = vb;
        }

        for (auto& bvidl : bvfree) {
            id bvid = std::get <0> (bvidl);
            size_t bvlen = std::get <1> (bvidl);
            z3::expr ebv = bvvar(bvid, bvlen).smt(ctxt);
            string vbv_s(Z3_ast_to_string(ctxt, model.eval(ebv, true)));
            std::get <2> (cex)[bvid] = bv(vbv_s);
        }

        ans = cex;
    }

    return ans;
}

size_t score(bfexpr_p spec, const subst_t& subst, const vector <val_t>& cex_s, size_t nslack = -1)
{
    size_t nscore = 0, nfail = 0;
    for (auto& cex : cex_s) {
        neval++;
        if (spec -> eval(subst, cex)) {
            nscore++;
        } else {
            nfail++;
            if (nfail > nslack) {
                nscore = 0;
                break;
            }
        }
    }
    return nscore;
}

// TODO. Revisit this code when adding big_bv support.
template <typename D>
vector <val_t> populate(const set <id>& zvar_s, const set <id>& bvar_s,
    const set <tuple<id, size_t>>& bvvar_s, size_t nsamples, D& rndm_dev)
{
    vector <val_t> ans;

    assert(typeid(bv) == typeid(small_bv));
    bv::unsigned_t bvdistr_max = bv(bv::digits, -1).x;
    uniform_int_distribution <int> zdistr(-10, 10), bdistr(0, 1);
    uniform_int_distribution <bv::unsigned_t> bvdistr(0, bvdistr_max);

    for (size_t i = 0; i < nsamples; i++) {
        val_t val;
        for (auto& zid : zvar_s) {
            std::get <0> (val)[zid] = zdistr(rndm_dev);
        }
        for (auto& bid : bvar_s) {
            std::get <1> (val)[bid] = (bdistr(rndm_dev) != 0);
        }
        for (auto& bvid : bvvar_s) {
            id bvid_id = std::get <0> (bvid);
            size_t bvid_len = std::get <1> (bvid);
            std::get <2> (val)[bvid_id] = bv(bvid_len, bvdistr(rndm_dev));
        }
        ans.push_back(val);
    }

    return ans;
}

void print_concrete(ostream& out, bfexpr_p spec, const subst_t& subst, const vector <val_t>& cex_s)
{
    for (auto& cex : cex_s) {
        out << __LOGSTR__;
        for (auto& zid : std::get <0> (cex)) {
            out << "x" << zid.first.v << ": " << zid.second << ". ";
        }
        for (auto& bid : std::get <1> (cex)) {
            out << "b" << bid.first.v << ": " << bid.second << ". ";
        }
        for (auto& bvid : std::get <2> (cex)) {
            out << "bv" << bvid.first.v << ": " << bvid.second << ". ";
        }

        /* if (condition) {
            verbose_mode = true;
        } */
        out << spec -> eval(subst, cex) << endl;
        verbose_mode = false;
    }
}

ostream& print_subst(ostream& out, const subst_t& subst)
{
    for (auto& afun : std::get <0> (subst)) {
        out << "fz" << afun.first.v << ": " << *afun.second << endl;
    }
    for (auto& bfun : std::get <1> (subst)) {
        out << "fb" << bfun.first.v << ": " << *bfun.second << endl;
    }
    for (auto& bvfun : std::get <2> (subst)) {
        out << "fbv" << bvfun.first.v << ": " << *bvfun.second << endl;
    }
    return out;
}

struct search_state
{
    template <typename D>
    search_state(bfexpr_p spec, size_t nseed, const set <id>& zvar_s,
        const set <id>& bvar_s, const set <tuple <id, size_t>>& bvvar_s,
        const aprodn& candidate, const vector <id>& afun_v,
        const vector <id>& bfun_v, const vector <id>& bvfun_v, D& rndm_dev)
    : nmutations(0), ngenerations(0), candidate(candidate), afun_v(afun_v),
    bfun_v(bfun_v), bvfun_v(bvfun_v)
    {
        cex_s = populate(zvar_s, bvar_s, bvvar_s, nseed, rndm_dev);
        auto subst = produce();

        *streams.log << __LOGSTR__ << "Proposal(" << candidate.size() << ")" << endl;
        print_subst(*streams.log, subst);
        *streams.log << __LOGSTR__ << "Initial candidate(" << candidate.size()
            << ") scores " << score(spec, subst, cex_s) << "." << endl;
    }

    subst_t produce() const
    {
        return uncombine(candidate, afun_v, bfun_v, bvfun_v);
    }

    vector <val_t> cex_s;
    size_t nmutations, ngenerations;
    size_t candidate_score, hi_score;

    // We are always synthesizing an aprodn. This is because after merging all
    // grammars, we have a dummy start terminal at the top of type integer.
    aprodn candidate;
    vector <id> afun_v, bfun_v, bvfun_v;
};

} // namespace stoch

#include "search/sizeful.hpp"
#include "search/sizefree.hpp"

#endif // __SEARCH_HPP_

