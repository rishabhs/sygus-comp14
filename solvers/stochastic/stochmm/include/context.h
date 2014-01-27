#ifndef __CONTEXT_H_
#define __CONTEXT_H_

#include <cassert>
#include <map>
#include <string>
#include <utility>
#include <vector>

#include <boost/optional.hpp>
#include <boost/variant.hpp>

#include "parser/iface.h"
#include "expr.h"
#include "fexpr.h"
#include "grammar.h"
#include "expr_search.h"

namespace stoch
{
namespace context
{

namespace sl2p = SynthLib2Parser;

enum class sort_class
{
    Integer, Boolean, BV
};

struct sort
{
    sort() : sc(sort_class::Integer), len(0) {}

    sort(sort_class sc) : sc(sc), len(0)
    {
        assert(sc != sort_class::BV);
    }

    sort(sort_class sc, size_t len) : sc(sc), len(len) {}

    sort_class sc;
    size_t len;
};

bool operator==(const sort& s1, const sort& s2)
{
    return s1.sc == s2.sc &&
           (s1.sc != sort_class::BV || s1.len == s2.len);
}

bool operator!=(const sort& s1, const sort& s2)
{
    return !(s1 == s2);
}

struct context
{
    context() : nz(0), nb(0) {};

    std::map <std::string, sort> symbol_table_sort;

    // Argument type -> Symbol name -> expr
    // Given a list of argument types, no symbol may appear in more than one
    // of the following tables.
    std::map <std::string, std::map <std::string, std::pair <aexpr_p, sort>>> symbol_table_zfun;
    std::map <std::string, std::map <std::string, std::pair <bexpr_p, sort>>> symbol_table_bfun;
    std::map <std::string, std::map <std::string, std::pair <bvexpr_p, sort>>> symbol_table_bvfun;

    size_t nz, nb;
    std::vector <size_t> nbv;
    std::map <std::string, std::pair <id, sort>> symbol_table_var;

    boost::optional <bfexpr_p> spec;
    boost::optional <std::tuple <std::string, std::string, sort>> synth_fun;
    grammar g;
    boost::variant <agsymb_t, bgsymb_t, bvgsymb_t> start_symbol;

    boost::optional <size_t> expr_size, mutation_limit, samples, random_seed;
    boost::optional <double> beta, move_probability;

    static const size_t default_mutation_limit, default_samples;
    static const double default_beta, default_move_probability;
};

const size_t context::default_mutation_limit = -1;
const size_t context::default_samples = 100;
const double context::default_beta = 0.5;
const double context::default_move_probability = 0.01;

} // namespace context
} // namespace stoch

#include "context/context_infr.h"

#endif // __CONTEXT_H_

