#ifndef __NONSTD_HPP_
#define __NONSTD_HPP_

#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <functional>
#include <iostream>
#include <istream>
#include <iterator>
#include <limits>
#include <map>
#include <memory>
#include <ostream>
#include <set>
#include <stdexcept>
#include <sstream>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

#include <boost/current_function.hpp>
#include <boost/iostreams/tee.hpp>
#include <boost/iostreams/stream.hpp>
#include <boost/lexical_cast.hpp>
#include <boost/optional.hpp>
#include <boost/regex.hpp>
#include <boost/variant.hpp>

#include <gmpxx.h>
#include <z3++.h>

namespace stoch {

struct streams_t;
extern streams_t streams;
extern size_t neval; // Number of evaluations performed
extern bool verbose_mode;

using std::accumulate;
using std::cerr;
using std::clog;
using std::cout;
using std::dynamic_pointer_cast;
using std::endl;
using std::function;
using std::geometric_distribution;
using boost::iostreams::tee_device;
using boost::iostreams::stream;
using std::make_pair;
using std::make_tuple;
using std::map;
using std::mt19937;
using std::ostream;
using std::pair;
using std::random_device;
using std::set;
using std::shared_ptr;
using std::string;
using std::tie;
using std::transform;
using std::tuple;
using std::geometric_distribution;
using std::uniform_int_distribution;
using std::uniform_real_distribution;
using std::vector;

using boost::lexical_cast;
using boost::optional;
using boost::variant;

typedef tee_device <ostream, ostream> ostream_tee;
typedef stream <ostream_tee> ostream_pair;

} // namespace stoch

#define __LOGSTR__ (string(__FILE__ ": ") + \
    lexical_cast <string> (__LINE__) + ". ")
#define __F_LOGSTR__ (string(__FILE__ ": ") + \
    lexical_cast <string> (__LINE__) + ": " + \
    lexical_cast <string> (BOOST_CURRENT_FUNCTION) + ". ")
#define __STOCH__ string("stoch. " __DATE__ ". " __TIME__ ". ")

#include "nonstd/bv.hpp"

namespace stoch {

#ifdef __BIG_Z_
    typedef mpz_class z_class;
#else
    typedef long z_class;
#endif

namespace nonstd {

size_t luby(size_t n)
{
    if ((n & (n + 1)) == 0) {
        return (n + 1) / 2;
    } else {
        double dn = static_cast <double> (n);
        size_t shift = static_cast <size_t> (floor(log2(dn)));
        size_t diff = size_t(1) << shift;
        assert(n - diff + 1 < n);
        return luby(n - diff + 1);
    }
}

} // namespace nonstd
} // namespace stoch

#include "nonstd/algo.hpp"
#include "nonstd/get.hpp"
#include "nonstd/io.hpp"
#include "nonstd/nonfunctional.hpp"

#endif // __NONSTD_HPP_

