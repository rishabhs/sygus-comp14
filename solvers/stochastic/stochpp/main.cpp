#include <fstream>
#include <iostream>
#include <sstream>
#include "base.hpp"
#include "expr.hpp"
#include "grammar.hpp"
#include "parser_iface.hpp"
#include "search.hpp"
using namespace std;
using namespace stoch;

namespace stoch {

streams_t streams;
size_t neval = 0;
bool verbose_mode = false;

}

int main(int argc, char *argv[])
{
    *streams.log << __LOGSTR__ << __STOCH__ << endl;

    if (argc >= 2) {
        string fname(argv[1]);
        streams.log_echo(fname);
        parser::parse(fname);
    } else {
        *streams.err << __LOGSTR__ << "Error. No input file specified." << endl;
        exit(1);
    }

    return 0;
}

