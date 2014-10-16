#include <fstream>
#include <iostream>
#include <sstream>
#include <boost/program_options/options_description.hpp>
#include <boost/program_options/parsers.hpp>
#include <boost/program_options/positional_options.hpp>
#include <boost/program_options/variables_map.hpp>
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
    using namespace boost::program_options;

    options_description desc("Allowed options");
    desc.add_options()("help", "Print this message")
                      ("logdir", value <string> (), "Specify directory to dump log files")
                      ("input", value <string> (), "Input file");

    positional_options_description p;
    p.add("input", 1);

    variables_map vm;
    store(command_line_parser(argc, argv).options(desc).positional(p).run(), vm);
    notify(vm);

    if (vm.count("help")) {
        cout << desc << endl;
        return 0;
    }

    if (vm.count("logdir")) {
        string logdir = vm["logdir"].as <string> ();
        if (!logdir.empty() && logdir.back() != '/') {
            logdir = logdir + '/';
        }
        streams.setup(logdir);
    } else {
        streams.setup("");
    }

    if (!vm.count("input")) {
        *streams.err << __LOGSTR__ << "Error. No input file specified." << endl;
        return 1;
    }

    string fname =  vm["input"].as <string> ();
    *streams.log << __LOGSTR__ << __STOCH__ << endl;
    streams.log_echo(fname);
    parser::parse(fname);

    return 0;
}

