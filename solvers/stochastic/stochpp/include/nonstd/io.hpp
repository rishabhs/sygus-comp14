#ifndef __NONSTD_IO_HPP_
#define __NONSTD_IO_HPP_

#include "nonstd.hpp"

namespace stoch {

struct streams_t
{
    streams_t()
    {
        std::stringstream clogname;
        clogname << "log-";

        random_device rd;
        uniform_int_distribution <size_t> distr(1000000000, 9999999999);
        clogname << distr(rd);

        log = new std::ofstream(clogname.str().c_str());
        err = new ostream_pair(ostream_tee(cerr, *log));

        *log << __LOGSTR__ << "Done initializing streams." << endl;
    }

    ~streams_t()
    {
        *log << __LOGSTR__ << "Closing streams." << endl;

        err -> flush();
        delete err;
        err = nullptr;

        log -> flush();
        delete log;
        log = nullptr;
    }

    void log_echo(const char *fname)
    {
        *log << __LOGSTR__ << "Echoing " << fname << "." << endl;
        std::ifstream fl(fname);
        string line;
        while (std::getline(fl, line)) {
            *log << line << endl;
        }
        *log << __LOGSTR__ << "Echoing input done." << endl;
    }

    void log_echo(const string& fname)
    {
        log_echo(fname.c_str());
    }

    ostream *log;
    ostream_pair *err;
};

} // namespace stoch

#endif // __NONSTD_IO_HPP_

