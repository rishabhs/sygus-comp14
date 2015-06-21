#ifndef __PARSER_IFACE_CHECK_SYNTH_CMD_HPP_
#define __PARSER_IFACE_CHECK_SYNTH_CMD_HPP_

#include "parser_iface.hpp"
#include "search.hpp"

namespace stoch {
namespace parser {

void visitor_t::VisitCheckSynthCmd(const CheckSynthCmd* cmd)
{
    *streams.log << __LOGSTR__ << location(cmd) << "random-seed: " << seed << endl;
    *streams.log << __LOGSTR__ << location(cmd) << "expr-size: " << expr_size << endl;
    *streams.log << __LOGSTR__ << location(cmd) << "samples: " << samples << endl;
    *streams.log << __LOGSTR__ << location(cmd) << "mutation-limit: " << mutation_limit << endl;
    *streams.log << __LOGSTR__ << location(cmd) << "beta: " << beta << endl;
    *streams.log << __LOGSTR__ << location(cmd) << "move-probability: " << move_probability << endl;

    *streams.log << __LOGSTR__ << location(cmd) << "constraint: " << *constraint << endl;

    mt19937 rndm_dev(seed);
    optional <subst_t> oresult;

    if (expr_size == 0) {
        *streams.log << __LOGSTR__ << location(cmd) << "Starting sizefree search." << endl;
        oresult = sizefree_search(constraint, afuns, bfuns, bvfuns, zfree, bfree,
            bvfree, move_probability, beta, samples, mutation_limit, rndm_dev);
    } else {
        *streams.log << __LOGSTR__ << location(cmd) << "Starting sizeful search." << endl;
        oresult = sizeful_search(constraint, afuns, bfuns, bvfuns, zfree, bfree,
            bvfree, expr_size, beta, samples, mutation_limit, rndm_dev);
    }

    if (oresult) {
        subst_t result = *oresult;
        for (auto& fun : synth) {
            stringstream sout;

            auto fun_id = std::get <0> (fun.second);
            auto& fun_name = std::get <1> (fun.first);
            auto fun_sort = std::get <1> (fun.second).s;
            auto& fun_args = std::get <0> (fun.first);

            sout << "(define-fun " << fun_name << " (";
            size_t nzargs(0), nbargs(0), nbvargs(0);
            for (size_t i = 0; i < fun_args.size(); i++) {
                switch (fun_args[i].type) {
                    case sort::type_t::INT: {
                        sout << "(x" << nzargs << " " << fun_args[i].get_string() << ") ";
                        nzargs++;
                        break;
                    } case sort::type_t::BOOL: {
                        sout << "(b" << nbargs << " " << fun_args[i].get_string() << ") ";
                        nbargs++;
                        break;
                    } case sort::type_t::BV: {
                        sout << "(v" << nbvargs << " " << fun_args[i].get_string() << ") ";
                        nbvargs++;
                        break;
                    }
                }
            }
            sout << ") " << fun_sort.get_string() << " ";

            switch (fun_sort.type) {
                case sort::type_t::INT: {
                    sout << *std::get <0> (result)[fun_id];
                    break;
                } case sort::type_t::BOOL: {
                    sout << *std::get <1> (result)[fun_id];
                    break;
                } case sort::type_t::BV: {
                    sout << *std::get <2> (result)[fun_id];
                    break;
                } default: {
                    assert (false);
                }
            }

            sout << ")";
            cout << sout.str() << endl;
            *streams.log << __LOGSTR__ << location(cmd) << sout.str() << endl;
        }
    } else {
        cout << "(fail)" << endl;
        *streams.log << __LOGSTR__ << location(cmd) << "(fail)" << endl;
    }
}

} // namespace parser
} // namespace stoch

#endif // __PARSER_IFACE_CHECK_SYNTH_CMD_HPP_

