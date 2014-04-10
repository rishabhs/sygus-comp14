// ESolverSynthLib.cpp --- 
// 
// Filename: ESolverSynthLib.cpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:55:07 2014 (-0500)
// 
// 
// Copyright (c) 2013, Abhishek Udupa, University of Pennsylvania
// All rights reserved.
// 
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in the
//    documentation and/or other materials provided with the distribution.
// 3. All advertising materials mentioning features or use of this software
//    must display the following acknowledgement:
//    This product includes software developed by The University of Pennsylvania
// 4. Neither the name of the University of Pennsylvania nor the
//    names of its contributors may be used to endorse or promote products
//    derived from this software without specific prior written permission.
// 
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER ''AS IS'' AND ANY
// EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
// WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
// DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
// DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
// (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
// LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
// ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
// SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
// 
// 

// Code:


#include "../main-solvers/SynthLib2Solver.hpp"
#include <boost/program_options.hpp>
#include "../utils/ResourceLimitManager.hpp"
#include "../common/ESolverOpts.hpp"
#include <random>
#include <z3.h>

using namespace ESolver;
namespace po = boost::program_options;

#define DEFAULT_LOG_LEVEL (0)
#define DEFAULT_BUDGET (10)
#define DEFAULT_RANDOM_SEED (0)

namespace ESolverSynthLib {

    static inline void ParseOptions(int argc, char* argv[], ESolverOpts& Opts, string& InputFileName)
    {
        po::options_description desc("Usage and Allowed Options");
        po::positional_options_description pdesc;
        pdesc.add("input-file", -1);

        desc.add_options()
            ("help", "produce this help message")
            ("input-file,i", po::value<string>(&InputFileName)->default_value(""),
             "SynthLib2 formatted input file")
            ("verbose,v", po::value<int32>(&Opts.StatsLevel)->default_value(DEFAULT_LOG_LEVEL),
             "Verbosity")
            ("memory-limit,m", po::value<uint64>(&Opts.MemoryLimit)->default_value(MEM_LIMIT_INFINITE),
             "Memory limit (bytes)")
            ("cpu-limit,t", po::value<uint64>(&Opts.CPULimit)->default_value(CPU_LIMIT_INFINITE),
             "CPU Time limit (seconds)")
            ("budget,s", po::value<uint32>(&Opts.CostBudget)->default_value(DEFAULT_BUDGET),
             "Maximum cost of expansions to explore")
            ("random,r", po::value<uint32>(&Opts.RandomSeed)->implicit_value(DEFAULT_RANDOM_SEED),
             "Start the solver with a random seed to the SMT solver, a random seed will be used if none specified")
            ("nodist,n", "Do not use distinguishability to prune search space");
        po::variables_map vm;
        po::store(po::command_line_parser(argc, argv).options(desc).positional(pdesc).run(), vm);
        po::notify(vm);
        if(vm.count("help") > 0 || argc < 2) {
            cout << desc << endl;
            exit(0);
        }
        if((vm.count("random") > 0) && (Opts.RandomSeed == DEFAULT_RANDOM_SEED)) {
            // generate a random seed
            struct timeval TV;
            gettimeofday(&TV, NULL);
            mt19937 randomgen((uint32)TV.tv_usec);
            auto NumToThrow = TV.tv_sec % 1024;
            // throw away some bits
            uint32 Seed = 0;
            for(uint32 i = 0; i < NumToThrow; ++i) {
                Seed = (Seed ^ randomgen());
            }
            Opts.RandomSeed = (Seed % (1 << 30));
        }
        if (vm.count("nodist") > 0) {
            Opts.NoDist = true;
        } else {
            Opts.NoDist = false;
        }
    }

} /* End ESolverSynthLib namespace */

using namespace ESolverSynthLib;

int main(int argc, char* argv[])
{
    ESolverOpts Opts;
    string InputFileName;
    ParseOptions(argc, argv, Opts, InputFileName);
    try {
        ESolver::SynthLib2ESolver::Solve(InputFileName, Opts);
        Z3_reset_memory();
        exit(0);
    } catch(const ESException& Ex) {
        cout << "Caught Exception:" << endl;
        cout << Ex << endl;
        Z3_reset_memory();
        exit(1);
    } catch (const bad_alloc& Ex) {
        cout << "Caught Exception:" << endl;
        cout << "Out of memory" << endl;
        Z3_reset_memory();
        exit(1);
    } catch (const exception& Ex) {
        cout << "Caught Exception:" << endl;
        cout << Ex.what() << endl;
        Z3_reset_memory();
        exit(1);
    }
}

// 
// ESolverSynthLib.cpp ends here
