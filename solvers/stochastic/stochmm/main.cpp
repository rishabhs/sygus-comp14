#include <iostream>
#include "nonstd.h"
#include "parser/binding.h"
using namespace std;
using namespace stoch;

int main(int argc, char *argv[])
{
    if (argc >= 2)
    {
        return context::parse(argv[1]);
    }
    else
    {
        std::cerr << __LOGSTR__ << "Error. No input file specified." << std::endl
                  << "stoch. Compiled on " << __DATE__ << " at " << __TIME__ << "." << std::endl;
        return 1;
    }
}

