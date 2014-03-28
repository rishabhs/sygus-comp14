#include <SynthLib2ParserIFace.hpp>

using namespace SynthLib2Parser;

int main(int argc, char* argv[])
{
    SynthLib2Parser::SynthLib2Parser* Parser = new SynthLib2Parser::SynthLib2Parser();
    try {
        (*Parser)(argv[1]);
    } catch (const exception& Ex) {
        cout << Ex.what() << endl;
        exit(1);
    }

    cout << (*Parser->GetProgram()) << endl;
    
    delete Parser;
}

