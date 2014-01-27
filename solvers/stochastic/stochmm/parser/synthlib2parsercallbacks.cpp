#include "parser/iface.h"
#include <cstdio>
#include <iostream>

using namespace std;

extern int yyparse();
extern FILE* yyin;

namespace SynthLib2Parser {

    extern const SynthLib2Parser* TheParser;

    template<typename T1, typename T2>
    static inline int DoCallbacks(const vector<T1>& Callbacks, T2 Cmd)
    {
        for(auto const& Callback : Callbacks) {
            auto Retval = Callback(Cmd);
            if(Retval != 0) {
                return Retval;
            }
        }
        return 0;
    }

    template<typename T1>
    static inline void AddCallback(vector<T1>& Callbacks, T1 NewCallback)
    {
        Callbacks.push_back(NewCallback);
    }

    SynthLib2Parser::SynthLib2Parser()
    {
        // Nothing here
    }

    SynthLib2Parser::~SynthLib2Parser()
    {
        // Nothing here
    }

    int SynthLib2Parser::operator () (const string& Filename) const
    {
        TheParser = this;
        yyin = fopen(Filename.c_str(), "r");
        if(yyin == NULL) {
            cerr << "Error: File \"" << Filename << "\" could not be opened!" << endl;
            return 1;
        }
        if(yyparse()) {
            cerr << "Parse Error!!" << endl;
            fclose(yyin);
            return 1;
        }
        TheParser = NULL;
        fclose(yyin);
        return 0;
    }

    void SynthLib2Parser::AddFunDefCallback(FunDefCallback Callback)
    {
        AddCallback(FunDefCallbacks, Callback);
    }

    void SynthLib2Parser::AddSynthFunCallback(SynthFunCallback Callback)
    {
        AddCallback(SynthFunCallbacks, Callback);
    }

    void SynthLib2Parser::AddSortDefCallback(SortDefCallback Callback)
    {
        AddCallback(SortDefCallbacks, Callback);
    }

    void SynthLib2Parser::AddSetOptsCallback(SetOptsCallback Callback)
    {
        AddCallback(SetOptsCallbacks, Callback);
    }

    void SynthLib2Parser::AddCheckSynthCallback(CheckSynthCallback Callback)
    {
        AddCallback(CheckSynthCallbacks, Callback);
    }

    void SynthLib2Parser::AddSetLogicCallback(SetLogicCallback Callback)
    {
        AddCallback(SetLogicCallbacks, Callback);
    }

    void SynthLib2Parser::AddConstraintCallback(ConstraintCallback Callback)
    {
        AddCallback(ConstraintCallbacks, Callback);
    }

    void SynthLib2Parser::AddVarDeclCallback(VarDeclCallback Callback)
    {
        AddCallback(VarDeclCallbacks, Callback);
    }

    const vector<FunDefCallback>& SynthLib2Parser::GetFunDefCallbacks() const
    {
        return FunDefCallbacks;
    }

    const vector<SynthFunCallback>& SynthLib2Parser::GetSynthFunCallbacks() const
    {
        return SynthFunCallbacks;
    }

    const vector<SortDefCallback>& SynthLib2Parser::GetSortDefCallbacks() const
    {
        return SortDefCallbacks;
    }

    const vector<SetOptsCallback>& SynthLib2Parser::GetSetOptsCallbacks() const
    {
        return SetOptsCallbacks;
    }

    const vector<CheckSynthCallback>& SynthLib2Parser::GetCheckSynthCallbacks() const
    {
        return CheckSynthCallbacks;
    }

    const vector<ConstraintCallback>& SynthLib2Parser::GetConstraintCallbacks() const
    {
        return ConstraintCallbacks;
    }

    const vector<VarDeclCallback>& SynthLib2Parser::GetVarDeclCallbacks() const
    {
        return VarDeclCallbacks;
    }

    int SynthLib2Parser::DoFunDefCallbacks(const FunDefCmd* Cmd) const
    {
        return DoCallbacks(FunDefCallbacks, Cmd);
    }

    int SynthLib2Parser::DoSynthFunCallbacks(const SynthFunCmd* Cmd) const
    {
        return DoCallbacks(SynthFunCallbacks, Cmd);
    }

    int SynthLib2Parser::DoSortDefCallbacks(const SortDefCmd* Cmd) const
    {
        return DoCallbacks(SortDefCallbacks, Cmd);
    }

    int SynthLib2Parser::DoSetOptsCallbacks(const SetOptsCmd* Cmd) const
    {
        return DoCallbacks(SetOptsCallbacks, Cmd);
    }

    int SynthLib2Parser::DoCheckSynthCallbacks() const
    {
        for(auto const& Callback : CheckSynthCallbacks) {
            auto Retval = Callback();
            if(Retval != 0) {
                return Retval;
            }
        }
        return 0;
    }

    int SynthLib2Parser::DoSetLogicCallbacks(const SetLogicCmd* Cmd) const
    {
        return DoCallbacks(SetLogicCallbacks, Cmd);
    }

    int SynthLib2Parser::DoConstraintCallbacks(const ConstraintCmd* Cmd) const
    {
        return DoCallbacks(ConstraintCallbacks, Cmd);
    }

    int SynthLib2Parser::DoVarDeclCallbacks(const VarDeclCmd* Cmd) const
    {
        return DoCallbacks(VarDeclCallbacks, Cmd);
    }

} /* End namespace */

