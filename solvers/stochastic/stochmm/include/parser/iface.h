#if !defined __SYNTH_LIB2_PARSER_IFACE_H
#define __SYNTH_LIB2_PARSER_IFACE_H

#include <string>
#include <utility>
#include <vector>
#include <functional>

namespace SynthLib2Parser {

    using namespace std;

    struct ASTBase;
    struct FunDefCmd;
    struct SynthFunCmd;
    struct ConstraintCmd;
    struct SortDefCmd;
    struct SetOptsCmd;
    struct SortExpr;
    struct VarDeclCmd;
    struct Term;
    struct GTerm;
    struct NTDef;
    struct Literal;
    typedef vector<pair<string, SortExpr*> > ArgList;

    struct ASTBase
    {
        long LineNum;
        long ColNum;
    };

    struct FunDefCmd : public ASTBase
    {
        string Symbol;
        ArgList Arguments;
        SortExpr* Type;
        Term* Def;
    };

    struct SynthFunCmd : public ASTBase
    {
        string SynthFunName;
        ArgList Arguments;
        SortExpr* FunType;
        vector<NTDef*> GrammarRules;
    };

    struct ConstraintCmd : public ASTBase
    {
        Term* TheTerm;
    };
    
    struct SortDefCmd : public ASTBase
    {
        string Symbol;
        SortExpr* Expr;
    };

    struct SetOptsCmd : public ASTBase
    {
        vector<pair<string, string> > Opts;
    };

    struct VarDeclCmd : public ASTBase
    {
        string VarName;
        SortExpr* VarType;
    };
    
    enum BaseSort {
        SORT_BV,
        SORT_INT,
        SORT_BOOL,
        SORT_ENUM,
        SORT_SYMBOL
    };

    struct SortExpr : public ASTBase
    {
        BaseSort BSort;
        long BVSize;
        string Symbol;
        vector<string> EnumConstructors;
    };

    enum TermType {
        TERMTYPE_FUNC,
        TERMTYPE_LITERAL,
        TERMTYPE_SYMBOL
    };

    struct Term : public ASTBase
    {
        TermType TType;
        string Symbol;
        vector<Term*> Children;
        Literal* TheLiteral;
    };

    enum GTermType {
        GTERMTYPE_SYMBOL,
        GTERMTYPE_LITERAL,
        GTERMTYPE_FUNC,
        GTERMTYPE_CONSTANT,
        GTERMTYPE_VARIABLE
    };

    struct GTerm : public ASTBase
    {
        GTermType GTType;
        string Symbol;
        vector<GTerm*> Children;
        SortExpr* TermSort;
        Literal* TheLiteral;
    };

    struct NTDef : public ASTBase
    {
        string Symbol;
        SortExpr* Sort;
        vector<GTerm*> Expansions;
    };

    enum LiteralType {
        LITERALTYPE_INT,
        LITERALTYPE_BOOL,
        LITERALTYPE_ENUM,
        LITERALTYPE_BV
    };

    struct Literal : public ASTBase
    {
        LiteralType LType;
        long IntValue;
        bool BoolValue;
        string LiteralString;
    };

    struct SetLogicCmd : public ASTBase
    {
        string LogicName;
    };

    extern ArgList DeepCopy(const ArgList& s);

    extern FunDefCmd* DeepCopy(const FunDefCmd* Cmd);
    extern SynthFunCmd* DeepCopy(const SynthFunCmd* Cmd);
    extern SortDefCmd* DeepCopy(const SortDefCmd* Cmd);
    extern SetOptsCmd* DeepCopy(const SetOptsCmd* Cmd);
    extern SortExpr* DeepCopy(const SortExpr* s);
    extern Term* DeepCopy(const Term* s);
    extern GTerm* DeepCopy(const GTerm* s);
    extern NTDef* DeepCopy(const NTDef* s);
    extern Literal* DeepCopy(const Literal* s);
    extern ConstraintCmd* DeepCopy(const ConstraintCmd* Cmd);
    extern VarDeclCmd* DeepCopy(const VarDeclCmd* Cmd);
    

    // Destructors
    extern void DestroyFunDefCmd(FunDefCmd* Cmd);
    extern void DestroySynthFunCmd(SynthFunCmd* Cmd);
    extern void DestroyConstraintCmd(ConstraintCmd* Cmd);
    extern void DestroySortDefCmd(SortDefCmd* Cmd);
    extern void DestroySetOptsCmd(SetOptsCmd* Cmd);
    extern void DestroySortExpr(SortExpr* Cmd);
    extern void DestroyTerm(Term* Obj);
    extern void DestroyGTerm(GTerm* Obj);
    extern void DestroyNTDef(NTDef* Obj);
    extern void DestroyLiteral(Literal* Lit);
    extern void DestroySetLogicCmd(SetLogicCmd* Cmd);
    extern void DestroyVarDeclCmd(VarDeclCmd* Cmd);

    // Callbacks
    
    typedef function<int (const FunDefCmd*)> FunDefCallback;
    typedef function<int (const SynthFunCmd*)> SynthFunCallback;
    typedef function<int (const SortDefCmd*)> SortDefCallback;
    typedef function<int (const SetOptsCmd*)> SetOptsCallback;
    typedef function<int (void)> CheckSynthCallback;
    typedef function<int (const SetLogicCmd*)> SetLogicCallback;
    typedef function<int (const ConstraintCmd*)> ConstraintCallback;
    typedef function<int (const VarDeclCmd*)> VarDeclCallback;
    
    // Class definition for the synthlib2 parser
    class SynthLib2Parser
    {
    private:
        vector<FunDefCallback> FunDefCallbacks;
        vector<SynthFunCallback> SynthFunCallbacks;
        vector<SortDefCallback> SortDefCallbacks;
        vector<SetOptsCallback> SetOptsCallbacks;
        vector<CheckSynthCallback> CheckSynthCallbacks;
        vector<SetLogicCallback> SetLogicCallbacks;
        vector<ConstraintCallback> ConstraintCallbacks;
        vector<VarDeclCallback> VarDeclCallbacks;

    public:
        SynthLib2Parser();
        ~SynthLib2Parser();

        // The main parse action
        int operator () (const string& Filename) const;
        
        void AddFunDefCallback(FunDefCallback Callback);
        void AddSynthFunCallback(SynthFunCallback Callback);
        void AddSortDefCallback(SortDefCallback Callback);
        void AddSetOptsCallback(SetOptsCallback Callback);
        void AddCheckSynthCallback(CheckSynthCallback Callback);
        void AddSetLogicCallback(SetLogicCallback Callback);
        void AddConstraintCallback(ConstraintCallback Callback);
        void AddVarDeclCallback(VarDeclCallback Callback);

        const vector<FunDefCallback>& GetFunDefCallbacks() const;
        const vector<SynthFunCallback>& GetSynthFunCallbacks() const;
        const vector<SortDefCallback>& GetSortDefCallbacks() const;
        const vector<SetOptsCallback>& GetSetOptsCallbacks() const;
        const vector<CheckSynthCallback>& GetCheckSynthCallbacks() const;
        const vector<SetLogicCallback>& GetSetLogicCallbacks() const;
        const vector<ConstraintCallback>& GetConstraintCallbacks() const;
        const vector<VarDeclCallback>& GetVarDeclCallbacks() const;

        int DoFunDefCallbacks(const FunDefCmd* Cmd) const;
        int DoSynthFunCallbacks(const SynthFunCmd* Cmd) const;
        int DoSortDefCallbacks(const SortDefCmd* Cmd) const;
        int DoSetOptsCallbacks(const SetOptsCmd* Cmd) const;
        int DoCheckSynthCallbacks() const;
        int DoSetLogicCallbacks(const SetLogicCmd* Cmd) const;
        int DoConstraintCallbacks(const ConstraintCmd* Cmd) const;
        int DoVarDeclCallbacks(const VarDeclCmd* Cmd) const;
    };

} /* End namespace */

#endif /* __SYNTH_LIB2_PARSER_IFACE_H */

