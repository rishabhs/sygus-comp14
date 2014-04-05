#if !defined __SYNTHLIB2_PARSER_LOGIC_SYMBOLS_HPP
#define __SYNTHLIB2_PARSER_LOGIC_SYMBOLS_HPP

#include "SynthLib2ParserFwd.hpp"
#include <boost/functional/hash.hpp>
#include <unordered_set>


// Change this to support larger bitvectors
#define SYNTHLIB2PARSER_MAX_BV_LEN (64)

namespace SynthLib2Parser {

    class SortExprPtrEquals
    {
    public:
        bool operator () (const SortExpr* SortPtr1, const SortExpr* SortPtr2) const;
    };

    class SortExprPtrHash
    {
    public:
        u32 operator () (const SortExpr* SortPtr) const;
    };

    typedef unordered_set<const SortExpr*, SortExprPtrHash, SortExprPtrEquals> SortExprPtrSet;
    
    class LogicSymbolLoader
    {
    private:
        static SortExprPtrSet RegisteredTypes;
        static bool BVLoaded;

    public:
        static void LoadLIA(SymbolTable* SymTab);
        static void LoadBV(SymbolTable* SymTab, u32 Size);
        static void LoadReal(SymbolTable* SymTab);
        static void LoadArrays(SymbolTable* SymTab, const ArraySortExpr* Sort);
        static void LoadCore(SymbolTable* SymTab);

        static void LoadAll(SymbolTable* SymTab);

        // Callback whenever a new type is registered
        // Should be called only for array types
        static void RegisterSort(SymbolTable* SymTab,
                                 const SortExpr* NewSort);
        static void Reset();
    };

} /* end namespace */

#endif /* __SYNTHLIB2_PARSER_LOGIC_SYMBOLS_HPP */

