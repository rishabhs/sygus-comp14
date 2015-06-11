#if !defined __SYNTHLIB2_PARSER_SYMBOL_TABLE_HPP
#define __SYNTHLIB2_PARSER_SYMBOL_TABLE_HPP

#include "SynthLib2ParserFwd.hpp"
#include "SynthLib2ParserExceptions.hpp"
#include "SynthLib2ParserIFace.hpp"

namespace SynthLib2Parser {


    // definitions for the symbol table and auxiliary structures
    // A symbol table entry
    enum SymtabEntryKind {
        STENTRY_QVARIABLE,
        STENTRY_BVARIABLE,
        STENTRY_ARG,
        STENTRY_USER_FUNCTION,
        STENTRY_THEORY_FUNCTION,
        STENTRY_SYNTH_FUNCTION,
        STENTRY_UNINTERP_FUNCTION,
        STENTRY_SORT
    };

    class SymbolTableEntry
    {
    private:
        SymtabEntryKind STEKind;
        const SortExpr* STESort;
        // This field is valid only for functions
        FunDefCmd* FunDef;
        // This field is valid only for let bound variables
        Term* LetBoundTerm;

    public:
        // For QVARS, ARGS, SORTS, THEORY FUNCTIONS and SYNTH_FUNCTIONS
        SymbolTableEntry(SymtabEntryKind STEKind, const SortExpr* STESort);
        // For USER_FUNCTIONs
        SymbolTableEntry(FunDefCmd* FunDef);
        // for BVARS
        SymbolTableEntry(Term* LetBoundTerm, const SortExpr* TermSort);
        virtual ~SymbolTableEntry();

        // accessors
        SymtabEntryKind GetKind() const;
        const SortExpr* GetSort() const;
        FunDefCmd* GetFunDef() const;
        Term* GetLetBoundTerm() const;
        
        // Cloner
        SymbolTableEntry* Clone() const;
    };
    
    // Scopes for symbol tables
    class SymbolTableScope
    {
    private:
        unordered_map<string, SymbolTableEntry*> Bindings;

    public:
        SymbolTableScope();
        virtual ~SymbolTableScope();

        SymbolTableEntry* Lookup(const string& Identifier) const;
        void Bind(const string& Identifier, SymbolTableEntry* STE);
        void CheckedBind(const string& Identifier, SymbolTableEntry* STE);

        // Cloning
        SymbolTableScope* Clone() const;
    };

    // Finally, the class for the symbol table
    class SymbolTable
    {
    private:
        vector<SymbolTableScope*> Scopes;

        // Utility functions for name mangling
        inline string MangleName(const string& Name, const vector<const SortExpr*>& ArgSorts) const;
        inline string MangleSortName(const string& Name) const;

    public:
        SymbolTable();
        ~SymbolTable();

        void Push();
        void Push(SymbolTableScope* Scope);
        SymbolTableScope* Pop();

        const SymbolTableEntry* Lookup(const string& Identifier) const;
        const SymbolTableEntry* LookupSort(const string& SortName) const;
        const SymbolTableEntry* LookupSortRecursive(const string& SortName) const;
        const SymbolTableEntry* LookupVariable(const string& VarName) const;
        const SymbolTableEntry* LookupFun(const string& FunName, 
                                          const vector<const SortExpr*>& ArgSorts) const;

        void BindSort(const string& Name, SortExpr* Sort);
        void BindVariable(const string& Name, SortExpr* Sort);
        void BindLetVariable(const string& Name, Term* LetBoundTerm);
        void BindFormal(const string& Name, const SortExpr* Sort);
        void BindTheoryFun(const string& Name, 
                           const vector<const SortExpr*>& ArgSorts, 
                           const SortExpr* RetSort);
        void BindUserFun(FunDefCmd* FunDef);
        void BindSynthFun(const string& Name, 
                          const vector<const SortExpr*>& ArgSorts, 
                          const SortExpr* RetSort);
        void BindUninterpFun(const string& Name,
                             const vector<const SortExpr*>& ArgSorts,
                             const SortExpr* RetSort);

        // Utility function for recursively looking up named sorts
        const SortExpr* ResolveSort(const SortExpr* TheSort) const;
    };

} /* end namespace */

#endif /* __SYNTHLIB2_PARSER_SYMBOL_TABLE_HPP */

