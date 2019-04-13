#if !defined __SYGUS2_PARSER_THEORY_MANAGER_HPP
#define __SYGUS2_PARSER_THEORY_MANAGER_HPP

#include "BaseTypes.hpp"
#include "Sygus2ParserCommon.hpp"
#include "Sygus2ParserIFace.hpp"
#include "SymbolTable.hpp"

namespace Sygus2Parser {

class SortExprCSPtrHasher
{
public:
    inline u64 operator () (const SortExprCSPtr& sort_expr) const
    {
        return sort_expr->get_hash();
    }
};

class SortExprCSPtrEquals
{
public:
    inline bool operator () (const SortExprCSPtr& sort1,
                             const SortExprCSPtr& sort2) const
    {
        return *sort1 == *sort2;
    }
};

class Resolver : public RefCountable<Resolver>
{
protected:
    mutable unordered_map<SymbolTableKey, FunctionDescriptorSPtr,
                          Hasher<SymbolTableKey>, Equals<SymbolTableKey>> function_descriptors;
    mutable unordered_map<SortExprCSPtr, SortDescriptorSPtr,
                          SortExprCSPtrHasher, SortExprCSPtrEquals> sort_descriptors;

protected:
    virtual SortDescriptorSPtr resolve_sort_impl(SortExprCSPtr sort_expr) const = 0;
    virtual FunctionDescriptorSPtr resolve_function_impl(const Identifier& identifier,
                                                         const vector<SortDescriptorCSPtr>& argument_sorts) const = 0;

public:
    SortDescriptorSPtr resolve_sort(SortExprCSPtr sort_expr) const;
    FunctionDescriptorSPtr resolve_function(const Identifier& identifier,
                                            const vector<SortDescriptorCSPtr>& argument_sorts) const;
};

typedef ManagedPointer<Resolver> ResolverSPtr;

class CoreResolver : public Resolver
{
private:
    static SortDescriptorSPtr get_bool_sort();

    const string not_string = "not";
    const string implies_string = "implies";
    const string and_string = "and";
    const string or_string = "or";
    const string xor_string = "xor";
    const string equals_string = "=";
    const string ite_string = "ite";
    const string distinct_string = "distinct";

public:
    CoreResolver();
    virtual ~CoreResolver();
    virtual SortDescriptorSPtr resolve_sort_impl(SortExprCSPtr sort_expr) const override;
    virtual FunctionDescriptorSPtr resolve_function_impl(const Identifier& identifier,
                                                         const vector<SortDescriptorCSPtr>& argument_sorts) const override;
};

class TheoryManager
{
private:
    TheoryManager() = delete;
    TheoryManager(const TheoryManager& other) = delete;
    TheoryManager(TheoryManager&& other) = delete;
    TheoryManager& operator = (const TheoryManager& other) = delete;
    TheoryManager& operator = (TheoryManager&& other) = delete;

    static vector<ResolverSPtr>& get_resolvers();
    static bool& get_initialized_status();

    static void initialize_core();
    static void initialize_bit_vectors();
    static void initialize_integers();
    static void initialize_reals();
    static void initialize_strings();
    static void initialize_arrays();

public:
    static void initialize();
    static SortDescriptorSPtr resolve_sort(SortExprCSPtr sort_expr);
    static FunctionDescriptorSPtr resolve_function(const Identifier& identifier);
    static FunctionDescriptorSPtr resolve_function(const Identifier& identifier,
                                                   const vector<SortDescriptorCSPtr>& argument_sorts);
    static void teardown();
};

} /* end namespace Sygus2Parser */

#endif /* __SYGUS2_PARSER_THEORY_MANAGER_HPP */
