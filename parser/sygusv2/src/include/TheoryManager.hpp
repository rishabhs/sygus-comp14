#if !defined __SYGUS2_PARSER_THEORY_MANAGER_HPP
#define __SYGUS2_PARSER_THEORY_MANAGER_HPP

#include "BaseTypes.hpp"
#include "Sygus2ParserCommon.hpp"
#include "Sygus2ParserIFace.hpp"
#include "SymbolTable.hpp"

#include <unordered_set>

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

class Resolver;
typedef ManagedPointer<Resolver> ResolverSPtr;

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
    static SortDescriptorCSPtr resolve_sort(const Identifier& identifier);
    static FunctionDescriptorCSPtr resolve_function(const Identifier& identifier);
    static FunctionDescriptorCSPtr resolve_function(const Identifier& identifier,
                                                   const vector<SortDescriptorCSPtr>& argument_sorts);
    static void teardown();
};

class Resolver : public RefCountable<Resolver>
{
protected:
    mutable unordered_map<SymbolTableKey, FunctionDescriptorCSPtr,
                          Hasher<SymbolTableKey>, Equals<SymbolTableKey>> function_descriptors;
    mutable unordered_map<Identifier, SortDescriptorCSPtr,
                          Hasher<Identifier>, Equals<Identifier>> sort_descriptors;

protected:
    virtual SortDescriptorCSPtr resolve_sort_impl(const Identifier& identifier) const = 0;
    virtual FunctionDescriptorCSPtr resolve_function_impl(const Identifier& identifier,
                                                          const vector<SortDescriptorCSPtr>& argument_sorts) const = 0;

public:
    SortDescriptorCSPtr resolve_sort(const Identifier& identifier) const;
    FunctionDescriptorCSPtr resolve_function(const Identifier& identifier,
                                             const vector<SortDescriptorCSPtr>& argument_sorts) const;
};

class CoreResolver : public Resolver
{
private:
    static constexpr auto not_string = "not";
    static constexpr auto implies_string = "implies";
    static constexpr auto and_string = "and";
    static constexpr auto or_string = "or";
    static constexpr auto xor_string = "xor";
    static constexpr auto equals_string = "=";
    static constexpr auto ite_string = "ite";
    static constexpr auto distinct_string = "distinct";

    static constexpr auto bool_sort_string = "Bool";

    static SortDescriptorCSPtr get_bool_sort_impl(bool destroy);
    static void drop_bool_sort();

public:
    CoreResolver();
    virtual ~CoreResolver();
    virtual SortDescriptorCSPtr resolve_sort_impl(const Identifier& identifier) const override;
    virtual FunctionDescriptorCSPtr resolve_function_impl(const Identifier& identifier,
                                                          const vector<SortDescriptorCSPtr>& argument_sorts) const override;
    static SortDescriptorCSPtr get_bool_sort();
};

class ArrayResolver : public Resolver
{
private:
    static constexpr auto array_sort_string = "Array";
    static constexpr auto select_string = "select";
    static constexpr auto store_string = "store";
    static constexpr auto array_key_placeholder_sort_name = "ArrayKey";
    static constexpr auto array_value_placeholder_sort_name = "ArrayValue";

    static SortDescriptorCSPtr get_array_sort_impl(bool destroy);
    static void drop_array_sort();
    static SortDescriptorCSPtr create_array_sort();

public:
    ArrayResolver();
    virtual ~ArrayResolver();

    virtual SortDescriptorCSPtr resolve_sort_impl(const Identifier& identifier) const override;
    virtual FunctionDescriptorCSPtr resolve_function_impl(const Identifier& identifier,
                                                          const vector<SortDescriptorCSPtr>& argument_sorts) const override;

    static bool is_array_sort(SortDescriptorCSPtr sort, SortDescriptorCSPtr& key_sort,
                              SortDescriptorCSPtr& value_sort);

    static SortDescriptorCSPtr get_array_sort();
};

class IntegerResolver : public Resolver
{
private:
    static constexpr auto integer_sort_string = "Int";
    static constexpr auto minus_string = "-";
    static constexpr auto plus_string = "+";
    static constexpr auto star_string = "*";
    static constexpr auto div_string = "div";
    static constexpr auto mod_string = "mod";
    static constexpr auto abs_string = "abs";
    static constexpr auto le_string = "<=";
    static constexpr auto lt_string = "<";
    static constexpr auto ge_string = ">=";
    static constexpr auto gt_string = ">";
    static constexpr auto divisible_string = "divisible";

    static SortDescriptorCSPtr get_integer_sort_impl(bool destroy = false);

public:
    IntegerResolver();
    virtual ~IntegerResolver();

    virtual SortDescriptorCSPtr resolve_sort_impl(const Identifier& identifier) const override;
    virtual FunctionDescriptorCSPtr resolve_function_impl(const Identifier& identifier,
                                                          const vector<SortDescriptorCSPtr>& argument_sorts) const override;
    static SortDescriptorCSPtr get_integer_sort();
    void drop_integer_sort();
};

class RealResolver : public Resolver
{
private:
    static constexpr auto real_sort_string = "Real";

    static constexpr auto minus_string = "-";
    static constexpr auto plus_string = "+";
    static constexpr auto star_string = "*";
    static constexpr auto div_string = "/";
    static constexpr auto le_string = "<=";
    static constexpr auto lt_string = "<";
    static constexpr auto ge_string = ">=";
    static constexpr auto gt_string = ">";

    static constexpr auto to_real_string = "to_real";
    static constexpr auto to_int_string = "to_int";
    static constexpr auto is_int_string = "is_int";

    static SortDescriptorCSPtr get_real_sort_impl(bool destroy);

public:
    RealResolver();
    virtual ~RealResolver();

    virtual SortDescriptorCSPtr resolve_sort_impl(const Identifier& identifier) const override;
    virtual FunctionDescriptorCSPtr resolve_function_impl(const Identifier& identifier,
                                                          const vector<SortDescriptorCSPtr>& argument_sorts) const override;
    static SortDescriptorCSPtr get_real_sort();
    void drop_real_sort();
};

class BitVectorResolver : public Resolver
{
private:
    static constexpr auto bitvector_sort_string = "BitVec";

    static constexpr auto bvnot_string = "bvnot";
    static constexpr auto bvneg_string = "bvneg";
    static constexpr auto bvand_string = "bvand";   // left-assoc
    static constexpr auto bvor_string = "bvor";     // left-assoc
    static constexpr auto bvnand_string = "bvnand"; // left-assoc
    static constexpr auto bvnor_string = "bvnor";   // left assoc
    static constexpr auto bvxor_string = "bvxor";   // left assoc
    static constexpr auto bvxnor_string = "bvxnor"; // left assoc

    static constexpr auto bvcomp_string = "bvcomp";
    static constexpr auto bvadd_string = "bvadd";   // left assoc
    static constexpr auto bvsub_string = "bvsub";   // left assoc
    static constexpr auto bvmul_string = "bvmul";   // left assoc
    static constexpr auto bvudiv_string = "bvudiv"; // left assoc
    static constexpr auto bvsdiv_string = "bvsdiv"; // left assoc
    static constexpr auto bvurem_string = "bvurem";
    static constexpr auto bvsrem_string = "bvsrem";
    static constexpr auto bvsmod_string = "bvsmod";

    static constexpr auto bvshl_string = "bvshl";
    static constexpr auto bvlshr_string = "bvlshr";
    static constexpr auto bvashr_string = "bvashr";

    static constexpr auto bvult_string = "bvult";   // chainable
    static constexpr auto bvule_string = "bvule";   // chainable
    static constexpr auto bvugt_string = "bvugt";   // chainable
    static constexpr auto bvuge_string = "bvuge";   // chainable
    static constexpr auto bvslt_string = "bvslt";   // chainable
    static constexpr auto bvsle_string = "bvsle";   // chainable
    static constexpr auto bvsgt_string = "bvsgt";   // chainable
    static constexpr auto bvsge_string = "bvsge";   // chainable


public:
    BitVectorResolver();
    virtual ~BitVectorResolver();

    virtual SortDescriptorCSPtr resolve_sort_impl(const Identifier& identifier) const override;
    virtual FunctionDescriptorCSPtr resolve_function_impl(const Identifier& identifier,
                                                          const vector<SortDescriptorCSPtr>& argument_sorts) const override;

    static bool parse_bitvector_identifier(const Identifier& identifier, u32& size);
};

class StringResolver : public Resolver
{
private:
    // const string char_sort_name = "Char";
    // const string reglan_sort_name = "RegLan";
    static constexpr auto string_sort_name = "String";

    static constexpr auto concat_name = "str.++";
    static constexpr auto replace_name = "str.replace";
    static constexpr auto at_name = "str.at";
    static constexpr auto strfromint_name = "str.from-int";
    static constexpr auto substr_name = "str.substr";

    static constexpr auto len_name = "str.len";
    static constexpr auto strtoint_name = "str.to-int";
    static constexpr auto indexof_name = "str.indexof";

    static constexpr auto prefixof_name = "str.prefixof";
    static constexpr auto suffixof_name = "str.suffixof";
    static constexpr auto contains_name = "str.contains";

    static SortDescriptorCSPtr get_string_sort_impl(bool destroy);

public:
    StringResolver();
    virtual ~StringResolver();

    virtual SortDescriptorCSPtr resolve_sort_impl(const Identifier& identifier) const override;
    virtual FunctionDescriptorCSPtr resolve_function_impl(const Identifier& identifier,
                                                          const vector<SortDescriptorCSPtr>& argument_sorts) const override;

    static SortDescriptorCSPtr get_string_sort();
    static void drop_string_sort();
};

} /* end namespace Sygus2Parser */

#endif /* __SYGUS2_PARSER_THEORY_MANAGER_HPP */
