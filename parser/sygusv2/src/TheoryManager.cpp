#include "include/TheoryManager.hpp"

namespace Sygus2Parser {

static inline bool identifier_is_string(const Identifier& identifier,
                                        const string& target_string)
{
    if (identifier.is_indexed()) {
        return false;
    }
    auto const& symbol = identifier.get_symbol();
    return symbol == target_string;
}

static inline bool identifier_is_string(const Identifier& identifier,
                                        const function<bool(string)>& predicate)
{
    if (identifier.is_indexed()) {
        return false;
    }
    auto const& symbol = identifier.get_symbol();
    return predicate(symbol);
}

// Implementation of TheoryManager;
vector<ResolverSPtr>& TheoryManager::get_resolvers()
{
    static vector<ResolverSPtr> resolvers;
    return resolvers;
}

bool& TheoryManager::get_initialized_status()
{
    static bool initialized_status = false;
    return initialized_status;
}

void TheoryManager::initialize()
{
    if (get_initialized_status()) {
        return;
    }

    initialize_core();
    initialize_bit_vectors();
    initialize_integers();
    initialize_reals();
    initialize_strings();
    initialize_arrays();

    bool& initialized_status = get_initialized_status();
    initialized_status = true;
}

void TheoryManager::initialize_core()
{
    auto& resolver_list = get_resolvers();
    resolver_list.push_back(new CoreResolver());
}

void TheoryManager::initialize_bit_vectors()
{
    auto& resolver_list = get_resolvers();
    resolver_list.push_back(new BitVectorResolver());
}

void TheoryManager::initialize_integers()
{
    auto& resolver_list = get_resolvers();
    resolver_list.push_back(new IntegerResolver());
}

void TheoryManager::initialize_reals()
{
    auto& resolver_list = get_resolvers();
    resolver_list.push_back(new RealResolver());
}

void TheoryManager::initialize_arrays()
{
    auto& resolver_list = get_resolvers();
    resolver_list.push_back(new ArrayResolver());
}

void TheoryManager::initialize_strings()
{
    auto& resolver_list = get_resolvers();
    resolver_list.push_back(new StringResolver());
}

void TheoryManager::teardown()
{
    auto& resolver_list = get_resolvers();
    resolver_list.clear();
    bool& initialized_status = get_initialized_status();
    initialized_status = false;
}

SortDescriptorCSPtr TheoryManager::resolve_sort(const Identifier& identifier)
{
    auto const& resolvers = get_resolvers();

    for (auto const& resolver : resolvers) {
        auto result = resolver->resolve_sort(identifier);
        if (!result.is_null()) {
            return result;
        }
    }

    return nullptr;
}

FunctionDescriptorCSPtr TheoryManager::resolve_function(const Identifier& identifier)
{
    vector<SortDescriptorCSPtr> sorts;
    return resolve_function(identifier, sorts);
}

FunctionDescriptorCSPtr TheoryManager::resolve_function(const Identifier& identifier,
                                                        const vector<SortDescriptorCSPtr>& argument_sorts)
{
    auto const& resolvers = get_resolvers();

    for(auto const& resolver : resolvers) {
        auto result = resolver->resolve_function(identifier, argument_sorts);
        if (!result.is_null()) {
            return result;
        }
    }

    return nullptr;
}

// Implementation of Resolver
SortDescriptorCSPtr Resolver::resolve_sort(const Identifier& identifier) const
{
    auto it = sort_descriptors.find(identifier);
    if (it == sort_descriptors.end()) {
        auto result = resolve_sort_impl(identifier);
        if (!result.is_null()) {
            sort_descriptors[identifier] = result;
        }
        return result;
    }
    return it->second;
}

FunctionDescriptorCSPtr Resolver::resolve_function(const Identifier& identifier,
                                                   const vector<SortDescriptorCSPtr>& argument_sorts) const
{
    SymbolTableKey key(identifier, argument_sorts);
    auto it = function_descriptors.find(key);
    if (it == function_descriptors.end()) {
        auto result = resolve_function_impl(identifier, argument_sorts);
        if (!result.is_null()) {
            function_descriptors[key] = result;
        }
        return result;
    }
    return it->second;
}

// Implementation of CoreResolver
CoreResolver::CoreResolver()
{
    auto bool_sort = get_bool_sort();
    vector<SortDescriptorCSPtr> arg_vec;
    arg_vec.push_back(bool_sort);

    function_descriptors[SymbolTableKey((string)not_string, arg_vec)] =
        new FunctionDescriptor((string)not_string, arg_vec, bool_sort, FunctionKind::Theory);
}

CoreResolver::~CoreResolver()
{
    drop_bool_sort();
}

SortDescriptorCSPtr CoreResolver::get_bool_sort_impl(bool destroy)
{
    static SortDescriptorCSPtr bool_sort = SortDescriptor::create_primitive_sort((string)bool_sort_string);

    if (destroy) {
        bool_sort = nullptr;
    }

    return bool_sort;
}

SortDescriptorCSPtr CoreResolver::get_bool_sort()
{
    return get_bool_sort_impl(false);
}

void CoreResolver::drop_bool_sort()
{
    get_bool_sort_impl(true);
}

SortDescriptorCSPtr CoreResolver::resolve_sort_impl(const Identifier& identifier) const
{
    if (identifier_is_string(identifier, bool_sort_string)) {
        return get_bool_sort();
    }

    return nullptr;
}

FunctionDescriptorCSPtr CoreResolver::resolve_function_impl(const Identifier& identifier,
                                                           const vector<SortDescriptorCSPtr>& argument_sorts) const
{
    if (identifier_is_string(identifier, and_string) ||
        identifier_is_string(identifier, or_string) ||
        identifier_is_string(identifier, xor_string) ||
        identifier_is_string(identifier, implies_string)) {
        // check that the arguments are all boolean, and that there are at least two args.
        if (argument_sorts.size() < 2) {
            return nullptr;
        }

        auto bool_sort = get_bool_sort();
        for(auto const& arg_sort : argument_sorts) {
            if (arg_sort != bool_sort) {
                return nullptr;
            }
        }

        return new FunctionDescriptor(identifier, argument_sorts, bool_sort, FunctionKind::Theory);
    }

    if (identifier_is_string(identifier, equals_string) ||
        identifier_is_string(identifier, distinct_string)) {
        // check that there are at least two args, and they're of the same sort
        if (argument_sorts.size() < 2) {
            return nullptr;
        }

        auto first_sort = argument_sorts[0];
        for(size_t i = 1; i < argument_sorts.size(); ++i) {
            if (*argument_sorts[i] != *first_sort) {
                return nullptr;
            }
        }

        return new FunctionDescriptor(identifier, argument_sorts, get_bool_sort(), FunctionKind::Theory);
    }

    if (identifier_is_string(identifier, ite_string)) {
        // there should be exactly three args, the last two should be of the same
        // sort and the first should be boolean sorted
        if (argument_sorts.size() != 3) {
            return nullptr;
        }

        auto bool_sort = get_bool_sort();
        if (*argument_sorts[0] != *bool_sort || *argument_sorts[1] != *argument_sorts[2]) {
            return nullptr;
        }

        return new FunctionDescriptor(identifier, argument_sorts, argument_sorts[1], FunctionKind::Theory);
    }

    return nullptr;
}

// Implementation of ArrayResolver
ArrayResolver::ArrayResolver()
{
    // Nothing here
}

ArrayResolver::~ArrayResolver()
{
    // Nothing here
}

SortDescriptorCSPtr ArrayResolver::create_array_sort()
{
    auto key_sort = SortDescriptor::create_sort_parameter_placeholder((string)array_key_placeholder_sort_name);
    auto value_sort = SortDescriptor::create_sort_parameter_placeholder((string)array_value_placeholder_sort_name);
    vector<SortDescriptorCSPtr> params;
    params.push_back(key_sort);
    params.push_back(value_sort);
    return SortDescriptor::create_parametric_sort((string)array_sort_string, params);
}

SortDescriptorCSPtr ArrayResolver::get_array_sort_impl(bool destroy)
{
    static SortDescriptorCSPtr array_sort = create_array_sort();

    if (destroy) {
        array_sort = nullptr;
    }

    return array_sort;
}

SortDescriptorCSPtr ArrayResolver::get_array_sort()
{
    return get_array_sort_impl(false);
}

void ArrayResolver::drop_array_sort()
{
    get_array_sort_impl(true);
}

SortDescriptorCSPtr ArrayResolver::resolve_sort_impl(const Identifier& identifier) const
{
    if (identifier_is_string(identifier, (string)array_sort_string)) {
        return get_array_sort();
    }

    return nullptr;
}

FunctionDescriptorCSPtr ArrayResolver::resolve_function_impl(const Identifier& identifier,
                                                             const vector<SortDescriptorCSPtr>& argument_sorts) const
{
    auto const& arg0_sort_identifier = argument_sorts[0]->get_identifier();
    if (!identifier_is_string(arg0_sort_identifier, "Array")) {
        return nullptr;
    }

    auto const& array_sort_params = argument_sorts[0]->get_sort_parameters();
    if (array_sort_params.size() != 2) {
        return nullptr;
    }

    auto key_sort = array_sort_params[0];
    auto value_sort = array_sort_params[1];

    if (identifier_is_string(identifier, (string)select_string)) {
        if (argument_sorts.size() != 2) {
            return nullptr;
        }

        if (*(argument_sorts[1]) != *key_sort) {
            return nullptr;
        }

        return new FunctionDescriptor(identifier, argument_sorts, value_sort, FunctionKind::Theory);
    }

    if (identifier_is_string(identifier, (string)store_string)) {
        if (argument_sorts.size() != 3) {
            return nullptr;
        }

        if (*argument_sorts[1] != *key_sort) {
            return nullptr;
        }

        if (*argument_sorts[2] != *value_sort) {
            return nullptr;
        }

        return new FunctionDescriptor(identifier, argument_sorts, argument_sorts[0], FunctionKind::Theory);
    }

    return nullptr;
}

bool ArrayResolver::is_array_sort(SortDescriptorCSPtr sort, SortDescriptorCSPtr& key_sort,
                                  SortDescriptorCSPtr& value_sort)
{
    auto const& sort_params = sort->get_sort_parameters();
    if (sort_params.size() != 2) {
        return false;
    }

    if (!identifier_is_string(sort->get_identifier(), array_sort_string)) {
        return false;
    }

    key_sort = sort_params[0];
    value_sort = sort_params[1];
    return true;
}

SortDescriptorCSPtr IntegerResolver::get_integer_sort_impl(bool destroy)
{
    static SortDescriptorCSPtr integer_sort = SortDescriptor::create_primitive_sort((string)integer_sort_string);

    if (destroy) {
        integer_sort = nullptr;
    }

    return integer_sort;
}

SortDescriptorCSPtr IntegerResolver::get_integer_sort()
{
    return get_integer_sort_impl(false);
}

void IntegerResolver::drop_integer_sort()
{
    get_integer_sort_impl(true);
}

IntegerResolver::IntegerResolver()
{
    auto int_sort = get_integer_sort();
    vector<SortDescriptorCSPtr> arg_sorts;
    arg_sorts.push_back(int_sort);

    function_descriptors[SymbolTableKey((string)minus_string, arg_sorts)] =
        new FunctionDescriptor((string)minus_string, arg_sorts, int_sort, FunctionKind::Theory);

    function_descriptors[SymbolTableKey((string)abs_string, arg_sorts)] =
        new FunctionDescriptor((string)abs_string, arg_sorts, int_sort, FunctionKind::Theory);

    arg_sorts.push_back(int_sort);

    function_descriptors[SymbolTableKey((string)mod_string, arg_sorts)] =
        new FunctionDescriptor((string)mod_string, arg_sorts, int_sort, FunctionKind::Theory);
}

IntegerResolver::~IntegerResolver()
{
    drop_integer_sort();
}

SortDescriptorCSPtr IntegerResolver::resolve_sort_impl(const Identifier& identifier) const
{
    if (identifier_is_string(identifier, (string)integer_sort_string)) {
        return get_integer_sort();
    }
    return nullptr;
}

FunctionDescriptorCSPtr IntegerResolver::resolve_function_impl(const Identifier& identifier,
                                                               const vector<SortDescriptorCSPtr>& argument_sorts) const
{
    auto int_sort = get_integer_sort();
    if (identifier_is_string(identifier, (string)minus_string) ||
        identifier_is_string(identifier, (string)plus_string) ||
        identifier_is_string(identifier, (string)star_string) ||
        identifier_is_string(identifier, (string)div_string)) {
        // check that all args are integer valued
        for(auto const& arg_sort : argument_sorts) {
            if (*(arg_sort) != *int_sort) {
                return nullptr;
            }
        }
        return new FunctionDescriptor(identifier, argument_sorts, int_sort, FunctionKind::Theory);
    }

    if (identifier_is_string(identifier, (string)le_string) ||
        identifier_is_string(identifier, (string)lt_string) ||
        identifier_is_string(identifier, (string)ge_string) ||
        identifier_is_string(identifier, (string)gt_string)) {
        // check that all args are integer valued
        for(auto const& arg_sort : argument_sorts) {
            if (*(arg_sort) != *int_sort) {
                return nullptr;
            }
        }
        return new FunctionDescriptor(identifier, argument_sorts, CoreResolver::get_bool_sort(),
                                      FunctionKind::Theory);
    }

    // Final check for divisible
    auto const& indices = identifier.get_indices();
    if (identifier.get_symbol() == divisible_string &&
        indices.size() == 1 && indices[0]->is_numeral() &&
        argument_sorts.size() == 1 &&
        *(argument_sorts[0]) == *int_sort) {
        return new FunctionDescriptor(identifier, argument_sorts, CoreResolver::get_bool_sort(),
                                      FunctionKind::Theory);
    }

    return nullptr;
}

SortDescriptorCSPtr RealResolver::get_real_sort_impl(bool destroy)
{
    static SortDescriptorCSPtr real_sort = SortDescriptor::create_primitive_sort((string)real_sort_string);

    if (destroy) {
        real_sort = nullptr;
    }

    return real_sort;
}

void RealResolver::drop_real_sort()
{
    get_real_sort_impl(true);
}

SortDescriptorCSPtr RealResolver::get_real_sort()
{
    return get_real_sort_impl(false);
}

RealResolver::RealResolver()
{
    auto real_sort = get_real_sort();
    auto int_sort = IntegerResolver::get_integer_sort();
    auto bool_sort = CoreResolver::get_bool_sort();

    vector<SortDescriptorCSPtr> arg_sorts;
    arg_sorts.push_back(int_sort);

    function_descriptors[SymbolTableKey((string)to_real_string, arg_sorts)] =
        new FunctionDescriptor((string)to_real_string, arg_sorts, real_sort, FunctionKind::Theory);

    arg_sorts.clear();
    arg_sorts.push_back(real_sort);
    function_descriptors[SymbolTableKey((string)to_int_string, arg_sorts)]
        = new FunctionDescriptor((string)to_int_string, arg_sorts, int_sort, FunctionKind::Theory);

    function_descriptors[SymbolTableKey((string)is_int_string, arg_sorts)]
        = new FunctionDescriptor((string)is_int_string, arg_sorts, bool_sort, FunctionKind::Theory);
}

RealResolver::~RealResolver()
{
    drop_real_sort();
}

SortDescriptorCSPtr RealResolver::resolve_sort_impl(const Identifier& identifier) const
{
    if (identifier_is_string(identifier, (string)real_sort_string)) {
        return get_real_sort();
    }

    return nullptr;
}

FunctionDescriptorCSPtr RealResolver::resolve_function_impl(const Identifier& identifier,
                                                            const vector<SortDescriptorCSPtr>& argument_sorts) const
{
    auto real_sort = get_real_sort();
    if (identifier_is_string(identifier, (string)minus_string) ||
        identifier_is_string(identifier, (string)plus_string) ||
        identifier_is_string(identifier, (string)star_string) ||
        identifier_is_string(identifier, (string)div_string)) {
        // check that all args are integer valued
        for(auto const& arg_sort : argument_sorts) {
            if (*(arg_sort) != *real_sort) {
                return nullptr;
            }
        }
        return new FunctionDescriptor(identifier, argument_sorts, real_sort, FunctionKind::Theory);
    }

    if (identifier_is_string(identifier, (string)le_string) ||
        identifier_is_string(identifier, (string)lt_string) ||
        identifier_is_string(identifier, (string)ge_string) ||
        identifier_is_string(identifier, (string)gt_string)) {
        // check that all args are integer valued
        for(auto const& arg_sort : argument_sorts) {
            if (*(arg_sort) != *real_sort) {
                return nullptr;
            }
        }
        return new FunctionDescriptor(identifier, argument_sorts, CoreResolver::get_bool_sort(),
                                      FunctionKind::Theory);
    }

    return nullptr;
}

BitVectorResolver::BitVectorResolver()
{
    // Nothing here
}

BitVectorResolver::~BitVectorResolver()
{
    // Nothing here
}

bool BitVectorResolver::parse_bitvector_identifier(const Identifier& identifier, u32& size)
{
    if (identifier.get_symbol() != bitvector_sort_string) {
        return false;
    }

    auto const& indices = identifier.get_indices();
    if (indices.size() != 1 || !indices[0]->is_numeral()) {
        return false;
    }

    size = indices[0]->get_numeral();

    if (size <= 0) {
        return false;
    }

    return true;
}

SortDescriptorCSPtr BitVectorResolver::resolve_sort_impl(const Identifier& identifier) const
{
    u32 size = 0;
    if (!parse_bitvector_identifier(identifier, size)) {
        return nullptr;
    }

    return SortDescriptor::create_primitive_sort(identifier);
}

FunctionDescriptorCSPtr BitVectorResolver::resolve_function_impl(const Identifier& identifier,
                                                                const vector<SortDescriptorCSPtr>& argument_sorts) const
{
    if (identifier_is_string(identifier, (string)bvnot_string) ||
        identifier_is_string(identifier, (string)bvneg_string) ||
        identifier_is_string(identifier, (string)bvcomp_string)) {
        // unary operators
        if (argument_sorts.size() != 1) {
            return nullptr;
        }

        u32 unused;
        if (parse_bitvector_identifier(argument_sorts[0]->get_identifier(), unused)) {
            return new FunctionDescriptor(identifier, argument_sorts, argument_sorts[0], FunctionKind::Theory);
        }
    }

    if (identifier_is_string(identifier, (string)bvurem_string) ||
        identifier_is_string(identifier, (string)bvsrem_string) ||
        identifier_is_string(identifier, (string)bvsmod_string) ||
        identifier_is_string(identifier, (string)bvshl_string) ||
        identifier_is_string(identifier, (string)bvlshr_string) ||
        identifier_is_string(identifier, (string)bvashr_string)) {
        // binary operators
        if (argument_sorts.size() != 2) {
            return nullptr;
        }

        u32 size1, size2;
        if (!parse_bitvector_identifier(argument_sorts[0]->get_identifier(), size1) ||
            !parse_bitvector_identifier(argument_sorts[1]->get_identifier(), size2) ||
            size1 != size2) {
            return nullptr;
        }

        return new FunctionDescriptor(identifier, argument_sorts, argument_sorts[0], FunctionKind::Theory);
    }

    if (identifier_is_string(identifier, (string)bvand_string) ||
        identifier_is_string(identifier, (string)bvor_string) ||
        identifier_is_string(identifier, (string)bvnand_string) ||
        identifier_is_string(identifier, (string)bvnor_string) ||
        identifier_is_string(identifier, (string)bvxor_string) ||
        identifier_is_string(identifier, (string)bvxnor_string) ||
        identifier_is_string(identifier, (string)bvadd_string) ||
        identifier_is_string(identifier, (string)bvsub_string) ||
        identifier_is_string(identifier, (string)bvmul_string) ||
        identifier_is_string(identifier, (string)bvudiv_string) ||
        identifier_is_string(identifier, (string)bvsdiv_string)) {
        // chainable/left-assoc binary operators
        if (argument_sorts.size() < 2) {
            return nullptr;
        }

        u32 size;
        if (!parse_bitvector_identifier(argument_sorts[0]->get_identifier(), size)) {
            return nullptr;
        }

        for(size_t i = 1; i < argument_sorts.size(); ++i) {
            u32 current_size;
            if (!parse_bitvector_identifier(argument_sorts[i]->get_identifier(), current_size) ||
                current_size != size) {
                return nullptr;
            }
        }

        return new FunctionDescriptor(identifier, argument_sorts, argument_sorts[0], FunctionKind::Theory);
    }

    if (identifier_is_string(identifier, (string)bvult_string) ||
        identifier_is_string(identifier, (string)bvule_string) ||
        identifier_is_string(identifier, (string)bvugt_string) ||
        identifier_is_string(identifier, (string)bvuge_string) ||
        identifier_is_string(identifier, (string)bvslt_string) ||
        identifier_is_string(identifier, (string)bvsle_string) ||
        identifier_is_string(identifier, (string)bvsgt_string) ||
        identifier_is_string(identifier, (string)bvsge_string)) {
        // chainable binary operators
        if (argument_sorts.size() < 2) {
            return nullptr;
        }

        u32 size;
        if (!parse_bitvector_identifier(argument_sorts[0]->get_identifier(), size)) {
            return nullptr;
        }

        for(size_t i = 1; i < argument_sorts.size(); ++i) {
            u32 current_size;
            if (!parse_bitvector_identifier(argument_sorts[i]->get_identifier(), current_size) ||
                current_size != size) {
                return nullptr;
            }
        }

        return new FunctionDescriptor(identifier, argument_sorts, CoreResolver::get_bool_sort(), FunctionKind::Theory);
    }

    return nullptr;
}

SortDescriptorCSPtr StringResolver::get_string_sort_impl(bool destroy)
{
    static SortDescriptorCSPtr string_sort = SortDescriptor::create_primitive_sort((string)string_sort_name);

    if (destroy) {
        string_sort = nullptr;
    }

    return string_sort;
}

SortDescriptorCSPtr StringResolver::get_string_sort()
{
    return get_string_sort_impl(false);
}

void StringResolver::drop_string_sort()
{
    get_string_sort_impl(true);
}

StringResolver::StringResolver()
{
    auto int_sort = IntegerResolver::get_integer_sort();
    auto string_sort = get_string_sort();
    auto bool_sort = CoreResolver::get_bool_sort();

    vector<SortDescriptorCSPtr> arg_sorts;
    arg_sorts.push_back(string_sort);
    arg_sorts.push_back(string_sort);
    arg_sorts.push_back(string_sort);

    function_descriptors[SymbolTableKey((string)replace_name, arg_sorts)] =
        new FunctionDescriptor((string)replace_name, arg_sorts, string_sort, FunctionKind::Theory);

    arg_sorts.clear();
    arg_sorts.push_back(string_sort);
    arg_sorts.push_back(int_sort);

    function_descriptors[SymbolTableKey((string)at_name, arg_sorts)] =
        new FunctionDescriptor((string)at_name, arg_sorts, string_sort, FunctionKind::Theory);

    arg_sorts.clear();
    arg_sorts.push_back(int_sort);

    function_descriptors[SymbolTableKey((string)strfromint_name, arg_sorts)] =
        new FunctionDescriptor((string)strfromint_name, arg_sorts, string_sort, FunctionKind::Theory);

    arg_sorts.clear();
    arg_sorts.push_back(string_sort);
    arg_sorts.push_back(int_sort);
    arg_sorts.push_back(int_sort);

    function_descriptors[SymbolTableKey((string)substr_name, arg_sorts)] =
        new FunctionDescriptor((string)substr_name, arg_sorts, string_sort, FunctionKind::Theory);

    arg_sorts.clear();
    arg_sorts.push_back(string_sort);

    function_descriptors[SymbolTableKey((string)len_name, arg_sorts)] =
        new FunctionDescriptor((string)len_name, arg_sorts, int_sort, FunctionKind::Theory);

    function_descriptors[SymbolTableKey((string)strtoint_name, arg_sorts)] =
        new FunctionDescriptor((string)len_name, arg_sorts, int_sort, FunctionKind::Theory);

    arg_sorts.clear();
    arg_sorts.push_back(string_sort);
    arg_sorts.push_back(string_sort);
    arg_sorts.push_back(int_sort);

    function_descriptors[SymbolTableKey((string)indexof_name, arg_sorts)] =
        new FunctionDescriptor((string)len_name, arg_sorts, int_sort, FunctionKind::Theory);

    arg_sorts.clear();
    arg_sorts.push_back(string_sort);
    arg_sorts.push_back(string_sort);

    function_descriptors[SymbolTableKey((string)prefixof_name, arg_sorts)] =
        new FunctionDescriptor((string)len_name, arg_sorts, bool_sort, FunctionKind::Theory);
    function_descriptors[SymbolTableKey((string)suffixof_name, arg_sorts)] =
        new FunctionDescriptor((string)len_name, arg_sorts, bool_sort, FunctionKind::Theory);
    function_descriptors[SymbolTableKey((string)contains_name, arg_sorts)] =
        new FunctionDescriptor((string)len_name, arg_sorts, bool_sort, FunctionKind::Theory);
}

StringResolver::~StringResolver()
{
    drop_string_sort();
}

SortDescriptorCSPtr StringResolver::resolve_sort_impl(const Identifier& identifier) const
{
    if (identifier_is_string(identifier, string_sort_name)) {
        return get_string_sort();
    }

    return nullptr;
}

FunctionDescriptorCSPtr StringResolver::resolve_function_impl(const Identifier& identifier,
                                                              const vector<SortDescriptorCSPtr>& argument_sorts) const
{
    if (identifier_is_string(identifier, concat_name)) {
        if (argument_sorts.size() < 2) {
            return nullptr;
        }

        if (*(argument_sorts[0]) != *(get_string_sort())) {
            return nullptr;
        }

        for(size_t i = 1; i < argument_sorts.size(); ++i) {
            if (*(argument_sorts[i]) != *(argument_sorts[0])) {
                return nullptr;
            }
        }

        return new FunctionDescriptor(identifier, argument_sorts, get_string_sort(), FunctionKind::Theory);
    }

    return nullptr;
}

} /* end namespace Sygus2Parser */
