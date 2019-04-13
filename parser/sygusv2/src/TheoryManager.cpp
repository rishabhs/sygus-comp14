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

SortDescriptorSPtr Resolver::resolve_sort(SortExprCSPtr sort_expr) const
{
    auto it = sort_descriptors.find(sort_expr);
    if (it == sort_descriptors.end()) {
        auto result = resolve_sort_impl(sort_expr);
        if (!result.is_null()) {
            sort_descriptors[sort_expr] = result;
        }
        return result;
    }
    return it->second;
}

FunctionDescriptorSPtr Resolver::resolve_function(const Identifier& identifier,
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

vector<ResolverSPtr>& TheoryManager::get_resolvers()
{
    static vector<ResolverSPtr> resolvers;
    return resolvers;
}

void TheoryManager::initialize()
{
    initialize_core();
    initialize_bit_vectors();
    initialize_integers();
    initialize_reals();
    initialize_strings();
    initialize_arrays();
}

void TheoryManager::initialize_core()
{
    auto& resolver_list = get_resolvers();
    resolver_list.push_back(new CoreResolver());
}

CoreResolver::CoreResolver()
{
    auto bool_sort = get_bool_sort();
    vector<SortDescriptorCSPtr> arg_vec;
    arg_vec.push_back(bool_sort);

    function_descriptors[SymbolTableKey(not_string, arg_vec)] =
        new FunctionDescriptor(not_string, arg_vec, bool_sort, FunctionKind::Theory);

    arg_vec.push_back(bool_sort);
    function_descriptors[SymbolTableKey(implies_string, arg_vec)] =
        new FunctionDescriptor(implies_string, arg_vec, bool_sort, FunctionKind::Theory);

    function_descriptors[SymbolTableKey(xor_string, arg_vec)]
        = new FunctionDescriptor(xor_string, arg_vec, bool_sort, FunctionKind::Theory);
}

SortDescriptorSPtr CoreResolver::get_bool_sort()
{
    static SortDescriptorSPtr bool_sort = new SortDescriptor((string)"Bool", SortKind::Primitive);
    return bool_sort;
}

SortDescriptorSPtr CoreResolver::resolve_sort_impl(SortExprCSPtr sort_expr) const
{
    // The only sort we resolve is the boolean sort
    // which should not be parametric
    if (sort_expr->get_param_sorts().size() > 0) {
        return nullptr;
    }

    auto const& identifier = sort_expr->get_identifier();
    if (identifier_is_string(*identifier, "Bool")) {
        return get_bool_sort();
    }

    return nullptr;
}

FunctionDescriptorSPtr CoreResolver::resolve_function_impl(const Identifier& identifier,
                                                           const vector<SortDescriptorCSPtr>& argument_sorts) const
{
    if (identifier_is_string(identifier, and_string) ||
        identifier_is_string(identifier, or_string)) {
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

    if (identifier_is_string(identifier, equals_string)) {
        // check that there are two args, and they're of the same sort
        if (argument_sorts.size() != 2 || (*(argument_sorts[0]) != *(argument_sorts[1]))) {
            return nullptr;
        }

        return new FunctionDescriptor(identifier, argument_sorts, get_bool_sort(), FunctionKind::Theory);
    }

    // TODO: finish implementation
    return nullptr;
}

} /* end namespace Sygus2Parser */
