#if !defined __SYGUS2_PARSER_THEORIES_HPP
#define __SYGUS2_PARSER_THEORIES_HPP

#include "Sygus2ParserCommon.hpp"
#include "BaseTypes.hpp"
#include "SymbolTable.hpp"

namespace Sygus2Parser {

class AbstractTheory;
typedef ManagedPointer<AbstractTheory> AbstractTheorySPtr;
typedef ManagedConstPointer<AbstractTheory> AbstractTheorySPtr;

class AbstractTheory : public RefCountable<AbstractTheory> {
private:
    string name;
    unordered_map<Identifier, SortDescriptorSPtr> sorts;
    unordered_map<Identifier, FunctionDescriptorSPtr> functions;

    AbstractTheory() = delete;
    AbstractTheory(const AbstractTheory& other) = delete;
    AbstractTheory(AbstractTheory&& other) = delete;
    AbstractTheory& operator = (const AbstractTheory& other) = delete;
    AbstractTheory& operator = (AbstractTheory&& other) = delete;

protected:
    AbstractTheory(const string& name);
    virtual SortDescriptorSPtr resolve_sort_impl(SortExprCSPtr sort_expr);
    virtual FunctionDescriptorSPtr resolve_function_impl(Identifier identifier,
                                                         const vector<SortDescriptorCSPtr>& argument_sorts);
    virtual FunctionDescriptorSPtr resolve_function_impl(FunctionApplicationTermCSPtr application);
    static vector<AbstractTheorySPtr>& get_registered_theory_list();

public:
    static SortDescriptorSPtr resolve_sort(SortExprCSPtr sort_expr);
    static FunctionDescriptorSPtr resolve_function(Identifier identifier,
                                                   const vector<SortDescriptorCSPtr>& argument_sorts);
    static FunctionDescriptorSPtr resolve_function(FunctionApplicationTermCSPtr application);
    static const vector<AbstractTheoryCSPtr>& get_registered_theories();
};

} /* end namespace Sygus2Parser */

#endif /* __SYGUS2_PARSER_THEORIES_HPP */
