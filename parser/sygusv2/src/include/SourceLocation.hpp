#if !defined __SYGUS2_PARSER_SOURCE_LOCATION_HPP
#define __SYGUS2_PARSER_SOURCE_LOCATION_HPP

#include <string>

#include "BaseTypes.hpp"
#include "Sygus2ParserCommon.hpp"

namespace Sygus2Parser {

using namespace std;

class SourceLocation : public Equatable<SourceLocation>,
                       public Hashable<SourceLocation>
{
private:
    i32 line;
    i32 column;

public:
    SourceLocation(i32 line, i32 column);
    SourceLocation(const SourceLocation& other);
    SourceLocation(SourceLocation&& other);

    ~SourceLocation();

    bool equals_(const SourceLocation& other) const;

    SourceLocation& operator = (const SourceLocation& Other);
    SourceLocation& operator = (SourceLocation&& other);
    u64 compute_hash_() const;

    i32 get_line() const;
    i32 get_column() const;

    string to_string() const;
    static SourceLocation none;
};

} /* end namespace Sygus2Parser */

#endif /* __SYGUS2_PARSER_SOURCE_LOCATION_HPP */
