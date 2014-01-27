#ifndef __NONFUNCTIONAL_H_
#define __NONFUNCTIONAL_H_

#include <functional>
#include <string>

namespace stoch
{
namespace nonstd
{

template <typename T, typename U> struct plus : public std::binary_function <T, T, U>
{
    U operator() (const T& x, const T& y) const
    {
        return x + y;
    }

    static const std::string op;
};

template <typename T, typename U>
const std::string plus <T, U>::op = "+";

template <typename T, typename U> struct minus : public std::binary_function <T, T, U>
{
    U operator() (const T& x, const T& y) const
    {
        return x - y;
    }

    static const std::string op;
};

template <typename T, typename U>
const std::string minus <T, U>::op = "-";

template <typename T, typename U> struct multiplies : public std::binary_function <T, T, U>
{
    U operator() (const T& x, const T& y) const
    {
        return x * y;
    }

    static const std::string op;
};

template <typename T, typename U>
const std::string multiplies <T, U>::op = "*";

template <typename T, typename U> struct divides : public std::binary_function <T, T, U>
{
    U operator() (const T& x, const T& y) const
    {
        return x / y;
    }

    static const std::string op;
};

template <typename T, typename U>
const std::string divides <T, U>::op = "/";

template <typename T, typename U> struct modulus : public std::binary_function <T, T, U>
{
    U operator() (const T& x, const T& y) const
    {
        return x % y;
    }

    static const std::string op;
};

template <typename T, typename U>
const std::string modulus <T, U>::op = "%";

template <typename T, typename U> struct negate : public std::unary_function <T, U>
{
    T operator() (const T& x) const
    {
        return -x;
    }

    static const std::string op;
};

template <typename T, typename U>
const std::string negate <T, U>::op = "-";

template <typename T, typename U> struct equal_to : public std::binary_function <T, T, U>
{
    U operator() (const T& x, const T& y) const
    {
        return x == y;
    }

    static const std::string op;
};

template <typename T, typename U>
const std::string equal_to <T, U>::op = "==";

template <typename T, typename U> struct not_equal_to : public std::binary_function <T, T, U>
{
    U operator() (const T& x, const T& y) const
    {
        return x != y;
    }

    static const std::string op;
};

template <typename T, typename U>
const std::string not_equal_to <T, U>::op = "!=";

template <typename T, typename U> struct greater : public std::binary_function <T, T, U>
{
    U operator() (const T& x, const T& y) const
    {
        return x > y;
    }

    static const std::string op;
};

template <typename T, typename U>
const std::string greater <T, U>::op = ">";

template <typename T, typename U> struct less : public std::binary_function <T, T, U>
{
    U operator() (const T& x, const T& y) const
    {
        return x < y;
    }

    static const std::string op;
};

template <typename T, typename U>
const std::string less <T, U>::op = "<";

template <typename T, typename U> struct greater_equal : public std::binary_function <T, T, U>
{
    U operator() (const T& x, const T& y) const
    {
        return x >= y;
    }

    static const std::string op;
};

template <typename T, typename U>
const std::string greater_equal <T, U>::op = ">=";

template <typename T, typename U> struct less_equal : public std::binary_function <T, T, U>
{
    U operator() (const T& x, const T& y) const
    {
        return x <= y;
    }

    static const std::string op;
};

template <typename T, typename U>
const std::string less_equal <T, U>::op = "<=";

template <typename T, typename U> struct logical_and : public std::binary_function <T, T, U>
{
    U operator() (const T& x, const T& y) const
    {
        return x && y;
    }

    static const std::string op;
};

template <typename T, typename U>
const std::string logical_and <T, U>::op = "&&";

template <typename T, typename U> struct logical_or : public std::binary_function <T, T, U>
{
    U operator() (const T& x, const T& y) const
    {
        return x || y;
    }

    static const std::string op;
};

template <typename T, typename U>
const std::string logical_or <T, U>::op = "||";

template <typename T, typename U> struct logical_eq : public std::binary_function <T, T, U>
{
    U operator() (const T& x, const T& y) const
    {
        return x == y;
    }

    static const std::string op;
};

template <typename T, typename U>
const std::string logical_eq <T, U>::op = "==";

template <typename T, typename U> struct logical_xor : public std::binary_function <T, T, U>
{
    U operator() (const T& x, const T& y) const
    {
        return x != y;
    }

    static const std::string op;
};

template <typename T, typename U>
const std::string logical_xor <T, U>::op = "!=";

template <typename T, typename U> struct logical_not : public std::unary_function <T, U>
{
    T operator() (const T& x) const
    {
        return !x;
    }

    static const std::string op;
};

template <typename T, typename U>
const std::string logical_not <T, U>::op = "!";

} // namespace nonstd
} // namespace stoch

#endif // __NONFUNCTIONAL_H_
