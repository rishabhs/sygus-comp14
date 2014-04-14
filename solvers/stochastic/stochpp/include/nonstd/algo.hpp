#ifndef __NONSTD_ALGO_HPP_
#define __NONSTD_ALGO_HPP_

#include "nonstd.hpp"

namespace stoch {
namespace nonstd {

template <typename T, typename ... Ts>
set <T> set_union(const set <T>& s1, Ts ... sr);

template <typename T>
set <T> set_union(const set <T>& s)
{
    return s;
}

template <typename T, typename ... Ts>
set <T> set_union(const set <T>& s1, Ts ... sr)
{
    set <T> ans(s1);
    for (auto& t : set_union(sr ...)) {
        ans.insert(t);
    }
    return ans;
}

template <typename T, typename ... Ts>
set <T> set_intersection(const set <T>& s1, Ts ... sr);

template <typename T>
set <T> set_intersection(const set <T>& s)
{
    return s;
}

template <typename T, typename ... Ts>
set <T> set_intersection(const set <T>& s1, Ts ... sr)
{
    set <T> ans;
    for (auto& t : set_intersection(sr ...)) {
        if (s1.find(t) != s1.end()) {
            ans.insert(t);
        }
    }
    return ans;
}

template <typename T>
set <T> set_diff(const set <T>& s1, const set <T>& s2)
{
    set <T> ans(s1);
    for (auto& t : s2) {
        ans.erase(t);
    }
    return ans;
}

template <typename ... Ts>
set <tuple <Ts ...>> cart(const set <Ts>& ... sr);

template <>
set <tuple <>> cart()
{
    return set <tuple <>> {};
}

template <typename T>
set <tuple <T>> cart(const set <T>& vt)
{
    set <tuple <T>> ans;
    for (auto& t : vt) {
        ans.insert(make_tuple(t));
    }
    return ans;
}

template <typename T, typename ... Ts>
set <tuple <T, Ts ...>> cart(const set <T>& vt, const set <Ts>& ... sr)
{
    set <tuple <T, Ts ...>> ans;
    for (auto& t : vt) {
        for (auto& r : cart(sr ...)) {
            ans.insert(tuple_cat(make_tuple(t), r));
        }
    }
    return ans;
}

template <typename T>
set <set <T>> powerset(const set <T>& s, typename set <T>::const_iterator it)
{
    if (it == s.cend()) {
        return set <set <T>> { set <T> () };
    }

    const T& val = *it;
    advance(it, 1);
    set <set <T>> smit = powerset(s, it);
    set <set <T>> spit;
    for (const set <T>& sub : smit) {
        set <T> subpv(sub);
        subpv.insert(val);
        spit.insert(subpv);
    }

    return nonstd::set_union(spit, smit);
}

template <typename T>
set <set <T>> powerset(const set <T>& s)
{
    return powerset(s, s.cbegin());
}

template <typename T>
bool subset(const set <T>& s1, const set <T>& s2)
{
    for (auto& t : s1) {
        if (s2.find(t) == s2.end()) {
            return false;
        }
    }

    return true;
}

} // namespace nonstd
} // namespace stoch

#endif // __NONSTD_ALGO_HPP_

