#ifndef __TEST_INCLUDE_T1_HPP_
#define __TEST_INCLUDE_T1_HPP_

namespace stoch {
namespace test {

void t1()
{
    grammar g(plia(2, 0, false, false, 3));
    g.print(*streams.err) << "---" << endl;

    agsymb_t start;
    tie(g, start) = unroll(g, agsymb_t(0), var_set());
    g.print(*streams.err);
    *streams.err << __LOGSTR__ << start.v << endl;
    grammar_sample gs(g);

    // mt19937 rd;
    random_device rd;

    for (size_t i = 10; i < 11; i++) {
        auto prodn_p = sample(gs, agsymb_t(0), i, rd);
        if (prodn_p) {
            auto prodn = *prodn_p;
            *streams.err << __LOGSTR__ << " " << i << " " << *(prodn.produce()) << endl;
            /* for (size_t j = 0; j < 1000000; j++) {
                prodn = mutate(prodn, gs, rd);
                *streams.err << __LOGSTR__ << " " << i << " " << j << " " << *(prodn.produce()) << endl;
            } */
        }
    }
}

} // namespace test
} // namespace stoch

#endif // __TEST_INCLUDE_T1_HPP_

