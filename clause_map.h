#ifndef CLAUSE_MAP_H
#define CLAUSE_MAP_H

#include "debug.h"
#include "cnf.h"


// Basically, maps clause_iterator -> T.
// This exploits the fact that clause_iterators are random-access iterators.
// Thus, the function "iterator - start_iterator" maps iterators to array indices.
template<typename T>
class clause_map {
private:
    int size;
    typedef cnf::clause_iterator key_t;
    key_t offset;
    std::unique_ptr<T[]> data;

    void on_resize(cnf::clause_iterator old_base,
                   cnf::clause_iterator new_base,
                   int new_size) {
        auto new_data = std::make_unique<T[]>(new_size);

        for (int i = 0; i < size; ++i) {
            new_data[i] = data[i];
        }

        size = new_size;
        offset = new_base;
        std::swap(data, new_data);
    }

    void on_remap(int* m, int n, cnf::clause_iterator start) {
        int checker = 0;
        // we iterate over SIZE, which is our actual array size
        for (int i = 0; i < size; ++i) {
            if (m[i] == -1) { continue; }
            //printf("%d %d %d %d\n", n, i, checker, m[i]);
            if (checker != m[i]) { break; }
            // maker sure we're incrementing things contiguously.
            ASSERT(checker == m[i]);
            ++checker;
            data[m[i]] = data[i];
        }
    }

public:
    clause_map(cnf& c, const int size, const key_t offset):
        size(size),
        offset(offset),
        data(std::make_unique<T[]>(size))
    {
        using namespace std::placeholders;
        // Register ourselves as needing a remap:
        std::function<void(key_t, key_t, int)> on_resizer =
            std::bind(&clause_map::on_resize, this, _1, _2, _3);
        c.resizers.push_back(on_resizer);
        c.remappers.push_back(std::bind(&clause_map::on_remap, this, _1, _2, _3));

        std::fill(data.get(), data.get()+size, T());
    }

    T& operator[](const key_t k) {
        return data[k-offset];
    }
    T get_copy(const key_t k) const {
        return data[k-offset];
    }

    key_t first_index() const { return offset; }
    key_t last_index() const { return offset+size; }

    T* first_value_iter() { return data.get(); }
    T* last_value_iter() { return data.get()+size; }
};

template<typename T>
auto begin(clause_map<T>& m) { return m.first_value_iter(); }
template<typename T>
auto end(clause_map<T>& m) { return m.last_value_iter(); }

#endif
