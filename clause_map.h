#ifndef CLAUSE_MAP_H
#define CLAUSE_MAP_H

#include "cnf_table.h"


// Basically, maps clause_iterator -> T.
// This exploits the fact that clause_iterators are random-access iterators.
// Thus, the function "iterator - start_iterator" maps iterators to array indices.
// TODO: static-assert that (not really a big deal, I'm the only maintainer..)
template<typename T>
class clause_map {
private:
    const int size;
    typedef cnf_table::clause_iterator key_t;
    key_t offset;
    std::unique_ptr<T[]> data;

public:
    clause_map(const int size, const key_t offset):
        size(size),
        offset(offset),
        data(std::make_unique<T[]>(size))
    {}

    T& operator[](const key_t k) {
        return data[k-offset];
    }
    T operator[](const key_t k) const {
        return data[k-offset];
    }
};

#endif
