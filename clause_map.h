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

    // hackneyed so it can be a drop-in replacement for a std::map (at least as
    // I'm using std::map). Really should revisit for more efficient implementation.
    struct iterator {
        int my_index = 0;
        const clause_map& my_map;
        std::pair<cnf_table::clause_iterator, T> operator*() {
            return std::make_pair(my_map.offset+my_index,my_map.data[my_index]);
        }
        iterator& operator++() {
            my_index++;
            return *this;
        }
        bool operator!=(const iterator& that) {
            return this->my_index != that.my_index;
        }
    };

    struct const_iterator {
        int my_index = 0;
        const clause_map& my_map;
        std::pair<cnf_table::clause_iterator, T> operator*() {
            return std::make_pair(my_map.offset+my_index, my_map.data[my_index]);
        }
        const_iterator& operator++() {
            my_index++;
            return *this;
        }
        bool operator!=(const const_iterator& that) {
            return this->my_index != that.my_index;
        }
    };

    //iterator begin() { return iterator{0, *this}; }
    //iterator end() { return iterator{size, *this}; }
    const_iterator begin() const { return const_iterator{0, *this}; }
    const_iterator end()   const { return const_iterator{size, *this}; }
};

#endif
