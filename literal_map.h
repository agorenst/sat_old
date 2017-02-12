#ifndef LITERAL_MAP_H
#define LITERAL_MAP_H

#include "debug.h"

#include <memory>

typedef int literal;

// Exploit the fact that literals are easily mapped to array indices
// to get an efficient "map", literal->T.
template <typename T>
class literal_map {
    std::unique_ptr<T[]> data;
    const int size;

public:

    static int literal_to_index(literal i) {
        int index = ((2*std::abs(i))-1) - ((i < 0) ? 1 : 0);
        return index;
    }

    static literal index_to_literal(int i) {
        if (i % 2) { return ((i + 1) / 2); }
        else { return -((i + 2) / 2); }
    }

    literal_map(size_t s): data(std::make_unique<T[]>(s)), size(s) {
        std::fill(data.get(), data.get()+size, T());
    }

    T& operator[](literal i) {
        // TODO: maybe have a different access pattern, or different
        // iteration pattern, because of potential cache misses. Do we
        // group (x, -x) closely, or (x, x+1) closely?
        int index = literal_to_index(i);
        return data[index];
    }
    T get_copy(literal i) const {
        // TODO: maybe have a different access pattern, or different
        // iteration pattern, because of potential cache misses. Do we
        // group (x, -x) closely, or (x, x+1) closely?
        int index = literal_to_index(i);
        if (index < 0 || index >= size) { TRACE("BAD INDEX: ", index, " ", i, "\n"); }
        ASSERT(index >= 0 && index < size);
        return data[index];
    }

    // Rather than maintain complicated iterator structures, we'll just iterate
    // using the C-style for-loop and keep things consistent.
    int first_index() const { return -(size/2); }
    int end_index() const { return (size/2)+1; }

    T* first_value_iter() { return data.get(); }
    T* last_value_iter() { return data.get()+size; }
};

#endif
