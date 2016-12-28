#ifndef LITERAL_MAP_H
#define LITERAL_MAP_H

#include <memory>

typedef int literal;

#ifdef LITERAL_MAP_VERBOSE
#include <cstdio>
#define TRACE(...) printf(__VA_ARGS__)
#else
#define TRACE(...)
#endif


// Exploit the fact that literals are easily mapped to array indices
// to get an efficient "map", literal->T.
template <typename T>
class literal_map {
    std::unique_ptr<T[]> m;
    const int size;


public:

    int literal_to_index(literal i) const {
        int index = ((2*std::abs(i))-1) - ((i < 0) ? 1 : 0);
        return index;
    }

    literal index_to_literal(int i) const {
        if (i % 2) { return ((i + 1) / 2); }
        else { return -((i + 2) / 2); }
    }

    literal_map(size_t s): m(std::make_unique<T[]>(s)), size(s) {}

    T& operator[](literal i) {
        // TODO: maybe have a different access pattern, or different
        // iteration pattern, because of potential cache misses. Do we
        // group (x, -x) closely, or (x, x+1) closely?
        int index = literal_to_index(i);
        TRACE("literal_map:operator[](%d), accessing elt: %d\n", i, index);
        return m[index];
    }
    T operator[](literal i) const {
        // TODO: maybe have a different access pattern, or different
        // iteration pattern, because of potential cache misses. Do we
        // group (x, -x) closely, or (x, x+1) closely?
        int index = literal_to_index(i);
        TRACE("literal_map:operator[]const(%d), accessing elt: %d\n", i, index);
        return m[index];
    }

    
    struct key_iterator {
        literal current_value;
        key_iterator& operator++() {
            ++current_value;
            if (!current_value) { current_value++; }
            return *this;
        };
        bool operator==(const key_iterator& other) const {
            return current_value == other.current_value;
        }
        bool operator!=(const key_iterator& other) const {
            return !(*this==other);
        }
        literal operator*() const {
            return current_value;
        }
    };
    key_iterator key_begin() const {
        return {-(size/2)};
    }
    key_iterator key_end() const {
        return {(size/2)+1};
    }

    struct pair_iterator {
        int current_literal;
        const literal_map<T>& my_map;
        std::pair<literal, T> operator*() {
            return std::make_pair(current_literal, my_map[current_literal]);
        }
        bool operator!=(const pair_iterator& that) const {
            // TODO: compare the my_map fields too...
            return this->current_literal != that.current_literal;
        }
        pair_iterator& operator++() {
            if (current_literal < (my_map.size/2)+1) {
                ++current_literal;
            }
            return *this;
        }
    };

    pair_iterator pair_begin() const {
        return {-(size/2), *this};
    }
    pair_iterator pair_end() const {
        return {(size/2)+1, *this};
    }
};

template <typename T>
class index_sequence {
    T& t;
    public:
    index_sequence(T& t): t(t) {};
    auto begin() { return t.key_begin(); }
    auto end() { return t.key_end(); }
};

template <typename T>
index_sequence<T> key_iter(T& t) { return index_sequence<T>(t); }

template <typename T>
class pair_sequence {
    const T& t;
    public:
    pair_sequence(const T& t): t(t) {};
    auto begin() const { return t.pair_begin(); }
    auto end() const { return t.pair_end(); }
};

template <typename T>
pair_sequence<T> pair_iter(T& t) { return pair_sequence<T>(t); }

#endif
