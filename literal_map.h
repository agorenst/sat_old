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
    literal_map(size_t s): m(std::make_unique<T[]>(s)), size(s) {}
    T& operator[](literal i) {
        // TODO: maybe have a different access pattern, or different
        // iteration pattern, because of potential cache misses. Do we
        // group (x, -x) closely, or (x, x+1) closely?
        int index = ((2*std::abs(i))-1) - ((i < 0) ? 1 : 0);
        TRACE("literal_map:operator[](%d), accessing elt: %d\n", i, index);
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
    key_iterator begin() const {
        return {-(size/2)};
    }
    key_iterator end() const {
        return {(size/2)+1};
    }
};

