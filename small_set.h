#ifndef SMALL_SET_H
#define SMALL_SET_H

#include <vector>
#include <algorithm>

template <typename T>
class small_set {
    // Because we use a vector underlying everything, we get value
    // semantics (and bad things like iterator invalidation) for free.
    std::vector<T> data;
    public:
    void insert(const T& t) {
        if (contains(t)) { return; }
        data.push_back(t);
    }

    template <typename Iter>
    void insert(Iter start, Iter finish) {
        std::for_each(start, finish, [&](const T& t) { this->insert(t); });
    }
    void clear() { data.clear(); }
    void erase(const T& t) {
        auto iter_to_remove = std::find(std::begin(data), std::end(data), t);
        ASSERT(iter_to_remove != std::end(data));
        std::swap(*iter_to_remove, *std::prev(std::end(data)));
        data.pop_back();
    }
    bool contains(const T& t) const {
        return std::find(std::begin(data), std::end(data), t) != std::end(data);
    }
    typename std::vector<T>::iterator begin() { return data.begin(); }
    typename std::vector<T>::iterator end() { return data.end(); }
    typename std::vector<T>::const_iterator begin() const { return data.begin(); }
    typename std::vector<T>::const_iterator end() const { return data.end(); }

    void print(std::ostream& o) const {
        std::for_each(std::begin(data), std::end(data), [&](const T& t) {
            o << t << " ";
        });
    }
    int size() const {
        return data.size();
    }
};

template <typename T>
void swap_elt(small_set<T>& from, small_set<T>& to, const T t) {
    from.erase(t);
    to.insert(t);
}

template <typename T>
std::ostream& operator<<(std::ostream& o, const small_set<T>& s) {
    s.print(o);
    return o;
}

#endif
