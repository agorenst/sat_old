#ifndef SMALL_SET_H
#define SMALL_SET_H
#include <vector>
#include <algorithm>
template <typename T>
class small_set {
    std::vector<T> data;
    public:
    void insert(const T& t) {
        if (contains(t)) { return; }
        data.push_back(t);
    }
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
};

template <typename T>
void swap_elt(small_set<T>& from, small_set<T>& to, const T t) {
    from.erase(t);
    to.insert(t);
}

#endif
