#ifndef COLLECTION_PARTITION_H
#define COLLECTION_PARTITION_H

#include <memory>
#include <iostream>

using namespace std;


#ifdef COLLECTION_PARTITION_DBG
#include <cassert>
#define ASSERT(x) assert(x)
#else
#define ASSERT(x)
#endif


// An exercise in using unique ptrs...
// TODO: look at resulting assembly: are unique pointers worth the hassle?
template <typename T>
struct collection_partition {
    struct node {
        const T t;
        std::unique_ptr<node> next;
        node(const T t, std::unique_ptr<node>&& next): t(t), next(std::move(next)) {}
    };

    std::unique_ptr<node> head;

    // Linus would call this tasteless. I'm just trying to get things to work...
    void insert_new(const T t) {
        if (head == nullptr || head->t > t) {
            head = std::make_unique<node>(t, std::move(head));
        }
        else {
            node* visitor = head.get();
            while (visitor->next && visitor->next->t < t) {
                visitor = visitor->next.get();
            }
            visitor->next = std::make_unique<node>(t, std::move(visitor->next));
        }
    }

    void insert_node(std::unique_ptr<node> to_insert) {
        cout << "Inserting node" << endl;
        if (head == nullptr) {
            cout << "head case" << endl;
            head = std::move(to_insert);
        }
        else if (to_insert->t < head->t) {
            to_insert->next = std::move(head);
            head = std::move(to_insert);
        }
        else {
            node* visitor = head.get();
            while (visitor->next && to_insert->t < visitor->next->t) {
                visitor = visitor->next.get();
            }
            ASSERT(visitor->t > to_insert->t && (!visitor->next || visitor->next->t < to_insert->t));
            if (visitor->next && visitor->next->next) {
                to_insert->next = std::move(visitor->next->next);
            }
            visitor->next = std::move(to_insert);
        };
    }

    std::unique_ptr<node> extract(const T t) {
        ASSERT(head);
        if (head->t == t) {
            std::unique_ptr<node> to_ret = std::move(head);
            head = std::move(to_ret->next);
            to_ret->next = nullptr;
            return to_ret;
        }
        node* visitor = head.get();
        while (visitor->next->t < t) {
            visitor = visitor->next.get();
        }
        ASSERT(visitor->next->t == t);
        std::unique_ptr<node> to_ret = std::move(visitor->next);
        visitor->next = std::move(to_ret->next);
        to_ret->next = nullptr;
        return to_ret;
    }

    bool contains(const T t) const {
        node* visitor = head.get();
        while (visitor && visitor->t < t) {
            visitor = visitor->next.get();
        }
        return visitor && visitor->t == t;
    }

    void print(std::ostream& o) const {
        node* visitor = head.get();
        o << "{ ";
        while (visitor) {
            o << visitor->t << " ";
            visitor = visitor->next.get();
        }
        o << "}";
    }

    struct iterator {
        node* visitor;
        iterator& operator++() {
            if (visitor) {
                visitor = visitor->next.get();
            }
            return *this;
        }
        T operator*() {
            return visitor->t;
        }
        bool operator!=(const iterator& that) const {
            return this->visitor != that.visitor;
        }
    };

    iterator begin() {
        return iterator{head.get()};
    }
    iterator end() {
        return iterator{nullptr};
    }
};

template <typename T>
std::ostream& operator<<(std::ostream& o, const collection_partition<T>& c) {
    c.print(o);
    return o;
}

template <typename T>
void swap_elt(collection_partition<T>& from, collection_partition<T>& to, const T elt) {
    cout << "swapping " << from << to << elt << endl;
    to.insert_node(from.extract(elt));
    cout << "done swapping " << from << to << endl;
}


#endif
