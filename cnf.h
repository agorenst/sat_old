#ifndef CNF_TABLE_H
#define CNF_TABLE_H

#include "literal_map.h"
#include "small_set.h"
#include "debug.h"

#include <memory>
#include <iostream>
#include <algorithm>

class cnf {
public:
    // The core types
    typedef literal* raw_iterator;
    struct clause {
        raw_iterator start, finish;
    };
    typedef clause* clause_iterator;


    int max_literal_count;
    int raw_data_max;
    int raw_data_count = 0;
    int clauses_max;
    int clauses_count = 0;

    std::unique_ptr<literal[]> raw_data;
    std::unique_ptr<clause[]> clauses;
    // If a datatype wants to register for when we remap our clause array...
    std::vector<std::function<void(clause_iterator,clause_iterator,int)>> resizers;
    std::vector<std::function<void(int*, int, clause_iterator)>> remappers;

    cnf(int MaxSize, int ClauseCount, size_t LiteralCount):
        max_literal_count(LiteralCount),
        raw_data_max(MaxSize),
        clauses_max(ClauseCount),
        raw_data(std::make_unique<literal[]>(MaxSize)),
        clauses(std::make_unique<clause[]>(ClauseCount))
    {}


    // Used for initializing the cnf.
    template <typename ClauseType>
    clause_iterator insert_clause(const ClauseType& c) {

        raw_iterator clause_start = raw_data.get() + raw_data_count;
        for (auto x : c) {
            raw_data[raw_data_count++] = x;
        }
        raw_iterator clause_end = raw_data.get() + raw_data_count;

        ASSERT(clause_end <= raw_data.get()+raw_data_max);

        clauses[clauses_count++] = {clause_start, clause_end};

        return clauses.get()+(clauses_count-1);
    }

    clause_iterator clause_begin() const { return clauses.get(); }
    clause_iterator clause_end() const { return clauses.get() + clauses_count; }

    // If we're learning a clause, we may want to see if it would actually
    // fit in our database...
    int remaining_size() const { return raw_data_max - raw_data_count; }
    int remaining_clauses() const { return clauses_max - clauses_count; }

    template<typename Assignment>
    bool confirm_is_implied_unit(const Assignment& a, literal l) {
        for (auto cit = clause_begin(); cit != clause_end(); ++cit) {
            auto implied = is_unit_clause_implying(cit, a);
            if (implied && implied == l) {
                trace("found implication reason: ", cit, "\n");
                return true;
            }
            if (implied) {
                trace("found implied: ", implied, " from clause ", cit, "\n");
            }
        }
        return false;
    }

    // Want to make sure that the CNF always has some reasonable guarantees...
    bool sanity_check() {
        for (auto cit = clause_begin(); cit != clause_end(); ++cit) {
            small_set<literal> explicit_set;
            explicit_set.insert(cit->start, cit->finish);
            if (explicit_set.size() != std::distance(cit->start, cit->finish)) {
                trace("ASSERT: found a bad clause: ", cit, " != ", explicit_set, "\n");
                return false;
            }
        }
        return true;
    }

    // This one is trickier, because clauses point into us.
    void resize_raw_data() {
        auto base = raw_data.get();
        int new_size = raw_data_max * 2;
        std::unique_ptr<literal[]> new_data = std::make_unique<literal[]>(new_size);
        for (int i = 0; i < raw_data_count; ++i) {
            new_data[i] = raw_data[i];
        }

        // We update the clauses.
        auto new_base = new_data.get();
        for (int i = 0; i < clauses_count; ++i) {
            auto new_start = (clauses[i].start - base) + new_base;
            auto new_finish = (clauses[i].finish - base) + new_base;
            clauses[i] = {new_start, new_finish};
        }

        raw_data_max = new_size;
        std::swap(new_data, raw_data);
    };

    // This invalidates any ckeys that may exist "in the wild".
    void resize_clauses() {
        int new_size = clauses_max * 2;
        std::unique_ptr<clause[]> new_data = std::make_unique<clause[]>(new_size);

        // copy the data over...
        for (int i = 0; i < clauses_count; ++i) {
            new_data[i] = clauses[i];
        }

        // Call all the remappers. Here we're just "rebasing" all the
        // old pointers.
        for (auto m : resizers) {
            m(clauses.get(), new_data.get(), new_size);
        }

        clauses_max = new_size;
        // And swap, in part to free the old memory.
        std::swap(new_data, clauses);
    };

    void consider_resizing() {
        if (clauses_count * 2 > clauses_max) {
            resize_clauses();
        }
        if (raw_data_count * 2 > raw_data_max) {
            resize_raw_data();
        }
    }

    void remap_clauses(int* m, int new_clause_count) {
        for (auto cit = clause_begin(); cit != clause_end(); ++cit) {
            int old_index = cit - clause_begin();
            int new_index = m[old_index];
            if (new_index == -1) { continue; } // this clause is deleted...
            ASSERT(new_index <= old_index);
            clauses[new_index] = clauses[old_index];
        }
        clauses_count = new_clause_count;

        for (auto r : remappers) {
            r(m, clauses_count, clause_begin());
        }
    }
};

// Iterating over a CNF means iterating over its clauses.
cnf::clause_iterator end(const cnf& c) { return c.clause_end(); }
cnf::clause_iterator begin(const cnf& c) { return c.clause_begin(); }

// We want to be able to iterate over clauses, or the clause iterators themselves.
// Perhaps equating clause iterators and clauses are not ideal, but...
cnf::raw_iterator begin(const cnf::clause& c) { return c.start; }
cnf::raw_iterator end(const cnf::clause& c) { return c.finish; }
cnf::raw_iterator begin(const cnf::clause_iterator& c) { return c->start; }
cnf::raw_iterator end(const cnf::clause_iterator& c) { return c->finish; }

bool clause_contains(cnf::clause_iterator cit, literal l) {
    return std::find(begin(cit), end(cit), l) != end(cit);
}


// In the backtrack loop, we have a clause against which
// we resolve many others. So it's useful to have a clause
// that can grow or shrink as needed. Note that it can't
// be bigger than #literals.
class flexsize_clause {
    public:
    std::unique_ptr<literal[]> raw_data;
    cnf::clause my_clause;
    public:
    flexsize_clause(const cnf& c):
        raw_data(std::make_unique<literal[]>(c.max_literal_count)),
        my_clause{raw_data.get(), raw_data.get()}
    {}
    void adopt(cnf::clause_iterator c) {
        TRACE("Adopting: ", c, "\n");
        my_clause.finish = std::copy(c->start, c->finish, my_clause.start);
    }
    void resolve(cnf::clause_iterator c, literal l) {
        trace(*this, " ", c, " :  ", l, "\n");
        ASSERT(contains(l));
        ASSERT(clause_contains(c, -l));
        erase(l);
        std::for_each(begin(c), end(c), [&](literal r) {
            if (r == -l) { return; }
            if (contains(r)) { return; }
            *my_clause.finish = r;
            my_clause.finish++;
        });
    }

    bool contains(literal l) const {
        return std::find(begin(my_clause), end(my_clause), l) != end(my_clause);
    }
    void erase(literal l) {
        ASSERT(contains(l));
        auto it = std::find(begin(my_clause), end(my_clause), l);
        ASSERT(it != end(my_clause));
        ASSERT(std::find(std::next(it), end(my_clause), l) == end(my_clause));
        my_clause.finish--;
        std::swap(*it, *my_clause.finish);
    }
    void insert(literal l) {
        ASSERT(!contains(l));
        *my_clause.finish = l;
        my_clause.finish++;
    }
    int size() { return my_clause.finish - my_clause.start; }
    void clear() { my_clause.finish = my_clause.start; }
};

std::ostream& operator<<(std::ostream& o, const flexsize_clause& c) {
    std::for_each(begin(c.my_clause), end(c.my_clause), [&](literal l) {
        o << l << " ";
    });
    return o;
}


cnf::raw_iterator begin(const flexsize_clause& c) { return c.my_clause.start; }
cnf::raw_iterator end(const flexsize_clause& c) { return c.my_clause.finish; }


// Helper functions over clauses and CNF tables.
// Everything is templated because we want to be compatible with any object
// that implements the appropriate "interface" (a clause is a seq of literals,
// and a cnf is a seq of clauses).

// A clause is trivial if it contains the negation of
// one of its own literals.
template <typename ClauseIter>
bool is_trivial_clause(ClauseIter start, ClauseIter finish) {
    return std::any_of(start, finish, [&](literal l) {
        return std::find(start, finish, -l) != finish;
    });
}

int size(const cnf::clause& cit) {
    return end(cit) - begin(cit);
}

int size(const cnf::clause_iterator cit) {
    int d = std::distance(begin(cit), end(cit));
    ASSERT(d >= 0);
    return d;
}


template<typename C, typename A>
bool clause_sat(const C& c, const A& a) {
    // if range is empty, return false. Consistent with notion of unsat clause.
    return std::any_of(begin(c), end(c), [&a](literal l) { return a.is_true(l); });
}

template<typename C, typename A>
bool clause_unsat(const C& c, const A& a) {
    // This is the fast version.
    for (auto x : c) {
        if (!a.is_false(x)) { return false; }
    }
    return true;
}

template<typename A>
bool is_cnf_sat(const cnf& c, const A& a) {
    return std::all_of(begin(c), end(c), [&a](auto cl) {
        return clause_sat(&cl, a);
    });
}

template<typename A>
auto has_conflict(const cnf& c, const A& a) {
    return std::find_if(begin(c), end(c), [&a](auto cl) {
        return clause_unsat(cl, a);
    });
}

// Absolutely dead-stupid way of finding unit clauses...
template<typename C, typename A>
literal clause_implies(const C& c, const A& a) {
    if (clause_sat(c, a)) { return 0; }
    if (clause_unsat(c, a)) { return 0; }

    auto l_ptr = std::find_if(begin(c), end(c), [&](literal l) {
        return a.is_unassigned(l);
    });
    auto nextl = std::find_if(l_ptr+1, end(c), [&](literal l) {
        return a.is_unassigned(l);
    });
    ASSERT(l_ptr != end(c));
    if (nextl == end(c)) { return *l_ptr; }
    return 0;
}

template<typename C, typename A>
std::pair<literal, cnf::clause_iterator> find_unit(const C& c, const A& a) {
    auto implying_clause = std::find_if(begin(c), end(c), [&](const auto& cl) {
        return clause_implies(cl, a) != 0;
    });
    if (implying_clause != end(c)) {
        literal implied = clause_implies(implying_clause, a);
        return std::make_pair(implied, implying_clause);
    }
    return std::make_pair(0, nullptr);
}

// Printing statements, mainly for debugging.
std::ostream& operator<<(std::ostream& o, const cnf::clause& c) {
    std::for_each(begin(c), end(c), [&](literal l) {
        o << l << " ";
    });
    return o;
}

std::ostream& operator<<(std::ostream& o, const cnf::clause_iterator& c) {
    return (o << *c);
}

std::ostream& operator<<(std::ostream& o, const cnf& c) {
    std::for_each(c.clauses.get(), c.clauses.get()+c.clauses_count, [&](const cnf::clause& cit) {
        o << cit << std::endl;
    });
    return o;
}

#endif
