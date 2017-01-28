#ifndef CNF_TABLE_H
#define CNF_TABLE_H

#include "literal_map.h"
#include "small_set.h"
#include "debug.h"

#include <memory>
#include <iostream>
#include <algorithm>

// A CNF is a sequence of clauses.
// A clause is a sequence of literals.
//
// For efficiency/sanity, its useful to associate each clause with a unique key.
//
// In this implementation, we have a flat array of literals, and a sequence of
// [begin, end) pairs that define the clauses over that flat array.
//
// Thus, a clause is simply a pair of pointers, and the clause is uniquely
// identified by the address of that pair (we define it as a clause_iterator).
//
// Under models where we may reallocate memory, the clause iterators may be
// invalidated -- just be aware.

class cnf_table {
public:
    int clauses_max;
    int max_literal_count;
    int raw_data_max;
    int raw_data_count = 0;
    int clauses_count = 0;

    std::unique_ptr<literal[]> raw_data;

    typedef literal* raw_iterator;
    struct clause {
        raw_iterator start, finish;
    };
    typedef clause* clause_iterator;

    std::unique_ptr<clause[]> clauses;

    cnf_table(size_t _max_size, size_t _max_clause_count, size_t max_literal_count):
        raw_data_max(_max_size),
        clauses_max(_max_clause_count),
        max_literal_count(max_literal_count),
        raw_data(std::make_unique<literal[]>(raw_data_max)),
        clauses(std::make_unique<clause[]>(clauses_max))
    {}

    // If a datatype wants to register for when we remap our clause array...
    std::vector<std::function<void(clause_iterator, clause_iterator, int)>> resizers;
    std::vector<std::function<void(int*, int, clause_iterator)>> remappers;

    // Used for initializing the cnf_table.
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
cnf_table::clause_iterator end(const cnf_table& c) { return c.clause_end(); }
cnf_table::clause_iterator begin(const cnf_table& c) { return c.clause_begin(); }

// We want to be able to iterate over clauses, or the clause iterators themselves.
// Perhaps equating clause iterators and clauses are not ideal, but...
cnf_table::raw_iterator begin(const cnf_table::clause& c) { return c.start; }
cnf_table::raw_iterator end(const cnf_table::clause& c) { return c.finish; }
cnf_table::raw_iterator begin(const cnf_table::clause_iterator& c) { return c->start; }
cnf_table::raw_iterator end(const cnf_table::clause_iterator& c) { return c->finish; }


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

// The definition of resolving.
// For now we always return a small_set, but maybe we can do something else.
template <typename ClauseIterA, typename ClauseIterB>
small_set<literal> resolve(ClauseIterA start_a,
                           ClauseIterA finish_a,
                           ClauseIterB start_b,
                           ClauseIterB finish_b,
                           literal pivot) {
    small_set<literal> resolvent;

    // The pivot must be in a, but not its negation.
    ASSERT(std::find(start_a, finish_a, pivot) != finish_a);
    ASSERT(std::find(start_a, finish_a, -pivot) == finish_a);

    // The negation of the pivot must be in b, but not itself.
    ASSERT(std::find(start_b, finish_b, -pivot) != finish_b);
    ASSERT(std::find(start_b, finish_b, pivot) == finish_b);

    std::for_each(start_a, finish_a, [&](literal l) {
        if (l != pivot) resolvent.insert(l);
    });
    std::for_each(start_b, finish_b, [&](literal l) {
        if (l != -pivot) resolvent.insert(l);
    });

    ASSERT(!is_trivial_clause(std::begin(resolvent), std::end(resolvent)));
    return resolvent;
}
template <typename ClauseA, typename ClauseB>
small_set<literal> resolve(const ClauseA& ca, const ClauseB& cb, literal pivot) {
    return resolve(std::begin(ca), std::end(ca),
                   std::begin(cb), std::end(cb),
                   pivot);
}

int size(cnf_table::clause_iterator cit) {
    int d = std::distance(begin(cit), end(cit));
    ASSERT(d >= 0);
    return d;
}

// Relative to an assignment (the interface defined in assignment.h),
// we can determine if a clause is satisfied, etc...

template<typename A>
bool clause_sat(cnf_table::clause_iterator c, const A& a) {
    // if range is empty, return false. Consistent with notion of unsat clause.
    return std::any_of(begin(c), end(c), [&a](literal l) { return a.is_true(l); });
}

template<typename C, typename A>
bool clause_unsat(const C& c, const A& a) {
    // if range is empty, return true. Consistent with notion of unsat clause.
    return std::all_of(begin(c), end(c), [&a](literal l) {
        return a.is_false(l);
    });
}

template<typename A>
bool is_cnf_satisfied(const cnf_table& c, const A& a) {
    return std::all_of(begin(c), end(c), [&a](auto cl) {
        return clause_sat(&cl, a);
    });
}

template<typename A>
auto has_conflict(const cnf_table& c, const A& a) {
    return std::find_if(begin(c), end(c), [&a](auto cl) {
        return clause_unsat(cl, a);
    });
}

// Absolutely dead-stupid way of finding unit clauses...
template <typename C, typename A>
literal is_unit_clause_implying(const C& c, const A& a) {
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


template <typename A>
literal find_unit_in_cnf(const cnf_table& c, const A& a) {
    for (auto cit = begin(c);
         cit != end(c);
         ++cit) {
        literal u = is_unit_clause_implying(cit, a);
        if (u) { return u; }
    }
    return 0;
}

bool clause_contains(cnf_table::clause_iterator cit, literal l) {
    return std::find(begin(cit), end(cit), l) != end(cit);
}

// Printing statements, mainly for debugging.
std::ostream& operator<<(std::ostream& o, const cnf_table::clause& c) {
    std::for_each(begin(c), end(c), [&](literal l) {
        o << l << " ";
    });
    return o;
}

std::ostream& operator<<(std::ostream& o, const cnf_table::clause_iterator& c) {
    return (o << *c);
}

std::ostream& operator<<(std::ostream& o, const cnf_table& cnf) {
    std::for_each(cnf.clauses.get(), cnf.clauses.get()+cnf.clauses_count, [&](const cnf_table::clause& cit) {
        o << cit << std::endl;
    });
    return o;
}

#endif
