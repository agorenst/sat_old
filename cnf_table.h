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
    const int max_size;
    const int max_clause_count;
    const int max_literal_count;
    int size = 0;
    int clause_count = 0;

    std::unique_ptr<literal[]> core_map;

    typedef literal* raw_iterator;
    struct clause {
        raw_iterator start, finish;
    };
    typedef clause* clause_iterator;

    std::unique_ptr<clause[]> clauses;

    cnf_table(size_t _max_size, size_t _max_clause_count, size_t max_literal_count):
        max_size(_max_size*10),
        max_clause_count(_max_clause_count*4),
        max_literal_count(max_literal_count),
        core_map(std::make_unique<literal[]>(max_size)),
        clauses(std::make_unique<clause[]>(max_clause_count))
    {}

    // Used for initializing the cnf_table.
    template <typename ClauseType>
    clause_iterator insert_clause(const ClauseType& c) {

        raw_iterator clause_start = core_map.get() + size;
        for (auto x : c) {
            core_map[size++] = x;
        }
        raw_iterator clause_end = core_map.get() + size;

        ASSERT(clause_end <= core_map.get()+max_size);

        clauses[clause_count++] = {clause_start, clause_end};

        return clauses.get()+(clause_count-1);
    }

    clause_iterator clause_begin() const { return clauses.get(); }
    clause_iterator clause_end() const { return clauses.get() + clause_count; }

    // If we're learning a clause, we may want to see if it would actually
    // fit in our database...
    int remaining_size() const { return max_size - size; }
    int remaining_clauses() const { return max_clause_count - clause_count; }

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

// Relative to an assignment (the interface defined in assignment.h),
// we can determine if a clause is satisfied, etc...

template <typename ClauseIter, typename Assignment>
bool is_clause_satisfied(ClauseIter start, ClauseIter finish, const Assignment& a) {
    // NOTE: std::any_of returns false for empty sequence.
    // This is consistent with what we want, under self-reduction model of CNF.
    return std::any_of(start, finish, [&a](literal l) { return a.is_true(l); });
}
template <typename C, typename A>
bool is_clause_satisfied(const C& c, const A& a) {
    return is_clause_satisfied(begin(c), end(c), a);
}

template <typename ClauseIter, typename Assignment>
bool is_clause_unsatisfied(ClauseIter start, ClauseIter finish, const Assignment& a) {
    // NOTE: all of returns true for empty sequence.
    // This is USUALLY NOT what we want, under self-reduction model.
    return std::all_of(start, finish, [&a](literal l) { return a.is_false(l); });
}
template <typename C, typename A>
bool is_clause_unsatisfied(const C& c, const A& a) {
    return is_clause_unsatisfied(begin(c), end(c), a);
}

template <typename CNFIter, typename Assignment>
bool is_cnf_satisfied(CNFIter start, CNFIter finish, const Assignment& a) {
    return std::all_of(start, finish, [&a](auto cl) {
        return is_clause_satisfied(begin(cl), end(cl), a);
    });
}
template <typename C, typename A>
bool is_cnf_satisfied(const C& c, const A& a) {
    return is_cnf_satisfied(begin(c), end(c), a);
}

template <typename CNFIter, typename Assignment>
CNFIter has_conflict(CNFIter start, CNFIter finish, const Assignment& a) {
    return std::find_if(start, finish, [&a](auto cl) {
        return is_clause_unsatisfied(begin(cl), end(cl), a);
    });
}
template <typename C, typename A>
auto has_conflict(const C& c, const A& a) {
    return has_conflict(begin(c), end(c), a);
}

// Absolutely dead-stupid way of finding unit clauses...
template <typename C, typename A>
literal is_unit_clause_implying(const C& c, const A& a) {
    if (is_clause_satisfied(c, a)) { return 0; }
    if (is_clause_unsatisfied(c, a)) { return 0; }

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
    std::for_each(cnf.clauses.get(), cnf.clauses.get()+cnf.clause_count, [&](const cnf_table::clause& cit) {
        o << cit << std::endl;
    });
    return o;
}

#endif
