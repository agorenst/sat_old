#ifndef CNF_TABLE_H
#define CNF_TABLE_H

#include "literal_map.h"
#include "debug.h"

#include <memory>
#include <iostream>
#include <algorithm>

// The core CNF data structure. For now I'm slightly designing for efficiency,
// but I'm not sure if this is the "final" design. For now it's a big flat static
// array of values.
//
// The "core map" is a contiguous list of literals expressing the clauses. Clauses
// are defined by pairs of iterators into the core map, delimiting the beginning
// and ending of that clause.
//
// We (currently) statically allocate the memory we'd like up-front.
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
cnf_table::raw_iterator begin(const cnf_table::clause& c) { return c.start; }
cnf_table::raw_iterator end(const cnf_table::clause& c) { return c.finish; }
cnf_table::raw_iterator begin(const cnf_table::clause_iterator& c) { return c->start; }
cnf_table::raw_iterator end(const cnf_table::clause_iterator& c) { return c->finish; }


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
