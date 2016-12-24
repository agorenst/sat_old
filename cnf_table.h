#ifndef CNF_TABLE_H
#define CNF_TABLE_H

#include "literal_map.h"
#include "simple_parser.h"

#include <set>
#include <memory>
#include <iostream>
#include <algorithm>

#ifdef CNF_TABLE_DBG
#include <cassert>
#define ASSERT(x) assert(x)
#else
#define ASSERT(x)
#endif

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

    // TODO: shouldn't use std::set here, I don't think.
    literal_map<std::set<clause_iterator>> literals_to_clauses;

    cnf_table(size_t max_size, size_t max_clause_count, size_t max_literal_count):
        max_size(max_size),
        max_clause_count(max_clause_count),
        max_literal_count(max_literal_count),
        core_map(std::make_unique<literal[]>(max_size)),
        clauses(std::make_unique<clause[]>(max_clause_count)),
        literals_to_clauses(max_literal_count)
    {}

    // Used for initializing the cnf_table.
    template <typename ClauseType>
    void insert_clause(const ClauseType& c) {
        raw_iterator clause_start = core_map.get() + size;
        for (auto x : c) {
            core_map[size++] = x;
        }
        raw_iterator clause_end = core_map.get() + size;

        ASSERT(clause_end <= end(core_map));

        clauses[clause_count++] = {clause_start, clause_end};
        for (auto x : c) {
            literals_to_clauses[x].insert(clauses.get()+(clause_count-1));
        }
    }

    bool check_invariants();
};

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


bool cnf_table::check_invariants() {
    // For every literal in each clause, that literal knows
    // it's in that clause.
    for (clause_iterator cit = clauses.get();
            cit != clauses.get() + clause_count;
            ++cit) {
        for (literal l : *cit) {
            if (literals_to_clauses[l].find(cit) == literals_to_clauses[l].end()) {
                return false;
            }
        }
    }
    // For every literal, every clause that literal thinks it's in
    // actually contains that literal.
    for (literal l : literals_to_clauses) {
        for (clause_iterator cit : literals_to_clauses[l]) {
            auto find_result = std::find(begin(cit), end(cit), l);
            if (find_result == end(cit)) {
                return false;
            }
        }
    }
    return true;
};

#endif
