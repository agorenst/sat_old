#ifndef WATCHED_LITERALS_H
#define WATCHED_LITERALS_H

#include "cnf_table.h"
#include "literal_map.h"

#include <iostream>

#include <map>
#include <queue>
#include <set>

class watched_literals {
    public:
    const cnf_table& cnf;
    struct watch_pair {
        literal watch1 = 0;
        literal watch2 = 0;
    };

    typedef std::map<literal, std::set<cnf_table::clause_iterator>> lits_to_clauses_t;
    typedef std::map<cnf_table::clause_iterator, watch_pair> clauses_to_lits_t;
    lits_to_clauses_t clauses_watched_by;
    clauses_to_lits_t literals_watching;

    watched_literals(const cnf_table& rt):
        cnf(rt)
        //clauses_watched_by(rt.max_literal_count)
    {}

    void initialize() {

        // Wipe out any old data
        clauses_watched_by.clear();
        //for (literal l : clauses_watched_by) {
        //    clauses_watched_by[l].clear();
        //}
        literals_watching.clear();

        // Initialize the watching pairs...
        for (cnf_table::clause_iterator it = cnf.clauses.get();
             it != cnf.clauses.get() + cnf.clause_count;
             ++it) {
            // need to have at least 2 literals to watch...
            ASSERT(end(it)-begin(it) >= 2);

            literal first = *begin(it);
            literal second = *std::next(begin(it));

            // Initialize the "bidirectional map"
            literals_watching[it] = {first, second};
            clauses_watched_by[first].insert(it);
            clauses_watched_by[second].insert(it);
        }
    }

    // This is probably something we can speed up a lot...
    template <typename AssignmentClass>
    literal find_new_literal(const cnf_table::clause_iterator& c,
                             const AssignmentClass& a,
                             literal negated,
                             literal other) {
        for (literal x : c) {
            if (x == negated) { continue; }
            if (x == other) { continue; }
            if (a.is_true(x)) { return x; }
        }
        for (literal x : c) {
            if (x == negated) { continue; }
            if (x == other) { continue; }
            if (!a.is_false(x)) { return x; }
        }
        return 0;
    }

    // The main work-loop: we've just added set_true to a, and now
    // we want to make sure all the induced unit clauses are properly
    // propogated.
    template <typename AssignmentClass>
    bool propogate_negation(AssignmentClass& a, literal set_true) {
        literal L = -set_true;
        std::queue<literal> worklist;
        worklist.push(L);
        while(worklist.size() > 0) {
            literal l = worklist.front(); worklist.pop();
            auto clauses_to_update = clauses_watched_by[l];

            for (cnf_table::clause_iterator c : clauses_to_update) {

                // Simple case: if the clause is already satisfied,
                // we can safely let it's other watcher (us) be "false"
                // without updating anything else.
                watch_pair& watchers = literals_watching[c];
                if (a.is_true(watchers.watch1)) {
                    continue;
                }
                if (a.is_true(watchers.watch2)) {
                    std::swap(watchers.watch1, watchers.watch2);
                    continue;
                }

                // Conflict case: This depends on us maintaining
                // invariants. If our other watcher was already set
                // to false, then we have a conflict.
                if (a.is_false(watchers.watch1) && a.is_false(watchers.watch2)) {
                    return false;
                }

                // For convenience, parse out the watcher pair into the watcher
                // we've negated, and the "other" one.
                literal& negated = watchers.watch1 == l ? watchers.watch1 : watchers.watch2;
                literal& other = watchers.watch1 == l ? watchers.watch2 : watchers.watch1;
                ASSERT(!a.is_true(other) && !a.is_false(other));
                ASSERT(a.is_false(negated));

                literal new_literal = find_new_literal(c, a, negated, other);

                // Unit case: we MUST assign "other" to be true.
                if (new_literal == 0) {
                    a.set_true(other);
                    worklist.push(-other);
                }
                // Continuation case: we update negated.
                else {
                    ASSERT(clauses_watched_by[negated].find(c) != clauses_watched_by[negated].end());
                    ASSERT(clauses_watched_by[new_literal].find(c) == clauses_watched_by[new_literal].end());

                    clauses_watched_by[negated].erase(c);
                    clauses_watched_by[new_literal].insert(c);
                    // update the pair.
                    negated = new_literal;
                }
            }
        }
        // we got through all unit prop without any conflict. Hooray.
        return true;
    }
};

std::ostream& operator<<(std::ostream& o, const watched_literals::lits_to_clauses_t& w) {
    for (const auto& lit_clause_pair : w) {
        o << lit_clause_pair.first << " watching: ";
        std::for_each(begin(lit_clause_pair.second), end(lit_clause_pair.second), [&](cnf_table::clause_iterator it) {
            o << "(" << it << ") ";
        });
        o << std::endl;
    }
    return o;
}

std::ostream& operator<<(std::ostream& o, const watched_literals::clauses_to_lits_t& w) {
    for (const auto& clause_to_watchers : w) {
        o << clause_to_watchers.first << " watched by: " << "{ ";
        o << clause_to_watchers.second.watch1 << ", " << clause_to_watchers.second.watch2 << "}" << std::endl;
    }
    return o;
}

std::ostream& operator<<(std::ostream& o, const watched_literals& w) {
    o << w.clauses_watched_by << std::endl;
    o << w.literals_watching << std::endl;
    return o;
}

#endif
