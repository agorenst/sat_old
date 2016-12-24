#ifndef WATCHED_LITERALS_H
#define WATCHED_LITERALS_H

#include "cnf_table.h"
#include "literal_map.h"

#include <iostream>

#include <map>
#include <queue>
#include <set>

#ifdef WATCHED_VERBOSE
#include <cstdio>
#define TRACE(...) printf(__VA_ARGS__)
#else
#define TRACE(...)
#endif

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
    {}

    void initialize() {

        // Wipe out any old data
        clauses_watched_by.clear();
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

    template <typename AssignmentClass>
    bool is_sat(const AssignmentClass& a) const {
        for (auto clause_watchers : literals_watching) {
            const watch_pair wp = clause_watchers.second;
            if (!a.is_true(wp.watch1) && !a.is_true(wp.watch2)) {
                return false;
            }
        }
        return true;
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
            if (a.is_true(x)) {
                //std::cout << "Returning " << x << " as a set-true literal" << std::endl;
                return x;
            }
        }
        for (literal x : c) {
            if (x == negated) { continue; }
            if (x == other) { continue; }
            if (!a.is_false(x)) {
                //std::cout << "Returning " << x << " as an unset literal" << std::endl;
                return x;
            }
        }
        return 0;
    }

    template <typename AssignmentClass>
    bool check_invariants(const AssignmentClass& a) {

        // each watch literal better be distinct from its partner.
        for (auto&& clause_watchers : literals_watching) {
            auto wp = clause_watchers.second;
            if (wp.watch1 == wp.watch2) {
                return false;
            }
        }


        // These next two for loops make sure all our
        // data structures are consistent with each other.
        for (auto&& lit_clauses : clauses_watched_by) {
            auto l = lit_clauses.first;
            auto clause_set = lit_clauses.second;

            // The clause better understand it's being
            // watched by both of these literals.
            for (auto c : clause_set) {
                auto wp = literals_watching[c];
                if (wp.watch1 != l && wp.watch2 != l) {
                    return false;
                }
            }
        }
        for (auto&& clauses_watchers : literals_watching) {
            auto cit = clauses_watchers.first;
            auto wp = clauses_watchers.second;

            // The watchers better know they're watching this clause
            if (clauses_watched_by[wp.watch1].find(cit) ==
                clauses_watched_by[wp.watch1].end()) {
                return false;
            }
            if (clauses_watched_by[wp.watch2].find(cit) ==
                clauses_watched_by[wp.watch2].end()) {
                return false;
            }
        }

        // next, we want to make sure that our data structure
        // is consistent with the invariants induced by the
        // assignment.
        for (auto&& clause_watchers : literals_watching) {
            auto cit = clause_watchers.first;
            auto wp = clause_watchers.second;
            // if both our watched literals are false, our whole
            // clause better be false.
            if (a.is_false(wp.watch1) && a.is_false(wp.watch2)) {
                if (std::any_of(begin(cit), end(cit), [&](literal l) {
                    return !a.is_false(l);
                })) {
                    return false;
                }
            }
        }
        return true;
    }

    // The main work-loop: we've just added set_true to a, and now
    // we want to make sure all the induced unit clauses are properly
    // propogated.
    template <typename AssignmentClass>
    bool apply_literal(AssignmentClass& a, literal set_true) {
        ASSERT(check_invariants(a));
        literal L = -set_true;
        std::queue<literal> worklist;
        worklist.push(L);
        while(worklist.size() > 0) {
            // l is a literal that's been induced false...
            literal l = worklist.front(); worklist.pop();
            //std::cout << "Setting true: " << -l << std::endl;
            a.set_true(-l);
            auto clauses_to_update = clauses_watched_by[l];

            for (cnf_table::clause_iterator c : clauses_to_update) {
                //std::cout << "Considering watched clause: " << c << std::endl;

                // Simple case: if the clause is already satisfied,
                // we can safely let it's other watcher (us) be "false"
                // without updating anything else.
                watch_pair& watchers = literals_watching[c];
                //std::cout << "Watch pair: { " << watchers.watch1 << ", " << watchers.watch2 << " }" << std::endl;
                if (a.is_true(watchers.watch1)) {
                    //std::cout << "Simple case, satisfied by: " << watchers.watch1 << std::endl;
                    continue;
                }
                if (a.is_true(watchers.watch2)) {
                    //std::cout << "Simple case, satisfied by: " << watchers.watch2 << std::endl;
                    std::swap(watchers.watch1, watchers.watch2);
                    continue;
                }

                // Conflict case: This depends on us maintaining
                // invariants. If our other watcher was already set
                // to false, then we have a conflict.
                if (a.is_false(watchers.watch1) && a.is_false(watchers.watch2)) {
                    //std::cout << "We assume this clause is false because both watchers are false" << std::endl;
                    ASSERT(check_invariants(a));
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
                    //std::cout << "Did not find a new literal, entering unit case for setting: " << other << " true." << std::endl;
                    worklist.push(-other);
                }

                // Continuation case: we update negated.
                else {
                    //std::cout << "Continuation case, updating watch information" << std::endl;
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
        //std::cout << "Prop completed without conflict, returning true" << std::endl;
        ASSERT(check_invariants(a));
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
