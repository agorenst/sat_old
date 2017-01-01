#ifndef WATCHED_LITERALS_H
#define WATCHED_LITERALS_H

#include "cnf_table.h"
#include "literal_map.h"
#include "clause_map.h"
#include "small_set.h"
#include "collection_partition.h"

#include <iostream>

#include <queue>


#include <cassert>

#ifdef WATCHED_VERBOSE
#include <cstdio>
#define TRACE(...) printf(__VA_ARGS__)
#else
#define TRACE(...)
#endif

class watched_literals {
    public:
    cnf_table& cnf;
    struct watch_pair {
        literal watch1 = 0;
        literal watch2 = 0;
    };

    // TODO: fix, these are *awful* names.
    typedef literal_map<small_set<cnf_table::clause_iterator>> lits_to_clauses_t;
    lits_to_clauses_t clauses_watched_by;
    typedef clause_map<watch_pair> clauses_to_lits_t;
    clauses_to_lits_t literals_watching;

    watched_literals(cnf_table& rt):
        cnf(rt),
        clauses_watched_by(rt.max_literal_count*2),
        literals_watching(cnf.max_clause_count, cnf.clauses.get())
    {}

    void watch_new_clause(cnf_table::clause_iterator it) {
        ASSERT(end(it)-begin(it) >= 2);
        literal first = *begin(it);
        literal second = *std::next(begin(it));

        // Initialize the "bidirectional map"
        literals_watching[it] = {first, second};
        clauses_watched_by[first].insert(it);
        clauses_watched_by[second].insert(it);
    }

    template <typename Assignment>
    void watch_new_clause(cnf_table::clause_iterator it, const Assignment& a) {
        ASSERT(end(it)-begin(it) >= 2);
        literal first = *begin(it);
        literal second = *std::next(begin(it));

        // Initialize the "bidirectional map"
        literals_watching[it] = {first, second};
        clauses_watched_by[first].insert(it);
        clauses_watched_by[second].insert(it);

        literal real_first = find_new_literal(it, a, first, second);
        if (real_first) {
            clauses_watched_by[real_first].insert(it);
            clauses_watched_by[first].erase(it);
        }
        else {
            real_first = first;
        }

        literal real_second = find_new_literal(it, a, real_first, second);
        if (real_second) {
            clauses_watched_by[real_second].insert(it);
            clauses_watched_by[second].erase(it);
        }
        else {
            real_second = second;
        }

        literals_watching[it] = {real_first, real_second};

        //assert(!a.is_false(real_first) && !a.is_false(real_second));
    }

    void initialize() {
        // Initialize the watching pairs...
        for (cnf_table::clause_iterator it = iterate_clauses(cnf).begin();
             it != iterate_clauses(cnf).end();
             ++it) {
            watch_new_clause(it);
        }
    }

    template <typename AssignmentClass>
    bool is_sat(const AssignmentClass& a) const {
        for (int i = 0; i < cnf.clause_count; ++i) {
            cnf_table::clause_iterator it = cnf.clauses.get()+i;
            const watch_pair wp = literals_watching[it];
            if (!a.is_true(wp.watch1) && !a.is_true(wp.watch2)) {
                return false;
            }
        }
        //for (auto clause_watchers : literals_watching) {
        //    const watch_pair wp = clause_watchers.second;
        //    if (!a.is_true(wp.watch1) && !a.is_true(wp.watch2)) {
        //        return false;
        //    }
        //}
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
                return x;
            }
        }
        for (literal x : c) {
            if (x == negated) { continue; }
            if (x == other) { continue; }
            if (!a.is_false(x)) {
                return x;
            }
        }
        return 0;
    }

    template <typename AssignmentClass>
    bool check_invariants(const AssignmentClass& a) {

        // each watch literal better be distinct from its partner.
        for (int i = 0; i < cnf.clause_count; ++i) {
            cnf_table::clause_iterator it = cnf.clauses.get()+i;
            auto wp = literals_watching[it];
            ASSERT(wp.watch1 != wp.watch2);
            if (wp.watch1 == wp.watch2) {
                return false;
            }
        }


        // These next two for loops make sure all our
        // data structures are consistent with each other.
        for (auto&& l : key_iter(clauses_watched_by)) {
            //auto l = lit_clauses.first;
            bool has_error = false;
            for_each(begin(clauses_watched_by[l]),
                     end(clauses_watched_by[l]),
                     [&](cnf_table::clause_iterator c) {
                // The clause better understand it's being
                // watched by both of these literals.
                auto wp = literals_watching[c];
                ASSERT(wp.watch1 == l || wp.watch2 == l);
                if (wp.watch1 != l && wp.watch2 != l) {
                    has_error = true;
                }
            });
            ASSERT(!has_error);
            if (has_error) { return false; }
        }
        for (int i = 0; i < cnf.clause_count; ++i) {
            cnf_table::clause_iterator cit = cnf.clauses.get()+i;
            auto wp = literals_watching[cit];

            // The watchers better know they're watching this clause
            ASSERT(clauses_watched_by[wp.watch1].contains(cit));
            if (!clauses_watched_by[wp.watch1].contains(cit)) {
                return false;
            }
            ASSERT(clauses_watched_by[wp.watch2].contains(cit));
            if (!clauses_watched_by[wp.watch2].contains(cit)) {
                return false;
            }
        }

        // next, we want to make sure that our data structure
        // is consistent with the invariants induced by the
        // assignment.
        for (int i = 0; i < cnf.clause_count; ++i) {
            cnf_table::clause_iterator cit = cnf.clauses.get()+i;
            auto wp = literals_watching[cit];
            // if both our watched literals are false, our whole
            // clause better be false.
            if (a.is_false(wp.watch1) && a.is_false(wp.watch2)) {
                if (std::any_of(begin(cit), end(cit), [&](literal l) {
                    return !a.is_false(l);
                })) {
                    ASSERT(false);
                    return false;
                }
            }
        }
        return true;
    }

    // The main work-loop: we've just added set_true to a, and now
    // we want to make sure all the induced unit clauses are properly
    // propogated.
    template <typename AssignmentClass, typename Recorder>
    literal apply_literal(AssignmentClass& a, literal set_true, Recorder r) {
        ASSERT(check_invariants(a));
        literal L = -set_true;

        // TODO: better data structure should be here...
        std::queue<literal> worklist;
        worklist.push(L);
        while(worklist.size() > 0) {
            // l is a literal that's been induced false...
            literal l = worklist.front(); worklist.pop();
            a.set_true(-l);

            small_set<cnf_table::clause_iterator> clauses_to_iter = clauses_watched_by[l];
            for (auto c : clauses_to_iter) {
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
                    ASSERT(check_invariants(a));
                    // return the litetral that caused the conflict
                    return l; 
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
                    // record the implied variable, and the clause implying it.
                    *r = {other, c};

                    worklist.push(-other);
                }

                // Continuation case: we update negated.
                else {
                    ASSERT(clauses_watched_by[negated].contains(c));
                    ASSERT(!clauses_watched_by[new_literal].contains(c));

                    swap_elt(clauses_watched_by[negated],
                             clauses_watched_by[new_literal],
                             c);
                    // update the pair.
                    negated = new_literal;
                }
            }
        }
        // we got through all unit prop without any conflict. Hooray.
        ASSERT(check_invariants(a));
        return 0;
    }
};

//std::ostream& operator<<(std::ostream& o, const watched_literals::lits_to_clauses_t& w) {
//    for (const auto& lit_clause_pair : pair_iter(w)) {
//        o << lit_clause_pair.first << " watching: ";
//        std::for_each(begin(lit_clause_pair.second), end(lit_clause_pair.second), [&](cnf_table::clause_iterator it) {
//            o << "(" << it << ") ";
//        });
//        o << std::endl;
//    }
//    return o;
//}
//
//std::ostream& operator<<(std::ostream& o, const watched_literals::clauses_to_lits_t& w) {
//    for (const auto& clause_to_watchers : w) {
//        o << clause_to_watchers.first << " watched by: " << "{ ";
//        o << clause_to_watchers.second.watch1 << ", " << clause_to_watchers.second.watch2 << "}" << std::endl;
//    }
//    return o;
//}
//
//std::ostream& operator<<(std::ostream& o, const watched_literals& w) {
//    o << w.clauses_watched_by << std::endl;
//    o << w.literals_watching << std::endl;
//    return o;
//}

#endif
