#include "cnf_table.h"
#include "small_set.h"
#include "simple_parser.h"
#include "decision_sequence.h"
#include "assignment.h"

#include <algorithm>
#include <iostream>

using namespace std;

// A clause is trivial if it contains the negation of
// one of its own literals.
template <typename ClauseIter>
bool is_trivial_clause(ClauseIter start, ClauseIter finish) {
    return std::any_of(start, finish, [&](literal l) {
        return std::find(start, finish, -l) != finish;
    });
}

// The definition of resolving.
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

    ASSERT(!is_trivial_clause(begin(resolvent), end(resolvent)));
    return resolvent;
}

template <typename ClauseIter, typename Assignment>
bool is_satisfied(ClauseIter start, ClauseIter finish, const Assignment& a) {
    return std::any_of(start, finish, [&a](literal l) { return a.is_true(l); });
}

template <typename ClauseIter, typename Assignment>
bool is_unsatisfied(ClauseIter start, ClauseIter finish, const Assignment& a) {
    return std::all_of(start, finish, [&a](literal l) { return a.is_false(l); });
}

template <typename CNFIter, typename Assignment>
bool is_cnf_satisfied(CNFIter start, CNFIter finish, const Assignment& a) {
    return std::all_of(start, finish, [&a](auto cl) {
        return is_satisfied(begin(cl), end(cl), a);
    });
}

template <typename CNFIter, typename Assignment>
CNFIter has_conflict(CNFIter start, CNFIter finish, const Assignment& a) {
    return std::find_if(start, finish, [&a](auto cl) {
        return is_unsatisfied(begin(cl), end(cl), a);
    });
}

bool solve(cnf_table& c) {
    TRACE("solve:enter\n");
    decision_sequence d(c.max_literal_count);
    const auto L = decision_sequence::LRSTATUS::LEFT;
    const auto R = decision_sequence::LRSTATUS::RIGHT;
    assignment a(c.max_literal_count);
    d.level = -1;
    //ASSERT(d.level == 0);

    small_set<literal> new_parent;
    std::vector<small_set<literal>> Parent(c.max_literal_count);
    for (;;) {

        // We do this before decisions because on some inputs
        // e.g., inputs/aim-100-1_6-yes1-4.cnf, we assert because
        // I guess we need to flip the variable before it's actually
        // SAT. So we'd make a 101st decision, null deref.
        if (is_cnf_satisfied(begin(c), end(c), a)) {
            TRACE("solve:exit, cnf satisfied\n");
            return true;
        }

        d.level++;
        TRACE("main iteration start\n");
        new_parent.clear();

        // Choose a new decision variable.
        literal next_decision = d.decisions[d.level];
        d.left_right[d.level] = L;
        //cout << "decision level: " << d.level << " made decision " << next_decision << endl;
        TRACE("decision level: %d made decision %d\n", d.level, next_decision);
        a.set_true(next_decision);

        //if (is_cnf_satisfied(begin(c), end(c), a)) {
        //    TRACE("solve:exit, cnf satisfied\n");
        //    return true;
        //}

        for (;;) {
            // Find a conflict clause if it exists
            auto conflict_clause = has_conflict(begin(c), end(c), a);
            if (conflict_clause != end(c)) {
                Parent[d.level].clear();
                Parent[d.level].insert(begin(conflict_clause), end(conflict_clause));
                //cout << "Set parent: " << Parent[d.level] << endl;
            }
            else if (new_parent.size() &&
                     is_unsatisfied(begin(new_parent), end(new_parent), a)) {
                Parent[d.level].clear();
                Parent[d.level].insert(begin(new_parent), end(new_parent));
                //cout << "Set parent: " << Parent[d.level] << endl;
            }
            else {
                break;
            }
            // The above linse basically transform the for(;;) loop into a
            // "while there is a conflict clause..." loop.
            literal to_flip = d.decisions[d.level];
            //cout << "found conflict with " << to_flip << endl;
            //cout << Parent[d.level] << endl;

            // flip the assignment...
            a.unassign(to_flip);
            to_flip = -to_flip;
            d.decisions[d.level] = to_flip;
            a.set_true(to_flip);
            //cout << "Just set to true: " << to_flip << endl;
            d.left_right[d.level] = R;

            // If there is still a conflict in the original assignment we must begin to backtrack.
            conflict_clause = has_conflict(begin(c), end(c), a);

            if (conflict_clause != end(c)) {
                //cout << "conflict clause remains after flipping: " << to_flip << endl;
                //cout << conflict_clause << endl;
                // In the Dershowitz Nadel SSS, new_parent is actually an index
                // (i.e., clause_iterator in our parlance), but because I'm not
                // yet building the conflict graph I'm going to copy it explicitly.
                new_parent.clear();
                new_parent.insert(begin(conflict_clause), end(conflict_clause));

                literal level_literal = d.decisions[d.level];
                while (d.level >= 0 && (d.left_right[d.level] == R ||
                                        !new_parent.contains(-level_literal))) {
                    //cout << "backtracking clause: " << new_parent << endl;
                    //cout << "Backtracking: " << d.level << " because: " << (d.left_right[d.level] == R) << " " << !new_parent.contains(-level_literal) << endl;

                    // if the new parent contains -level_literal, then it must be able to be resolved
                    // with Parent[d.level].
                    if (d.left_right[d.level] == R && new_parent.contains(-level_literal)) {
                        //cout << "Resolving: " << Parent[d.level] << "\t" << new_parent << "\t" << d.decisions[d.level] << endl;
                        //new_parent = resolve(begin(new_parent), end(new_parent),
                                             //begin(Parent[d.level]), end(Parent[d.level]), -d.decisions[d.level]);
                        new_parent = resolve(begin(Parent[d.level]), end(Parent[d.level]),
                                             begin(new_parent), end(new_parent), d.decisions[d.level]);
                    }
                    a.unassign(d.decisions[d.level]);
                    //d.decisions[d.level] = std::abs(d.decisions[d.level]);
                    d.level--;

                    level_literal = d.decisions[d.level];
                }
                if (d.level == -1) { return false; }
            }
        }

    };
}

cnf_table load_cnf_table() {
    auto simple_table = cnf_from_stdin();
    int size = 0;
    int literal_count = 0;
    int clause_count = 0;
    for (auto cl : simple_table) {
        size += cl.size();
        clause_count++;
        for (auto x : cl) {
            auto y = std::abs(x);
            literal_count = std::max(literal_count, y);
        }
    }
    literal_count *= 2;

    cnf_table result(size, clause_count, literal_count);

    for (auto cl : simple_table) {
        result.insert_clause(cl);
    }
    return result;
}

int main(int argc, char* argv[]) {
    auto table = load_cnf_table();
    cout << solve(table) << endl;
}
