#include "cnf_table.h"
#include "small_set.h"
#include "simple_parser.h"
#include "decision_sequence.h"
#include "assignment.h"

#include <algorithm>
#include <iostream>

using namespace std;

template <typename Assignment>
small_set<literal> find_conflict_augment(const cnf_table& c,
                                         const small_set<literal>& new_parent,
                                         const Assignment& a) {
    small_set<literal> result;

    auto conflict_clause = has_conflict(c, a);
    if (conflict_clause != end(c)) {
        result.insert(begin(conflict_clause), end(conflict_clause));
    }
    else if (new_parent.size() && is_clause_unsatisfied(begin(new_parent), end(new_parent), a)) {
        result.insert(begin(new_parent), end(new_parent));
    }
    return result;
}


// This is the main SSS implementation.
bool solve(cnf_table& c) {
    decision_sequence d(c.max_literal_count);
    const auto L = decision_sequence::LRSTATUS::LEFT;
    const auto R = decision_sequence::LRSTATUS::RIGHT;
    assignment a(c.max_literal_count);
    ASSERT(d.level == 0);

    small_set<literal> new_parent;
    std::vector<small_set<literal>> Parent(c.max_literal_count);
    for (;;) {
        trace("main iteration start\n");

        // We do this before decisions because on some inputs
        // e.g., inputs/aim-100-1_6-yes1-4.cnf, we assert because
        // I guess we need to flip the variable before it's actually
        // SAT. So we'd make a 101st decision, null deref.
        if (is_cnf_satisfied(c, a)) {
            trace("done, cnf satisfied by ", a, "\n");
            return true;
        }

        new_parent.clear();

        // Choose a new decision variable.
        //std::transform(d.decisions.get()+d.level, d.decisions.get()+d.max_literal,
        //               d.decisions.get()+d.level,
        //               [](literal l) { return std::abs(l); });
        //std::sort(d.decisions.get()+d.level, d.decisions.get()+d.max_literal);

        //////////////////////////////////////////////////////////////////
        // PROPOGATING SIMPLE UNITS STARTS HERE
        literal unit = find_unit_in_cnf(c, a);
        if (unit) {
            ASSERT(a.is_unassigned(unit));
            auto to_swap = std::find_if(d.decisions.get(),
                                        d.decisions.get()+d.max_literal,
                                        [unit](literal l) {
                                return std::abs(l) == std::abs(unit);
                           });
            ASSERT(to_swap >= d.decisions.get()+d.level);
            ASSERT(to_swap < d.decisions.get()+d.max_literal);
            std::swap(d.decisions[d.level], *to_swap);
            d.left_right[d.level] = L;
            ASSERT(std::abs(d.decisions[d.level]) == std::abs(unit));
            d.decisions[d.level] = -unit; // set it to the right sign.
            trace("unit: ", d.decisions[d.level], "\n");
            a.set_true(d.decisions[d.level]);
        }
        //
        //////////////////////////////////////////////////////////////////
        else {
            trace("choosing literal for decision level: ", d.level, "\n");
            literal next_decision = d.decisions[d.level];
            d.left_right[d.level] = L;
            trace("chose ", next_decision, "\n");
            a.set_true(next_decision);
        }

        for (;;) {
            // Find a conflict clause if it exists
            const auto parent_clause = find_conflict_augment(c, new_parent, a);
            if (!parent_clause.size()) {
                trace("no conflict on current decision ", d, " breaking\n");
                break;
            }
            trace("conflict with clause ", parent_clause, "\n");

            //////////////////////////////////////////////////////////////////
            // NCB STARTS HERE
            //
            // When we get here we've already committed to flipping the literal.
            //
            // Extra conditional: make sure the conflict is worthwhile...
            if (parent_clause.size() > 1) {
                int g = d.level;
                auto NCB_clause = parent_clause;
                ASSERT(NCB_clause.contains(-d.decisions[d.level]));
                NCB_clause.erase(-d.decisions[d.level]);

                // find the minimal g such that the NCB clause is still unsat...
                do {
                    a.unassign(d.decisions[g]);
                    --g;
                } while (is_clause_unsatisfied(begin(NCB_clause), end(NCB_clause), a));
                ASSERT(!is_clause_unsatisfied(begin(NCB_clause), end(NCB_clause), a));
                ++g;
                a.set_true(d.decisions[g]);
                ASSERT(is_clause_unsatisfied(begin(NCB_clause), end(NCB_clause), a));

                // Optional is to move forward past all the R variables.
                // TODO: do that.

                // Now we finish backtracking:
                trace("NCB backtracked to level ", g, "\n");
                trace("current decisions: ", d, "\n");
                ASSERT(g+1 <= d.level);
                // To avoid infinite looping, we only backtrack when we're reordering
                // decision variables "backwards". This is built off the idea that we
                // assign literals from abs(1) ... abs(max_variable), and avoids
                // us getting in an infinite loop where we swap -8 with 14 and then
                // 14 with -8. This would come up in the UNSAT cases.
                if (std::abs(d.decisions[g+1]) > std::abs(d.decisions[d.level])) {
                    // NCB is bad,
                    // Reset all our NCB.
                    for (; g+1 < d.level; ++g) {
                        a.set_true(d.decisions[g+1]);
                    }
                    a.set_true(d.decisions[g+1]);
                    ASSERT(g+1 == d.level);
                }
                else {
                    // NCB is good,
                    // Finish our NCB:
                    std::swap(d.decisions[g+1],d.decisions[d.level]);
                    a.set_true(d.decisions[g+1]);
                    d.level = g+1;
                    trace("level is now: ", d.level, " with decision ", d.decisions[d.level], "\n");
                }
            }
            // NCB ENDS HERE
            //////////////////////////////////////////////////////////////////

            trace("Parent[", d.level, "] = ", parent_clause, "\n");
            ASSERT(is_clause_unsatisfied(begin(parent_clause), end(parent_clause), a));
            ASSERT(parent_clause.contains(-d.decisions[d.level]));
            Parent[d.level] = parent_clause;
            // The above lines basically transform the for(;;) loop into a
            // "while there is a conflict clause..." loop.


            literal to_flip = d.decisions[d.level];
            trace("flipping literal: ", to_flip, "\n");

            // flip the assignment...
            a.unassign(to_flip);
            to_flip = -to_flip;
            d.decisions[d.level] = to_flip;
            a.set_true(to_flip);
            d.left_right[d.level] = R;

            // If there is still a conflict in the original assignment we backtrack
            auto conflict_clause = has_conflict(begin(c), end(c), a);

            if (conflict_clause != end(c)) {
                trace("After flipping, still has conflict: ", conflict_clause, "\n");
                // In the Dershowitz Nadel SSS, new_parent is actually an index
                // (i.e., clause_iterator in our parlance), but because I'm not
                // yet building the conflict graph I'm going to copy it explicitly.
                new_parent.clear();
                new_parent.insert(begin(conflict_clause), end(conflict_clause));
                trace("new parent: ", new_parent, "\n");

                literal level_literal = d.decisions[d.level];
                trace("level literal: ", d.decisions[d.level], "\n");
                while (d.level >= 0 && (d.left_right[d.level] == R ||
                                        !new_parent.contains(-level_literal))) {

                    // if the new parent contains -level_literal, then it must be
                    // able to be resolved with Parent[d.level].
                    if (d.left_right[d.level] == R && new_parent.contains(-level_literal)) {
                        trace("parent resolution possible against", Parent[d.level],  "\n");
                        new_parent = resolve(Parent[d.level], new_parent, level_literal);
                        trace("new parent: ", new_parent, "\n");
                    }
                    a.unassign(d.decisions[d.level]);
                    // Uncommenting this leads to a 3x slowdown. Why?
                    //d.decisions[d.level] = std::abs(d.decisions[d.level]);
                    d.level--;

                    /////////////////////////////////////////////////
                    // CONFLICT DIRECTED BACKJUMPING
                    if (new_parent.contains(-d.decisions[d.level])) {
                        int g = -1;
                        for (int i = d.level; i >= 0; --i) {
                            if (d.left_right[i] == L) {
                                g = i;
                                break;
                            }
                        }
                        //ASSERT(g != -1);
                        ASSERT(g <= d.level);
                        // g is the highest left-decision level.

                        if (g >= 0 && g < d.level) {
                            bool clause_still_unsat = std::all_of(begin(new_parent),
                                    end(new_parent),
                                    [&](literal l) {
                                    if (l == -d.decisions[d.level]) { return true; }
                                    for (int i = 0; i < g; ++i) {
                                    if (-d.decisions[i] == l) { return true; }
                                    }
                                    return false;
                                    });

                            if (clause_still_unsat) {
                                std::swap(d.decisions[g], d.decisions[d.level]);
                                for (int i = d.level; i > g; --i) {
                                    a.unassign(d.decisions[i]);
                                }
                                Parent[g] = new_parent;
                                d.level = g;
                            }
                        }
                    }
                    //
                    /////////////////////////////////////////////////

                    /////////////////////////////////////////////////
                    // CONFLICT CLAUSE RECORDING
                    if (d.left_right[d.level] == L &&
                        new_parent.contains(-d.decisions[d.level]) &&
                        c.clause_count < c.max_clause_count &&
                        c.size + new_parent.size() < c.max_size) {
                        c.insert_clause(new_parent);
                    }
                    //
                    /////////////////////////////////////////////////

                    level_literal = d.decisions[d.level];
                    trace("level literal: ", d.decisions[d.level], "\n");
                }
                if (d.level == -1) { return false; }
            }
        }
        d.level++;
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
