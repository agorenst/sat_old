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
    trace("starting main solver\n");
    
    // TODO: push the Parent sequence into the decision_sequence.
    decision_sequence d(c.max_literal_count);

    // TODO: clean this up.
    const auto L = decision_sequence::LRSTATUS::LEFT;
    const auto R = decision_sequence::LRSTATUS::RIGHT;
    assignment a(c.max_literal_count);
    ASSERT(d.level == 0);

    small_set<literal> new_parent;
    std::vector<small_set<literal>> Parent(c.max_literal_count);
    for (;;) {
        trace("main iteration start\n");
        trace("current assignment: ", a, "\n");
        new_parent.clear();

        // We do this before decisions because on some inputs
        // e.g., inputs/aim-100-1_6-yes1-4.cnf, we assert because
        // I guess we need to flip the variable before it's actually
        // SAT. So we'd make a 101st decision, null deref.
        if (is_cnf_satisfied(c, a)) {
            trace("done, cnf satisfied by ", a, "\n");
            return true;
        }


        //////////////////////////////////////////////////////////////////
        // PROPOGATING SIMPLE UNITS STARTS HERE
        literal unit = find_unit_in_cnf(c, a);
        if (unit) {
            trace("unit literal found: ", unit, "\n");
            ASSERT(a.is_unassigned(unit));

            // maintain our current way of choosing literals.
            // TODO: this should ultimately be deprecated with better literal
            // selection.
            auto to_swap = std::find_if(d.decisions.get(),
                                        d.decisions.get()+d.max_literal,
                                        [unit](literal l) {
                                return std::abs(l) == std::abs(unit);
                           });
            // we haven't chosen as our unit an already-assigned variable.
            ASSERT(to_swap >= d.decisions.get()+d.level);
            ASSERT(to_swap < d.decisions.get()+d.max_literal);

            // set the unit to our next-to-assign state.
            std::swap(d.decisions[d.level], *to_swap);
            d.left_right[d.level] = L; // we know it will actually be R soon enough.
            ASSERT(std::abs(d.decisions[d.level]) == std::abs(unit));
            d.decisions[d.level] = -unit; // set it to the right sign.
            trace("choice induced by unit: ", d.decisions[d.level], "\n");
            a.set_true(d.decisions[d.level]);
        }
        //
        //////////////////////////////////////////////////////////////////
        else {
            trace("choosing literal for decision level: ", d.level, "\n");
            d.decisions[d.level] = d.decisions[d.level];
            d.left_right[d.level] = L;
            trace("chose ", d.decisions[d.level], "\n");
            a.set_true(d.decisions[d.level]);
        }

        for (;;) {
            trace("entering conflict loop\n");
            // Find a conflict clause if it exists
            const auto parent_clause = find_conflict_augment(c, new_parent, a);
            if (!parent_clause.size()) {
                trace("no conflict on current decision ", d, " breaking\n");
                break;
            }
            trace("conflict with clause ", parent_clause, "\n");

            //////////////////////////////////////////////////////////////////
            // NCB STARTS HERE
            // OK, this rewrite is super gnarly, but it seems at least to always
            // terminate. I'm sure a second look will clean things up a lot, but
            // I need to let this bake in more.
            int orig_level = d.level;
            auto NCB_clause = parent_clause;
            literal needed_flip = -d.level_literal();
            ASSERT(NCB_clause.contains(needed_flip));
            NCB_clause.erase(needed_flip);


            trace("Before backtracking: ", d, "\n");
            // We have a conflict, so we must undo at least one iteration.
            trace("undoing: ");
            do {
                trace(d.level_literal(), " ");
                a.unassign(d.level_literal());
                d.level--;
            }
            while (NCB_clause.size() &&
                   is_clause_unsatisfied(begin(NCB_clause), end(NCB_clause), a));
            trace("\n");
            // Weird case: if parent_clause is unit (i.e., NCB_clause is empty), we
            // still want to iterate at least once, but no more.
            d.level++;
            a.set_true(d.level_literal());

            if (d.level < orig_level) {
                trace("redoing: ");
                do {
                    d.level++;
                    a.set_true(d.level_literal());
                    trace(d.level_literal(), " ");
                    trace("curdir:(", d.level_direction(), ") ");
                    ASSERT(!NCB_clause.size() ||
                            is_clause_unsatisfied(begin(NCB_clause), end(NCB_clause), a));
                } while (d.level < orig_level &&
                        d.level_direction() == R);
                trace("\n");
            }

            trace("After backtracking: ", d, "\n");
            // Make sure I understand what happens in the unit-clause case:
            ASSERT(    NCB_clause.size()
                   || (   is_clause_unsatisfied(begin(parent_clause), end(parent_clause), a)
                       && orig_level == d.level));

            if (d.level < orig_level) {
                ASSERT(d.level_direction() == L);
                ASSERT(is_clause_unsatisfied(begin(NCB_clause), end(NCB_clause), a));
                a.unassign(d.level_literal());
                d.level--;
                ASSERT(is_clause_unsatisfied(begin(NCB_clause), end(NCB_clause), a));
                trace("swapping: ", d.decisions[d.level+1], " ", d.decisions[orig_level], "\n");
                std::swap(d.decisions[d.level+1], d.decisions[orig_level]);
                ASSERT(d.decisions[d.level+1] == -needed_flip);
                d.level++;
                a.set_true(d.level_literal());
                ASSERT(is_clause_unsatisfied(begin(parent_clause), end(parent_clause), a));
            }
            // NCB ENDS HERE
            //////////////////////////////////////////////////////////////////

            trace("Parent[", d.level, "] = ", parent_clause, "\n");
            ASSERT(is_clause_unsatisfied(begin(parent_clause), end(parent_clause), a));
            ASSERT(parent_clause.contains(-d.decisions[d.level]));
            Parent[d.level] = parent_clause;

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

                while (d.level >= 0 && (d.level_direction() == R ||
                                        !new_parent.contains(-d.level_literal()))) {
                trace("level literal during backtrack: ", d.level_literal(), "\n");

                    // if the new parent contains -level_literal, then it must be
                    // able to be resolved with Parent[d.level].
                    if (d.level_direction() == R &&
                        new_parent.contains(-d.level_literal())) {

                        trace("parent resolution possible against ", Parent[d.level],  "\n");
                        new_parent = resolve(Parent[d.level], new_parent, d.level_literal());
                        trace("new parent: ", new_parent, "\n");
                    }
                    a.unassign(d.level_literal());
                    // Uncommenting this leads to a 3x slowdown. Why?
                    //d.decisions[d.level] = std::abs(d.decisions[d.level]);
                    d.level--;

                    /////////////////////////////////////////////////
                    // CONFLICT DIRECTED BACKJUMPING
                    if (new_parent.contains(-d.decisions[d.level])) {
                        trace("entering conflict-directed backjumping\n");
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
                        trace("recording new clause: ", new_parent, "\n");
                        c.insert_clause(new_parent);
                    }
                    //
                    /////////////////////////////////////////////////
                }

                // Did we resolve into an empty clause?
                if (d.level == -1) {
                    ASSERT(d.level == -1);
                    return false;
                }
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
