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
    else if (new_parent.size() && is_clause_unsatisfied(new_parent, a)) {
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

        // We do this before decisions because on some inputs
        // e.g., inputs/aim-100-1_6-yes1-4.cnf, we assert because
        // I guess we need to flip the variable before it's actually
        // SAT. So we'd make a 101st decision, null deref.
        if (is_cnf_satisfied(c, a)) {
            return true;
        }

        new_parent.clear();

        // Choose a new decision variable.
        literal next_decision = d.decisions[d.level];
        d.left_right[d.level] = L;
        a.set_true(next_decision);
        
        for (;;) {
            // Find a conflict clause if it exists
            auto parent_clause = find_conflict_augment(c, new_parent, a);
            if (!parent_clause.size()) { break; }
            Parent[d.level] = parent_clause;
            // The above lines basically transform the for(;;) loop into a
            // "while there is a conflict clause..." loop.


            literal to_flip = d.decisions[d.level];

            // flip the assignment...
            a.unassign(to_flip);
            to_flip = -to_flip;
            d.decisions[d.level] = to_flip;
            a.set_true(to_flip);
            d.left_right[d.level] = R;

            // If there is still a conflict in the original assignment we backtrack
            auto conflict_clause = has_conflict(begin(c), end(c), a);

            if (conflict_clause != end(c)) {
                // In the Dershowitz Nadel SSS, new_parent is actually an index
                // (i.e., clause_iterator in our parlance), but because I'm not
                // yet building the conflict graph I'm going to copy it explicitly.
                new_parent.clear();
                new_parent.insert(begin(conflict_clause), end(conflict_clause));

                literal level_literal = d.decisions[d.level];
                while (d.level >= 0 && (d.left_right[d.level] == R ||
                                        !new_parent.contains(-level_literal))) {

                    // if the new parent contains -level_literal, then it must be
                    // able to be resolved with Parent[d.level].
                    if (d.left_right[d.level] == R && new_parent.contains(-level_literal)) {
                        new_parent = resolve(Parent[d.level], new_parent, level_literal);
                    }
                    a.unassign(d.decisions[d.level]);
                    //d.decisions[d.level] = std::abs(d.decisions[d.level]);
                    d.level--;

                    level_literal = d.decisions[d.level];
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
