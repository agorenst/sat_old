#include "cnf_table.h"
#include "small_set.h"
#include "simple_parser.h"
#include "decision_sequence.h"
#include "assignment.h"
#include "watched_literals.h"

#include <algorithm>
#include <iostream>

using namespace std;

cnf_table::clause_iterator find_conflict_augment(const cnf_table& c,
                                                 const assignment& a) {
    auto conflict_clause = has_conflict(c, a);
    if (conflict_clause == end(c)) { return nullptr; }
    return conflict_clause;
}

small_set<literal> self_subsuming_resolution(small_set<literal> clause_1,
                                            cnf_table::clause_iterator clause_2,
                                            literal pivot) {
    auto result = resolve(begin(clause_2),
                         end(clause_2),
                         begin(clause_1),
                         end(clause_1), pivot);
    if (result.size() < clause_1.size()) {
        std::sort(begin(result), end(result));
        std::sort(begin(clause_1), end(clause_1));
        if (std::includes(begin(clause_1), end(clause_1),
                          begin(result), end(result))) {
            //trace("SSR: ", clause_1, ", ", clause_2, ", ", result, "\n");
            //std::cout << "SSR: " << std::endl 
            //          << "\t" << clause_1 << std::endl
            //          << "\t" << clause_2 << std::endl
            //          << "\t" << result << std::endl;
            return result;
        }
    }
    return clause_1;
}

// TODO: figure out how to manage this better...
const auto L = decision_sequence::LRSTATUS::LEFT;
const auto R = decision_sequence::LRSTATUS::RIGHT;

bool decision_and_assignment_consistent(const decision_sequence& d,
                                        const assignment& a) {
    for (int i = -(a.literal_count/2); i <= (a.literal_count/2); ++i) {
        if (!i) { continue; }
        if (!a.is_true(i)) { continue; }
        literal x = i;
        bool assigned_literal_found = false;
        for (int i = 0; i <= d.level; ++i) {
            if (d.decisions[i] == x) { assigned_literal_found = true; }
        }
        if (!assigned_literal_found) {
            trace("case 1 never found: ", x, "\n");
            trace("d: ", d, "\n");
            trace("a: ", a, "\n");
            return false;
        }
    }

    for (int i = 0; i <= d.level; ++i) {
        if (!a.is_true(d.decisions[i])) {
            trace("case 2 never found: ", d.decisions[i], "\n");
            trace("d: ", d, "\n");
            trace("a: ", a, "\n");
            return false;
        }
    }

    return true;
};

// This is the main SSS implementation.
bool solve(cnf_table& c) {
    ASSERT(c.sanity_check());
    trace("SSS: start\n");

    // We initialize our data structures:
    // d contains the information about the <order> of
    //    our decisions and how the assignment evolves.
    // a contains exactly the assigned literals, nothing
    //    more.
    decision_sequence d(c, c.max_literal_count);
    assignment a(c.max_literal_count);
    watched_literal_db wl(c);
    ASSERT(d.level == 0);

    // A helper value that will store a small clause.
    small_set<literal> new_parent;

    // All setup complete. This loop is the rest of the function.
    for (;;) {
        trace("SSS: main loop top\n");
        trace("a: ", a, "\n");
        trace("d: ", d, "\n");

        ASSERT(c.sanity_check());
        ASSERT(d.decisions[d.level] == 0);
        ASSERT(d.Parent[d.level] == nullptr);
        ASSERT(d.left_right[d.level] == L);
        ASSERT(d.sanity_check(a));

        new_parent.clear();

        // We choose a new literal to act on.
        // If there's a unit literal, we choose that,
        // otherwise we make a decision according to some
        // heuristic.

        literal decision_lit = 0;
        //////////////////////////////////////////////////////////////////
        // PROPOGATING SIMPLE UNITS STARTS HERE
        if (wl.has_units()) {
            ASSERT(has_conflict(c, a) == end(c));
            while (literal unit = wl.get_unit()) {
                trace("BCP: unit found = ", unit, "\n");
                if (!a.is_unassigned(unit)) {
                    trace("BCP: break, conflict\n");
                    break;
                }

                ASSERT(c.confirm_is_implied_unit(a, unit));

                d.decisions[d.level] = unit;
                d.left_right[d.level] = R;
                d.Parent[d.level] = wl.get_cause(); // this pops the unit. TODO: fix
                d.level++;
                a.set_true(unit);
                wl.apply_literal(a, unit);
            }

            // We're either out of units, or we had a conflict. We need
            // to backtrack to the last non-conflict so we can set up
            // our real conflict-handling logic to manage this.
            wl.clear_units();

            // while there's a conflict, we want to pop assignments...
            auto cc = has_conflict(c, a);
            if (cc != end(c)) {
                while (cc != end(c)) {
                    while (clause_unsat(cc, a)) {
                        d.level--;
                        a.unassign(d.decisions[d.level]);
                        decision_lit = d.decisions[d.level];
                        d.decisions[d.level] = 0;
                        d.Parent[d.level] = nullptr;
                    }
                    cc = has_conflict(c, a);
                }

                // If we had a conflict, then the decision literal is
                // chosen to pass that conflict on to our "real"
                // conflict handling logic.
                a.set_true(decision_lit);
                ASSERT(has_conflict(c, a) != end(c));
                a.unassign(decision_lit);
                ASSERT(has_conflict(c, a) == end(c));
            }
        }
        //
        //////////////////////////////////////////////////////////////////

        ASSERT(!wl.has_units());
        ASSERT(has_conflict(c, a) == end(c));

        if (is_cnf_satisfied(c, a)) {
            trace("SAT: ", a, "\n");
            return true;
        }
        // MAKE A DECISION
        else if (!decision_lit) { // if our unit-prop hasn't made our decision for us.
            // We go backwards thru the CNF to find an unassigned variable.
            // Backwards seems to be a lot faster than forwards, presumably because
            // the newly-learned clauses keep things interesting (hackneyed version
            // of the clause-based heuristic). This sets a fairly low bar, but a bar
            // for any variable-choosing heuristic actually has to pass.
            for (cnf_table::clause_iterator cit = end(c) - 1;
                 cit >= begin(c);
                 --cit) {
                if (clause_sat(cit, a)) { continue; };
                for (auto x : cit) {
                    if (a.is_unassigned(x)) {
                        decision_lit = x;
                        // We could break, but let's keep control flow simple.
                    }
                }
                if (decision_lit) { break; }
            }
            trace("SSS decided on literal: ", decision_lit, "\n");
        }
        d.decisions[d.level] = decision_lit;
        // DONE MAKING A DECISION

        ASSERT(d.decisions[d.level] != 0);
        ASSERT(a.is_unassigned(d.decisions[d.level]));
        ASSERT(!decision_lit || d.decisions[d.level] == decision_lit);

        // Commit the decision to our assignment.
        d.left_right[d.level] = L;
        a.set_true(d.decisions[d.level]);
        wl.apply_literal(a, d.decisions[d.level]);
        trace("SSS: decided literal ", d.decisions[d.level], "\n");
        ASSERT(decision_and_assignment_consistent(d, a));

        // If the CNF is satisfied by our current assignment,
        // we're done.
        if (is_cnf_satisfied(c, a)) {
            trace("SAT: ", a, "\n");
            return true;
        }

        // In D&N we look for conflict at both the CNF and the new_parent
        // clause. Original design meant that new_parent was a value, and not
        // necessarily in the CNF. However, after CRR the new_parent is always
        // in the CNF. This allows us to get rid of all value types, and
        // unify our reasoning to only think about clause_iterators.
        // I don't have 100% understanding, but it is *necessary* that the
        // new_parent clause be added to the CNF. If the CNF ever stops changing
        // (e.g., if our out-of-memory-mode is to just stop learning clauses)
        // then we will get stuck in what looks like an infinite loop.
        while (const auto parent_clause = find_conflict_augment(c, a)) {
            trace("conflict loop: start\n");
            trace("conflict clause: ", parent_clause, "\n");
            trace("a: ", a, "\n");
            trace("d: ", d, "\n");

            // Here's where we really have to clear the units...
            wl.clear_units();

            ASSERT(clause_contains(parent_clause, -d.level_literal()));

            //////////////////////////////////////////////////////////////////
            // NCB STARTS HERE
            // The intuition behind NCB is that we are demoting an "L" decision
            // to an "R" decision. We want to go back in history as early as
            // possible that still implies our L decision being demoted.
            //
            // D&N provide a framework modeling why this helps, for now I'll
            // appeal to intuition that we'd want to move as many implications
            // of our earlier decisions higher up.
            //
            // From experience, this optimization is rife with off-by-one
            // sorts of errors. I think the D&N notation is just very strange.
            //
            // Basically: get to the lowest level that implies conflict\decision
            // is still false. Then we'll consider the next decision level.
            // We will increment that one until we find an L.
            trace("NCB: start\n");
            int orig_level = d.level;
            small_set<literal> NCB_clause;
            NCB_clause.insert(begin(parent_clause), end(parent_clause));
            literal needed_flip = -d.level_literal();
            ASSERT(NCB_clause.contains(needed_flip));
            NCB_clause.erase(needed_flip);

            // Reminder: the literal at the current level *is assigned*
            ASSERT(a.is_true(d.level_literal()));
            ASSERT(d.level_direction() == L);

            // Step one: undo our previous decisions so long as our parent
            // clause (assuming our needed_flip is false) is unsatisfied.
            // Things get weird when our parent clause is unit! We undo
            // everything?
            trace("NCB: undoing ");
            while (d.level >= 0 && clause_unsat(NCB_clause, a)) {
                trace(d.level_literal(), " ");
                a.unassign(d.level_literal());
                d.level--;
                // deliberately >saving< our old decisions.
            }
            ASSERT(!NCB_clause.size() || !clause_unsat(NCB_clause, a));
            trace("\n");
            trace("NCB: d after initial undoes = ", d, "\n");

            ASSERT(d.level >= -1);
            d.level++;
            trace("NCB: redoing ", d.level_literal(), " to make clause unsat\n");
            a.set_true(d.level_literal());
            ASSERT(clause_unsat(NCB_clause, a));
            
            trace("NCB: redoing R decisions ");
            while (d.level+1 < orig_level &&
                   d.left_right[d.level+1] == R) {
                d.level++;
                ASSERT(d.level_literal());
                a.set_true(d.level_literal());
                trace("l=",d.level_literal(), "(", d.level_direction(), ") ");
            }
            trace("\n");

            ASSERT(clause_unsat(NCB_clause, a));
            ASSERT(d.level >= 0);

            trace("NCB: new level = ", d.level, " orig level = ", orig_level, "\n");
            trace("NCB: d = ", d, "\n");

            if (d.level < orig_level) {
                ASSERT(clause_unsat(NCB_clause, a));
                // Here's where we really have to clear the units...

                trace("NCB: swapping: ", d.decisions[d.level+1], " ", d.decisions[orig_level], "\n");
                std::swap(d.decisions[d.level+1], d.decisions[orig_level]);
                ASSERT(d.decisions[d.level+1] == -needed_flip);
                d.level++;
                ASSERT(d.level_literal());
                a.set_true(d.level_literal());
                trace("NCB: d = ", d, "\n");
                ASSERT(clause_unsat(NCB_clause, a));

                // Maybe useless? maintain invariant...
                for (int i = d.level+1; i < d.max_literal; ++i) {
                    d.decisions[i] = 0;
                    d.Parent[i] = nullptr;
                    d.left_right[i] = L;
                }
            }
            trace("NCB: done\n");
            // NCB ENDS HERE
            //////////////////////////////////////////////////////////////////

            // We've extracted as much as we could out of the fact that we wanted
            // to assign X, but found ourselves obliged to consider -X.
            // We do that here. Note that -X may very well not help, and that's when
            // we'll really backtrack.
            ASSERT(clause_unsat(parent_clause, a));
            ASSERT(clause_contains(parent_clause, -d.decisions[d.level]));
            trace("conflict loop: d.Parent[", -d.decisions[d.level], "(", d.level, ")] = ", parent_clause, "\n");
            d.Parent[d.level] = parent_clause;

            literal to_flip = d.decisions[d.level];
            trace("conflict loop: flipping literal: ", to_flip, " to assign ", -to_flip, "\n");

            a.unassign(to_flip);
            to_flip = -to_flip;
            d.decisions[d.level] = to_flip;
            a.set_true(to_flip);
            d.left_right[d.level] = R;
            ASSERT(clause_contains(d.Parent[d.level], d.decisions[d.level]));

            wl.apply_literal(a, d.decisions[d.level]);

            // Here's the moment of truth: are we really going to backtrack?
            auto conflict_clause = has_conflict(c, a);
            if (conflict_clause != end(c)) {
                trace("conflict loop: after flipping conflict remains: ", c, "\n");


                // In the Dershowitz Nadel SSS, new_parent is actually an index
                // (i.e., clause_iterator in our parlance), but because I'm not
                // yet building the conflict graph I'm going to copy it explicitly.
                new_parent.clear();
                new_parent.insert(begin(conflict_clause), end(conflict_clause));
                trace("conflict loop: new parent = ", new_parent, "\n");

                // The loop invariant in the backtrack loop is a bit strange,
                // it's several conditionals compressed together.
                //   1) d.level < 0: if we've gotten to that point, then UNSAT, easy.
                // Assuming d.level >= 0:
                //   2) If d.level_direction() == R, then we already know it's pointless
                //      to try to flip it back to L, so we should continue backtracking.
                // And what if the direction is L?
                //   3) If new_parent contains -d.level_literal(), then we know the
                //      conflict we care about will be addressed by flipping L. So
                //      we should flip it. It seems that we simply trust the next
                //      go-around of the conflcit loop will find that conflict,
                //      and bring the full force of NCB and so on behind hit. That's
                //      conjecture on my part...
                //   4) And if the parent does not contain our level's literal,
                //      then obviously undoing that (even if it's L) won't address the
                //      resolution conflict we're trying to reverse, so again we
                //      continue backtracking.


                // Loop invariant:
                ASSERT(clause_unsat(new_parent, a));
                while (d.level >= 0 && (d.level_direction() == R ||
                                        !new_parent.contains(-d.level_literal()))) {
                    trace("backtrack loop: d.level         = ", d.level, "\n"
                          "              , d.level_literal = ", d.level_literal(), "\n"
                          "              , new_parent      = ", new_parent, "\n");

                    // If this level was forced (i.e., direction = R), then there's a
                    // parent clause we can potentially resolve against new_parent.
                    // If possible, do this resolution to get a "smarter" new_parent.
                    if (d.level_direction() == R &&
                        new_parent.contains(-d.level_literal())) {

                        trace("backtrack loop: resolving against ", d.Parent[d.level],  "\n");
                        new_parent = resolve(begin(d.Parent[d.level]),
                                             end(d.Parent[d.level]),
                                             begin(new_parent),
                                             end(new_parent), d.level_literal());
                        trace("backtrack loop: new parent = ", new_parent, "\n");
                    }

                    trace("backtrack loop: unassigning: ", d.level_literal(), "\n");
                    a.unassign(d.level_literal());
                    d.decisions[d.level] = 0;
                    d.Parent[d.level] = nullptr;
                    d.left_right[d.level] = L;
                    d.level--;
                    
                    // The big question: why do we do CDB and CCR *after* backtracking?
                    // And why not do this at the start of each backtrack iteration?
                    // For the second, presumably now we've done some resolution about
                    // new_parent.
                    // For the first, I will observe that a loop invariant is that
                    // new_parent is *always* unsatisified in this loop, both at the
                    // beginning and at the end.

                    /////////////////////////////////////////////////
                    // CONFLICT DIRECTED BACKJUMPING
                    //
                    // Very similar to NCB in spirit. Briefly, if we find an R-variable
                    // that comes after an L variable, and by our resolution reasoning
                    // we can "swap them out" without invalidating any of the reasoning,
                    // do it. This moves the R variable "up" the tree, I suppose.
                    // 
                    if (d.level >= 0 && new_parent.contains(-d.decisions[d.level])) {
                        trace("CDB: starting\n");
                        int g = -1;
                        for (int i = d.level; i >= 0; --i) {
                            if (d.left_right[i] == L) {
                                g = i;
                                break;
                            }
                        }
                        // g is the highest left-decision level.
                        trace("CDB candidate: ", g, " origlevel: ", d.level, "\n");

                        // Only continue if there is an L-decision level.
                        // (See Nadel's thesis for a statement that an L-decision is a
                        // necessary condition, but I don't know why vs., say, the "-1"-th
                        // level. I guess that mean's we're UNSAT anyways...)
                        if (g >= 0) {
                            bool clause_still_unsat =
                                std::all_of(begin(new_parent), end(new_parent), [&](literal l) {
                                    if (l == -d.decisions[d.level]) { return true; }
                                    for (int i = 0; i <= g - 1; ++i) {
                                        if (-d.decisions[i] == l) { return true; }
                                    }
                                    return false;
                                });

                            if (clause_still_unsat) {
                                // Save d.level by bringing it below g. So we don't have
                                // to reassign it or anything like that.
                                std::swap(d.decisions[g], d.decisions[d.level]);
                                for (int i = d.level; i > g; --i) {
                                    a.unassign(d.decisions[i]);
                                    d.decisions[i] = 0;
                                    d.Parent[i] = nullptr;
                                    d.left_right[i] = L;
                                }
                                ASSERT(clause_unsat(new_parent, a));
                                // This no longer works so well (as new_parent isn't
                                // yet in the clause database), and also weird.
                                // D&N says that this is part of CDB, but it only
                                // makes sense that R decisions have parents...
                                //d.Parent[g] = new_parent;
                                d.left_right[g] = L;
                                trace("CDB set d.level: ", d.level, " = ", g, "\n");
                                d.level = g;
                            } else { trace("CDB: clause did not remain unsat\n"); }
                        } else { trace("CDB: bailing for lack of L literals\n"); }
                    }
                    //
                    /////////////////////////////////////////////////

                    /////////////////////////////////////////////////
                    // CONFLICT CLAUSE RECORDING
                    //
                    // Basically, we've found that new_parent is a certificate
                    // why we made a bad choice (hence, d.level should be L).
                    if (d.level >= 0 && d.left_right[d.level] == L &&
                            new_parent.contains(-d.decisions[d.level])) {
                        if (c.clauses_count >= c.clauses_max ||
                            c.raw_data_count + new_parent.size() >= c.raw_data_max) {
                            c.consider_resizing();
                        }
                        ASSERT(c.clauses_count < c.clauses_max &&
                               c.raw_data_count + new_parent.size() < c.raw_data_max);
                        trace("CRR: ", new_parent, "\n");

                        // CCR minimization:
                        // From Sorensson and Biere, a nice and simple paper.
                        // Gives a 5.9->5.7 second improvement on my computer on the ssa benchmarks.
                        // Presumably also helps memory usage (once better implementations are made...)
                        for (int i = d.level; i >= 0; --i) {
                            if (d.left_right[i] == R &&
                                    new_parent.contains(-d.decisions[i])) {
                                new_parent = self_subsuming_resolution(new_parent, d.Parent[i], d.decisions[i]);
                            }
                        }
                        auto new_clause_ptr = c.insert_clause(new_parent);
                        trace("CRR: learned ", new_clause_ptr, "\n");
                        wl.add_clause(new_clause_ptr);
                    }
                    //
                    /////////////////////////////////////////////////
                    ASSERT(!new_parent.size() || clause_unsat(new_parent, a));
                }

                // Did we resolve into an empty clause?
                if (d.level == -1) {
                    ASSERT(new_parent.size() == 0);
                    ASSERT(d.level == -1);
                    return false;
                }
            } // End case where conflict clause was found
        } // End conflict loop
        d.level++;
    } // End main loop.
    ASSERT(false);
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
