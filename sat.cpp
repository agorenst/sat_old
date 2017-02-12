#include "cnf.h"
#include "assignment.h"
#include "watched_literals.h"
#include "glue_clauses.h"
#include "vsids.h"

#include "simple_parser.h"

literal decide_literal(cnf& c, assignment& a) {
    for (auto cl : c) {
        if (!clause_sat(cl, a)) {
            for (auto x : cl) {
                if (a.is_unassigned(x)) { return x; }
            }
        }
    }
    return 0;
    for (int i = a.is_assigned_true.first_index();
             i != a.is_assigned_true.end_index();
             ++i) {
        if (i == 0) { continue; }
        if (a.is_unassigned(i)) { return i; }
    }
    //for (int i = 1; i <= c.max_literal_count; ++i) {
    //    if (a.is_unassigned(i)) { return i; }
    //}
    return 0;
}

literal has_uip(flexsize_clause& p, assignment& a) {
    int hitcount = 0;
    literal r = 0;
    // we increment by 1 because we ignore the actual decision level.
    std::for_each(a.first_lit_latest_level(),
                  a.last_lit_latest_level(),
                  [&](literal l) {
        if (p.contains(-l)) {
            r = l;
            hitcount++;
        }
    });
    ASSERT(hitcount > 0);
    if (hitcount == 1) { return r; }
    TRACE("Not a uip!", p, "\n");
    return 0;
}

bool solve(cnf& c) {
    // Create all the helper data structures.
    assignment         a(c);
    watched_literals   w(c);
    flexsize_clause    p(c);
    glue_clauses       g(c);
    vsids              v(c);

    int conflict_counter = 0;

    for (;;) {
        p.clear();
        TRACE("main loop start\n");


        ASSERT(c.sanity_check());
        ASSERT(a.sanity_check());
        ASSERT(w.sanity_check());
        TRACE(a, "\n", c, "\n");

        auto problem = has_conflict(c, a);
        if (problem != end(c)) {
            TRACE("BUG: ", problem, "\n");
        }
        ASSERT(problem == end(c));

        // We start out with BCP. This covers degenerate inputs,
        // and leads to a cleaner induction loop.
        // This means that upon backtracking, we have to promise that we've
        // already computed the units.
        cnf::clause_iterator conflict_clause = nullptr;// has_conflict(c, a);
        trace("BCP: start\n");

        while (w.has_units()) {
            literal unit; cnf::clause_iterator reason;
            std::tie(unit, reason) = w.pop_unit();
            TRACE("BCP: unit = ", unit, ", reason = ", reason, "\n");
            if (clause_unsat(reason, a)) {
                TRACE("BCP: reason is conflict, breaking.\n");
                conflict_clause = reason;
                w.clear_units();
                break;
            }
            else {
                TRACE("BCP: pushing implicant ", unit, " -> ", reason, "\n");
                ASSERT(unit == clause_implies(reason, a));
                a.push_implicant(unit, reason);
                w.apply(a, unit);
            }
        }
        trace("BCP: done\n");

        // If there's a conflict, we'll learn from that
        // and continue.
        if (conflict_clause) {
            if (a.curr_level() == -1) { return false; }

            // trace backwards to make p a UIP.
            p.adopt(conflict_clause); // a helper class with easier resolution.

            const int old_level = a.curr_level();
            // backtrack until there's only one literal from our decision
            // level left.
            while (!has_uip(p, a)) {
                if (!a.curr_lit_is_implied()) {
                    std::cout << p << std::endl << a << std::endl;
                }
                ASSERT(a.curr_lit_is_implied());
                // we have to resolve against our reasons
                if (p.contains(-a.curr_lit())) {
                    auto unit = a.curr_lit();
                    auto reason = a.curr_reason();
                    p.resolve(reason, -unit);
                    TRACE("Resolved p: ", p, "\n");
                }
                a.pop_single_lit();
                ASSERT(clause_unsat(p, a));
            }

            // we better not have actually backtracked beyond our current level.
            ASSERT(a.curr_level() == old_level);
            literal uip = has_uip(p, a);
            TRACE("Found uip: ", uip, "\n");
            TRACE("With clause: ", p, "\n");
            ASSERT(uip != 0);
            uip = -uip;
            ASSERT(clause_unsat(p, a));

            int clause_lbd = g.calculate_lbd(a, p);

            // At this point p is a clause that has a UIP.
            // We should first learn it, and then backtrack.
            // We must apply what we've learned to avoid infinite
            // looping (see useful lecture notes).
            //
            // Note that p is now a new unit clause, given a.
            // And that it's asserting the UIP.
            // That may induce more BCP.
            // However, something inconsistent would arise in the case
            // where *that* BCP would induce more conflict: if p is
            // asserting using only assignments from "much earlier"
            // decision levels, then if we imagine ourselves going back
            // in time where the CNF always had p, we would have backtracked
            // even then.
            //
            // The point is, in that second-order conflict case, the unit
            // propogation induced by the UIP isn't honestly associated
            // at the latest decision level.
            //
            // To head that off, we do the NCB so that we go back in time
            // just to when the learned clause P should have always
            // been there.
            //
            // Note: another weird case is that our decision variable
            // itself may be the UIP.
            // Nonetheless, the desired level is the max level of the learend
            // clause --without-- the UIP literal.
            //
            // What if the clause is unit? In that case the max level is
            // defined as 0. That actually seems somewhat well-defined.

            a.pop_level();
            ASSERT(std::all_of(begin(c), end(c), [&](const auto cl) {
                return !clause_implies(cl, a) || size(cl) == 1;
            }));
            // There should be at least 1 unassigned literal in p,
            // and it should not somehow be made sat...
            ASSERT(!clause_unsat(p, a));
            ASSERT(!clause_sat(p, a));
            ASSERT(end(c) == has_conflict(c, a));
            p.erase(uip);
            ASSERT(clause_unsat(p, a));
            // Note that this is *inclusive", we want to keep all the assigned
            // literals in p.
            int max_level = a.max_literal_level(p);
            TRACE("NCB backtrack level: ", max_level, "\n");
            // we can be = because we already popped a level.
            ASSERT(max_level <= a.curr_level());
            while (a.curr_level() > max_level) {
                a.pop_level();
            }
            // 
            // now we've made a unit clause!
            p.insert(uip);
            ASSERT(uip == clause_implies(p, a));

            // At this point we've cleared our watch literals, so
            // we better not have any more conflict or unit clauses...
            ASSERT(std::all_of(begin(c), end(c), [&](const auto cl) {
                return !clause_implies(cl, a) || size(cl) == 1;
            }));

            // We learn and apply.
            c.consider_resizing();
            if (g.current_clause_count <= c.clauses_count) {
                int n = 0;
                auto m = g.generate_mapping(c, a, n);
                c.remap_clauses(m.get(), n);
                g.current_clause_count *= 2;
            }

            auto new_clause_ptr = c.insert_clause(p);
            g.lbd[new_clause_ptr] = clause_lbd;
            w.add_clause(new_clause_ptr, uip, a);
            ASSERT(uip == clause_implies(new_clause_ptr, a));
            a.push_implicant(uip, new_clause_ptr);
            v.apply_clause(new_clause_ptr);
            w.apply(a, uip);

            conflict_counter++;
        }
        else {

            ASSERT(std::all_of(begin(c), end(c), [&](const auto cl) {
                if (clause_implies(cl, a) && size(cl) > 1) {
                    std::cout << "Problem clause: " << cl << std::endl;
                }
                return !clause_implies(cl, a) || size(cl) == 1;
            }));

            //if (conflict_counter >= 512) {
            //    conflict_counter = 0;
            //    a.restart();
            //}

            //literal decision = decide_literal(c, a);
            literal decision = v.get_literal(a);
            if (decision == 0) { return true; }
            TRACE("decision: ", decision, "\n");

            // increments the decision level
            a.push_decision(decision);
            w.apply(a, decision);
        }
    }
}

using namespace std;

cnf load_cnf() {
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

    cnf result(size, clause_count, literal_count);

    for (auto cl : simple_table) {
        result.insert_clause(cl);
    }
    return result;
}

int main(int argc, char* argv[]) {
    auto table = load_cnf();
    cout << solve(table) << endl;
}
