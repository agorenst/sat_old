#include "cnf.h"
#include "assignment.h"
#include "watched_literals.h"
//#include "glue_clause.h"
//#include "vsids.h"

#include "simple_parser.h"

literal decide_literal(cnf& c, assignment& a) {
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
    return 0;
}

bool solve(cnf& c) {
    // Create all the helper data structures.
    assignment         a(c);
    watched_literals   w(c);
    //glue_clauses       g(c);
    //vsids              v(c);
    flexsize_clause    p(c);

    for (;;) {
        trace("Start main loop\n");
        ASSERT(c.sanity_check());
        ASSERT(a.sanity_check());
        ASSERT(w.sanity_check());
        std::cout << "C = " << c << std::endl;
        std::cout << "A = " << a << std::endl;

        //ASSERT(!is_cnf_sat(c, a));
        ASSERT(has_conflict(c, a) == end(c));

        literal decision = decide_literal(c, a);

        if (decision == 0) { return true; }

        trace("About to push decision ", decision, "\n");
        //std::cout << a << std::endl;
        a.push_decision(decision);
        //std::cout << a << std::endl;
        w.apply(a, decision);

        cnf::clause_iterator conflict_clause = nullptr;

        while (w.has_units()) {
            trace("Unit prop\n");
            literal unit;
            cnf::clause_iterator reason;
            std::tie(unit, reason) = w.pop_unit();

            trace("Reason clause: ", reason, " for unit ", unit, "\n");
            ASSERT(unit == clause_implies(reason, a) ||
                   clause_unsat(reason, a));
            if (clause_unsat(reason, a)) {
                conflict_clause = reason;
                w.clear_units();
                break;
            }
            else {
                trace("About to push implicant ", unit, "\n");
                a.push_implicant(unit, reason);
                w.apply(a, unit);
                //std::cout << a << std::endl;
            }
            a.sanity_check();
            w.sanity_check();
        }

        if (conflict_clause) {
            //std::cout << a << std::endl;
            p.adopt(conflict_clause);

            while (a.decision_level() - 1 > 0) {
                ASSERT(clause_unsat(p, a));
                ASSERT(p.size() > 0);
                trace("Testing level for UIP: ");
                std::for_each(a.first_lit_latest_level(),
                        a.last_lit_latest_level(),
                        [&](literal l) {
                    trace(l, " ");
                    if (p.contains(-l)) {
                        trace("(in) ");
                    }
                });
                trace("\n");

                if (literal uip = has_uip(p, a)) {
                    trace("Found uip: ", uip, "\n");
                    if (c.remaining_clauses() < 1 ||
                        c.remaining_size() < p.size()) {
                        c.consider_resizing();
                    }
                    auto new_clause_ptr = c.insert_clause(p);
                    trace("New learned clause: ", new_clause_ptr, "\n");
                    w.add_clause(new_clause_ptr);
                    std::cout << "Assignment now: " << a << std::endl;

                    // Now we backtrack to the next level.
                    literal old_decision = a.pop_level();
                    a.push_decision(uip);
                    trace("new implication: ", new_clause_ptr, "\n");
                    std::cout << a << std::endl;
                    trace("Testing implication: ", old_decision, " ", uip, "\n");
                    if (old_decision != uip) {
                        ASSERT(-old_decision == clause_implies(new_clause_ptr, a));
                        w.add_unit(-old_decision, new_clause_ptr);
                    }
                    //ASSERT(clause_unsat(new_clause_ptr, a));
                    //do {
                    //    a.pop_single_lit();
                    //} while (-uip != clause_implies(new_clause_ptr, a));
                    //ASSERT(-uip == clause_implies(new_clause_ptr, a));
                    //ASSERT(a.is_unassigned(uip));
                    //a.pop_level();
                    std::cout << "Assignment post-pop-level: " << a << std::endl;
                    //a.push_implicant(-uip, new_clause_ptr);
                    //w.add_unit(-uip, new_clause_ptr);
                    break;
                }
                else {
                    if (a.curr_lit_is_implied() &&
                            p.contains(-a.curr_lit())) {
                        auto unit = a.curr_lit();
                        auto reason = a.curr_reason();
                        p.resolve(reason, -unit);
                        trace("Resolved p: ", p, "\n");
                    }
                    a.pop_single_lit();
                    ASSERT(clause_unsat(p, a));
                }
                a.sanity_check();
                w.sanity_check();
            }

            if (a.decision_level() - 1 == 0) {
                return false;
            }
            ASSERT(a.decision_level() > 0);
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
