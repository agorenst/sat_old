#include "cnf_table.h"
#include "simple_parser.h"
#include "watched_literals.h"
#include "small_set.h"

#include "assignment.h"

#include <iostream>

#include <cassert>

using namespace std;

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


// We will use the watched_literals data structure to expedite this:
bool is_sat(watched_literals& wl, const assignment& a) {
    return wl.is_sat(a);
}

typedef std::pair<literal, cnf_table::clause_iterator> implication_history;
ostream& operator<<(ostream& o, const implication_history& ih) {
    return o << "\t" << ih.first << " <- " << ih.second;
}
typedef std::vector<implication_history> implication_graph;
ostream& operator<<(ostream& o, const implication_graph& g) {
    std::for_each(begin(g), end(g), [&](const implication_history& i) {
        o << i << endl;
    });
    return o;
}
typedef std::pair<literal, implication_graph> decision_entry;
ostream& operator<<(ostream& o, const decision_entry de) {
    return o << de.first << ": " << endl << de.second;
}
typedef std::vector<decision_entry> decision_history;
ostream& operator<<(ostream& o, const decision_history dh) {
    std::for_each(begin(dh), end(dh), [&](const decision_entry& de) {
        o << de << endl;
    });
    return o;
}

// I *think* this learns the decision variable clause...
small_set<literal> extract_decisions(literal conflict, const decision_history& h) {
    small_set<literal> conflict_clause;
    conflict_clause.insert(conflict);
    conflict_clause.insert(-conflict);
    for (auto it = h.rbegin(); it != h.rend(); ++it) {
        const implication_graph& g = it->second;
        bool can_be_expanded = true;
        while (can_be_expanded) {
            can_be_expanded = false;
            for (const implication_history& h : g) {
                if (conflict_clause.contains(h.first)) {
                    //cout << "conflict clause contains: " << h.first << endl;
                    for (auto l : h.second) {
                        if (l != h.first) {
                            //cout << "adding " << -l << endl;
                            conflict_clause.insert(-l);
                        }
                    }
                    can_be_expanded = true;
                    conflict_clause.erase(h.first);
                }
            }
        }
    }
    small_set<literal> real_conflict;
    for (literal l : conflict_clause) {
        real_conflict.insert(-l);
    }
    return real_conflict;
    //return conflict_clause;
}

// What's not obvious: how do we make sure our decision variables lead to
// a sound and complete exploration of the tree? We need to get that
// right before actually learning any clauses...
bool clause_learning_dpll(watched_literals& wl) {
    assignment a(wl.cnf.max_literal_count);
    decision_history history;
    int decision_level = 0;

    while (!is_sat(wl, a)) {

        literal decision = a.get_next_decision();

        LRStatus[decision] = LRStatus::L;

        // Record the unit propogation of setting "decision" to be true.
        implication_graph implicants;
        auto history_recorder = std::back_inserter(implicants);
        literal conflict = wl.apply_literal(a, decision, history_recorder);

        // first see if it's a superficial conflict where we just negate
        // the literal.
        if (conflict) {
            a.pop_last_decision();
            implicants.clear();
            history_recorder = std::back_inserter(implicants);
            LRStatus[decision] = LRStatus::R;
            conflict = wl.apply_literal(a, -decision, history_recorder);
        }

        // Ok, we have a real backtrack situation:
        if (conflict) {
            // This holds on the first iteration obviously.
            while (a.decision_level && LRStatus[decision] == LRStatus::R) {
                a.decision_level--;

            }
        }












        a.set_decision_level(++decision_level);

        literal decision = a.get_next_unassigned();
        //cout << a << endl;
        //cout << "Next decision: " << decision << endl;

        implication_graph implicants;

        literal conflict = wl.apply_literal(a, decision, std::back_inserter(implicants));
        //cout << "done applying literal: " << decision << " found conflict: " << conflict << endl;

        history.push_back({decision, implicants});
        if (conflict) {
            //cout << "history: " << endl;
            //cout << history << endl;
            //cout << "conflict literal: " << conflict << " from decision: " << decision << endl;
            //cout << implicants << endl;
            auto learned_clause = extract_decisions(conflict, history);
            //int backtrack_to = 0;
            //std::for_each(begin(learned_clause), end(learned_clause), [&](literal l) {
            //    if (a.get_decision_level(l) != -1 &&
            //        (!backtrack_to || 
            //        a.get_decision_level(l) > backtrack_to)) {
            //        backtrack_to = a.get_decision_level(l);
            //    }
            //});
            //cout << "I want to backtrack to " << backtrack_to << endl;
            //cout << "Because I learned clause: " << learned_clause << endl;


            literal undone_literal;
            do {
                undone_literal = a.pop_decision_level();
                //cout << "undid literal: " << undone_literal << endl;
                a.set_decision_level(--decision_level);
                if (decision_level == -1) { return false; }
                history.pop_back();
            } while (undone_literal < 0);

            if (wl.cnf.remaining_clauses() > 0 && learned_clause.size() < wl.cnf.remaining_size() && learned_clause.size() > 2 && learned_clause.size() < 6) {
                auto to_watch = wl.cnf.insert_clause(learned_clause);
                //cout << "learned clause: " << learned_clause << endl;
                wl.watch_new_clause(to_watch, a);
            }

            a.negate = true;
            if (undone_literal == 0) { return false; }
        }
    }
    return true;

}

int main(int argc, char* argv[]) {
    auto table = load_cnf_table();
    watched_literals initial{table};
    initial.initialize();
    if (clause_learning_dpll(initial)) {
        cout << "true" << endl;
    }
    else {
        cout << "false" << endl;
    }
}

