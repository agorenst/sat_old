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

//small_set<literal> extract_decisions(literal conflict, const decision_history& h) {
//    small_set<literal> conflict_clause;
//    conflit_clause.insert(conflict);
//    for (auto it = h.rbegin(); it != h.rend(); ++it) {
//    }
//}

// What's not obvious: how do we make sure our decision variables lead to
// a sound and complete exploration of the tree? We need to get that
// right before actually learning any clauses...
bool clause_learning_dpll(watched_literals& wl) {
    assignment a(wl.cnf.max_literal_count);
    decision_history history;
    int decision_level = 0;

    while (!is_sat(wl, a)) {
        //cout << a << endl;
        history.clear(); // isnt going to be actually used yet.
        a.set_decision_level(++decision_level);

        literal decision = a.get_next_unassigned();
        //cout << "Next decision: " << decision << endl;

        implication_graph implicants;

        literal conflict = wl.apply_literal(a, decision, std::back_inserter(implicants));

        if (conflict) {
            //cout << "history: " << endl;
            //cout << history << endl;
            //cout << "conflict literal: " << conflict << " from decision: " << decision << endl;
            //cout << implicants << endl;
            history.push_back({decision, implicants});

            // for now, simply backtrack:
            literal undone_literal;
            do {
                undone_literal = a.pop_decision_level();
                //cout << "popping: " << undone_literal << endl;
                a.set_decision_level(--decision_level);
            } while (undone_literal < 0);
            a.negate = true;
            if (undone_literal == 0) { return false; }
        }
        else {
            history.push_back({decision, implicants});
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

