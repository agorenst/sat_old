#include "cnf_table.h"
#include "simple_parser.h"
#include "watched_literals.h"

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

struct assignment_t {
    std::set<literal> data;
    void insert(literal l) {
        data.insert(l);
    }
    void set_true(literal l) {
        data.insert(l);
    }
    bool is_true(literal l) const {
        return data.find(l) != data.end();
    }
    bool is_false(literal l) const {
        return data.find(-l) != data.end();
    }
    bool is_unassigned(literal l) const {
        return !is_true(l) && !is_false(l);
    }
};

// We will use the watched_literals data structure to expedite this:
bool is_sat(const watched_literals& wl, const assignment_t& a) {
    return wl.is_sat(a);
}

// returns false if we've become unsat...
bool bcp(watched_literals& wl, assignment_t& a, literal l) {
    ASSERT(a.is_unassigned(l));
    return wl.apply_literal(a, l);
}

int find_next_var(const cnf_table& c, const assignment_t a) {
    for (cnf_table::clause_iterator cit = c.clauses.get();
         cit != c.clauses.get() + c.clause_count;
         ++cit) {
        for (literal l : cit) {
            if (a.is_unassigned(l)) {
                return std::abs(l);
            }
        }
    }
    ASSERT(0);
    return 0;
}

std::ostream& operator<<(std::ostream& o, const assignment_t& a) {
    std::for_each(begin(a.data), end(a.data), [&](literal l) { o << l << " "; });
    return o;
}

bool basic_dpll(watched_literals& wl, assignment_t a) {
    if (is_sat(wl, a)) {
        //cout << "dpll with " << a << endl;
        return true;
    }
    int next_var = find_next_var(wl.cnf, a);
    auto true_a = a;
    if (bcp(wl, true_a, next_var)) {
        if (basic_dpll(wl, true_a)) {
            return true;
        }
    }
    auto false_a = a;
    if (bcp(wl, false_a, -next_var)) {
        if (basic_dpll(wl, false_a)) {
            return true;
        }
    }
    return false;
}

int main(int argc, char* argv[]) {
    auto table = load_cnf_table();
    watched_literals initial{table};
    initial.initialize();
    if (basic_dpll(initial, {})) {
        cout << "true" << endl;
    }
    else {
        cout << "false" << endl;
    }
}
