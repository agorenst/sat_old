#include "cnf_table.h"
#include "simple_parser.h"

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

typedef std::set<literal> assignment_t;

bool is_sat(const cnf_table& c, const assignment_t assignment) {
    for (cnf_table::clause_iterator cit = c.clauses.get();
         cit != c.clauses.get() + c.clause_count;
         ++cit) {
        bool clause_is_sat = std::any_of(begin(cit), end(cit), [&](literal l) {
            return assignment.find(l) != assignment.end();
        });
        if (!clause_is_sat) { return false; }
    }
    return true;
}

bool is_unsat(const cnf_table& c, const assignment_t assignment) {
    for (cnf_table::clause_iterator cit = c.clauses.get();
         cit != c.clauses.get() + c.clause_count;
         ++cit) {
        bool clause_is_false = std::all_of(begin(cit), end(cit), [&](literal l) {
            return assignment.find(-l) != assignment.end();
        });
        if (clause_is_false) {
            return true;
        }
    }
    return false;
}

literal get_unit(const cnf_table& c, const assignment_t assignment) {
    for (cnf_table::clause_iterator cit = c.clauses.get();
         cit != c.clauses.get() + c.clause_count;
         ++cit) {

        literal potential_unit = 0;
        for (literal l : cit) {
            if (assignment.find(l) != assignment.end()) {
                potential_unit = 0;
                break;
            }
            if (assignment.find(-l) == assignment.end()) {
                if (potential_unit == 0) {
                    potential_unit = l;
                }
                else {
                    potential_unit = 0;
                    break;
                }
            }
        }
        if (potential_unit) { return potential_unit; }
    }
    return 0;
}

assignment_t bcp(const cnf_table& c, const assignment_t assignment, literal l) {
    ASSERT(assignment.find(l) == assignment.end());
    ASSERT(assignment.find(-l) == assignment.end());
    assignment_t result = assignment;
    result.insert(l);
    while (literal unit = get_unit(c, result)) {
        result.insert(unit);
    }
    return result;
}

int find_next_var(const cnf_table& c, const assignment_t a) {
    for (cnf_table::clause_iterator cit = c.clauses.get();
         cit != c.clauses.get() + c.clause_count;
         ++cit) {
        for (literal l : cit) {
            if (a.find(l) == a.end() && a.find(-l) == a.end()) {
                return std::abs(l);
            }
        }
    }
    ASSERT(0);
    return 0;
}

std::ostream& operator<<(std::ostream& o, const assignment_t& a) {
    std::for_each(begin(a), end(a), [&](literal l) { o << l << " "; });
    return o;
}

bool basic_dpll(const cnf_table& c, assignment_t assignment) {
    //cout << "dpll with " << assignment << endl;
    if (is_sat(c, assignment)) { return true; }
    if (is_unsat(c, assignment)) { return false; }
    int next_var = find_next_var(c, assignment);
    auto true_assignment = bcp(c, assignment, next_var);
    if (basic_dpll(c, true_assignment)) {
        return true;
    }
    else {
        auto false_assignment = bcp(c, assignment, -next_var);
        if (basic_dpll(c, false_assignment)) {
            return true;
        }
    }
    return false;
}

int main(int argc, char* argv[]) {
    auto table = load_cnf_table();
    if (basic_dpll(table, {})) {
        cout << "true" << endl;
    }
    else {
        cout << "false" << endl;
    }
}
