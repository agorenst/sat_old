#include "literal_map.h"

#include <iostream>

class assignment {
    private:
    int next_variable = 1;
    int decision_level = 0;
    const literal max_literal;
    literal_map<bool> is_assigned_true;
    literal_map<int> decision_levels;
    public:
    bool negate = false;
    assignment(literal max_literal):
        max_literal(max_literal),
        is_assigned_true(max_literal*2),
        decision_levels(max_literal*2) {

        for (literal l : key_iter(is_assigned_true)) {
            is_assigned_true[l] = false;
            decision_levels[l] = -1;
        }

    }
    bool is_true(literal l) const { return is_assigned_true[l]; }
    bool is_false(literal l) const { return is_assigned_true[-l]; }
    bool is_unassigned(literal l) const { return !is_true(l) && !is_false(l); }
    void set_true(literal l) {
        is_assigned_true[l] = true;
        decision_levels[l] = decision_level;
    }
    void set_decision_level(int dl) { decision_level = dl; }
    int get_next_unassigned() {
        while (!is_unassigned(next_variable)) { ++next_variable; }
        if (negate) {
            negate = false;
            return -next_variable;
        }
        else {
            return next_variable;
        }
    }
    // TODO: make sure we're only setting 1 of the fields false, the other should
    // already be false.
    void undo(literal l) {
        is_assigned_true[l] = false;
        is_assigned_true[-l] = false;
    }

    void print(std::ostream& o) const {
        for (auto l : key_iter(is_assigned_true)) {
            if (is_true(l)) { o << l << " "; }
        }
    }

    literal pop_decision_level() {
        literal smallest_abs_val = 0;
        for (auto l : key_iter(is_assigned_true)) {
            if (decision_levels[l] == decision_level) {
                if (!smallest_abs_val || abs(l) < abs(smallest_abs_val)) {
                    smallest_abs_val = l;
                }
                is_assigned_true[l] = false;
                decision_levels[l] = -1;
            }
        }
        next_variable = abs(smallest_abs_val);
        return smallest_abs_val;
    }
};


std::ostream& operator<<(std::ostream& o, const assignment& a) {
    a.print(o);
    return o;
}
