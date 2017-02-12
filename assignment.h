#ifndef ASSIGNMENT_H
#define ASSIGNMENT_H

#include "cnf.h"
#include "literal_map.h"
#include "small_set.h"
#include "debug.h"

class assignment {
    public:
    const int R = 0;
    const int L = 1;
    private:
    void on_resize(cnf::clause_iterator old_base,
                     cnf::clause_iterator new_base,
                     int new_size) {
        for (int i = 0; i < assigned_count; ++i) {
            if (Parent[i]) {
                auto old_index = Parent[i] - old_base;
                auto new_index = old_index + new_base;
                Parent[i] = new_index;
            }
        }
    }

    void on_remap(int* m, int n, cnf::clause_iterator start) {
        for (int i = 0; i < assigned_count; ++i) {
            if (Parent[i]) {
                auto old_index = Parent[i] - start;
                ASSERT(m[old_index] != -1);
                Parent[i] = start + m[old_index];
                ASSERT(clause_contains(Parent[i], decision_sequence[i]));
            }
        }
    }
    public:

    void restart() {
        // Note: sometimes we'll have implied literals
        // that are at level -1. So we'll still have some
        // literals implied, that's fine.
        while (level > 0) {
            pop_level();
        }
    }

    bool is_true(literal l) const;
    bool is_false(literal l) const;
    bool is_unassigned(literal l) const;

    void push_decision(literal l);
    void push_implicant(literal l, cnf::clause_iterator c);

    const int literal_count;


    assignment(int literal_count):
        literal_count(literal_count),
        is_assigned_true(literal_count),
        lit_dec_level(literal_count),
        decision_sequence(std::make_unique<literal[]>(literal_count)),
        Parent(std::make_unique<cnf::clause_iterator[]>(literal_count)),
        left_right(std::make_unique<int[]>(literal_count))
    {}

    assignment(cnf& c): assignment(c.max_literal_count) {
        using namespace std::placeholders;
        c.resizers.push_back(std::bind(&assignment::on_resize, this, _1, _2, _3));
        c.remappers.push_back(std::bind(&assignment::on_remap, this, _1, _2, _3));
    }

    // TODO: const
    void print(std::ostream& o) const;

    int level = 0;
    int assigned_count = 0;

    public:
    int decision_level() { return level; }
    int* first_lit_latest_level() {
        int i = 0;
        while (lit_dec_level[decision_sequence[i]] != level-1) {
            i++;
        }
        return decision_sequence.get() + i;
    }
    int* last_lit_latest_level() {
        return decision_sequence.get() + assigned_count;
    }

    void pop_level() {
        TRACE("A: pop_level\n");
        ASSERT(level > 0);
        ASSERT(assigned_count > 0);
        level--;
        literal lit_actual = 0;
        while (assigned_count > 0 &&
               lit_dec_level[decision_sequence[assigned_count-1]] == level) {
            lit_actual = decision_sequence[assigned_count-1];
            assigned_count--;
            Parent[assigned_count] = nullptr;
            is_assigned_true[lit_actual] = false;
        }
        //return lit_actual;
    }
    void pop_single_lit() {
        TRACE("A: pop_single_lit\n");
        ASSERT(level > 0);
        ASSERT(assigned_count > 0);
        literal lit_actual = decision_sequence[assigned_count-1];
        is_assigned_true[lit_actual] = false;

        assigned_count--;
        Parent[assigned_count] = nullptr;
        level = lit_dec_level[decision_sequence[assigned_count-1]]+1;
    }

    bool curr_lit_is_implied() {
        return Parent[assigned_count-1] != nullptr;
    }

    literal curr_lit() { return decision_sequence[assigned_count-1]; }
    cnf::clause_iterator curr_reason() { return Parent[assigned_count-1]; }
    int curr_level() const { return level - 1; }

    // This returns 0 on the empty clause, as desired.
    template<typename C>
    int max_literal_level(const C& c) {
        int m = -1;
        for (int x : c) {
            ASSERT(is_false(x));
            m = std::max(m, lit_dec_level[-x]);
        }
        return m;
    }

    // Check a number of invariants.
    // Largely concerned with the monotonicity and correctness of tracking
    // the decision level sequence.
    bool sanity_check() {
        ASSERT(level >= 0);
        ASSERT(assigned_count >= level);
        if (assigned_count == 0) { return true; }
        for (int i = 1; i < assigned_count; ++i) {
            literal curr = decision_sequence[i];
            literal prev = decision_sequence[i-1];
            ASSERT(lit_dec_level[curr] == lit_dec_level[prev] ||
                   lit_dec_level[curr] - 1 == lit_dec_level[prev]);
        }
        //std::cout << (assigned_count -1) << " "
        //          << decision_sequence[assigned_count-1] << " "
        //          << lit_dec_level[decision_sequence[assigned_count-1]] << " "
        //          << (level-1) << std::endl;
        ASSERT(lit_dec_level[decision_sequence[assigned_count-1]] == level-1);

        // the levels are monotically increasing.
        //int level_tracer = 0;
        //for (int i = 0; i < assigned_count; ++i) {
        //    int newest_level = lit_dec_level[decision_sequence[assigned_count-1]];
        //    if (newest_level != level_tracer) {
        //        ASSERT(newest_level = level_tracer + 1);
        //        level_tracer = newest_level;
        //    }
        //}
        //ASSERT(level_tracer == level - 1);

        // make sure the assigned_true is consistent with our decision_sequnece
        for (int i = 0; i < assigned_count; ++i) {
            ASSERT(is_assigned_true[decision_sequence[i]]);

            // Exactly every R better have a parent clause.
            if (left_right[i] == R) { ASSERT(Parent[i]); }
            else { ASSERT(!Parent[i]); }
        }

        // everything assigned true should be in the decision sequence.
        for (int i = is_assigned_true.first_index();
             i != is_assigned_true.end_index();
             ++i) {
            if (i == 0) { continue; }
            if (is_assigned_true[i]) {
                ASSERT(std::find(decision_sequence.get(),
                                 decision_sequence.get()+assigned_count,
                                 i) != decision_sequence.get()+assigned_count);
            }
        }
        // no two equiv. literals are assigned simultaneously.
        for (int i = is_assigned_true.first_index();
             i != is_assigned_true.end_index();
             ++i) {
            if (i == 0) { continue; }
            if (is_assigned_true[i]) {
                ASSERT(!is_assigned_true[-i]);
            }
        }

        return true;
    };

    literal_map<bool> is_assigned_true;

    literal* begin() const {
        return decision_sequence.get();
    }
    literal* end() const {
        return decision_sequence.get() + assigned_count;
    }
    int decision_number(literal l) const {
        auto it = std::find(decision_sequence.get(),
                            decision_sequence.get() + assigned_count,
                            l);
        ASSERT(it != decision_sequence.get() + assigned_count);
        return it - decision_sequence.get();
    }
    int decision_level(literal l) const {
        ASSERT(!is_unassigned(l));
        return lit_dec_level.get_copy(l);
    }

    bool is_reason_clause(const cnf::clause_iterator cit) const {
        for (int i = 0; i < assigned_count; ++i) {
            if (Parent[i] == cit) { return true; }
        }
        return false;
    }
    private:
    literal_map<int> lit_dec_level;
    std::unique_ptr<literal[]> decision_sequence;
    std::unique_ptr<cnf::clause_iterator[]> Parent;
    std::unique_ptr<int[]> left_right;
};

literal* begin(const assignment& a) { return a.begin(); }
literal* end(const assignment& a) { return a.end(); }

bool assignment::is_true(literal l) const { return is_assigned_true.get_copy(l); }
bool assignment::is_false(literal l) const { return is_assigned_true.get_copy(-l); }
bool assignment::is_unassigned(literal l) const {
    return !this->is_true(l) && !this->is_false(l);
}

void assignment::push_decision(literal l) {
    ASSERT(is_unassigned(l));
    is_assigned_true[l] = true;
    Parent[assigned_count] = nullptr;
    left_right[assigned_count] = L;
    decision_sequence[assigned_count] = l;
    assigned_count++;
    lit_dec_level[l] = level;
    level++;
}

void assignment::push_implicant(literal l, cnf::clause_iterator reason) {
    ASSERT(is_unassigned(l));
    is_assigned_true[l] = true;
    Parent[assigned_count] = reason;
    left_right[assigned_count] = R;
    decision_sequence[assigned_count] = l;
    assigned_count++;
    lit_dec_level[l] = level-1;
}

// print out every field
void assignment::print(std::ostream& o) const {
    for (int i = 0; i < assigned_count; ++i) {
        o << i << ": " << decision_sequence[i] << " = " <<
                          is_assigned_true.get_copy(decision_sequence[i]) << "; " <<
                          (left_right[i] == L ? "L" : "R") << " at level " <<
                          lit_dec_level.get_copy(decision_sequence[i]);
        if (Parent[i]) o << " by (" << Parent[i] <<")";
        o << std::endl;
    }
    for (literal i = is_assigned_true.first_index();
         i != is_assigned_true.end_index();
         ++i) {

        if (i && is_assigned_true.get_copy(i)) {
            o << i << " ";
        }
    }
}

//TODO: Const
std::ostream& operator<<(std::ostream& o, const assignment& a) {
    a.print(o);
    return o;
}

#endif
