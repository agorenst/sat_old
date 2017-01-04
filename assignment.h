#include "literal_map.h"

#include <iostream>

#include <stack>
#include "small_set.h"


// An assignment is simply a database of variables tracking
// their assignment status (true, false, or unassigned).
//
// It can also be read as a sequence of assigned literals.
//
// Note that we predicate things on *LITERALS*, not variables.
// So we ask "is -x true" to mean if the variable x has been assigned
// the boolean value false. In other words, we ask "is the clause [-x]
// satisfied by this assignment?".
class assignment {
    public:
    bool is_true(literal l) const;
    bool is_false(literal l) const;
    bool is_unassigned(literal l) const;

    void set_true(literal l);
    void unassign(literal l);

    const int literal_count;
    assignment(const int literal_count):
        literal_count(literal_count),
        is_assigned_true(literal_count)
    {}

    void print(std::ostream& o) const;

    private:
    literal_map<bool> is_assigned_true;
};

bool assignment::is_true(literal l) const { return is_assigned_true.get_copy(l); }
bool assignment::is_false(literal l) const { return is_assigned_true.get_copy(-l); }
bool assignment::is_unassigned(literal l) const {
    return !this->is_true(l) && !this->is_false(l);
}

void assignment::set_true(literal l) {
    ASSERT(this->is_unassigned(l));
    is_assigned_true[l] = true;
};
void assignment::unassign(literal l) {
    ASSERT(!this->is_unassigned(l));
    is_assigned_true[l] = false;
    is_assigned_true[-l] = false;
};

void assignment::print(std::ostream& o) const {
    for (literal i = is_assigned_true.first_index();
         i != is_assigned_true.end_index();
         ++i) {
        if (is_assigned_true.get_copy(i)) {
            o << i << " ";
        }
    }
}

std::ostream& operator<<(std::ostream& o, const assignment& a) {
    a.print(o);
    return o;
}
