// A mapping of decision level to the literals chosen at that level.

#include <memory>
#include <iostream>

#include "debug.h"
#include "small_set.h"

class decision_sequence {
    void on_resize(cnf_table::clause_iterator old_base,
                     cnf_table::clause_iterator new_base,
                     int new_size) {
        for (int i = 0; i < level; ++i) {
            if (Parent[i]) {
                auto old_index = Parent[i] - old_base;
                auto new_index = old_index + new_base;
                Parent[i] = new_index;
            }
        }
    }

    public:
    const int max_literal;
    enum class LRSTATUS {
        LEFT,
        RIGHT
    };
    std::unique_ptr<literal[]> decisions;
    std::unique_ptr<LRSTATUS[]> left_right;
    std::unique_ptr<cnf_table::clause_iterator[]> Parent;
    decision_sequence(cnf_table& c, literal max_literal):
        max_literal(max_literal),
        decisions(std::make_unique<literal[]>(max_literal)),
        left_right(std::make_unique<LRSTATUS[]>(max_literal)),
        Parent(std::make_unique<cnf_table::clause_iterator[]>(max_literal))
    {
        // The default decisions.
        for (int i = 0; i < max_literal; ++i) {
            decisions[i] = 0;
            left_right[i] = LRSTATUS::LEFT;
        }

        using namespace std::placeholders;
        // Register ourselves as needing a remap:
        std::function<void(cnf_table::clause_iterator,
                           cnf_table::clause_iterator,
                           int)> m =
            std::bind(&decision_sequence::on_resize, this, _1, _2, _3);
        c.resizers.push_back(m);
    }

    template<typename Assignment>
    bool sanity_check(const Assignment& a) const {
       for (int i = 0; i < level; ++i) {
           if (left_right[i] == LRSTATUS::RIGHT) {
               if (Parent[i] == nullptr) {
                   trace("Error: right decision=", i, " has no parent!\n");
                   return false;
               }
           }
           else {
               if (Parent[i] != nullptr) {
                   trace("Error: left decision=", i, " has parent=", Parent[i], "\n");
                   return false;
               }
           }
       }
       return true;
    }
    

    literal level_literal() const { return decisions[level]; }
    LRSTATUS level_direction() const { return left_right[level]; }
    int level = 0;
};

std::ostream& operator<<(std::ostream& o, const decision_sequence::LRSTATUS s) {
    if (s == decision_sequence::LRSTATUS::LEFT) {
        return o << "L";
    }
    else {
        return o << "R";
    }
}

std::ostream& operator<<(std::ostream& o, const decision_sequence& d) {
    for (int i = 0; i < d.level+1; ++i) {
        o << d.decisions[i] << "(" << i << "," << d.left_right[i] << ") ";
    }
    o << "| ";
    for (int i = d.level+1; i < d.max_literal; ++i) {
        o  << d.decisions[i] << " ";
    }
    return o;
}
