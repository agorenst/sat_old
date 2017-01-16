// A mapping of decision level to the literals chosen at that level.

#include <memory>
#include <iostream>

#include "debug.h"
#include "small_set.h"

class decision_sequence {
    public:
    const int max_literal;
    enum class LRSTATUS {
        LEFT,
        RIGHT
    };
    std::unique_ptr<literal[]> decisions;
    std::unique_ptr<LRSTATUS[]> left_right;
    std::unique_ptr<small_set<literal>[]> Parent;
    decision_sequence(literal max_literal):
        max_literal(max_literal),
        decisions(std::make_unique<literal[]>(max_literal)),
        left_right(std::make_unique<LRSTATUS[]>(max_literal)),
        Parent(std::make_unique<small_set<literal>[]>(max_literal))
    {
        // The default decisions.
        for (int i = 0; i < max_literal; ++i) {
            decisions[i] = i+1;
            left_right[i] = LRSTATUS::LEFT;
        }
    }

    template<typename Assignment>
    bool sanity_check(const Assignment& a) const {
       for (int i = 0; i < level; ++i) {
           if (left_right[i] == LRSTATUS::RIGHT) {
               if (Parent[i].size() < 0) { return false;
                   for (auto x : Parent[i]) {
                       if (x == decisions[i]) { continue; }
                       if (std::find(decisions.get(), decisions.get()+i, x) != decisions.get()+i) { continue; }

                       trace("decision_sequence error: invalid parent ", Parent[i], " : ", decisions[i], ", ", i, "\n");
                       return false;
                   }
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
