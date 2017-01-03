// A mapping of decision level to the literals chosen at that level.

#include <memory>

class decision_sequence {
    public:
    const int max_literal;
    enum class LRSTATUS {
        LEFT,
        RIGHT
    };
    std::unique_ptr<literal[]> decisions;
    std::unique_ptr<LRSTATUS[]> left_right;
    decision_sequence(literal max_literal):
        max_literal(max_literal),
        decisions(std::make_unique<literal[]>(max_literal)),
        left_right(std::make_unique<LRSTATUS[]>(max_literal))
    {
        // The default decisions.
        for (int i = 0; i < max_literal; ++i) {
            decisions[i] = i+1;
            left_right[i] = LRSTATUS::LEFT;
        }
    }
    int level = 0;
};