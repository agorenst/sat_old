#define LITERAL_MAP_VERBOSE
#include "literal_map.h"

#include <string>
#include <iostream>

using namespace std;

int main() {
    const int numLiterals = 8;
    literal_map<string> tester(numLiterals);
    for (int i = -4; i < 5; ++i) {
        if (i == 0) { continue; }
        tester[i] += "hello";
    }
    for (literal l : key_iter(tester)) {
        cout << "Key: l " << l << ", tester["<<l<<"]: " << tester[l] << endl;
    }

    for (int i = -8; i < 9; ++i) {
        cout << i << " " << tester.literal_to_index(i) << " " << tester.index_to_literal(tester.literal_to_index(i)) << endl;
    }

    for (auto&& p : pair_iter(tester)) {
        cout << p.first << " " << p.second << endl;
    }
}
