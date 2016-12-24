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
    for (literal l : tester) {
        cout << "Key: l " << l << ", tester["<<l<<"]: " << tester[l] << endl;
    }
}
