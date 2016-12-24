#include "simple_parser.h"

#include <iostream>
#include <sstream>
#include <iterator>

using namespace std;
typedef int variable;
typedef int literal;

typedef vector<literal> basic_clause;
typedef vector<basic_clause> basic_cnf;

vector<vector<int>> cnf_from_stdin() {
    // very simple parsing, assuming things are pretty well-formatted.
    basic_cnf result;
    std::string line;
    while (getline(std::cin, line)) {
        if (line.size() < 1 ||
                line[0] == 'c' ||
                line[0] == 'p') {
            continue;
        }
        basic_clause new_clause;
        auto to_parse = std::istringstream(line);
        std::istream_iterator<literal> literal_reader{to_parse};
        std::istream_iterator<literal> end_of_line;
        while (literal_reader != end_of_line) {
            literal l = *literal_reader++;
            if (l == 0) { break; }
            new_clause.push_back(l);
        }
        result.push_back(new_clause);
    }
    return result;
}
