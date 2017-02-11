#ifndef VSIDS_H
#define VSIDS_H

#include "literal_map.h"
#include "assignment.h"

class vsids {
    literal_map<int> frequency;
    const int max_freq;

    void zero_freqs() {
        for (int i = frequency.first_index();
                 i != frequency.end_index();
                 ++i) {
            if (i == 0) { continue; }
            frequency[i] = 0;
        }
    }
    void cut_freqs() {
        for (int i = frequency.first_index();
                 i != frequency.end_index();
                 ++i) {
            if (i == 0) { continue; }
            frequency[i] /= 2;
        }
    }

    public:
    vsids(const cnf& c):
        frequency(c.max_literal_count),
        max_freq(2*c.clauses_max) {
        zero_freqs();
        for (auto cl : c) {
            apply_clause(cl);
        }
    }

    literal get_literal(const assignment& a) {
        literal choice = 0;
        int best_freq = 0;
        for (int i = frequency.first_index();
                 i != frequency.end_index();
                 ++i) {
            if (i == 0) { continue; }
            if (!a.is_unassigned(i)) { continue; }

            if (best_freq < frequency[i]) {
                best_freq = frequency[i];
                choice = i;
            }
        }
        return choice;
    }

    template<typename C>
    void apply_clause(const C& c) {
        bool should_cut = false;
        for (literal x : c) {
            frequency[x]++;
            if (frequency[x] > max_freq) {
                should_cut = true;
            }
        }
        if (should_cut) { cut_freqs(); }
    }
};

#endif
