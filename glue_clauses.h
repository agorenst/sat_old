#ifndef GLUE_CLAUSES_H
#define GLUE_CLAUSES_H

#include "clause_map.h"
#include "decision_sequence.h"

class glue_clauses_db {
    public:
    clause_map<int> lbd;

    // these are essentially static values for calculating LBD.
    literal_map<int> literal_levels;
    small_set<int> present_levels;

    // this is for computing the bottom half of the LBD
    // clauses we want to keep. Note a clause cannot have LBD
    // higher than the number of variables.
    std::unique_ptr<int[]> lbd_buckets;

    const int literal_count;
    int current_clause_count;

    // given a clause, calculate how many decisions levels it crosses.
    int calculate_lbd(const decision_sequence& d,
                      const small_set<int>& new_parent) {
        present_levels.clear();

        int level_num = 0;
        for (int i = 0; i <= d.level; ++i) {
            if (d.left_right[i] == decision_sequence::LRSTATUS::LEFT) { level_num++; }
            literal_levels[d.decisions[i]] = level_num;
        }
        for (literal l : new_parent) {
            //ASSERT(std::find(d.decisions.get(), d.decisions.get()+d.level+1, -l) != (d.decisions.get()+d.level+1));
            present_levels.insert(literal_levels[-l]);
        }

        return present_levels.size();
    }

    std::pair<int,int> compute_cutoff_values(const cnf_table& c) {
        int current_clauses = c.clauses_count;
        ASSERT(current_clauses > 2);
        int desired_clauses = current_clauses / 2; // integer division is fine.

        std::fill(lbd_buckets.get(), lbd_buckets.get()+literal_count, 0);

        // Count the buckets.
        for (auto cit = c.clause_begin(); cit != c.clause_end(); ++cit) {
            lbd_buckets[lbd[cit]]++;
        }
        for (int i = 0; i < literal_count; ++i) {
            //printf("bucket[%d] = %d\n", i, lbd_buckets[i]);
        }

        int max_lbd = 0;
        int max_count = 0;
        int seen_so_far = 0;
        for (int i = 0; i < literal_count; ++i) {
            max_lbd = i;
            if (seen_so_far + lbd_buckets[i] > desired_clauses) {
                max_count = desired_clauses - seen_so_far;
                //printf("%d %d %d\n", max_count, desired_clauses, seen_so_far);
                break;
            }
            else {
                seen_so_far += lbd_buckets[i];
            }
        }
        ASSERT(max_count > 0); // this means we've broken out of the loop.
        ASSERT(max_lbd); // now we're in trouble...
        int recounter = max_count;
        for (int i = 0; i < max_lbd; ++i) {
            recounter += lbd_buckets[i];
        }
        //printf("new count: %d\n", recounter);
        //printf("desired  : %d\n", desired_clauses);

        return std::make_pair(max_lbd, max_count);
    }

    std::unique_ptr<int[]> generate_mapping(const cnf_table& c, int& new_index) {
        int max_lbd, max_count;
        std::tie(max_lbd, max_count) = compute_cutoff_values(c);
        //printf("cutoff: %d %d\n", max_lbd, max_count);

        auto m = std::make_unique<int[]>(c.clauses_count);
        std::fill(m.get(), m.get()+c.clauses_count, 0);

        // clause_end is the number of *valid* clauses.
        //printf("Computing m index for #%ld %d\n", std::distance(c.clause_begin(), c.clause_end()), c.clauses_count);
        for (auto cit = c.clause_begin(); cit != c.clause_end(); ++cit) {
            int lbd_score = lbd[cit];
            int old_index = cit - c.clause_begin();
            if (lbd_score <= max_lbd) {
                if (lbd_score == max_lbd) { --max_count; }
                m[old_index] = new_index++;
            }
            else {
                m[old_index] = -1; // this is to be removed.
            }
        }
        return m;
    }



    glue_clauses_db(cnf_table& c):
        lbd(c, c.clauses_max, c.clauses.get()),
        literal_levels(c.max_literal_count),
        lbd_buckets(std::make_unique<int[]>(c.max_literal_count)),
        literal_count(c.max_literal_count),
        current_clause_count(c.clauses_count*4) // * 2 is a quick way of avoiding trying to delete 0-lbd-score clauses (i.e., clauses we must keep in).
    {
        std::fill(begin(lbd), end(lbd), 0);
        std::fill(lbd_buckets.get(), lbd_buckets.get()+literal_count, 0);
    };
};

#endif
