#include <iterator>
#include "cnf_table.h"
#include "debug.h"
#include "clause_map.h"

class watched_literal_db {
    private:
    struct watch_struct {
        literal w1, w2;
    };
    clause_map<watch_struct> watches_by_clause;
    literal_map<small_set<cnf_table::clause_iterator>> watch_lists;
    small_set<std::pair<literal,cnf_table::clause_iterator>> units;
    int clause_count;

    void on_resize(cnf_table::clause_iterator old_base,
                     cnf_table::clause_iterator new_base,
                     int new_size) {
        // the watches_by_clause is already remapped...
        trace("Starting to remap watched_literal_db\n");
        for (auto it = watch_lists.first_index();
                  it != watch_lists.end_index();
                  ++it) {
            if (it == 0) { continue; };
            small_set<cnf_table::clause_iterator> new_watchers;
            auto old_set = watch_lists[it];
            for (auto w : old_set) {
                int old_index = w - old_base;
                int new_index = old_index;
                cnf_table::clause_iterator new_clause = new_base + new_index;
                new_watchers.insert(new_clause);
            }
            trace("new watch_list: ", new_watchers, "\n");
            watch_lists[it] = new_watchers;
        }

        for (auto it = units.begin(); it != units.end(); ++it) {
            int old_index = std::get<1>(*it) - old_base;
            int new_index = old_index;
            *it = {std::get<0>(*it), new_base + new_index};
        }
    }

    public:

    bool check() {
        for (auto it = watches_by_clause.first_index();
                  it != watches_by_clause.first_index() + clause_count;
                  ++it) {
            const auto p = watches_by_clause[it];
            ASSERT(watch_lists[p.w1].contains(it));
            ASSERT(watch_lists[p.w2].contains(it));
            ASSERT(p.w1 != p.w2);
        }
        for (auto lit = watch_lists.first_index();
                  lit != watch_lists.end_index();
                  ++lit) {
        }
        return true;
    };

    watched_literal_db(cnf_table& cnf):
        watches_by_clause(cnf, cnf.clauses_max, cnf.clauses.get()),
        watch_lists(cnf.max_literal_count*2)
    {
        for (cnf_table::clause_iterator it = cnf.clauses.get();
                it != cnf.clauses.get() + cnf.clauses_count;
                ++it) {
            add_clause(it);
        }

        using namespace std::placeholders;
        // Register ourselves as needing a remap:
        std::function<void(cnf_table::clause_iterator, cnf_table::clause_iterator, int)> m =
            std::bind(&watched_literal_db::on_resize, this, _1, _2, _3);
        cnf.resizers.push_back(m);
    }

    //std::pair<literal,cnf_table::clause_iterator> get_unit() {
    literal get_unit() {
        if (units.size()) {
            auto u = *(units.begin());
            return std::get<0>(u);
        }
        return 0;
    }
    cnf_table::clause_iterator get_cause() {
        ASSERT(units.size());
        auto u = *(units.begin());
        units.erase(u);
        return std::get<1>(u);
    }

    void clear_units() {
        trace("WL: clearing units\n");
        units.clear();
    }

    // maybe this is faster than just clearing the cache?;
    template<typename Assignment>
    void unapply(const Assignment& a, literal l) {
        for (int i = 0; i < units.size(); ++i) {
            auto l = std::get<0>(units[i]);
            auto p = std::get<1>(units[i]);

            if (is_unit_clause_implying(p, a) != l) {
                trace("WL: unapplication leads to popping ", p, " for ", l, "\n");
                units.erase(units[i]);
                --i;
            }
        }
    }

    void add_clause(cnf_table::clause_iterator cit) {
        trace("WL: adding clause ", cit, "\n");
        literal w1 = *(cit->start);
        literal w2;
        if (cit->start+1 == cit->finish) {
            w2 = 0;
        }
        else {
            w2 = *(cit->start+1);
        }
        trace("WL: watched by: ", w1, " ", w2, "\n");
        watches_by_clause[cit] = {w1, w2};
        watch_lists[w1].insert(cit);
        if (w2) watch_lists[w2].insert(cit);
        clause_count++;
    }

    template<typename Assignment>
    literal find_new_literal(cnf_table::clause_iterator cit, const Assignment& a, const watch_struct& p) {
        if (p.w2 == 0) { return 0; } // if our clause is actually a unit clause, we know we'll fail.
        literal safe_lit = 0;
        for (auto x : cit) {
            if (x == p.w1) { continue; }
            if (x == p.w2) { continue; }
            if (a.is_true(x)) { return x; }
            if (!safe_lit && a.is_unassigned(x)) { safe_lit = x; }
        }
        return safe_lit;
    }

    bool has_units() const { return units.size() > 0; }

    template<typename Assignment>
    void apply_literal(const Assignment& a, const literal applied) {
        ASSERT(a.is_true(applied));
        small_set<literal> worklist;
        worklist.insert(-applied);

        small_set<cnf_table::clause_iterator> to_visit = watch_lists[-applied];
        trace("WL: from applied ", applied, " considering clauses:\n");
        for (cnf_table::clause_iterator cit : to_visit) {
            watch_struct& p = watches_by_clause[cit];
            trace("WL: clause ", cit, " watched by ", p.w1, " ", p.w2, "\n");

            if (a.is_true(p.w1)) { continue; }
            if (p.w2 && a.is_true(p.w2)) {
                std::swap(p.w1, p.w2);
                continue;
            }

            if (a.is_false(p.w1) && p.w2 && a.is_false(p.w2)) {
                ASSERT(p.w1 == -applied || p.w2 == -applied);
                // found a conflict. We will have to trust the
                // rest of the machinery's conflict analysis to take
                // things from here.
                // TODO: does this ever in execute?
                return;
            }

            if (p.w2 == -applied) { std::swap(p.w2, p.w1); }
            ASSERT(p.w1 == -applied);

            literal wn = find_new_literal(cit, a, p);

            // We found a new literal to watch in lieu of the
            // negated one.
            if (wn != 0) {
                trace("WL: clause updating watched literal with: ", wn, "\n");
                watch_lists[-applied].erase(cit);
                watch_lists[wn].insert(cit);
                p.w1 = wn;
            }
            // New unit found, save for later.
            else {
                trace("WL: found new unit: ", p.w2, " from clause ", cit, "\n");
                if (!units.contains([&](auto set_p) {
                    return std::get<0>(set_p) == p.w2;
                })) {
                    units.insert({p.w2, cit});
                }
            }
        }
        trace("WL: done applying ", applied, " unit set: ", units, "\n");
    }
};

std::ostream& operator<<(std::ostream& o, const std::pair<literal, cnf_table::clause_iterator> p) {
    return o << "{" << std::get<0>(p) << "|" << std::get<1>(p) << "}";
}
