#ifndef WATCHED_LITERALS
#define WATCHED_LITERALS

#include <iterator>
#include "cnf.h"
#include "debug.h"
#include "clause_map.h"

#include <iostream>

std::ostream& operator<<(std::ostream& o, const std::pair<literal, cnf::clause_iterator> p) {
    return o << "{" << std::get<0>(p) << "|" << std::get<1>(p) << "}";
}

class watched_literals {
    private:
    struct watch_struct {
        literal w1, w2;
    };
    clause_map<watch_struct> watches_by_clause;
    literal_map<small_set<cnf::clause_iterator>> watch_lists;
    small_set<std::pair<literal,cnf::clause_iterator>> units;
    int clause_count = 0;

public:
    void print(std::ostream& o) const {
        for (auto i=watch_lists.first_index(); i != watch_lists.end_index(); ++i) {
            if (i == 0) continue;
            o << i << " : ";
            for (auto cit : watch_lists.get_copy(i)) { o << "[" << cit << "]"; }
            o << std::endl;
        }
        o << "------------------" << std::endl;
        for (auto cit = watches_by_clause.first_index();
                  cit != watches_by_clause.first_index() + clause_count;
                  ++cit) {
            o << cit << " : {" << watches_by_clause.get_copy(cit).w1 << ", " << watches_by_clause.get_copy(cit).w2 << "}" << std::endl;
        }
        o << "-------units------" << std::endl;
        for (auto&& p : units) {
            o << p.second << " -> " << p.first << std::endl;
        }
    }
private:

    void on_resize(cnf::clause_iterator old_base,
                     cnf::clause_iterator new_base,
                     int new_size) {
        // the watches_by_clause is already remapped...
        TRACE(*this);
        TRACE("Starting to resize watched_literals\n");
        //print(std::cout);
        for (auto it = watch_lists.first_index();
                  it != watch_lists.end_index();
                  ++it) {
            if (it == 0) { continue; };
            small_set<cnf::clause_iterator> new_watchers;
            auto old_set = watch_lists[it];
            for (auto w : old_set) {
                int index = w - old_base;
                cnf::clause_iterator new_clause = new_base + index;
                new_watchers.insert(new_clause);
            }
            trace("new watch_list for ",  it, ": ", new_watchers, "\n");
            watch_lists[it] = new_watchers;
        }

        for (auto it = units.begin(); it != units.end(); ++it) {
            int index = std::get<1>(*it) - old_base;
            *it = {std::get<0>(*it), new_base + index};
        }

        TRACE("Done\n");
        TRACE(*this);
        ASSERT(sanity_check());
    }

    void on_remap(int* m, int n, cnf::clause_iterator start) {
        // note that the watches_by_clause has already been remapped.
        // this fails: ASSERT(sanity_check());
        //print(std::cout);

        for (auto i=watch_lists.first_index(); i != watch_lists.end_index(); ++i) {
            if (i == 0) { continue; }
            small_set<cnf::clause_iterator> new_watchers;
            auto old_set = watch_lists[i];
            for (auto c : old_set) {
                int old_index = c - start;
                ASSERT(old_index >= 0);
                if (m[old_index] == -1) { continue; } // clause removed
                auto new_clause = start + m[old_index]; // remap...
                ASSERT(new_clause - start >= 0);
                new_watchers.insert(new_clause);
            }
            watch_lists[i] = new_watchers;
        }

        // let's just keep things simple for now..
        clause_count = n;
        units.clear();
        //print(std::cout);
        //printf("Resizing to size: %d\n", n);
        ASSERT(sanity_check());
    }

    public:

    bool sanity_check() {
        for (auto it = watches_by_clause.first_index();
                  it != watches_by_clause.first_index() + clause_count;
                  ++it) {
            //trace("WL CHECK: ", it, "\n");
            const auto p = watches_by_clause[it];
            ASSERT(watch_lists[p.w1].contains(it));
            if (p.w2) { ASSERT(watch_lists[p.w2].contains(it)); }
            else { ASSERT(size(it) == 1); }
            ASSERT(p.w1 != p.w2);
        }
        for (auto lit = watch_lists.first_index();
                  lit != watch_lists.end_index();
                  ++lit) {
            if (lit == 0) { continue; }
            for (auto cit : watch_lists[lit]) {
                //trace("testing: ", cit, " | ", lit, "\n");
                ASSERT(clause_contains(cit, lit));
            }
        }
        return true;
    };

    watched_literals(cnf& cnf):
        watches_by_clause(cnf, cnf.clauses_max, cnf.clauses.get()),
        watch_lists(cnf.max_literal_count)
    {
        for (cnf::clause_iterator it = cnf.clauses.get();
                it != cnf.clauses.get() + cnf.clauses_count;
                ++it) {
            add_clause(it);
        }
        ASSERT(sanity_check());

        using namespace std::placeholders;
        // Register ourselves as needing a remap:
        std::function<void(cnf::clause_iterator, cnf::clause_iterator, int)> m =
            std::bind(&watched_literals::on_resize, this, _1, _2, _3);
        cnf.resizers.push_back(m);
        cnf.remappers.push_back(std::bind(&watched_literals::on_remap, this, _1, _2, _3));
    }

    std::pair<literal,cnf::clause_iterator> pop_unit() {
        auto u = *(units.begin());
        units.erase(u);
        return u;
    }

    void clear_units() {
        trace("WL: clearing units\n");
        units.clear();
    }

    void add_unit(literal l, const cnf::clause_iterator c) {
        if (!units.contains([&](auto set_p) {
            return std::get<0>(set_p) == l;
        })) {
            units.insert({l, c});
        }
    }

    void add_clause(cnf::clause_iterator cit, literal l, const assignment& a) {
        trace("WL: adding clause ", cit, "\n");
        ASSERT(cit->start < cit->finish);
        ASSERT(std::find(begin(cit), end(cit), l) != end(cit));
        literal w1 = l;
        literal w2 = 0; // case where size is unary.
        int largest_index = -2; // must be smaller than any real index.
        for (auto x : cit) {
            if (x == w1) { continue; }
            ASSERT(!a.is_unassigned(x));
            TRACE("About to find decision number: ", -x, "\n");
            if (a.decision_number(-x) > largest_index) {
                w2 = x;
                largest_index = a.decision_number(-x);
            }
        }

        // w2 == 0 if and only if size(cit) == 1
        ASSERT(size(cit) > 1 || w2 == 0);
        ASSERT(w2 != 0 || size(cit) == 1);

        ASSERT(w1 != w2);
        trace("WL: watched by: ", w1, " ", w2, "\n");
        watches_by_clause[cit] = {w1, w2};
        watch_lists[w1].insert(cit);
        if (w2) watch_lists[w2].insert(cit);
        clause_count++;


        ASSERT(sanity_check());
    }

    void add_clause(cnf::clause_iterator cit) {
        trace("WL: adding clause ", cit, "\n");
        ASSERT(cit->start < cit->finish);
        literal w1 = *(cit->start);
        literal w2;
        if (cit->start+1 == cit->finish) {
            w2 = 0;
        }
        else {
            w2 = *(cit->start+1);
        }
        trace("WL: watched by: ", w1, " ", w2, "\n");
        ASSERT(w1 != w2);
        watches_by_clause[cit] = {w1, w2};
        watch_lists[w1].insert(cit);
        if (w2) watch_lists[w2].insert(cit);
        clause_count++;


        ASSERT(sanity_check());
    }

    template<typename Assignment>
    literal find_new_literal(cnf::clause_iterator cit, const Assignment& a, const watch_struct& p) {
        if (p.w2 == 0) { return 0; } // if our clause is actually a unit clause, we know we'll fail.
        literal safe_lit = 0;
        for (auto x : cit) {
            if (x == p.w1) { continue; }
            if (x == p.w2) { continue; }
            if (a.is_true(x)) { return x; }
            if (safe_lit == 0 && a.is_unassigned(x)) { safe_lit = x; }
        }
        return safe_lit;
    }

    bool has_units() const { return units.size() > 0; }

    template<typename Assignment>
    void reapply(const Assignment& a) {
        for (auto l : a) {
            apply(a, l);
        }
    }

    template<typename Assignment>
    void apply(const Assignment& a, const literal applied) {
        ASSERT(a.is_true(applied));

        small_set<cnf::clause_iterator> to_visit = watch_lists[-applied];
        trace("WL: from applied ", applied, " considering clauses:\n");
        for (cnf::clause_iterator cit : to_visit) {
            watch_struct& p = watches_by_clause[cit];
            trace("WL: clause ", cit, " watched by ", p.w1, " ", p.w2, "\n");

            if (p.w2 == -applied) { std::swap(p.w2, p.w1); }
            ASSERT(p.w1 == -applied);

            // This is a unit clause.
            if (p.w2 == 0) {
                TRACE("WL: found failed clause ", cit, "\n");
                // this must have been implied, but also contradicted.
                add_unit(-applied, cit);
                continue;
            }

            ASSERT(p.w2 != 0);

            if (a.is_false(p.w2)) {
                literal wn = find_new_literal(cit, a, p);
                if (wn) {
                    watch_lists[p.w2].erase(cit);
                    watch_lists[wn].insert(cit);
                    p.w2 = wn;
                }
                else {
                    TRACE("WL: found failed clause ", cit, "\n");
                    // this must have been implied, but also contradicted.
                    add_unit(-applied, cit);
                    continue;
                }
            }

            if (a.is_true(p.w2)) { continue; }

            literal wn = find_new_literal(cit, a, p);
            if (wn) {
                watch_lists[p.w1].erase(cit);
                watch_lists[wn].insert(cit);
                p.w1 = wn;
                ASSERT(!a.is_false(p.w1) && !a.is_false(p.w2));
            }
            else {
                TRACE("WL: found new unit: ", cit, " by ", p.w2, "\n");
                ASSERT(p.w2 == clause_implies(cit, a));
                add_unit(p.w2, cit);
            }
        }
        trace("WL: done applying ", applied, " unit set: ", units, "\n");
        ASSERT(sanity_check());
    }
};

std::ostream& operator<<(std::ostream& o, const watched_literals& w) {
    w.print(o);
    return o;
}

#endif
