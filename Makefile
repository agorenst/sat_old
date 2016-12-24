watched_literals_test: watched_literals.h watched_literals_test.cpp simple_parser cnf_table.h
	clang++ -Wall -O2 -std=c++14 watched_literals_test.cpp simple_parser.o -o watched_literals_test
basic_dpll: cnf_table.h simple_parser
	clang++ -Wall -O2 -std=c++14 basic_dpll.cpp simple_parser.o -o basic_dpll
cnf_table_test: cnf_table_test.cpp cnf_table.h simple_parser
	clang++ -Wall -O2 -std=c++14 cnf_table_test.cpp simple_parser.o -o cnf_table_test
literal_map_test: literal_map_test.cpp literal_map.h
	clang++ -Wall -O2 -std=c++14 literal_map_test.cpp -o literal_map_test

simple_parser: simple_parser.cpp simple_parser.h
	clang++ -Wall -O2 -std=c++14 simple_parser.cpp -c -o simple_parser.o

clean:
	rm -f *~ *.o literal_map_test cnf_table_test basic_dpll watched_literals_test
