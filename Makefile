sat: simple_parser sat.cpp cnf_table.h small_set.h
	clang++ -g -Wall -O2 -std=c++14 sat.cpp simple_parser.o -o sat
	#clang++ -g -D ASSERTS_ON -Wall -O2 -std=c++14 sat.cpp simple_parser.o -o sat
	#clang++ -g -D VERBOSE_ON -D ASSERTS_ON -Wall -O2 -std=c++14 sat.cpp simple_parser.o -o sat
simple_parser: simple_parser.cpp simple_parser.h
	clang++ -Wall -O2 -std=c++14 simple_parser.cpp -c -o simple_parser.o

clean:
	rm -f *~ *.o sat
