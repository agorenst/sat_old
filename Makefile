sat: sat.cpp *.h
	clang++ -g -Wall -O2 -std=c++14 sat.cpp -o sat
	#clang++ -g -D ASSERTS_ON -Wall -O2 -std=c++14 sat.cpp simple_parser.o -o sat
	#clang++ -g -D VERBOSE_ON -D ASSERTS_ON -Wall -O2 -std=c++14 sat.cpp simple_parser.o -o sat
clean:
	rm -f *~ *.o sat
