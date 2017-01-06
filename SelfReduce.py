import sys

def load_cnf(instream):
    for line in instream:
        words = line.split()
        if len(words) == 0:
            continue
        if words[0] in {'c', 'p'}:
            continue
        assert words[-1] == '0'
        yield { int(w) for w in words if w != '0' }

def load_assignment(instream):
    for line in instream:
        for w in line.split():
            yield int(w)

def print_cnf_clause(clause):
    print(' '.join(map(str,clause))+' 0')

def renormalize_cnf(cnf):
    literal_set = {abs(x) for c in cnf for x in c}
    remapper = {}
    for i,x in enumerate(sorted(literal_set)):
        remapper[x] = i + 1
        remapper[-x] = -(i + 1)
    for c in cnf:
        yield { remapper[x] for x in c }


if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.exit(1)

    assignment = set(load_assignment(open(sys.argv[2])))
    negative_assignment = {-x for x in assignment}
    cnf = []

    for c in load_cnf(open(sys.argv[1])):
        if len(c & assignment) != 0:
            continue
        cnf.append(c - negative_assignment)

    new_cnf = list(renormalize_cnf(cnf))
    for new_clause in new_cnf:
        print_cnf_clause(new_clause)
