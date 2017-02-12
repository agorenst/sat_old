import sys
lines = []
for line in sys.stdin:
    if len(line) == 0:
        continue
    lines.append([int(x) for x in line.split()])

sets = []
for l in lines:
    sets.append({x for x in l})

result = sets[0]
for s in sets[1:]:
    result = result & s

print(result)
