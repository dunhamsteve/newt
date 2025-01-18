stats = {}
acc = ''
name = ''
for line in open('newt.js'):
    if line.startswith('const'):
        if name: stats[name] = len(acc)
        acc = line
        name = line.split()[1]
    else:
        acc += line
if name: stats[name] = len(acc)

sorted_stats = sorted(((v, k) for k, v in stats.items()))
for value, key in sorted_stats:
  print(value, key)
