import csv, collections, json
rows=list(csv.DictReader(open('../audit/declarations.tsv'),delimiter='\t'))
print("rows",len(rows))
names=[r['name'] for r in rows]
print("distinct names",len(set(names)))
c=collections.Counter(names)
dups={k:v for k,v in c.items() if v>1}
print("names in >1 row",len(dups), "total extra rows", sum(v-1 for v in dups.values()))
# names in >1 module
bymod=collections.defaultdict(set)
for r in rows: bymod[r['name']].add(r['module'])
multi={k:v for k,v in bymod.items() if len(v)>1}
print("names in >1 module",len(multi))
mods=set(r['module'] for r in rows)
print("modules with decls",len(mods))
print("kinds",collections.Counter(r['kind'] for r in rows))
print("internal",collections.Counter(r['internal'] for r in rows))
print("axiom cones",collections.Counter(r['axioms'] for r in rows))
# dups by pair
bypair=collections.Counter()
for k,v in multi.items():
    bypair[tuple(sorted(v))]+=1
for k,v in bypair.most_common(10): print(" pair",v,k)
# companion heuristic
comp=sum(1 for k,v in multi.items() if any(s in k for s in ['.ctorIdx','.mk.inj','._abel_','.eq_','.congr_simp','.casesOn','.recOn','.rec','.below','.brecOn','.noConfusion','.sizeOf','.toCtorIdx','.ofFn']))
print("dup names w/ companion-ish substring",comp)
