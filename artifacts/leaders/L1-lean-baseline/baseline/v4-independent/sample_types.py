import csv, re, json, sys
rows=list(csv.DictReader(open('baseline/audit/declarations.tsv'),delimiter='\t'))
# every 400th row (1-based rows 1,401,...)
sample=[rows[i] for i in range(0,len(rows),400)]
def load(path):
    types={}
    cur=None;buf=[]
    for line in open(path,encoding='utf-8',errors='replace'):
        if line.startswith('L1TYPE\t'):
            if cur: types[cur]='\n'.join(buf)
            parts=line.rstrip('\n').split('\t',2)
            cur=parts[1]; buf=[parts[2] if len(parts)>2 else '']
        elif line.startswith('L1TYPEDONE'):
            if cur: types[cur]='\n'.join(buf)
            cur=None
        elif cur is not None:
            buf.append(line.rstrip('\n'))
    if cur: types[cur]='\n'.join(buf)
    return types
t=load('baseline/c1/logs/frozen-type-audit-G1.log'); t.update(load('baseline/c1/logs/frozen-type-audit-G2.log'))
print("types loaded",len(t))
out=[]
for r in sample:
    ty=t.get(r['name'])
    out.append({'name':r['name'],'kind':r['kind'],'module':r['module'],'axioms':r['axioms'],'type':ty})
    print('='*100)
    print(r['name'],'|',r['kind'],'|',r['module'],'| cone:',r['axioms'] or '{}')
    print((ty or '<TYPE NOT FOUND>')[:1200])
json.dump(out,open('baseline/v4-independent/sample-30-types.json','w'),indent=1)
