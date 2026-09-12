import json,re,collections
def load(path):
    types={};cur=None;buf=[]
    for line in open(path,encoding='utf-8',errors='replace'):
        if line.startswith('L1TYPE\t'):
            if cur: types[cur]=' '.join(buf)
            p=line.rstrip('\n').split('\t',2); cur=p[1]; buf=[p[2] if len(p)>2 else '']
        elif line.startswith('L1TYPEDONE'):
            if cur: types[cur]=' '.join(buf)
            cur=None
        elif cur is not None: buf.append(line.rstrip('\n'))
    if cur: types[cur]=' '.join(buf)
    return types
T=load('baseline/c1/logs/frozen-type-audit-G1.log'); T.update(load('baseline/c1/logs/frozen-type-audit-G2.log'))
decl=json.load(open('baseline/audit/axiom-audit.json'))['declarations']
def norm(s): return re.sub(r'\s+',' ',s).strip()
def depth_split(s,sep='→'):
    segs=[];depth=0;cur=''
    i=0
    while i<len(s):
        ch=s[i]
        if ch in '([{': depth+=1
        elif ch in ')]}': depth-=1
        if depth==0 and s.startswith(sep,i):
            segs.append(cur);cur='';i+=len(sep);continue
        cur+=ch;i+=1
    segs.append(cur);return segs
def strip_binders(s):
    s=s.strip()
    for _ in range(60):
        if s.startswith('∀'):
            d=0
            for i,ch in enumerate(s):
                if ch in '([{': d+=1
                elif ch in ')]}': d-=1
                elif ch==',' and d==0: s=s[i+1:].strip();break
            else: break
        else:
            m=re.match(r'^[\(\{\[][^\(\)\{\}\[\]]*[\)\}\]]\s*→\s*',s)
            if m: s=s[m.end():].strip();continue
            break
    return s
pairs=[];checked=0;noarrow=0
for name,ty in T.items():
    if name not in decl or decl[name]['kind']!='theorem': continue
    checked+=1
    body=strip_binders(norm(ty))
    segs=depth_split(body)
    if len(segs)<2: noarrow+=1; continue
    concl=norm(segs[-1])
    hyps=[norm(h) for h in segs[:-1]]
    for h in hyps:
        hb=h
        # strip a hypothesis label 'h : P' (top-level colon)
        d=0
        for i,ch in enumerate(h):
            if ch in '([{': d+=1
            elif ch in ')]}': d-=1
            elif ch==':' and d==0 and i>0:
                cand=h[i+1:].strip()
                if len(cand)>4: hb=cand
                break
        if len(hb)>4 and hb==concl:
            pairs.append((name,hb,concl,ty))
print("theorems checked",checked,"body-no-arrow",noarrow,"self-implication (hyp==concl) hits:",len(pairs))
for n,h,c,ty in pairs:
    print('---',n)
    print('   hyp==concl:',h[:200])
    print('   module:',decl[n]['module'])
json.dump([{'name':n,'prop':h,'module':decl[n]['module']} for n,h,c,ty in pairs],
          open('baseline/v4-independent/self-implication-hits.json','w'),indent=1)
