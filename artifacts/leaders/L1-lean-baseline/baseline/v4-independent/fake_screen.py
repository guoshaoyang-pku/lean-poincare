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
def split_arrows(s):
    # return list of top-level segments split on unicode arrow, respecting (), [], {}
    segs=[];depth=0;cur=''
    i=0
    while i < len(s):
        ch=s[i]
        if ch in '([{': depth+=1
        elif ch in ')]}': depth-=1
        if depth==0 and s.startswith('→',i):
            segs.append(cur);cur='';i+=1;continue
        cur+=ch;i+=1
    segs.append(cur)
    return segs
def conclusion_body(ty):
    # drop leading binders: repeat: strip leading '∀ ... ,' and '{...} →' and '(...) →' and '[...] →'
    s=ty.strip()
    while True:
        s2=s
        if s2.startswith('∀'):
            # find ',' at depth 0
            depth=0
            for i,ch in enumerate(s2):
                if ch in '([{': depth+=1
                elif ch in ')]}': depth-=1
                elif ch==',' and depth==0:
                    s2=s2[i+1:].strip();break
            else: break
        else:
            # leading binder group followed by arrow
            m=re.match(r'^([\{\(\[][^\n]*?[\}\)\]])\s*→\s*',s2)
            if m: s2=s2[m.end():].strip()
        if s2==s: break
        s=s2
    return s
susp=[];checked=0;noarrow=0
for name,ty in T.items():
    if name not in decl: continue
    kind=decl[name]['kind']
    if kind!='theorem': continue
    checked+=1
    segs=split_arrows(norm(ty))
    if len(segs)<2: noarrow+=1; continue
    concl=norm(segs[-1])
    # conclusion after binder stripping too, as fallback
    concl2=norm(conclusion_body(' '.join(segs[:-1])+' → '+segs[-1]).split('→')[-1])
    hyps=[norm(h) for h in segs[:-1]]
    # strip leading binder prefixes from each hyp for the comparison (h : P → compare P)
    for h in hyps:
        hb=h
        m=re.search(r'[\)\}\,\]]\s*:\s*(.*)$',h)
        if m and len(hb)>len(m.group(1)): hb=norm(m.group(1))
        for c in {concl,concl2}:
            if len(hb)>8 and hb==c:
                susp.append((name,kind,hb[:160],c[:160]))
print("theorems with types checked:",checked,"no top-level arrow:",noarrow)
print("suspicious hyp==concl:",len(susp))
for s in susp[:40]: print(s)
# also collect all 'X : P' binder-style hypothesis names for a secondary check: conclusion identical to a hypothesis tail
