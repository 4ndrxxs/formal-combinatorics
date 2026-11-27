"""Independent exact reconstruction of the seventh-dimensional finite ray arrangement."""
from collections import Counter,deque
from itertools import product
from math import isqrt
SEED=((0,0,0,0,0,0),(1,4,5,3,3,1),(4,1,3,5,3,1),(5,3,1,4,1,3),
      (3,5,4,1,1,3),(3,3,1,1,4,5),(1,1,3,3,5,4))
ROOT=((2,0),(1,1),(-1,1),(-2,0),(-1,-1),(1,-1))
def add(a,b):
    return tuple((x+y)%6 for x,y in zip(a,b))
def row_dot(a,b):
    terms=[ROOT[(y-x)%6] for x,y in zip((0,*a),(0,*b))]
    return tuple(sum(t) for t in zip(*terms))
def group():
    known={SEED[0]}
    q=deque(known)
    while q:
        a=q.popleft()
        for b in SEED[1:]:
            g=add(a,b)
            if g not in known:known.add(g);q.append(g)
    return known
def check(labels,name):
    ids={v:i for i,v in enumerate(sorted(labels))}
    contexts={tuple(sorted(ids[add(t,b)] for b in SEED)) for t in labels}
    val=Counter(v for C in contexts for v in C)
    assert len(val)==len(labels) and set(val.values())=={7}
    assert len(contexts)==len(labels) and len(contexts)%7
    print(name,len(labels),'rays',len(contexts),'bases;',len(contexts)%7,'mod 7;',7,'bases per ray')
if __name__=='__main__':
    assert all(row_dot(a,b)==((14,0) if a==b else (0,0)) for a in SEED for b in SEED)
    print('all 49 exact cyclotomic Gram entries passed')
    check(group(),'generated subgroup')
    check(set(product(range(6),repeat=6)),'full phase group')

