"""Independent verification against original edge-mask game on all K4 boards.

Breaker may delete any subset of at most the bias, including the empty set.
Maker claims original edges; reachability is checked without contraction.
Deterministic exhaustive comparison for biases 1,2 and horizons 1..4.
"""
from functools import lru_cache
from itertools import combinations,product
from horizon_solver import FiniteHorizonSearch,canonical

EDGES=list(combinations(range(4),2))


def components(maker):
    parent=list(range(4))
    def find(v):
        while parent[v]!=v: v=parent[v]
        return v
    for bit,(u,v) in enumerate(EDGES):
        if maker>>bit&1: parent[find(u)]=find(v)
    return [find(v) for v in range(4)]


def compressed(maker,breaker):
    labels=components(maker)
    if labels[0]==labels[1]: return None
    order=[labels[0],labels[1]]+sorted(set(labels)-{labels[0],labels[1]})
    b=[[0]*len(order) for _ in order]
    for bit,(u,v) in enumerate(EDGES):
        if (maker|breaker)>>bit&1: continue
        i,j=order.index(labels[u]),order.index(labels[v])
        if i!=j: b[i][j]+=1; b[j][i]+=1
    return canonical(tuple(map(tuple,b)))


@lru_cache(None)
def raw(maker,breaker,bias,horizon,phase):
    labels=components(maker)
    if labels[0]==labels[1]: return True
    if horizon==0: return False
    free=[bit for bit in range(len(EDGES)) if not ((maker|breaker)>>bit&1)]
    if phase=='maker':
        return any(raw(maker|1<<bit,breaker,bias,horizon-1,'breaker') for bit in free)
    return all(raw(maker,breaker|sum(1<<bit for bit in ds),bias,horizon,'maker')
               for size in range(min(bias,len(free))+1) for ds in combinations(free,size))


if __name__=='__main__':
    comparisons=0
    engines={n:FiniteHorizonSearch(n,seconds=30,four_shortcut=False) for n in [1,2]}
    for assignment in product(range(3),repeat=len(EDGES)):
        maker=sum(1<<i for i,v in enumerate(assignment) if v==1)
        breaker=sum(1<<i for i,v in enumerate(assignment) if v==2)
        board=compressed(maker,breaker)
        for bias in [1,2]:
            for h in range(1,5):
                for phase in ['maker','breaker']:
                    expected=raw(maker,breaker,bias,h,phase)
                    if board is None: actual=True
                    else:
                        # Counters bound each comparison; reuse only completed cache entries.
                        engine=engines[bias]
                        engine.states=0; engine.response_count=0
                        result=engine.solve(board,h,phase)
                        assert result['wins'] is not None,result
                        actual=result['wins']
                    assert actual==expected,(assignment,bias,h,phase,actual,expected)
                    comparisons+=1
    print({'method':'exhaustive original-edge-mask cross-check','boards':3**len(EDGES),
           'biases':[1,2],'horizons':[1,2,3,4],'phases':['maker','breaker'],
           'comparisons':comparisons,'passed':True,'seed':None})
