"""Independent finite checks of cut reduction, legality and threat score."""
import random
import sys
from pathlib import Path
from functools import lru_cache
from moving_cut import cuts, breaker, next_two_move_repair
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'upper-bound'/'experiments'))
from horizon_solver import contract, two_move_blocking_cost


def run():
    rng=random.Random(215)
    policies=['mincut','regularized_density','balanced','density_0.5',
              'regularized_density_repair','global_repair','global_swap','global_batch']
    for trial in range(120):
        count=rng.randrange(4,8); bias=rng.randrange(1,5)
        b=[[0]*count for _ in range(count)]
        for i in range(count):
            for j in range(i+1,count):
                b[i][j]=b[j][i]=rng.randrange(5)
        # Include actual twin classes, which a fully random board rarely has.
        if trial%2==0:
            for v in range(3,count):
                b[0][v]=b[v][0]=b[0][2]
                b[1][v]=b[v][1]=b[1][2]
            for i in range(2,count):
                for j in range(i+1,count): b[i][j]=b[j][i]=1
        sizes=(1,)*count; state=tuple(map(tuple,b)),sizes
        original=set()
        for mask in range(1<<(count-2)):
            side={0}|{v+2 for v in range(count-2) if mask>>v&1}
            cap=sum(b[i][j] for i in side for j in range(count) if j not in side)
            original.add((cap,len(side)*(count-len(side))))
        assert original=={(cap,mass) for cap,mass,_ in cuts(state)}
        for policy in policies:
            after,status=breaker(state,bias,policy)
            if status=='over_budget': assert b[0][1]>bias
            elif status=='closed_cut':
                q=[row[:] for row in b];q[0][1]=q[1][0]=0
                assert min(c for c,_,_ in cuts((tuple(map(tuple,q)),sizes)))<=bias-b[0][1]
            else:
                q,_=after
                assert q[0][1]==0
                assert all(0<=q[i][j]<=b[i][j] and q[i][j]==q[j][i]
                           for i in range(count) for j in range(count))
                assert sum(b[i][j]-q[i][j] for i in range(count)
                           for j in range(i+1,count))<=bias
        b[0][1]=b[1][0]=0
        board=tuple(map(tuple,b))
        expected=max([0]+[two_move_blocking_cost(contract(board,i,j),bias)
                     for i in range(count) for j in range(i+1,count) if b[i][j]])
        assert expected==next_two_move_repair(board,bias)
    print({'method':'seeded finite cross-checks','seed':215,'boards':120,
           'policies':policies,'cuts_legality_and_threat_score':'passed'})
    print({'method':'original edge-mask policy check, including internal claims',
           'm':6,'bias':2,'policy':'global_repair',**raw_check(6,2)})


def raw_check(m,bias):
    edges=[(i,j) for i in range(m) for j in range(i+1,m)]
    def components(maker):
        parent=list(range(m))
        def find(v):
            while parent[v]!=v:v=parent[v]
            return v
        for z,(i,j) in enumerate(edges):
            if maker>>z&1:parent[find(j)]=find(i)
        groups={}
        for v in range(m):groups.setdefault(find(v),[]).append(v)
        groups=sorted(groups.values(),key=min)
        lookup={v:i for i,g in enumerate(groups) for v in g}
        return groups,lookup
    calls=0
    @lru_cache(None)
    def maker_turn(free,maker):
        nonlocal calls
        calls+=1
        if calls>50000:raise RuntimeError('raw check resource limit')
        groups,lookup=components(maker)
        if lookup[0]==lookup[1]:return True
        for z,(i,j) in enumerate(edges):
            if not free>>z&1:continue
            newfree=free^(1<<z);newmaker=maker|(1<<z)
            if lookup[i]==lookup[j]:
                # Policy explicitly passes after a claim inside a component.
                result=maker_turn(newfree,newmaker)
            else:result=breaker_turn(newfree,newmaker)
            if result:return True
        return False
    @lru_cache(None)
    def breaker_turn(free,maker):
        groups,lookup=components(maker)
        if lookup[0]==lookup[1]:return True
        # Put terminal groups first; the abstract contraction retains these labels.
        groups=sorted(groups,key=lambda g:(0 if 0 in g else 1 if 1 in g else 2,min(g)))
        lookup={v:i for i,g in enumerate(groups) for v in g}
        b=[[0]*len(groups) for _ in groups]
        for z,(i,j) in enumerate(edges):
            if free>>z&1 and lookup[i]!=lookup[j]:
                a,c=lookup[i],lookup[j];b[a][c]+=1;b[c][a]+=1
        state=tuple(map(tuple,b)),tuple(map(len,groups))
        after,status=breaker(state,bias,'global_repair')
        if status=='over_budget':return True
        if status=='closed_cut':return False
        q,_=after
        remaining=[[b[i][j]-q[i][j] for j in range(len(b))] for i in range(len(b))]
        deleted=0
        for z,(i,j) in enumerate(edges):
            a,c=lookup[i],lookup[j]
            if free>>z&1 and a!=c and remaining[a][c]:
                free^=1<<z;remaining[a][c]-=1;remaining[c][a]-=1;deleted+=1
        assert deleted<=bias
        return maker_turn(free,maker)
    maker_wins=breaker_turn((1<<len(edges))-1,0)
    assert not maker_wins
    return {'policy_wins':not maker_wins,'raw_maker_states':calls}


if __name__=='__main__': run()
