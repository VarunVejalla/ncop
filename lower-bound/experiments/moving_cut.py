"""Moving-cut Breaker policies against exhaustive, adaptive Maker play.

Breaker first, bias n, full K_m. All Maker component-merging moves are tried;
internal claims are dominated. Resource exhaustion is unknown. No randomness.
This checks fixed policies, not optimal Breaker play or asymptotic endpoints.
The raw extension of each policy passes after any internal Maker claim.
"""
import json
from functools import lru_cache
from time import monotonic
from itertools import product


def initial(m):
    return tuple(tuple(int(i!=j) for j in range(m)) for i in range(m)),(1,)*m


def contract(state,i,j):
    board,sizes=state
    order=[v for v in range(len(board)) if v!=j]
    groups=[(i,j) if v==i else (v,) for v in order]
    merged=tuple(tuple(0 if a==b else sum(board[u][v] for u in ga for v in gb)
                 for b,gb in enumerate(groups)) for a,ga in enumerate(groups))
    return merged,tuple(sum(sizes[u] for u in group) for group in groups)


def cuts(state):
    board,sizes=state
    total=sum(sizes); count=len(board)
    # True twins are interchangeable in cut capacity and vertex mass. Enumerate
    # their selected counts, retaining one representative per equivalent cut.
    groups=[]
    for v in range(2,count):
        for group in groups:
            u=group[0]
            if sizes[u]==sizes[v] and all(board[u][w]==board[v][w]
                                         for w in range(count) if w not in (u,v)):
                group.append(v);break
        else: groups.append([v])
    for selections in product(*(range(len(g)+1) for g in groups)):
        side={0}|{v for g,k in zip(groups,selections) for v in g[:k]}
        cap=sum(board[i][j] for i in side for j in range(count) if j not in side)
        mass=sum(sizes[i] for i in side)
        yield cap,mass*(total-mass),side


def breaker(state,bias,policy):
    batch=policy=='global_batch'
    swaps=policy=='global_swap'
    global_repair=policy in ('global_repair','global_swap','global_batch')
    if global_repair: policy='regularized_density_repair'
    repair=policy.endswith('_repair')
    if repair: policy=policy[:-7]
    board,sizes=state
    joins=board[0][1]
    if joins>bias: return None,'over_budget'
    q=[list(row) for row in board]; q[0][1]=q[1][0]=0
    forced=[row[:] for row in q]
    left=bias-joins
    options=list(cuts((tuple(map(tuple,q)),sizes)))
    minimum=min(options,key=lambda item:item[0])
    if minimum[0]<=left: return None,'closed_cut'
    if policy=='mincut': chosen=minimum
    elif policy=='regularized_density':
        chosen=min(options,key=lambda item:((item[0]+bias)/item[1],item[0]))
    elif policy.startswith('density_'):
        regularizer=float(policy.split('_')[1])
        chosen=min(options,key=lambda item:((item[0]+regularizer*bias)/item[1],item[0]))
    elif policy=='balanced':
        chosen=min(options,key=lambda item:(item[0]-1.1*item[1],item[0]))
    else: raise ValueError(policy)
    side=chosen[2]
    # Greedy endpoint-threat priority, recomputed after each deletion.
    # Edges within Maker components are absent. Parallel edges interchangeable.
    for _ in range(left):
        choices=[]
        for i in side:
            for j in range(len(q)):
                if j in side or not q[i][j]: continue
                if i in (0,1) or j in (0,1):
                    terminal=i if i in (0,1) else j
                    vertex=j if i in (0,1) else i
                    p=q[terminal][vertex]; opposite=q[1-terminal][vertex]
                    score=(int(p>bias and opposite>0),p+opposite,p)
                else:
                    score=(0,max(q[0][i]+q[1][i],q[0][j]+q[1][j]),q[i][j])
                choices.append((score,-min(i,j),-max(i,j),i,j))
        if global_repair:
            selected={(min(c[-2:]),max(c[-2:])) for c in choices}
            for i in range(len(q)):
                for j in range(i+1,len(q)):
                    if q[i][j] and (i,j) not in selected:
                        choices.append(((-1,0,0),-i,-j,i,j))
        if not choices: break
        if repair:
            scored=[]
            for choice in choices:
                i,j=choice[-2:]
                q[i][j]-=1;q[j][i]-=1
                risk=next_two_move_repair(q,bias)
                q[i][j]+=1;q[j][i]+=1
                scored.append((-risk,choice))
            *_,i,j=max(scored)[1]
        else:
            *_,i,j=max(choices)
        q[i][j]-=1; q[j][i]-=1
    if swaps:
        # Improve a completed batch, rather than greedily placing each deletion.
        # Mandatory terminal joins are never restored.
        for _ in range(bias):
            risk=next_two_move_repair(q,bias)
            if risk<=bias:break
            best=None;best_risk=risk
            deleted=[(i,j) for i in range(len(q)) for j in range(i+1,len(q))
                     if forced[i][j]>q[i][j]]
            free=[(i,j) for i in range(len(q)) for j in range(i+1,len(q)) if q[i][j]]
            for i,j in deleted:
                q[i][j]+=1;q[j][i]+=1
                for u,v in free:
                    if (i,j)==(u,v):continue
                    q[u][v]-=1;q[v][u]-=1
                    candidate=next_two_move_repair(q,bias)
                    q[u][v]+=1;q[v][u]+=1
                    if candidate<best_risk:best_risk=candidate;best=(i,j,u,v)
                q[i][j]-=1;q[j][i]-=1
            if best is None:break
            i,j,u,v=best
            q[i][j]+=1;q[j][i]+=1;q[u][v]-=1;q[v][u]-=1
    if batch:
        best_risk=next_two_move_repair(q,bias)
        if best_risk>bias:
            for index,candidate in enumerate(deletion_batches(forced,left)):
                if index>=2000:break
                risk=next_two_move_repair(candidate,bias)
                if risk<best_risk:q=[list(row) for row in candidate];best_risk=risk
                if best_risk<=bias:break
    return (tuple(map(tuple,q)),sizes),'continue'


def deletion_batches(board,budget):
    """All full-budget allocations on a board with mandatory joins removed."""
    q=[list(row) for row in board]
    edges=[(i,j) for i in range(len(q)) for j in range(i+1,len(q)) if q[i][j]]
    suffix=[0]*(len(edges)+1)
    for z in reversed(range(len(edges))):
        i,j=edges[z];suffix[z]=suffix[z+1]+q[i][j]
    def rec(z,left):
        if z==len(edges):
            if not left:yield tuple(map(tuple,q))
            return
        i,j=edges[z];cap=q[i][j]
        for d in range(max(0,left-suffix[z+1]),min(cap,left)+1):
            q[i][j]=q[j][i]=cap-d
            yield from rec(z+1,left-d)
        q[i][j]=q[j][i]=cap
    yield from rec(0,min(budget,suffix[0]))


def next_two_move_repair(board,bias):
    """Max exact two-move blocking cost after any one Maker contraction."""
    def block(p,q):return min(p,q,max(p-bias,0)+max(q-bias,0))
    vertices=range(2,len(board)); p=board[0]; q=board[1]
    costs=[block(p[v],q[v]) for v in vertices]; base=sum(costs)
    worst=0
    for v in vertices:
        if p[v]:
            worst=max(worst,q[v]+sum(block(p[w]+board[v][w],q[w])
                                     for w in vertices if w!=v))
        if q[v]:
            worst=max(worst,p[v]+sum(block(p[w],q[w]+board[v][w])
                                     for w in vertices if w!=v))
        for w in range(v+1,len(board)):
            if board[v][w]:
                worst=max(worst,base-costs[v-2]-costs[w-2]
                          +block(p[v]+p[w],q[v]+q[w]))
    return worst


class Limit(Exception): pass


def verify(m,n,policy,max_states=50000,seconds=3):
    started=monotonic(); deadline=started+seconds; states=0
    @lru_cache(None)
    def visit(state):
        nonlocal states
        states+=1
        if states>max_states or monotonic()>deadline: raise Limit
        after,status=breaker(state,n,policy)
        if status=='over_budget': return ()
        if status=='closed_cut': return None
        board,_=after
        if board[0][1]: return ((0,1),)
        # Maker tries terminal attachments first, then auxiliary mergers.
        edges=[(i,j) for i in range(len(board)) for j in range(i+1,len(board))
               if board[i][j] and (i,j)!=(0,1)]
        for i,j in edges:
            suffix=visit(contract(after,i,j))
            if suffix is not None: return ((i,j),)+suffix
        return None
    try:
        witness=visit(initial(m))
        outcome='policy_wins' if witness is None else 'maker_counterexample'
    except Limit:
        witness=None;outcome='unknown_resource_limit'
    return {'m':m,'bias':n,'ratio':m/n,'policy':policy,'status':outcome,
            'states':states,'seconds':round(monotonic()-started,4),
            'counterexample_component_moves':witness}


def verify_menu(m,n,max_states=50000,seconds=3):
    """Exact AND/OR search within a restricted menu of legal Breaker responses."""
    started=monotonic(); deadline=started+seconds; states=0
    policies=['regularized_density','mincut','balanced',
              'density_0.25','density_0.5','density_2','density_4']
    @lru_cache(None)
    def visit(state):
        nonlocal states
        states+=1
        if states>max_states or monotonic()>deadline: raise Limit
        candidates=[]
        for policy in policies:
            after,status=breaker(state,n,policy)
            if status=='over_budget': return False
            if status=='closed_cut': return True
            if after not in candidates: candidates.append(after)
        for after in candidates:
            board,_=after
            if all(visit(contract(after,i,j))
                   for i in range(len(board)) for j in range(i+1,len(board))
                   if board[i][j] and (i,j)!=(0,1)):
                return True
        return False
    try:
        result=visit(initial(m))
        outcome='menu_strategy_wins' if result else 'no_winning_menu_strategy'
    except Limit:
        result=None;outcome='unknown_resource_limit'
    return {'m':m,'bias':n,'ratio':m/n,'status':outcome,'wins':result,
            'states':states,'seconds':round(monotonic()-started,4),
            'breaker_menu':policies}


if __name__=='__main__':
    print(json.dumps({'method':'fixed Breaker policy, exhaustive adaptive Maker',
        'turn_order':'Breaker first','seed':None,'seconds_per_case':3,
        'states_per_case':50000}),flush=True)
    for n in [2,3,4]:
        for m in [2*n,2*n+1,2*n+2]:
            for policy in ['mincut','regularized_density','balanced']:
                print(json.dumps(verify(m,n,policy)),flush=True)
    for n,m in [(2,6),(3,8),(4,11),(5,13),(6,15)]:
        for policy in ['mincut_repair','regularized_density_repair','balanced_repair',
                       'global_repair','global_swap','global_batch']:
            print(json.dumps(verify(m,n,policy)),flush=True)
    for n,m in [(2,6),(3,8),(4,10),(4,11),(5,12),(5,13)]:
        print(json.dumps(verify_menu(m,n)),flush=True)
    print(json.dumps(verify(12,5,'regularized_density')),flush=True)
