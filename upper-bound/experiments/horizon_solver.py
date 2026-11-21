"""Exact finite-horizon minimax on contracted Maker components.

Parallel free-edge counts retain all legal deletion allocations. Terminal
components occupy indices 0,1; outside components follow. Breaker first in
before(), Maker next in after(). No randomness, no seed.
"""
from functools import lru_cache
from itertools import permutations
from time import monotonic


def canonical(board):
    n=len(board)
    choices=[]
    # Full symmetry reduction is factorial. Skipping it on larger positions
    # reduces performance, never correctness.
    outside_orders=permutations(range(2,n)) if n<=7 else [tuple(range(2,n))]
    for outside in outside_orders:
        for terminals in [(0,1),(1,0)]:
            order=terminals+outside
            choices.append(tuple(tuple(board[i][j] for j in order) for i in order))
    return min(choices)


def contract(board,i,j):
    # Called with i<j and never i=0,j=1. Terminal labels therefore survive.
    order=[v for v in range(len(board)) if v!=j]
    groups=[(i,j) if v==i else (v,) for v in order]
    merged=tuple(tuple(0 if a==b else sum(board[u][v] for u in ga for v in gb)
                       for b,gb in enumerate(groups)) for a,ga in enumerate(groups))
    return canonical(merged)


def responses(board,budget):
    n=len(board)
    joins=board[0][1]
    if joins>budget: return
    q=[list(row) for row in board]
    q[0][1]=q[1][0]=0
    edges=[(i,j) for i in range(n) for j in range(i+1,n)
           if (i,j)!=(0,1) and q[i][j]>0]
    remaining=min(budget-joins,sum(q[i][j] for i,j in edges))
    suffix=[0]*(len(edges)+1)
    for z in reversed(range(len(edges))):
        i,j=edges[z]; suffix[z]=suffix[z+1]+q[i][j]
    def rec(z,left):
        if z==len(edges):
            if left==0: yield canonical(tuple(map(tuple,q)))
            return
        i,j=edges[z]; cap=q[i][j]
        for d in range(max(0,left-suffix[z+1]),min(cap,left)+1):
            q[i][j]=q[j][i]=cap-d
            yield from rec(z+1,left-d)
        q[i][j]=q[j][i]=cap
    yield from rec(0,remaining)


@lru_cache(None)
def after(board,bias,horizon):
    if horizon==0: return False
    if board[0][1]>0: return True
    if horizon==1: return False
    if horizon==2:
        return any((board[0][v]>0 and board[1][v]>bias) or
                   (board[1][v]>0 and board[0][v]>bias)
                   for v in range(2,len(board)))
    for i in range(len(board)):
        for j in range(i+1,len(board)):
            if board[i][j]>0 and before(contract(board,i,j),bias,horizon-1):
                return True
    return False


@lru_cache(None)
def before(board,bias,horizon):
    if horizon==0: return False
    if board[0][1]>bias: return True
    if horizon==2:
        return two_move_blocking_cost(board,bias)>bias
    # It suffices to use the full available budget: additional deletions
    # cannot improve Maker's chances. Joining edges must all be deleted.
    return all(after(q,bias,horizon) for q in responses(board,bias))


def two_move_blocking_cost(board,bias):
    from three_move_search import blocking_cost
    return board[0][1]+sum(blocking_cost(board[0][v],board[1][v],bias)
                            for v in range(2,len(board)))


def four_move_witness(board,bias):
    """Sufficient adaptive auxiliary-triple threat, not a complete detector.

    Claim u-v. A third vertex w is robust if the terminal-degree totals of
    u,v,w remain a two-move threat after ANY bias-sized deletion. Breaker
    must both neutralize the pair and delete every pair--robust-third edge.
    Those sets are disjoint. If their sum exceeds bias, Maker wins in <=4.
    """
    from three_move_search import blocking_cost
    if board[0][1]: return None  # immediate win handled by caller
    for u in range(2,len(board)):
        for v in range(u+1,len(board)):
            if not board[u][v]: continue
            p=board[0][u]+board[0][v]
            q=board[1][u]+board[1][v]
            required=blocking_cost(p,q,bias)
            robust=[]
            boundary=0
            for w in range(2,len(board)):
                if w in (u,v): continue
                pw=p+board[0][w]; qw=q+board[1][w]
                if pw>2*bias and qw>2*bias and pw+qw>4*bias:
                    robust.append(w)
                    boundary+=board[u][w]+board[v][w]
            if required+boundary>bias:
                return {'first_edge':[u,v],'robust_third_vertices':robust,
                        'pair_blocking_cost':required,'boundary_cost':boundary}
    return None


def terminal_cut_capacity(board):
    outside=len(board)-2
    return min(sum(board[i][j] for i in side for j in range(len(board)) if j not in side)
               for mask in range(1<<outside)
               for side in [{0}|{i+2 for i in range(outside) if mask>>i&1}])


class SearchLimit(Exception):
    pass


class FiniteHorizonSearch:
    """General minimax with explicit unknown on resource exhaustion."""
    def __init__(self,bias,max_states=20000,max_responses=100000,seconds=5,
                 four_shortcut=True):
        self.bias=bias
        self.max_states=max_states; self.max_responses=max_responses
        self.seconds=seconds
        self.four_shortcut=four_shortcut
        self.cache={}; self.cut_cache={}
        self.states=0; self.response_count=0

    def check(self):
        if (self.states>self.max_states or self.response_count>self.max_responses
                or monotonic()>self.deadline):
            raise SearchLimit

    def evaluate(self,board,horizon,phase):
        self.check()
        key=board,horizon,phase
        if key in self.cache: return self.cache[key]
        self.states+=1
        self.check()
        n=self.bias
        if horizon==0:
            result=False
        elif phase=='maker':
            if board[0][1]>0: result=True
            elif horizon==1: result=False
            elif horizon==2:
                result=any((board[0][v]>0 and board[1][v]>n) or
                           (board[1][v]>0 and board[0][v]>n)
                           for v in range(2,len(board)))
            elif self.four_shortcut and horizon>=4 and four_move_witness(board,n) is not None:
                result=True
            else:
                result=False
                for i in range(len(board)):
                    for j in range(i+1,len(board)):
                        if board[i][j] and self.evaluate(contract(board,i,j),horizon-1,'breaker'):
                            result=True; break
                    if result: break
        else:
            if board[0][1]>n: result=True
            elif horizon==2: result=two_move_blocking_cost(board,n)>n
            else:
                if board not in self.cut_cache:
                    self.cut_cache[board]=terminal_cut_capacity(board)
                if self.cut_cache[board]<=n:
                    result=False
                else:
                    result=True
                    for q in responses(board,n):
                        self.response_count+=1
                        self.check()
                        if not self.evaluate(q,horizon,'maker'):
                            result=False; break
        self.cache[key]=result
        return result

    def solve(self,board,horizon,phase='maker'):
        self.deadline=monotonic()+self.seconds
        started=monotonic()
        try:
            result=self.evaluate(canonical(board),horizon,phase)
            status='win' if result else 'loss_within_horizon'
        except SearchLimit:
            result=None; status='unknown_resource_limit'
        return {'status':status,'wins':result,'horizon':horizon,'bias':self.bias,
                'phase':phase,'states':self.states,'responses':self.response_count,
                'seconds':round(monotonic()-started,4)}


def position(degrees,outside_edges):
    n=len(degrees)+2
    b=[[0]*n for _ in range(n)]
    for v,(p,q) in enumerate(degrees,2):
        b[0][v]=b[v][0]=p; b[1][v]=b[v][1]=q
    for u,v in outside_edges:
        b[u+2][v+2]=b[v+2][u+2]=1
    return canonical(tuple(map(tuple,b)))


if __name__=='__main__':
    cases=[
        ('auxiliary pair',4,[(4,4),(4,4)],[(0,1)],3,True),
        ('activated pure vertex',4,[(5,0),(4,4)],[(0,1)],3,True),
        ('balanced boundary depth three',4,[(3,3)]*3,
         [(0,1),(0,2),(1,2)],3,False),
        ('balanced boundary depth four',4,[(3,3)]*3,
         [(0,1),(0,2),(1,2)],4,True),
    ]
    for name,bias,degrees,edges,horizon,expected in cases:
        actual=after(position(degrees,edges),bias,horizon)
        assert actual==expected,(name,actual,expected)
        print(name,{'bias':bias,'horizon':horizon,'wins':actual},flush=True)
    print('cache',after.cache_info(),before.cache_info(),flush=True)
