"""Restricted regular-block asymptotic model, not a universal counting proof.

Breaker-first; measured after deletion; degrees and vertex counts scaled by n.
SciPy MILP chooses retained outside-edge densities and which type pairs exist.
Within each type all vertices have the same retained degree to every type.
This regularity and sampled type distributions are substantive restrictions.
"""
import json
import random
from math import sqrt
from itertools import combinations_with_replacement
import numpy as np
from scipy.optimize import milp, Bounds, LinearConstraint


def blocking(p,q): return min(p,q,max(p-1,0)+max(q-1,0))


def optimize(types,masses,x,forks):
    active=[i for i,m in enumerate(masses) if m>1e-8]
    types=[types[i] for i in active]; masses=np.array([masses[i] for i in active])
    pairs=list(combinations_with_replacement(range(len(types)),2)); size=len(pairs)
    caps=np.array([masses[i]*masses[j]/(2 if i==j else 1) for i,j in pairs])
    for z,(i,j) in enumerate(pairs):
        if blocking(types[i][0]+types[j][0],types[i][1]+types[j][1])>1+1e-9:
            caps[z]=0
    degree=np.zeros((len(types),len(types),2*size))
    for z,(i,j) in enumerate(pairs):
        degree[i,j,z]=(2 if i==j else 1)/masses[i]
        if i!=j: degree[j,i,z]=1/masses[j]
    rows=[]; bounds=[]
    def add(row,bound): rows.append(row); bounds.append(bound)
    pure_a=[i for i,(p,q) in enumerate(types) if p>1 and q==0]
    pure_b=[i for i,(p,q) in enumerate(types) if q>1 and p==0]
    for i,(p,q) in enumerate(types):
        if q>0: add(degree[i,pure_a].sum(axis=0),max(0,1-p))
        if p>0: add(degree[i,pure_b].sum(axis=0),max(0,1-q))
    big=4*sum(masses)+4
    for z,(i,j) in enumerate(pairs):
        row=np.zeros(2*size); row[z]=1; row[size+z]=-caps[z]
        add(row,0)
        p=types[i][0]+types[j][0]; q=types[i][1]+types[j][1]
        robust=[w for w,(a,b) in enumerate(types)
                if p+a>2+1e-9 and q+b>2+1e-9 and p+q+a+b>4+1e-9]
        if robust:
            row=degree[i,robust].sum(axis=0)+degree[j,robust].sum(axis=0)
            row[size+z]=big
            add(row,1-blocking(p,q)+big)
        if forks:
            for total,other,pure in [(p,q,pure_b),(q,p,pure_a)]:
                if total>=2-1e-9 and 0<other<=1+1e-9 and pure:
                    row=degree[i,pure].sum(axis=0)+degree[j,pure].sum(axis=0)
                    row[size+z]=big
                    add(row,1-other+big)
    objective=np.r_[-np.ones(size),np.zeros(size)]
    result=milp(objective,integrality=np.r_[np.zeros(size),np.ones(size)],
        bounds=Bounds(np.zeros(2*size),np.r_[caps,np.ones(size)]),
        constraints=LinearConstraint(np.array(rows),-np.inf,np.array(bounds)),
        options={'time_limit':2,'presolve':False})
    if not result.success: raise RuntimeError(result.message)
    terminal=sum(m*(2*x-p-q) for m,(p,q) in zip(masses,types))
    y=sum(masses)
    return x*x+terminal+y*y/2+result.fun-2*x


def distributions(x,y):
    # Exact low/high benchmark and deterministic asymmetric/pure mixtures.
    yield [(2/3,2/3)],[y],'uniform_two_thirds'
    yield [(1,1)],[y],'uniform_high'
    # Interpret the saturated coordinate as a limit from below. Single-edge
    # activation at exactly degree n is not stable under epsilon*n deficits.
    yield [(0.5,1)],[y],'uniform_asymmetric_limit'
    rng=random.Random(414)
    balanced=[(1,0.25),(1,0.5),(1,0.75),(0.25,1),(0.5,1),
              (0.75,1),(2/3,2/3),(0.5,0.5),(1,1),(1/3,1),(1,1/3)]
    for trial in range(60):
        types=rng.sample(balanced,2)+[(x,0),(0,x)]
        weights=[rng.randrange(5) for _ in types]
        if not sum(weights): weights[0]=1
        yield types,[y*w/sum(weights) for w in weights],f'mixture_{trial}'
    for fraction in [0.1,0.25,0.5]:
        yield [(1,0.25),(1,0.75),(0,x)],\
              [y*(1-fraction)/2,y*(1-fraction)/2,y*fraction],f'fork_family_{fraction}'


def run():
    print(json.dumps({'method':'restricted regular-block MILP, sampled distributions',
        'seed':414,'mixtures':60,'turn_order':'Breaker first, after deletion',
        'degrees':'scaled by bias','milp_seconds_per_case':2}),flush=True)
    for x in [1.04103520853922,1.125,1.2,1.224744871391589,1.25]:
        for c in [3.4,3.41540375041177,3.45]:
            best={False:(float('inf'),None),True:(float('inf'),None)}
            improvements=[]
            for types,masses,label in distributions(x,c-2*x):
                values={fork:optimize(types,masses,x,fork) for fork in [False,True]}
                for fork in values:
                    if values[fork]<best[fork][0]: best[fork]=(values[fork],label)
                if values[True]-values[False]>1e-7:
                    improvements.append((values[True]-values[False],label))
            print(json.dumps({'x':x,'c':c,'worst_without_fork':best[False],
                'worst_with_fork':best[True],
                'fork_improved_distributions':len(improvements),
                'largest_improvement':max(improvements,default=None)}),flush=True)
    x=sqrt(1.5); c=1+sqrt(6)
    for forks in [False,True]:
        rows=[(optimize(t,m,x,forks),label)
              for t,m,label in distributions(x,c-2*x)]
        print(json.dumps({'critical_x':x,'critical_c':c,'forks':forks,
                          'minimum_margin':min(rows)}),flush=True)


if __name__=='__main__': run()
