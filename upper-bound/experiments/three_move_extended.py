"""Additional three-move threats: activate one-sided outside vertices.

Breaker first, exhaustive degree/density grids, no randomness.
Grid-positive results are exploratory, not endpoint proofs.
Run: python upper-bound/experiments/three_move_extended.py
"""
import numpy as np
from fractions import Fraction
from three_move_search import dangerous_pair


class Search:
    def __init__(self, degree_grid=8, density_grid=20):
        g=[Fraction(i,degree_grid) for i in range(degree_grid+1)]
        types=[(p,q) for p in g for q in g]
        low=[t for t in types if not dangerous_pair(t,t,Fraction(1))]
        high=[t for t in types if dangerous_pair(t,t,Fraction(1))]
        self.low=np.array(low,dtype=float)
        self.high=np.array(high,dtype=float)
        self.compat=np.array([[not dangerous_pair(l,h,Fraction(1)) for h in high]
                              for l in low])
        self.grid=density_grid

    @staticmethod
    def costs(types,a,b,x):
        p,q=types.T
        # To survive attaching v to B, first delete p*n joining edges.
        # Each surviving v--pure-A edge then creates a two-move win.
        # Different pure vertices require distinct further deletions.
        return (2*x-p-q+(q>0)*np.maximum(0,a+p-1)
                +(p>0)*np.maximum(0,b+q-1))

    def fixed_densities(self,x,c,a,b):
        z=c-2*x-a-b
        if z < -1e-9: return float('inf'),None
        z=max(z,0)
        lc=self.costs(self.low,a,b,x)
        hc=self.costs(self.high,a,b,x)
        d=lc[:,None]-hc[None,:]
        highmass=np.clip(d,0,z)
        matrix=z*lc[:,None]-d*highmass+highmass**2/2
        matrix=np.where(self.compat,matrix,float('inf'))
        il=int(lc.argmin()); ih=int(hc.argmin())
        options=[(z*lc[il],tuple(self.low[il]),None,0.),
                 (z*hc[ih]+z*z/2,None,tuple(self.high[ih]),z)]
        i,j=np.unravel_index(matrix.argmin(),matrix.shape)
        options.append((matrix[i,j],tuple(self.low[i]),tuple(self.high[j]),highmass[i,j]))
        value,lo,hi,h=min(options,key=lambda item:item[0])
        pure_cross=a*b if x>1.5 else 0
        margin=x*x+(a+b)*x+pure_cross+value-2*x
        return margin,{'pure_A':a,'pure_B':b,'balanced_low':lo,
                       'balanced_high':hi,'balanced_high_mass':float(h),
                       'balanced_mass':z}

    def minimum(self,x,c):
        y=c-2*x
        best=(float('inf'),None)
        for i in range(self.grid+1):
            for j in range(self.grid+1-i):
                a=y*i/self.grid; b=y*j/self.grid
                value,witness=self.fixed_densities(x,c,a,b)
                if value<best[0]: best=value,witness
        return best

    def threshold(self,x):
        lo=max(2*x,x+2); hi=3.8
        for _ in range(24):
            mid=(lo+hi)/2
            if self.minimum(x,mid)[0]>0: hi=mid
            else: lo=mid
        return hi


if __name__=='__main__':
    print('Breaker-first, exhaustive grid; degree grid 8, density grid 20',flush=True)
    search=Search(8,20)
    rows=[]
    for i in range(22,29):
        x=i/20
        c=search.threshold(x)
        rows.append((c,x))
        print('threshold',x,c,flush=True)
    c,x=min(rows)
    print('best',x,c,search.minimum(x,c),flush=True)
    for dg,mg in [(8,40),(16,40),(32,80)]:
        model=Search(dg,mg)
        print('refinement',dg,mg,x,model.threshold(x),flush=True)
