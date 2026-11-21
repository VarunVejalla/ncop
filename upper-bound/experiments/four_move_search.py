"""Seeded discovery, followed by exact minimax checks; no endpoint claim."""
import json
import random
from horizon_solver import FiniteHorizonSearch, position, four_move_witness
from four_move_patterns import forked_pair_witness


def run():
    rng=random.Random(413)
    counts={}
    found=[]
    print(json.dumps({'method':'random positions, exact bounded-horizon minimax',
        'seed':413,'samples':1500,'bias':4,'outside_vertices':3,
        'terminal_degrees':'independent uniform integers 0..6',
        'outside_edge_probability':0.8,'turn_order':'Breaker first, sampled after deletion',
        'states_per_case':20000,'responses_per_case':100000,
        'seconds_h3':0.2,'seconds_h4':0.3}),flush=True)
    for _ in range(1500):
        degrees=[(rng.randrange(7),rng.randrange(7)) for _ in range(3)]
        edges=[(i,j) for i in range(3) for j in range(i+1,3)
               if rng.random()<0.8]
        board=position(degrees,edges)
        if four_move_witness(board,4): continue
        three=FiniteHorizonSearch(4,seconds=0.2,four_shortcut=False).solve(board,3)
        if three['wins'] is not False: continue
        four=FiniteHorizonSearch(4,seconds=0.3,four_shortcut=False).solve(board,4)
        counts[four['status']]=counts.get(four['status'],0)+1
        if four['wins']:
            found.append((degrees,edges))
            print(json.dumps({'degrees':degrees,'edges':edges,'four':four,
                             'new_certificate':forked_pair_witness(board,4)}),flush=True)
    print(json.dumps({'summary':counts}),flush=True)
    for degrees,edges in found:
        for scale in [2,3,4,8,16]:
            board=position([(p*scale,q*scale) for p,q in degrees],edges)
            three=FiniteHorizonSearch(4*scale,seconds=2,four_shortcut=False).solve(board,3)
            four=FiniteHorizonSearch(4*scale,seconds=2,four_shortcut=False).solve(board,4)
            print(json.dumps({'degrees':degrees,'edges':edges,'scale':scale,
                             'three':three,'four':four}),flush=True)
    # The analytic certificate has no resource limit and applies to every n=4s.
    board=position([(0,1250),(1000,250),(1000,750)],[(0,1),(1,2)])
    assert four_move_witness(board,1000) is None
    assert forked_pair_witness(board,1000) is not None
    print(json.dumps({'bias':1000,'certificate':forked_pair_witness(board,1000)}))


if __name__=='__main__': run()
