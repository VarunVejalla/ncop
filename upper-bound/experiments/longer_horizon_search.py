"""Reproducible local pattern search; not an asymptotic endpoint proof."""
import json
from itertools import combinations
from horizon_solver import FiniteHorizonSearch,position,four_move_witness


def run():
    print(json.dumps({'method':'exact bounded-horizon minimax, with resource limits',
                      'turn_order':'Breaker first; positions shown after deletion',
                      'seed':None,'states_per_case':20000,'responses_per_case':100000,
                      'seconds_per_case':2}),flush=True)
    for bias in [4,8,12,24]:
        for label,degree in [('two_thirds',2*bias//3),('three_quarters',3*bias//4)]:
            board=position([(degree,degree)]*3,list(combinations(range(3),2)))
            for h in [3,4,5]:
                engine=FiniteHorizonSearch(bias,seconds=2,four_shortcut=False)
                result=engine.solve(board,h)
                result.update({'family':label,'degree':degree,'outside_vertices':3,
                               'four_move_certificate':four_move_witness(board,bias)})
                print(json.dumps(result),flush=True)
    # Larger bias: a sound local certificate can be checked without enumerating
    # all budget allocations. It does not assert that Maker can reach this state.
    bias=1000
    board=position([(750,750)]*3,[(0,1),(1,2)])
    print(json.dumps({'family':'scaled_path','bias':bias,
                      'four_move_certificate':four_move_witness(board,bias)}),flush=True)
    # Larger auxiliary components: increasing horizon uses the same game engine.
    # Stop at the first certified win; an exhausted resource budget is unknown.
    for bias in [2,3,4]:
        for count in [4,5]:
            for degree in sorted({bias//2,2*bias//3,3*bias//4}):
                board=position([(degree,degree)]*count,
                               list(combinations(range(count),2)))
                for horizon in [3,4,5,6]:
                    result=FiniteHorizonSearch(bias,max_states=15000,
                        max_responses=60000,seconds=1,
                        four_shortcut=False).solve(board,horizon)
                    result.update({'family':'larger_auxiliary','degree':degree,
                                   'outside_vertices':count})
                    print(json.dumps(result),flush=True)
                    if result['wins'] is True: break


if __name__=='__main__': run()
