# -*- coding: utf-8 -*-
"""
Created on Thu Mar  5 02:44:47 2026

@author: Varun
"""

import random
import math
from collections import defaultdict

def connected_0_1(edges):
    
    # Build adjacency list
    adj = defaultdict(list)
    for i, j in edges:
        adj[i].append(j)
        adj[j].append(i)

    # DFS from node 0
    stack = [0]
    visited = set()

    while stack:
        v = stack.pop()
        if v == 1:
            return True
        if v in visited:
            continue
        visited.add(v)
        stack.extend(adj[v])

    return False

def simulate(edges, num_edges):
    robber = random.sample(edges, num_edges)
    
    # check wlog whether 0 and 1 are connected
    return connected_0_1(robber)

def run(m, power, num_iters = 100000):
    edges = [(i,j) for i in range(m) for j in range(i)]
    num_edges = math.ceil((len(edges)-power)/(power+1))
    print(num_edges)
    return sum(int(simulate(edges, num_edges)) for _ in range(num_iters))/num_iters