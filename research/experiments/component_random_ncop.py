import random
from collections import defaultdict

# ---------- graph utilities ----------

def connected_0_1(edges):
    """Return True iff 0 and 1 are connected in the undirected graph with given edge list."""
    adj = defaultdict(list)
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)

    stack = [0]
    seen = set()
    while stack:
        v = stack.pop()
        if v == 1:
            return True
        if v in seen:
            continue
        seen.add(v)
        stack.extend(adj[v])
    return False


# ---------- DSU for robber components (robber graph is always a forest) ----------

class DSU:
    __slots__ = ("p", "sz")
    def __init__(self, n):
        self.p = list(range(n))
        self.sz = [1] * n

    def find(self, x):
        while self.p[x] != x:
            self.p[x] = self.p[self.p[x]]
            x = self.p[x]
        return x

    def union(self, a, b):
        ra, rb = self.find(a), self.find(b)
        if ra == rb:
            return False
        if self.sz[ra] < self.sz[rb]:
            ra, rb = rb, ra
        self.p[rb] = ra
        self.sz[ra] += self.sz[rb]
        return True

    def same(self, a, b):
        return self.find(a) == self.find(b)


# ---------- simulation of your "component-restricted" game ----------

def simulate_component_restricted(m, n, rng=None, stop_when_connected=True):
    """
    Simulate one run on K_m.
      - robber takes 1 random admissible edge per round
      - cop takes n random admissible edges per round
    Admissible: unclaimed AND endpoints are in different robber components.
    Returns True iff robber ends with a path 0-1 (equivalently robber components contain both).
    """
    if rng is None:
        rng = random

    # All edges of K_m (store as (u,v) with u < v)
    all_edges = [(u, v) for u in range(m) for v in range(u + 1, m)]
    rng.shuffle(all_edges)

    dsu = DSU(m)
    robber_edges = []

    # We'll keep a pointer into the shuffled list and "skip" ineligible edges lazily.
    i = 0
    N = len(all_edges)

    # helper: pop next edge that is (a) unclaimed (always true via pointer)
    # and (b) crosses robber components.
    def next_admissible():
        nonlocal i
        while i < N:
            u, v = all_edges[i]
            i += 1
            if not dsu.same(u, v):
                return (u, v)
        return None  # exhausted

    # Each round consumes 1 robber edge + n cop edges, all admissible at selection time.
    while True:
        # robber move
        e = next_admissible()
        if e is None:
            break
        u, v = e
        dsu.union(u, v)
        robber_edges.append(e)

        if stop_when_connected and dsu.same(0, 1):
            return True

        # cop move: consume n admissible edges (deleted), does NOT change dsu
        for _ in range(n):
            e2 = next_admissible()
            if e2 is None:
                # no more admissible edges -> game ends
                break
        else:
            # cop successfully took n edges; continue rounds
            continue

        # if we broke because exhaustion, end game
        break

    # terminal check
    # (equivalently dsu.same(0,1), but robber_edges check is fine too)
    return dsu.same(0, 1)


def run_component_restricted(c, n, num_iters=10000, seed=None, stop_when_connected=True):
    """
    Convenience runner with m = ceil(c*n).
    Returns empirical win probability for the robber.
    """
    rng = random.Random(seed)
    m = int((c * n) + 0.999999999)  # ceil without importing math
    wins = 0
    for _ in range(num_iters):
        wins += int(simulate_component_restricted(m, n, rng=rng, stop_when_connected=stop_when_connected))
    return wins / num_iters


# ---------- example usage ----------
if __name__ == "__main__":
    for c in [1.2, 1.5, 1.9, 2.1, 2.5]:
        n = 300
        est = run_component_restricted(c=c, n=n, num_iters=2000, seed=123)
        print(f"c={c:>3}, n={n}:  P(win)≈{est:.4f}")