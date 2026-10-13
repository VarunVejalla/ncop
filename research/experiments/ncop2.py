def iterate(G, n, m, r):
    (S,T,F) = G
    assert m == S+T+F
    assert r == S+T-2
    assert S >= T
    assert 0 <= S-T <= 1
    assert F >= 0
    num_deletions = (r+1)*n
    
    # if we can win immediately; 1-edge lookahead
    print(num_deletions)
    num_deletions -= S*T
    if num_deletions < 0:
        return 1
    
    
    # this is the 1-node lookahead (i.e. 2-edge lookahead)
    # if we can win in the next turn via F
    # if there is some node in F such that we can either choose S or T to connect it to and then in the next turn, we can choose the other one
    #   return True
    # robber can implement this if there is some node in F such that (S-a > 0 AND T-b > num_deletions - (a+b) + n) or similarly for T, S
    # a given node is dangerous for cop if it has at least one connection to a side and at least n+1 connections to other side
    # minimum decrease to get from (S, T) to (0, k) or (k, 0) or (n, n)
    # for each node, if S <= n and T <= n:
        # don't worry about it.
    # if S > n and T <= n:
        # don't need to worry if they're connecting it to S and then connecting it to T (we'll be able to handle it next round)
        # but need to prevent connecting to T and then connecting it to S; either spend T or spend S-n
    # if S > n and T > n:
        # either spend T, S, or S-n + T-n
    if S > n or T > n:
        if S <= n:
            assert False # S >= T should be guaranteed
            
        # need to delete the minimum deletion for every single node in F
        if T <= n:
            num_deletions -= F*min(T, S-n)
        else:
            num_deletions -= F*min(S, T, S-n+T-n)
        
        if num_deletions < 0:
            return 1
        
    # TODO: implement 2-node lookahead (i.e. 3-edge lookahead)
    
    # if we can make progress
    num_deletions -= F * min(S, T)
    
    if num_deletions >= 0:
        return -1
    F -= 1
    
    if S == T:
        S += 1
        return (S,T,F)
    if S-1 == T:
        T += 1
        return (S,T,F)
    
    # this should never be happening
    assert False
    

def check(n, m):
    G = (1, 1, m-2)
    r = 0
    while True:
        print(r, G)
        o = iterate(G, n, m, r)
        if o == 1:
            return True
        if o == -1:
            return False
        r += 1
        G = o