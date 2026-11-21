"""Sound additional four-move certificates; not endpoint theorems."""


def forked_pair_witness(board, bias):
    """Adaptive pair threat with one or many pure opposite-terminal neighbors.

    P>=2n, 0<Q<=n, Q+sum_w min(boundary_w,degree_w-n)>n suffices.
    Pure neighbors have zero first-terminal degree and >n second-terminal
    degree. Each deletion can reduce the displayed sum by at most one.
    """
    for a,b in [(0,1),(1,0)]:
        for u in range(2,len(board)):
            for v in range(u+1,len(board)):
                if not board[u][v]: continue
                p=board[a][u]+board[a][v]
                q=board[b][u]+board[b][v]
                if p<2*bias or q<=0: continue
                pure=[]
                activation=0
                for w in range(2,len(board)):
                    if w in (u,v): continue
                    if (board[a][w]==0 and board[b][w]>bias
                            and board[u][w]+board[v][w]>0):
                        pure.append(w)
                        activation+=min(board[u][w]+board[v][w],board[b][w]-bias)
                if pure and (q>bias or q+activation>bias):
                    return {'pattern':'forked_pair','first_edge':[u,v],
                            'pure_vertices':pure,'terminal_order':[a,b],
                            'pair_degrees':[p,q],'activation_cost':activation}
    return None
