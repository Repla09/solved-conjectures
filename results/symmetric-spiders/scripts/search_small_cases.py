"""Check 0-rotatability of symmetric spiders T(k, L) for small k, L.

T(k, L): a root with k legs, each a path of L edges. q = k*L edges.
A graceful labeling gives vertices distinct labels in {0..q} so that the
edge differences |f(u)-f(v)| are exactly {1..q}.
0-rotatable: for every vertex v there is a graceful labeling with f(v) = 0.
By symmetry it is enough to test the root and one vertex at each depth 1..L.

Usage: python3 spider_rotatable.py K_MAX L_MIN L_MAX
"""
import sys
import time


def spider(k, L):
    adj = {0: []}
    nid = 1
    for _ in range(k):
        prev = 0
        for _ in range(L):
            adj[nid] = [prev]
            adj[prev].append(nid)
            prev = nid
            nid += 1
    return adj


def graceful_with_zero(adj, v0, time_limit=60.0):
    """DFS over vertices in BFS order from v0, with f(v0) = 0."""
    n = len(adj)
    q = n - 1
    order, parent, seen = [v0], {v0: None}, {v0}
    i = 0
    while i < len(order):
        u = order[i]
        i += 1
        for w in adj[u]:
            if w not in seen:
                seen.add(w)
                parent[w] = u
                order.append(w)
    f = {v0: 0}
    used_lab = [False] * (q + 1)
    used_lab[0] = True
    used_diff = [False] * (q + 1)
    start = time.time()
    nodes = [0]

    def rec(idx):
        nodes[0] += 1
        if nodes[0] % 20000 == 0 and time.time() - start > time_limit:
            raise TimeoutError
        if idx == n:
            return True
        # the largest unused difference must still be achievable; cheap prune:
        v = order[idx]
        pl = f[parent[v]]
        # try labels giving large differences first (they are hardest to place)
        for d in range(q, 0, -1):
            if used_diff[d]:
                continue
            for lab in (pl + d, pl - d):
                if 0 <= lab <= q and not used_lab[lab]:
                    used_lab[lab] = True
                    used_diff[d] = True
                    f[v] = lab
                    if rec(idx + 1):
                        return True
                    used_lab[lab] = False
                    used_diff[d] = False
                    del f[v]
        return False

    try:
        ok = rec(1)
    except TimeoutError:
        return None
    return dict(f) if ok else False


def main():
    kmax, lmin, lmax = (int(a) for a in sys.argv[1:4])
    for L in range(lmin, lmax + 1):
        for k in range(1, kmax + 1):
            adj = spider(k, L)
            res = []
            for depth in range(L + 1):
                v = 0 if depth == 0 else depth  # first leg's vertex at that depth
                t = time.time()
                r = graceful_with_zero(adj, v)
                res.append("ok" if r else ("TIMEOUT" if r is None else "NONE"))
            print(f"T({k},{L}) q={k*L}: " + " ".join(f"d{d}:{s}" for d, s in enumerate(res)), flush=True)


if __name__ == "__main__":
    main()
