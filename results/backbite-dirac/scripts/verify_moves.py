"""Exercise the explicit backbite constructions in PROOF.md on labelled paths."""
from collections import Counter
from itertools import permutations
import subprocess

from backbite import connected, ham_paths, neighbours, norm, parse_g6


def edge(u, v):
    return (min(u, v), max(u, v))


def cycle_edges(cycle):
    return [edge(cycle[i - 1], v) for i, v in enumerate(cycle)]


def bite(path, pivot, adj):
    i = path.index(pivot)
    assert i >= 2
    result = path[:i][::-1] + path[i:]
    assert norm(result) in neighbours(path, adj)
    return result


def check_descent():
    count = 0
    for n in range(3, 8):
        full = (1 << n) - 1
        complete = [full ^ (1 << u) for u in range(n)]
        raw = subprocess.check_output(['geng', '-cq', f'-d{(n + 1) // 2}', str(n)], text=True)
        for line in raw.splitlines():
            _, h = parse_g6(line)

            def excess(p):
                return sum(not (h[u] >> v & 1) for u, v in zip(p, p[1:]))

            for p in permutations(range(n)):
                if p[0] > p[-1] or not (before := excess(p)):
                    continue
                count += 1
                if not (h[p[0]] >> p[-1] & 1):
                    i = next(i for i in range(1, n - 2)
                             if h[p[0]] >> p[i + 1] & h[p[-1]] >> p[i] & 1)
                    p = bite(p, p[i + 1], complete)
                assert h[p[0]] >> p[-1] & 1
                for _ in range(n):
                    if excess(p) < before:
                        break
                    p = bite(p, p[-1], complete)[::-1]
                assert excess(p) < before
    return count


def check_attachments():
    count = 0
    for m in range(3, 13):
        v = m
        adj = [(1 << ((u-1) % m)) | (1 << ((u+1) % m)) | (1 << v) for u in range(m)]
        adj.append((1 << m) - 1)
        for start in range(m):
            for direction in (-1, 1):
                cycle = tuple((start + direction*j) % m for j in range(m))
                p = (v,) + cycle
                turned = bite(p[::-1], start, adj)
                assert norm(turned) == norm((v, start) + cycle[:0:-1])
                for j in range(1, m):
                    q = bite(p, cycle[j], adj)
                    q = bite(q[::-1], start, adj)
                    expected = (v,) + cycle[j:] + cycle[:j]
                    assert norm(q) == norm(expected)
                    count += 1
    return count


def check_lifted_closures():
    # Check both directions of each witness, with each allowable insertion in place.
    m = 6
    v = m
    count = 0
    raw = subprocess.check_output(['geng', '-cq', '-d4', str(m)], text=True)
    for line in raw.splitlines():
        _, h = parse_g6(line)
        for mask in range(1 << m):
            if mask.bit_count() < 5:
                continue
            adj = [a | (((mask >> i) & 1) << v) for i, a in enumerate(h)] + [mask]
            for path in ham_paths(m, h):
                for p in (path, path[::-1]):
                    x, y = p[0], p[-1]
                    if h[x] >> y & 1:
                        continue
                    witnesses = [i for i in range(1, m-2)
                                 if h[x] >> p[i+1] & h[y] >> p[i] & 1]
                    assert len(witnesses) >= 3
                    for i in witnesses:
                        closed = p[:i+1] + p[i+1:][::-1]
                        base_edges = set(cycle_edges(closed))
                        if mask >> y & 1:
                            q = bite(p + (v,), p[i+1], adj)
                            assert q[-1] == v and q[-2] == y
                            assert set(cycle_edges(q[:-1])) == base_edges
                            count += 1
                        for j in range(1, m):
                            u, w = p[j-1:j+1]
                            if j == i+1 or not (mask >> u & mask >> w & 1):
                                continue
                            q = bite(p[:j] + (v,) + p[j:], p[i+1], adj)
                            expected = (base_edges - {edge(u, w)}) | {edge(u, v), edge(v, w)}
                            assert set(cycle_edges(q)) == expected
                            count += 1
    return count


def check_exchange(a, b, order, cut_side):
    # Consecutive excursions at one occurrence of a type share a flank.
    types = []
    centres = {}
    for pos, i in enumerate(order):
        if pos == 0 or a[i] != a[order[pos - 1]]:
            types.extend((100 + pos, a[i]))
        centres[i] = len(types)
        types.extend((b[i], a[i]))
    n = len(types)
    initial = tuple(range(n))
    old = Counter(edge(types[u], types[v]) for u, v in cycle_edges(initial))
    target = old.copy()
    allowed = set(old)
    for i in range(len(a)):
        blue = edge(b[i], a[(i + 1) % len(a)])
        target[edge(a[i], b[i])] -= 1
        target[blue] += 1
        allowed.add(blue)
    adj = [sum(1 << j for j, y in enumerate(types) if edge(x, y) in allowed) for x in types]
    p = tuple((centres[0] + cut_side * j) % n for j in range(n))
    fixed = p[-1]
    for i in range(1, len(a)):
        centre_pos = p.index(centres[i])
        assert 0 < centre_pos < n - 1
        assert types[p[centre_pos - 1]] == types[p[centre_pos + 1]] == a[i]
        p = bite(p, p[centre_pos + 1], adj)
        assert p[0] == centres[i] and p[-1] == fixed
    assert adj[p[0]] >> fixed & 1
    assert Counter(edge(types[u], types[v]) for u, v in cycle_edges(p)) == +target


def check_exchanges():
    count = 0
    for k in range(2, 8):
        patterns = [(list(range(k)), list(range(10, 10+k)))]
        if k >= 4:
            repeated = [i % 2 for i in range(k)]
            if k % 2:
                repeated[-1] = 2
            patterns.append((repeated, list(range(10, 10+k))))
        if k == 6:
            patterns.append(([0, 1]*3, [10, 11, 10, 11, 12, 13]))
        for a, b in patterns:
            for tail in permutations(range(1, k)):
                for side in (-1, 1):
                    check_exchange(a, b, (0,) + tail, side)
                    count += 1
    return count


def check_alternating_paths():
    counts = []
    for h in range(1, 6):
        n = 2*h + 1
        small = (1 << h) - 1
        large = ((1 << n) - 1) ^ small
        ok, total, _ = connected(n, [large]*h + [small]*(h+1))
        assert ok and total > 0
        counts.append(total)
    return counts


if __name__ == '__main__':
    print('outside-edge descents:', check_descent(), flush=True)
    print('pendant reattachments:', check_attachments(), flush=True)
    print('lifted closures:', check_lifted_closures(), flush=True)
    print('alternating exchanges:', check_exchanges(), flush=True)
    print('alternating path counts:', check_alternating_paths(), flush=True)
