"""Certify Dirac graphs of one order up to isomorphism, using PROOF.md."""
import argparse
from collections import Counter
import subprocess

from backbite import connected, parse_g6


def squared_path(adj):
    full = (1 << len(adj)) - 1

    def extend(prev, last, left):
        if not left:
            return True
        candidates = adj[prev] & adj[last] & left
        while candidates:
            bit = candidates & -candidates
            if extend(last, bit.bit_length() - 1, left ^ bit):
                return True
            candidates ^= bit
        return False

    return any(extend(u, v, full ^ (1 << u) ^ (1 << v))
               for u in range(len(adj)) for v in range(len(adj)) if adj[u] >> v & 1)


def one_switch_component(adj):
    """Enumerate cycles up to dihedral symmetry and try the sufficient 2-opt test."""
    n = len(adj)
    cycles = set()

    def extend(path, left):
        if not left:
            if adj[path[-1]] & 1 and path[1] < path[-1]:
                cycles.add(path)
            return
        candidates = adj[path[-1]] & left
        while candidates:
            bit = candidates & -candidates
            extend(path + (bit.bit_length() - 1,), left ^ bit)
            candidates ^= bit

    extend((0,), (1 << n) - 2)
    if not cycles:
        raise ValueError('no Hamilton cycle in promised Dirac input')
    stack = [cycles.pop()]
    while stack and cycles:
        p = stack.pop()
        for i in range(n - 2):
            for j in range(i + 2, n):
                if i == 0 and j == n - 1:
                    continue
                if adj[p[i]] >> p[j] & adj[p[i + 1]] >> p[(j + 1) % n] & 1:
                    q = p[:i + 1] + p[i + 1:j + 1][::-1] + p[j + 1:]
                    if q[1] > q[-1]:
                        q = q[:1] + q[:0:-1]
                    if q in cycles:
                        cycles.remove(q)
                        stack.append(q)
    return not cycles


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int, choices=range(3, 63))
    n = parser.parse_args().n
    d = (n + 1) // 2
    counts = Counter()
    with subprocess.Popen(['geng', '-cq', f'-d{d}', str(n)],
                          stdout=subprocess.PIPE, text=True) as process:
        for line in process.stdout:
            order, adj = parse_g6(line)
            if order != n or min(a.bit_count() for a in adj) < d:
                raise ValueError('unexpected graph from geng')
            counts['all'] += 1
            high = sum(1 << u for u, a in enumerate(adj) if a.bit_count() > d)
            if any(high >> u & 1 and a & high for u, a in enumerate(adj)):
                continue
            counts['minimal'] += 1
            if squared_path(adj):
                counts['square'] += 1
            elif one_switch_component(adj):
                counts['2-opt'] += 1
            else:
                ok, total, reached = connected(n, adj)
                if not ok or total == 0:
                    raise RuntimeError(f'{line.strip()}: reached {reached} of {total}')
                counts['full BFS'] += 1
        if process.wait() != 0 or not counts['minimal']:
            raise RuntimeError('incomplete graph generation')
    print(n, dict(counts), flush=True)


if __name__ == '__main__':
    main()
