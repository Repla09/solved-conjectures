"""Construct and check the six zero placements on a length-five spider."""

import argparse
from itertools import pairwise

from general import construct_general


def rooted(k):
    """Center and legs in increasing depth order, including the empty spider."""
    legs = []
    for i in range(k):
        high = 5 * (k - i)
        low = 5 * i + 1
        legs.append((high, low, high - 1, low + 1, high - 2))
    return 0, legs


def insert_at_center(k, center, seed):
    """Stretch the high labels of an alternating seed and insert a rooted spider."""
    extra = k - len(seed)
    gap = 5 * extra
    legs = [tuple(x + gap if x > center else x for x in leg) for leg in seed]
    _, inner = rooted(extra)
    legs.extend(tuple(center + x for x in leg) for leg in inner)
    return center, legs


def construct(k, depth):
    if k < 1 or depth not in range(6):
        raise ValueError("expected k >= 1 and a depth from 0 to 5")
    if depth <= 1:
        center, legs = rooted(k)
    elif depth <= 3 and k == 1:
        center, legs = 1, [(4, 0, 5, 3, 2)]
    elif depth <= 3:
        center, legs = insert_at_center(k, 4, [(7, 0, 10, 1, 9), (5, 3, 8, 2, 6)])
    else:
        center, legs = insert_at_center(k, 2, [(3, 1, 4, 0, 5)])
    if depth % 2:
        q = 5 * k
        return q - center, [tuple(q - x for x in leg) for leg in legs]
    return center, legs


def check(k, depth, center, legs, length=5):
    """Read the actual vertex labels and recompute each edge difference."""
    if len(legs) != k or any(len(leg) != length for leg in legs):
        raise ValueError("incorrect spider shape")
    q = length * k
    vertices = [center] + [x for leg in legs for x in leg]
    if sorted(vertices) != list(range(q + 1)):
        raise ValueError("vertex labels do not permute 0 through q")
    weights = [abs(x - y) for leg in legs for x, y in pairwise((center, *leg))]
    if sorted(weights) != list(range(1, q + 1)):
        raise ValueError("edge differences do not permute 1 through q")
    target = center if depth == 0 else legs[0][depth - 1]
    if target != 0:
        raise ValueError(f"the designated vertex is labeled {target}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("max_k", type=int, nargs="?", default=60)
    parser.add_argument("--general-through", type=int, metavar="L",
                        help="also check the general construction at lengths 5 through L")
    args = parser.parse_args()
    limit = args.max_k
    if args.general_through is not None and args.general_through < 5:
        parser.error("--general-through must be at least 5")
    if limit < 1:
        parser.error("max_k must be positive")
    for k in range(1, limit + 1):
        for d in range(6):
            try:
                check(k, d, *construct(k, d))
            except ValueError as exc:
                raise SystemExit(f"FAILED for k={k}, depth={d}: {exc}") from exc
    print(f"Verified {6 * limit} labelings: k=1..{limit}, depths 0..5.")
    if args.general_through is not None:
        for length in range(5, args.general_through + 1):
            for k in range(1, limit + 1):
                for d in range(length + 1):
                    try:
                        check(k, d, *construct_general(k, length, d), length=length)
                    except ValueError as exc:
                        raise SystemExit(f"FAILED for k={k}, L={length}, depth={d}: {exc}") from exc
            print(f"General construction verified: L={length}, k=1..{limit}, depths 0..{length}.")
