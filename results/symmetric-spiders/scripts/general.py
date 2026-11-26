"""Arbitrary leg length L >= 5, using two graceful paths as in PROOF.md."""

from functools import cache


@cache
def path_seed(size, fixed_position, fixed_label, alternating):
    """Find a graceful permutation of range(size) with the specified entry.

    In the alternating case, even positions take the lower block of labels.
    Grow both sides from the pinned position, using each label and weight once.
    """
    cut = (size - 1) // 2
    path = [None] * size
    path[fixed_position] = fixed_label
    order = [*range(fixed_position + 1, size), *range(fixed_position - 1, -1, -1)]
    labels = {fixed_label}
    weights = set()

    def extend(step):
        if step == len(order):
            return True
        pos = order[step]
        neighbor = path[pos - 1 if pos > fixed_position else pos + 1]
        candidates = range(size)
        if alternating:
            candidates = range(cut + 1, size) if pos % 2 else range(cut + 1)
        for x in sorted(candidates, key=lambda x: -abs(x - neighbor)):
            w = abs(x - neighbor)
            if x in labels or w in weights:
                continue
            path[pos] = x
            labels.add(x)
            weights.add(w)
            if extend(step + 1):
                return True
            weights.remove(w)
            labels.remove(x)
        return False

    if not extend(0):
        raise ValueError("no path satisfies the requested constraints")
    return tuple(path)


def construct_general(k, length, depth):
    if k < 1 or length < 5 or not 0 <= depth <= length:
        raise ValueError("expected k >= 1, L >= 5, and 0 <= depth <= L")
    cut = length // 2
    extreme = length if depth % 2 else 0
    seed = path_seed(length + 1, depth, extreme, alternating=True)
    center = seed[0]
    n = k - 1
    gap = n * length
    legs = [tuple(x if x <= cut else x + gap for x in seed[1:])]

    if n:
        # Zero-based entries. Adding one gives the a_j of the proof.
        offsets = path_seed(length, 0, length - 1 + center - cut, alternating=False)
        for i in range(n):
            leg = []
            for j, x in enumerate(offsets, start=1):
                block = n - 1 - i if j % 2 else i
                leg.append(cut + 1 + length * block + x)
            legs.append(tuple(leg))

    if depth % 2:
        q = k * length
        return q - center, [tuple(q - x for x in leg) for leg in legs]
    return center, legs
