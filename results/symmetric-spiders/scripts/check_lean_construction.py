"""Check the constructive proof on small paths and spiders."""

from functools import cache


def walecki(n):
    return [j // 2 for j in range(n)]


def reflect(p):
    return [(len(p) - 1 - j % 2) // 2 - a for j, a in enumerate(p)]


def join(p, q):
    t = len(p)
    assert p[-1] + q[0] == (t - 1) // 2
    return p + [a + (t + 1 - j % 2) // 2 for j, a in enumerate(q, t)]


def admissible(n, x):
    return 0 <= 2 * x < n and (x == 0 or n != 4 * x + 1)


@cache
def endpoint(n, x):
    assert admissible(n, x)
    if x == 0:
        return walecki(n)
    y = (n - 1) // 2 - x
    if y < x:
        return reflect(endpoint(n, y))
    t = next(t for t in (2*x + 1, 2*x + 2) if admissible(n-t, x))
    return join(walecki(t)[::-1], endpoint(n-t, x))


def prescribed(n, d):
    if d > n - 1 - d:
        return prescribed(n, n - 1 - d)[::-1]
    for t in (d + 1, d + 2):
        if admissible(n - t, (t - 1) // 2):
            return join(walecki(t)[::-1], endpoint(n - t, (t - 1) // 2))
    if (n, d) == (9, 3):
        return [1, 2, 2, 0, 0, 1, 4, 3, 3]
    if (n, d) == (13, 6):
        return [2, 5, 6, 4, 5, 3, 0, 0, 1, 1, 3, 2, 4]
    t = d + 2
    front = join([1, 0, 0], endpoint(t - 3, 1))[::-1]
    return join(front, endpoint(n - t, (t - 1) // 2 - 1))


def labels(p):
    return [len(p) - 1 - a if j % 2 else a for j, a in enumerate(p)]


def ordinary(n, x):
    if 2*x >= n:
        return [n - 1 - a for a in ordinary(n, n - 1 - x)]
    if admissible(n, x):
        return labels(endpoint(n, x))
    t = 2*x + 1
    first = [n-1-a if j % 2 else a for j, a in enumerate(walecki(t)[::-1])]
    return first + [x + 1 + a for a in labels(reflect(walecki(2*x)))]


def spider(length, k, d):
    n = k - 1
    seed = labels(prescribed(length + 1, d))
    cut = length // 2
    a = ordinary(length, length - 1 + seed[0] - cut)
    f = [v if v <= cut else v + length*n for v in seed]
    for i in range(n):
        f.extend(cut + 1 + v + length*(i if j % 2 else n-1-i)
                 for j, v in enumerate(a))
    return [length*k-v for v in f] if d % 2 else f


if __name__ == '__main__':
    for length in range(5, 61):
        for x in range(length):
            a = ordinary(length, x)
            assert a[0] == x and sorted(a) == list(range(length))
            assert sorted(abs(v-u) for u, v in zip(a, a[1:])) == list(range(1, length))
        for d in range(length + 1):
            for k in (1, 2, 3, 6):
                f = spider(length, k, d)
                assert f[d] == 0 and sorted(f) == list(range(length*k + 1))
                w = [abs(f[j]-f[0 if (j-1) % length == 0 else j-1])
                     for j in range(1, len(f))]
                assert sorted(w) == list(range(1, length*k + 1))
    print('Passed all depths for lengths 5 through 60 and k in {1,2,3,6}.')
