#!/usr/bin/env python3
"""Exact checks of the worked example and of the small claims of the paper (standard library only).

The example is one square: G = 2 letters, Q = 2 digits, R = 1, with one occurrence on each of the four cells.
1. The trading identity on random matrices.
2. The two wires: det(A - D) is the crossing product, on all bits.
3. The window of the square, and the rank of k - I.
4. The identity for the square on all bits, and the values printed in the paper.
5. The letters in the example of the blocks; the implication o_j = g_i.
6. The whole formula: T, t, S, xi and the factorization by letters, on all bits.
7. The bound of the section on long reads, for Q = 1, 2, 3, and that it is attained for Q = 2.
"""
import random
from fractions import Fraction as F
from itertools import combinations, permutations, product


def det(A):
    A = [r[:] for r in A]
    n = len(A)
    d = F(1)
    for c in range(n):
        p = next((i for i in range(c, n) if A[i][c] != 0), None)
        if p is None:
            return F(0)
        if p != c:
            A[c], A[p] = A[p], A[c]
            d = -d
        d *= A[c][c]
        for i in range(c + 1, n):
            if A[i][c] != 0:
                g = A[i][c] / A[c][c]
                A[i] = [x - g * y for x, y in zip(A[i], A[c])]
    return d


def rank(A):
    A = [r[:] for r in A]
    r = 0
    for c in range(len(A[0])):
        p = next((i for i in range(r, len(A)) if A[i][c] != 0), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        for i in range(r + 1, len(A)):
            if A[i][c] != 0:
                g = A[i][c] / A[r][c]
                A[i] = [x - g * y for x, y in zip(A[i], A[r])]
        r += 1
    return r


def subsets(s):
    s = list(s)
    for m in range(len(s) + 1):
        yield from map(frozenset, combinations(s, m))


def sign(p):
    s = 1
    for i in range(len(p)):
        for j in range(i + 1, len(p)):
            if p[i] > p[j]:
                s = -s
    return s


def eq(a, b):
    return F(1) if a == b else F(0)


rng = random.Random(1)
for n, r in [(5, 2), (6, 3), (4, 0), (3, 3)]:
    for _ in range(10):
        D = [[F(rng.randint(-3, 3)) for _ in range(n)] for _ in range(n)]
        basis = [[F(rng.randint(-3, 3)) for _ in range(n)] for _ in range(r)]
        E = []
        for _ in range(n):
            co = [rng.randint(-3, 3) for _ in range(r)]
            E.append([sum((a * b[j] for a, b in zip(co, basis)), F(0)) for j in range(n)])
        A = [[D[i][j] + E[i][j] for j in range(n)] for i in range(n)]
        total = F(0)
        for T in subsets(range(n)):
            if len(T) <= r:
                total += (-1) ** len(T) * det([E[i] if i in T else A[i] for i in range(n)])
        assert total == det(D)
print("1. det D = sum_{|T|<=r} (-1)^|T| det<T>, on random matrices")

Q, R = 2, 1
cells = [(0, 0), (0, 1), (1, 0), (1, 1)]  # first words; the second word is the complement
idx = {c: i for i, c in enumerate(cells)}
n = 4


def swap(E, c):
    return tuple(1 - c[i] if i in E else c[i] for i in range(Q))


def bar(c):
    return swap({0, 1}, c)


kappa = {(): F(-1), (0,): F(1), (1,): F(1)}


def Eij(i, j):
    """The unique E with tau_E c_i = d_j, where d_j is the transposed cell of c_j."""
    d = bar(cells[j])
    return tuple(t for t in range(Q) if cells[i][t] != d[t])


k = [[kappa.get(Eij(i, j), F(0)) for j in range(n)] for i in range(n)]
assert rank([[k[i][j] - (1 if i == j else 0) for j in range(n)] for i in range(n)]) == 1
r = 2
print("3. the window tau_1 + tau_2 - 1 on the square: rank(k - I) = 1, so r = 2")

two = [idx[(0, 0)], idx[swap({0}, (0, 0))]]
k2 = [[k[i][j] for j in two] for i in two]
assert k2 == [[0, 1], [1, 0]]
assert rank([[k2[i][j] - (1 if i == j else 0) for j in range(2)] for i in range(2)]) == 1
for x1, x2, y1, y2 in product([0, 1], repeat=4):
    e = lambda a, b: 1 if a == b else 0
    assert e(x1, y1) * e(x2, y2) - e(x1, y2) * e(x2, y1) == (x2 - x1) * (y2 - y1)
print("2. two wires: k - I has rank 1, and det(A - D) = [x1=y1][x2=y2] - [x1=y2][x2=y1] = (x2-x1)(y2-y1)")


def Fk(x, y):
    A = [[k[i][j] * eq(x[i], y[j]) for j in range(n)] for i in range(n)]
    D = [[eq(x[i], y[j]) if i == j else F(0) for j in range(n)] for i in range(n)]
    E = [[A[i][j] - D[i][j] for j in range(n)] for i in range(n)]
    out = [F(0)] * 3
    for size in range(3):
        for T in map(frozenset, combinations(range(n), size)):
            out[size] += det([E[i] if i in T else A[i] for i in range(n)])
    return out, det(D)


for bits in product([0, 1], repeat=8):
    x, y = bits[:4], bits[4:]
    vals, dD = Fk(x, y)
    assert vals[0] - vals[1] + vals[2] == dD
    assert dD == all(a == b for a, b in zip(x, y))
print("4. the identity for the square holds on all 256 bit points")
for x, y, want in [((0, 0, 0, 0), (0, 0, 0, 0), 1), ((1, 0, 1, 0), (1, 0, 1, 0), 1), ((1, 0, 0, 0), (0, 0, 0, 0), 0)]:
    vals, dD = Fk(x, y)
    print(f"   x={x} y={y}: F_0, F_1, F_2 = {[str(v) for v in vals]}, det D = {dD}")
    assert dD == want


def padd(p, q):
    o = dict(p)
    for key, v in q.items():
        o[key] = o.get(key, F(0)) + v
    return {key: v for key, v in o.items() if v != 0}


def pmul(p, q):
    o = {}
    for key, v in p.items():
        for l, w in q.items():
            m = (key[0] + l[0], key[1] + l[1])
            o[m] = o.get(m, F(0)) + v * w
    return {key: v for key, v in o.items() if v != 0}


def pdet(A):
    m = len(A)
    res = {}
    for p in permutations(range(m)):
        term = {(0, 0): F(sign(p))}
        for i in range(m):
            term = pmul(term, A[i][p[i]])
            if not term:
                break
        res = padd(res, term)
    return res


def mono(E):
    return (1 if 0 in E else 0, 1 if 1 in E else 0)


def coef(T, t, S, i, j):
    """The coefficient gamma_ij of H_{T,t,S}: a rational times a monomial, or empty."""
    E = Eij(i, j)
    if (t in E) != (i in S):
        return {}
    v = k[i][j]
    if i in T:
        v = v - (1 if i == j else 0)
    return {mono(E): v} if v != 0 else {}


def s_letter(i, t):
    return cells[i][t]


def o_letter(j, t):
    return 1 - cells[j][t]


for t in range(Q):
    for S in subsets(range(n)):
        for T in subsets(range(n)):
            for i in range(n):
                g = o_letter(i, t) if i in S else s_letter(i, t)
                for j in range(n):
                    if coef(T, t, S, i, j):
                        assert o_letter(j, t) == g


def rows_of(t, S, g):
    return [i for i in range(n) if (o_letter(i, t) if i in S else s_letter(i, t)) == g]


def cols_of(t, g):
    return [j for j in range(n) if o_letter(j, t) == g]


S0 = frozenset({idx[(0, 0)], idx[(1, 0)]})
for g in (0, 1):
    print(f"   t=1, S={{00,10}}: letter {g} rows", [cells[i] for i in rows_of(0, S0, g)], "columns", [cells[j] for j in cols_of(0, g)])
S1 = frozenset({idx[(0, 0)]})
print("   t=1, S={00}: rows per letter", len(rows_of(0, S1, 0)), len(rows_of(0, S1, 1)), "columns per letter", len(cols_of(0, 0)), len(cols_of(0, 1)))
print("5. nonzero coefficients have o_j = g_i")


def sum_t(poly, t, bound):
    return sum((v for a, v in poly.items() if a[t] <= bound and all(a[u] > bound for u in range(t))), F(0))


for bits in product([0, 1], repeat=8):
    x, y = bits[:4], bits[4:]
    total = F(0)
    for T in subsets(range(n)):
        if len(T) > r:
            continue
        for t in range(Q):
            for S in subsets(range(n)):
                if len(S) > 2 * r:
                    continue
                rows = [rows_of(t, S, g) for g in (0, 1)]
                cols = [cols_of(t, g) for g in (0, 1)]
                if any(len(a) != len(b) for a, b in zip(rows, cols)):
                    full = pdet([[pmul(coef(T, t, S, i, j), {(0, 0): eq(x[i], y[j])}) for j in range(n)] for i in range(n)])
                    assert full == {}
                    continue
                eps = sign(rows[0] + rows[1]) * sign(cols[0] + cols[1])
                xi = {i: x[i] for i in S}
                prod = {(0, 0): F(eps)}
                for g in (0, 1):
                    M = [[pmul(coef(T, t, S, i, j), {(0, 0): eq(xi.get(i, x[i]), y[j])}) for j in cols[g]] for i in rows[g]]
                    prod = pmul(prod, pdet(M))
                total += (-1) ** len(T) * sum_t(prod, t, 2 * r)
    assert total == eq(x, y)
print("6. the whole formula equals the product of the wires on all 256 bit points")

for q in (1, 2, 3):
    corners = list(product([0, 1], repeat=q))
    z = {}
    for a in corners:
        if a in z:
            continue
        co = tuple(1 - v for v in a)
        if 2 * sum(a) > q:
            z[a], z[co] = 1, 0
        else:
            z[a], z[co] = 0, 1
    assert all(z[a] != z[tuple(1 - v for v in a)] for a in corners)
    bound = sum(abs(q - 2 * sum(a)) for a in corners)
    best = None
    for p in permutations(corners):
        if all(z[a] != z[b] for a, b in zip(corners, p)):
            length = sum(sum(u != v for u, v in zip(a, b)) for a, b in zip(corners, p))
            best = length if best is None else min(best, length)
    assert best >= bound
    print(f"7. Q = {q}: bound {bound}, least length over permutations that do not vanish {best}")

corners = list(product([0, 1], repeat=2))
pts = list(product([0, 1], repeat=8))


def perm_prod(p, x, y):
    v = F(1)
    for i, a in enumerate(corners):
        v *= eq(x[i], y[corners.index(p[i])])
    return v


anti = [tuple(1 - v for v in a) for a in corners]
for limit, expected in ((2, False), (4, True)):
    fam = [p for p in permutations(corners) if sum(sum(u != v for u, v in zip(a, b)) for a, b in zip(corners, p)) <= limit]
    A = [[perm_prod(p, pt[:4], pt[4:]) for p in fam] for pt in pts]
    B = [row + [perm_prod(anti, pt[:4], pt[4:])] for row, pt in zip(A, pts)]
    in_span = rank(A) == rank(B)
    print(f"7. Q = 2: antipodal product in the span of the products of length at most {limit}: {in_span}")
    assert in_span == expected
