#!/usr/bin/env python3
"""Exact test of the digit-free form of the uncrossing proof, as Lean states it.

A level has K = K' * K' words. The word (a, b) has the number a * K' + b. The weight w(x, y) is symmetric, and
w(x, x) is allowed. An assignment B gives each word x and each word y a number B[x][y] < 2 ** w(x, y). It is symmetric if
B[x][y] = B[y][x]. val(K, w, F) is the sum over symmetric B of the product over x of F(x, B[x]).

One step: for a choice code c and a direction, new weights w' on K' words, and new word functions F'. The claim is

    2 ** (M * #rectangles) * val(K, w, F) = sum over valid c of val(K', w'_c, F'_c).

Only the standard library. Exact integers.
"""
import itertools
import random
from fractions import Fraction
from math import comb


def bit(x, j):
    return (x >> j) & 1


def pop(x):
    return bin(x).count("1")


def chi(c, a, b):
    if c == 0:
        return 1 if a == b else 0
    if c == 1:
        return 1 if a != b else 0
    if c == 2:
        return (1 if a == 0 else -1) if a == b else 0
    return (1 if a == 0 else -1) if a != b else 0


def fpat(pi, p, q):
    out = 1
    for j, c in enumerate(pi):
        out *= chi(c, bit(p, j), bit(q, j))
        if out == 0:
            return 0
    return out


def oddmin(a, b):
    t = min(a, b)
    if t == 0:
        return 0
    return t if t % 2 == 1 else t - 1


def thr(m):
    return (m + 1) // 2


def dlen(cheap, m):
    return m + (8 * (m // 2) + 4) // 5 if cheap else 2 * m


def decode(cheap, is_row, m, xi):
    """Returns (valid, letters)."""
    if not cheap:
        return True, [(xi >> (2 * j)) & 3 for j in range(m)]
    M = xi % 2 ** m
    c = xi >> m
    if not c < 3 ** (m - pop(M)):
        return False, None
    spec = 3 if is_row else 0
    out = []
    for j in range(m):
        if bit(M, j):
            out.append(spec)
        else:
            d = (c // 3 ** (j - pop(M % 2 ** j))) % 3
            out.append(d if is_row else d + 1)
    return True, out


def coef(is_row, pol_row, m, pi):
    n0 = pi.count(0)
    n3 = pi.count(3)
    t = thr(m)

    def cond(r):
        return r >= t if pol_row else r < t
    if is_row:
        return sum(comb(n3, r) * (-2) ** r for r in range(n3 + 1) if cond(r))
    return (-1) ** n3 * sum(comb(n0, r) * 2 ** (n0 - r) * (-1) ** r for r in range(n0 + 1) if cond(m - n0 + r))


def rect_a(is_row, pol_row, scale, m, xi, p, q):
    cheap = is_row == pol_row
    ok, pi = decode(cheap, is_row, m, xi)
    if not ok:
        return 0
    return 2 ** (scale - m) * coef(is_row, pol_row, m, pi) * fpat(pi, p, q)


def rect_b(is_row, pol_row, m, xi, r, s):
    cheap = is_row == pol_row
    ok, pi = decode(cheap, is_row, m, xi)
    if not ok:
        return 0
    return fpat(pi, r, s)


class Level:
    """The derived numbers of one step. K1 is K', dir_row is the direction, c is the choice code."""

    def __init__(self, K1, w, c, dir_row):
        self.K1, self.w, self.c, self.dir_row = K1, w, c, dir_row

    def mk(self, u, v):
        return u * self.K1 + v if self.dir_row else v * self.K1 + u

    def pm(self, u, u2, v, v2):
        """Paired wires on the diagonal (u, v) - (u2, v2), in the coordinates of the direction."""
        if u == u2 or v == v2:
            return 0
        return oddmin(self.w(self.mk(u, v), self.mk(u2, v2)), self.w(self.mk(u, v2), self.mk(u2, v)))

    def idx(self, u, u2, v, v2):
        """The choice bit of a rectangle with u < u2, v < v2, in the coordinates of rows and columns."""
        K1 = self.K1
        a, a2, b, b2 = (u, u2, v, v2) if self.dir_row else (v, v2, u, u2)
        return ((a * K1 + a2) * K1 + b) * K1 + b2

    def pol(self, u, u2, v, v2):
        return bit(self.c, self.idx(u, u2, v, v2)) == 0  # bit 0 is the piece with many S, "row"

    def dd(self, u, u2, v, v2):
        """Index wires of the segment (v, v2) of the pair u < u2. Only v < v2 has any."""
        if v >= v2:
            return 0
        return dlen(self.pol(u, u2, v, v2) == self.dir_row, self.pm(u, u2, v, v2))

    def carry(self, u, u2, v, v2):
        return self.w(self.mk(u, v), self.mk(u2, v2)) - self.pm(u, u2, v, v2)

    def seg(self, u, u2, v, v2):
        return self.carry(u, u2, v, v2) + self.dd(u, u2, v, v2)

    def new_w(self, u, u2):
        if u == u2:
            return 0
        a, b = min(u, u2), max(u, u2)
        return sum(self.seg(a, b, v, v2) for v in range(self.K1) for v2 in range(self.K1))

    def soff(self, u, u2, v, v2):
        """Offset of the segment (v, v2) in the wires of the pair u < u2, in the order of v * K' + v2."""
        K1 = self.K1
        return sum(self.seg(u, u2, t // K1, t % K1) for t in range(v * K1 + v2))


def seg_part(lv, u1, u2, v, v2, b):
    return (b >> lv.soff(u1, u2, v, v2)) % 2 ** lv.seg(u1, u2, v, v2)


def trans(lv, scale, u, B, Bn):
    """T: B[v][x] is the number at word mk(u, v) towards x. Bn[u2] is the new number at u towards u2."""
    K1 = lv.K1
    out = 1
    for v in range(K1):
        for v2 in range(v + 1, K1):
            if B[v][lv.mk(u, v2)] != B[v2][lv.mk(u, v)]:
                return 0
    for u2 in range(K1):
        if u2 == u:
            continue
        for v in range(K1):
            for v2 in range(K1):
                if u < u2:
                    u1, u_2 = u, u2
                    own = v
                    x = lv.mk(u2, v2)
                else:
                    u1, u_2 = u2, u
                    own = v2
                    x = lv.mk(u2, v)
                b = seg_part(lv, u1, u_2, v, v2, Bn[u2])
                m = lv.pm(u1, u_2, v, v2)
                cc = lv.carry(u1, u_2, v, v2)
                if b % 2 ** cc != B[own][x] >> m:
                    return 0
                if v < v2:
                    xi = b >> cc
                    pol = lv.pol(u1, u_2, v, v2)
                    if u < u2:
                        p = B[v][lv.mk(u2, v2)] % 2 ** m
                        q = B[v2][lv.mk(u2, v)] % 2 ** m
                        out *= rect_a(lv.dir_row, pol, scale_of(scale), m, xi, p, q)
                    else:
                        r = B[v][lv.mk(u2, v2)] % 2 ** m
                        s = B[v2][lv.mk(u2, v)] % 2 ** m
                        out *= rect_b(lv.dir_row, pol, m, xi, r, s)
                    if out == 0:
                        return 0
    return out


def scale_of(s):
    return s


def assignments_at(ws):
    return itertools.product(*[range(2 ** t) for t in ws])


def new_F(lv, scale, F, K1):
    K = K1 * K1

    def Fn(u, Bn):
        # sum over the numbers of all words of the row of u
        sizes = [lv.w(lv.mk(u, v), x) for v in range(K1) for x in range(K)]
        total = 0
        for vals in assignments_at(sizes):
            B = [list(vals[v * K:(v + 1) * K]) for v in range(K1)]
            t = trans(lv, scale, u, B, Bn)
            if t == 0:
                continue
            for v in range(K1):
                t *= F(lv.mk(u, v), B[v])
                if t == 0:
                    break
            total += t
        return total
    return Fn


def val(K, w, F):
    """Sum over symmetric B."""
    pairs = [(x, y) for x in range(K) for y in range(x, K)]
    sizes = [w(x, y) for x, y in pairs]
    total = 0
    for vals in assignments_at(sizes):
        B = [[0] * K for _ in range(K)]
        for (x, y), b in zip(pairs, vals):
            B[x][y] = b
            B[y][x] = b
        t = 1
        for x in range(K):
            t *= F(x, B[x])
            if t == 0:
                break
        total += t
    return total


def rects(K1):
    return [(a, a2, b, b2) for a in range(K1) for a2 in range(a + 1, K1) for b in range(K1) for b2 in range(b + 1, K1)]


def valid(K1, c):
    good = {((a * K1 + a2) * K1 + b) * K1 + b2 for a, a2, b, b2 in rects(K1)}
    return all(bit(c, i) == 0 or i in good for i in range(K1 ** 4))


def psi(K, w):
    return sum(w(x, y) ** 2 for x in range(K) for y in range(K))


def choose_dir(K1, w, c):
    """Row if its sum of squares is at most that of the columns."""
    lr = Level(K1, w, c, True)
    lc = Level(K1, w, c, False)
    return psi(K1, lr.new_w) <= psi(K1, lc.new_w)


def test_step(K1, w_table, F, scale, force_dir=None, stats=None):
    K = K1 * K1

    def w(x, y):
        return w_table[x][y]
    lhs = 2 ** (scale * len(rects(K1))) * val(K, w, F)
    rhs = 0
    for c in range(2 ** (K1 ** 4)):
        if not valid(K1, c):
            continue
        d = choose_dir(K1, w, c) if force_dir is None else force_dir
        lv = Level(K1, w, c, d)
        # potential inequality, for this code
        lr = Level(K1, w, c, True)
        lc = Level(K1, w, c, False)
        pr, pc = psi(K1, lr.new_w), psi(K1, lc.new_w)
        assert 25 * (pr + pc) <= 48 * K1 ** 2 * psi(K, w), (pr, pc, psi(K, w))
        assert 25 * min(pr, pc) <= 24 * K1 ** 2 * psi(K, w)
        # the wire number does not grow
        assert sum(lv.new_w(u, x) for u in range(K1) for x in range(K1)) <= sum(w(x, y) for x in range(K) for y in range(K))
        Fn = new_F(lv, scale, F, K1)
        rhs += val(K1, lv.new_w, Fn)
    assert lhs == rhs, (lhs, rhs)
    if stats is not None:
        stats["steps"] = stats.get("steps", 0) + 1
    return lhs


def random_F(K, rng, w_table):
    tabs = {}

    def F(x, Bx):
        key = (x, tuple(Bx))
        if key not in tabs:
            tabs[key] = rng.randint(-3, 3)
        return tabs[key]
    return F


def sym_table(K, rng, total):
    t = [[0] * K for _ in range(K)]
    for _ in range(total):
        x, y = rng.randrange(K), rng.randrange(K)
        t[x][y] += 1
        if x != y:
            t[y][x] += 1
    return t


def hat(a):
    return 1 - 2 * a


def formula_checks():
    """The identity of Section 2 and the two expansions of the factors, on every input for m <= 3."""
    for x, y, u, v in itertools.product((0, 1), repeat=4):
        X, Y, Z, T = hat(x), hat(y), hat(u), hat(v)
        cross = int(x == v and y == u)
        U = chi(0, x, u) * chi(0, y, v)
        S = chi(3, x, y) * chi(3, u, v)
        assert 4 * cross == (1 + X * T) * (1 + Y * Z)
        assert 4 * U == (1 + X * Z) * (1 + Y * T)
        assert 4 * S == (X - Y) * (Z - T)
        assert cross == U - S
        assert 2 * U == sum(chi(c, x, y) * chi(c, u, v) for c in range(4))
        assert 2 * S == chi(0, x, u) * chi(0, y, v) - chi(1, x, u) * chi(1, y, v) - chi(2, x, u) * chi(2, y, v) + chi(3, x, u) * chi(3, y, v)
        for a, b in ((x, y), (u, v), (x, u), (y, v)):
            A, B = hat(a), hat(b)
            assert 2 * chi(0, a, b) == 1 + A * B and 2 * chi(1, a, b) == 1 - A * B
            assert 2 * chi(2, a, b) == A + B and 2 * chi(3, a, b) == A - B
    for m in range(0, 4):
        strings = list(itertools.product(range(4), repeat=m))
        for x, y, u, v in itertools.product(range(2 ** m), repeat=4):
            for z in (Fraction(0), Fraction(1), Fraction(-3, 2), Fraction(5, 7)):
                g = Fraction(1)
                for j in range(m):
                    Uj = chi(0, bit(x, j), bit(u, j)) * chi(0, bit(y, j), bit(v, j))
                    Sj = chi(3, bit(x, j), bit(y, j)) * chi(3, bit(u, j), bit(v, j))
                    g *= Uj - z * Sj
                r = sum((1 - 2 * z) ** pi.count(3) * fpat(pi, x, y) * fpat(pi, u, v) for pi in strings) / 2 ** m
                c = sum((-1) ** pi.count(3) * (1 - z / 2) ** pi.count(0) * (z / 2) ** (m - pi.count(0)) * fpat(pi, x, u) * fpat(pi, y, v) for pi in strings)
                assert g == r == c
    print("the identity and the expansions of U and S, on every input for m <= 3: pass", flush=True)


def seed_checks():
    """The rectangle sums on every input for small m."""
    for m in range(0, 4):
        for x, y, u, v in itertools.product(range(2 ** m), repeat=4):
            # the two pieces
            pieces = {}
            for pol in (True, False):
                tot = 0
                for r in range(m + 1):
                    if (r >= thr(m)) != pol:
                        continue
                    for I in itertools.combinations(range(m), r):
                        term = 1
                        for j in range(m):
                            U = int(bit(x, j) == bit(u, j) and bit(y, j) == bit(v, j))
                            sx = (1 if bit(x, j) == 0 else -1) if bit(x, j) != bit(y, j) else 0
                            su = (1 if bit(u, j) == 0 else -1) if bit(u, j) != bit(v, j) else 0
                            term *= -sx * su if j in I else U
                        tot += term
                pieces[pol] = tot
            assert pieces[True] + pieces[False] == int(x == v and y == u)
            for pol in (True, False):
                for is_row in (True, False):
                    d = dlen(is_row == pol, m)
                    a, b, c2, e = (x, y, u, v) if is_row else (x, u, y, v)
                    tot = sum(rect_a(is_row, pol, m, m, xi, a, b) * rect_b(is_row, pol, m, xi, c2, e) for xi in range(2 ** d))
                    assert tot == 2 ** m * pieces[pol], (m, x, y, u, v, pol, is_row, tot, pieces[pol])
    # the code lengths
    for w2 in range(0, 3000):
        m = oddmin(w2, w2)
        for w1 in (w2, w2 + 1, w2 + 7):
            f = w1 + w2 - 2 * m + dlen(True, m)
            assert 10 * f <= 10 * w1 + 9 * w2
            assert f <= w1 + w2
            big = (w1 + w2) ** 2 + f ** 2
            assert 25 * big <= 96 * (w1 * w1 + w2 * w2)
    print("seed sums on every input for m <= 3, and the width bound for min <= 3000: pass", flush=True)


def piece_checks():
    """P^r and P^c from sets T, and their expansions across each cut, with exact coefficients."""
    def chi_c(c, a, b):
        return Fraction(chi(c, a, b))
    for m in (1, 3):
        k = (m - 1) // 2
        strings = list(itertools.product(range(4), repeat=m))
        for x, y, u, v in itertools.product(range(2 ** m), repeat=4):
            b = [(bit(x, j), bit(y, j), bit(u, j), bit(v, j)) for j in range(m)]
            Uj = [chi(0, p, s) * chi(0, q, r) for p, q, s, r in [(b0, b1, b2, b3) for b0, b1, b2, b3 in b]]
            Sj = [chi(3, p, q) * chi(3, s, r) for p, q, s, r in b]
            cross = 1 if x == v and y == u else 0
            pr = pc = 0
            for size in range(m + 1):
                for T in itertools.combinations(range(m), size):
                    val_t = 1
                    for j in range(m):
                        val_t *= -Sj[j] if j in T else Uj[j]
                    if size >= m / 2:
                        pr += val_t
                    else:
                        pc += val_t
            assert pr + pc == cross
            # Across the rows, P^r has only strings with at most k letters other than 3.
            rows = Fraction(0)
            for pi in strings:
                if sum(1 for c in pi if c != 3) > k:
                    continue
                n3 = sum(1 for c in pi if c == 3)
                coef = sum(Fraction(comb(n3, i) * (-1) ** i * 2 ** i, 2 ** m) for i in range(k + 1, n3 + 1))
                f = Fraction(1)
                for j, c in enumerate(pi):
                    f *= chi_c(c, b[j][0], b[j][1]) * chi_c(c, b[j][2], b[j][3])
                rows += coef * f
            assert rows == pr
            # Across the columns, P^c has only strings with at most k letters other than 0.
            cols = Fraction(0)
            for pi in strings:
                nz = [j for j, c in enumerate(pi) if c != 0]
                if len(nz) > k:
                    continue
                coef = Fraction(0)
                for size in range(len(nz), k + 1):
                    for T in itertools.combinations(range(m), size):
                        if not set(nz) <= set(T):
                            continue
                        term = Fraction(1, 2 ** size)
                        for j in T:
                            if pi[j] in (0, 3):
                                term = -term
                        coef += term
                f = Fraction(1)
                for j, c in enumerate(pi):
                    f *= chi_c(c, b[j][0], b[j][2]) * chi_c(c, b[j][1], b[j][3])
                cols += coef * f
            assert cols == pc
    print("pieces from sets T, and the cheap expansions with exact coefficients, on every input for m = 1 and 3: pass", flush=True)


def main():
    piece_checks()
    formula_checks()
    seed_checks()
    rng = random.Random(7)
    stats = {}
    # K' = 2
    for total in range(0, 10):
        for _ in range(6):
            t = sym_table(4, rng, total)
            if sum(t[x][y] for x in range(4) for y in range(x, 4)) > 9:
                continue
            scale = max(max(r) for r in t) + 1
            for force in (True, False, None):
                test_step(2, t, random_F(4, rng, t), scale, force, stats)
    print("K'=2:", stats, flush=True)
    # A crossing with a larger m
    for w1, w2 in [(1, 1), (2, 1), (2, 2), (3, 2), (3, 3), (4, 3)]:
        t = [[0] * 4 for _ in range(4)]
        t[0][3] = t[3][0] = w1
        t[1][2] = t[2][1] = w2
        scale = w1 + 1
        for force in (True, False):
            test_step(2, t, random_F(4, rng, t), scale, force, stats)
    print("K'=2 with crossings:", stats, flush=True)
    # K' = 3: only a few codes are cheap to run, so test the valid codes on few wires
    # The last table has two crossing rectangles: rows 0, 1 and columns 0, 1, and rows 1, 2 and columns 1, 2.
    two = [[0] * 9 for _ in range(9)]
    for x, y in [(0, 4), (1, 3), (4, 8), (5, 7)]:
        two[x][y] = two[y][x] = 1
    for t in [sym_table(9, rng, 3) for _ in range(4)] + [two]:
        scale = max(max(r) for r in t) + 1
        k1 = 3

        def w(x, y, t=t):
            return t[x][y]
        F = random_F(9, rng, t)
        lhs = 2 ** (scale * len(rects(k1))) * val(9, w, F)
        rhs = 0
        rs = rects(k1)
        for bits in itertools.product((0, 1), repeat=len(rs)):
            c = 0
            for (a, a2, b, b2), bt in zip(rs, bits):
                c |= bt << (((a * k1 + a2) * k1 + b) * k1 + b2)
            lv = Level(k1, w, c, choose_dir(k1, w, c))
            rhs += val(k1, lv.new_w, new_F(lv, scale, F, k1))
        assert lhs == rhs
        stats["K3"] = stats.get("K3", 0) + 1
    print("K'=3:", stats, flush=True)
    print("ALL PASS")


if __name__ == "__main__":
    main()
