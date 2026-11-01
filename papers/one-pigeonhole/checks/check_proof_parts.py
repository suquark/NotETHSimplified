#!/usr/bin/env python3
"""Exact checks of the steps and constants of proof.tex, and of the identity with c_k in main.tex."""
import random, sys
from fractions import Fraction as F
from itertools import combinations, product
from math import comb, ceil, floor, log2, e as EUL

P = 2 ** 61 - 1


def rank_mod(A, p=P):
    A = [[x % p for x in r] for r in A]
    if not A:
        return 0
    n, m = len(A), len(A[0])
    r = 0
    for c in range(m):
        q = next((i for i in range(r, n) if A[i][c]), None)
        if q is None:
            continue
        A[r], A[q] = A[q], A[r]
        inv = pow(A[r][c], -1, p)
        for i in range(r + 1, n):
            if A[i][c]:
                g = A[i][c] * inv % p
                A[i] = [(x - g * y) % p for x, y in zip(A[i], A[r])]
        r += 1
    return r


def det_F(A):
    A = [r[:] for r in A]
    n = len(A)
    d = F(1)
    for c in range(n):
        q = next((i for i in range(c, n) if A[i][c] != 0), None)
        if q is None:
            return F(0)
        if q != c:
            A[c], A[q] = A[q], A[c]
            d = -d
        d *= A[c][c]
        for i in range(c + 1, n):
            if A[i][c] != 0:
                g = A[i][c] / A[c][c]
                A[i] = [x - g * y for x, y in zip(A[i], A[c])]
    return d


def det_mod(A, p=P):
    A = [[x % p for x in r] for r in A]
    n = len(A)
    d = 1
    for c in range(n):
        q = next((i for i in range(c, n) if A[i][c]), None)
        if q is None:
            return 0
        if q != c:
            A[c], A[q] = A[q], A[c]
            d = -d
        d = d * A[c][c] % p
        inv = pow(A[c][c], -1, p)
        for i in range(c + 1, n):
            if A[i][c]:
                g = A[i][c] * inv % p
                A[i] = [(x - g * y) % p for x, y in zip(A[i], A[c])]
    return d % p


def lagrange(window):
    def p(k):
        tot = F(0)
        for a in window:
            t = F((-1) ** a)
            for b in window:
                if b != a:
                    t *= F(k - b, a - b)
            tot += t
        return tot
    return p


def binom_poly(Q, R):
    """A closed form of the window polynomial: g(k)=(-1)^{k0} sum_{l<=R} C(k-k0,l)(-2)^l, with integer or negative k-k0."""
    k0 = (Q - R) // 2

    def gbin(x, l):
        r = F(1)
        for i in range(l):
            r *= F(x - i, i + 1)
        return r

    def g(k):
        return (-1) ** k0 * sum(gbin(k - k0, l) * (-2) ** l for l in range(R + 1))
    return g


def kappa_by_size(Q, R, p):
    out = []
    for e in range(Q + 1):
        s = F(0)
        for k in range(Q + 1):
            kr = sum((-1) ** i * comb(e, i) * comb(Q - e, k - i) for i in range(0, min(e, k) + 1) if k - i <= Q - e)
            s += p(k) * kr
        out.append(s / 2 ** Q)
    return out


def check_lemma():
    print("== Lemma 1: window polynomial, the explicit sum over exceptional vectors, rank on one cube")
    for Q, R in [(4, 2), (6, 2), (6, 4), (8, 2), (8, 4), (8, 6), (10, 4), (5, 2), (5, 3), (7, 2), (7, 4)]:
        window = [k for k in range(Q + 1) if abs(Q - 2 * k) <= R]
        assert len(window) <= R + 1
        p = lagrange(window)
        if (Q - R) % 2 == 0:
            assert len(window) == R + 1
            g = binom_poly(Q, R)
            assert all(p(k) == g(k) for k in range(Q + 1)), "binomial form differs from Lagrange"
        kap = kappa_by_size(Q, R, p)
        assert all(kap[e] == 0 for e in range(R + 1, Q + 1)), "degree above R"
        # eigenvalues
        exceptions = 0
        nonzero_err = 0
        for sig in product((1, -1), repeat=Q):
            k = sum(1 for x in sig if x < 0)
            val = F(0)
            for sz in range(R + 1):
                for E in combinations(range(Q), sz):
                    prod = 1
                    for i in E:
                        prod *= sig[i]
                    val += kap[sz] * prod
            par = (-1) ** k
            if abs(sum(sig)) <= R:
                assert val == par
            else:
                exceptions += 1
                if val != par:
                    nonzero_err += 1
        b = 2 ** Q
        assert exceptions * R * R <= b * Q
        # the formula of the proof, on corners F, F' of one cube
        if Q <= 7:
            sigs = list(product((1, -1), repeat=Q))
            def chi(sig, mask):
                prod = 1
                for i in range(Q):
                    if mask >> i & 1:
                        prod *= sig[i]
                return prod
            rho = {}
            for sig in sigs:
                val = F(0)
                for sz in range(R + 1):
                    for E in combinations(range(Q), sz):
                        val += kap[sz] * chi(sig, sum(1 << i for i in E))
                rho[sig] = val - chi(sig, b - 1)
                assert rho[sig] == 0 or abs(sum(sig)) > R
            for Fm in range(0, b, max(1, b // 8)):
                for Gm in range(b):
                    diff = Fm ^ Gm
                    lhs = (kap[bin(diff).count("1")] if bin(diff).count("1") <= R else F(0)) - (1 if diff == b - 1 else 0)
                    rhs = sum((rho[sig] * chi(sig, Fm) * chi(sig, Gm) for sig in sigs if abs(sum(sig)) > R), F(0)) / b
                    assert lhs == rhs, "formula of Lemma 1"
        # explicit matrix on corners, modulo a prime
        den = 1
        for sz in range(R + 1):
            den = den * kap[sz].denominator // __import__("math").gcd(den, kap[sz].denominator)
        Wm = [[0] * b for _ in range(b)]
        for a in range(b):
            for sz in range(R + 1):
                for E in combinations(range(Q), sz):
                    m = sum(1 << i for i in E)
                    Wm[a][a ^ m] += int(kap[sz] * den)
            Wm[a][a ^ (b - 1)] -= den
        rk = rank_mod(Wm)
        assert rk == nonzero_err, (rk, nonzero_err)
        print(f"  Q={Q} R={R}: window size {len(window)}, exceptions {exceptions}, rank {rk}, bound bQ/R^2={b*Q/R/R:.1f}")
    # Q=2 example
    Wm = [[0] * 4 for _ in range(4)]
    for a in range(4):
        Wm[a][a] += -1
        Wm[a][a ^ 1] += 1
        Wm[a][a ^ 2] += 1
        Wm[a][a ^ 3] += -1
    print("  Q=2: rank of tau_1+tau_2-1-tau_1tau_2 =", rank_mod(Wm), "; odd R=1: Q-R odd, so k_0=(Q-R)/2 is not an integer")


def check_trade():
    print("== Section 3: expansion over T; and, for main.tex, the identities with G(w) and with c_k")
    rng = random.Random(3)
    for trial in range(60):
        M = rng.randint(1, 7)
        r = rng.randint(0, M + 2)
        rr = min(r, M)
        # D diagonal, rows of A-D in a space of dimension <= r
        basis = [[F(rng.randint(-3, 3)) for _ in range(M)] for _ in range(rr)]
        D = [F(rng.randint(-3, 3)) for _ in range(M)]
        B = []
        for i in range(M):
            co = [F(rng.randint(-2, 2)) for _ in range(rr)]
            B.append([sum((co[l] * basis[l][j] for l in range(rr)), F(0)) for j in range(M)])
        A = [[B[i][j] + (D[i] if i == j else 0) for j in range(M)] for i in range(M)]
        prodD = F(1)
        for x in D:
            prodD *= x
        # equation (2): rows in T from A-D, the other rows from A; terms with |T|>r vanish
        lhsT = F(0)
        for k in range(M + 1):
            for T in combinations(range(M), k):
                Mx = [B[i][:] if i in T else A[i][:] for i in range(M)]
                dT = det_F(Mx)
                if k > r:
                    assert dT == 0, "more than r rows of A-D"
                else:
                    lhsT += (-1) ** k * dT
        assert lhsT == prodD, "expansion over T"
        # G(w) at M+1 points, interpolate: degree <= r, G(1)=prod D
        pts = [F(i) for i in range(M + 1)]
        vals = [det_F([[(1 - w) * A[i][j] + (w * D[i] if i == j else 0) for j in range(M)] for i in range(M)]) for w in pts]
        # Newton coefficients in monomial basis
        coef = [F(0)] * (M + 1)
        for a, pa in enumerate(pts):
            poly = [F(1)]
            den = F(1)
            for b, pb in enumerate(pts):
                if a != b:
                    poly = [(poly[i - 1] if i else 0) - pb * (poly[i] if i < len(poly) else 0) for i in range(len(poly) + 1)]
                    den *= pa - pb
            for i, c in enumerate(poly):
                coef[i] += vals[a] * c / den
        assert all(coef[k] == 0 for k in range(r + 1, M + 1)), "degree of G above r"
        assert sum(coef[: r + 1]) == prodD, "sum of low coefficients is not prod D"
        # form of main.tex, when r<M: sum c_k [s^k] P with c_k=(-1)^{r-k} C(M-k-1,r-k)
        if r < M:
            valsP = [det_F([[A[i][j] + (s * D[i] if i == j else 0) for j in range(M)] for i in range(M)]) for s in pts]
            coefP = [F(0)] * (M + 1)
            for a, pa in enumerate(pts):
                poly = [F(1)]
                den = F(1)
                for b, pb in enumerate(pts):
                    if a != b:
                        poly = [(poly[i - 1] if i else 0) - pb * (poly[i] if i < len(poly) else 0) for i in range(len(poly) + 1)]
                        den *= pa - pb
                for i, c in enumerate(poly):
                    coefP[i] += valsP[a] * c / den
            lhs = sum((-1) ** (r - k) * comb(M - k - 1, r - k) * coefP[k] for k in range(r + 1))
            assert lhs == prodD, "trade identity with closed-form c_k"
    # a small example
    A = [[F(2), F(1)], [F(1), F(2)]]
    Gw = lambda w: det_F([[(1 - w) * A[i][j] + (w if i == j else 0) for j in range(2)] for i in range(2)])
    assert all(Gw(F(w)) == 3 - 2 * F(w) for w in range(-3, 4))
    # partial-sum identity relating the two forms: sum_{h<=p} (-1)^h C(n,h) = (-1)^p C(n-1,p)
    for n in range(1, 12):
        for pp in range(0, n):
            assert sum((-1) ** h * comb(n, h) for h in range(pp + 1)) == (-1) ** pp * comb(n - 1, pp)
    print("  ok: expansion over T; deg G<=r, G(1)=prod D for r>=M too; c_k closed form agrees; G=3-2w example; partial-sum identity")


def check_real_matrix():
    print("== Sections 2-3 on real cells: rank(B-I), and rows of A-D in a space of dimension 2 rank(B-I), modulo a prime")
    rng = random.Random(5)
    for Q, R, fracused in [(4, 2, 1.0), (4, 2, 0.75), (6, 2, 1.0), (6, 4, 1.0), (6, 2, 0.5), (8, 4, 0.25)]:
        window = [k for k in range(Q + 1) if abs(Q - 2 * k) <= R]
        kap = kappa_by_size(Q, R, lagrange(window))
        den = 1
        import math
        for sz in range(R + 1):
            den = den * kap[sz].denominator // math.gcd(den, kap[sz].denominator)
        b = 2 ** Q
        corners = list(range(b))
        used = sorted(rng.sample(corners, int(b * fracused)))
        M = len(used)
        idx = {a: i for i, a in enumerate(used)}
        full = b - 1
        # c_i = corner a; d_j = complement of the corner of j
        Bm = [[0] * M for _ in range(M)]
        for i, a in enumerate(used):
            for sz in range(R + 1):
                for E in combinations(range(Q), sz):
                    m = sum(1 << t for t in E)
                    target = a ^ m  # tau_E c_i
                    # d_j = corner a_j ^ full
                    aj = target ^ full
                    j = idx.get(aj)
                    if j is not None:
                        Bm[i][j] += int(kap[sz] * den)
        rk = rank_mod([[Bm[i][j] - (den if i == j else 0) for j in range(M)] for i in range(M)])
        r = 2 * rk
        x = [rng.randint(0, 1) for _ in range(M)]
        y = [rng.randint(0, 1) for _ in range(M)]
        ind = lambda u, v: 1 if u == v else 0
        Am = [[Bm[i][j] * ind(x[i], y[j]) % P for j in range(M)] for i in range(M)]
        Dm = [den * ind(x[j], y[j]) % P for j in range(M)]
        rkAD = rank_mod([[(Am[i][j] - (Dm[i] if i == j else 0)) % P for j in range(M)] for i in range(M)])
        ok = rkAD <= r
        print(f"  Q={Q} R={R} M={M}: rank(B-I)={rk}, bound bQ/R^2={b*Q/R/R:.1f}, rank(A-D)={rkAD} <= r={r}: {ok}")
        assert ok


def check_constants():
    print("== Constants")
    for m in list(range(60, 200)) + [1000]:
        Q, R = m ** 4, m ** 3
        L = 6 * Q
        assert F(Q, R * R) == F(1, m * m)
        for Delta in {3, 16, 28, min(m, 100), m}:
            if not 3 <= Delta <= m:
                continue
            # 2N/m^2 <= 28 Delta n/m^2 <= r = Delta n/m
            assert 28 * m <= m * m
            # letter bits: (2n+N)/L <= 16 Delta n/L <= n/m
            assert 2 + 14 * Delta <= 16 * Delta
            assert 16 * Delta * m <= L
            # 2n/m <= r
            assert 2 <= Delta
            # M R + r Q <= 2 r Q: Delta n R = r Q
            for n in (1, 7, 1000):
                rr = F(Delta * n, m)
                assert Delta * n * R == rr * Q
        # (1-1/(2Q))^Q>=1/2 by Bernoulli: 1-3Q/L=1/2
        assert F(L - 3, L) == 1 - F(1, 2 * Q)
        assert 1 - F(3 * Q, L) == F(1, 2)
    # 8 e^2 < 60
    assert 8 * EUL ** 2 < 60
    # one instance of the exact bound (1-3/L)^Q>=1/2 for small Q
    for Q in range(1, 40):
        L = 6 * Q
        assert F(L - 3, L) ** Q >= F(1, 2)
    print("  ok")
    # the sums of the cost, exact for sample values: sum_{k<=aw} C(M,k) <= m^{aw} (1+1/m)^M, with r>=M/m
    for M, m in [(100, 60), (300, 60), (1000, 60), (5000, 61)]:
        w = F(M, m)
        for a in (1, 2):
            s = sum(comb(M, k) for k in range(0, floor(a * w) + 1))
            assert s <= m ** ceil(a * w) * (1 + F(1, m)) ** M
            assert (1 + 1 / m) ** M <= EUL ** float(w) * (1 + 1e-12)
    print("  ok: cost sums")


def check_placement():
    print("== Section 1: greedy placement and counts")
    rng = random.Random(11)
    for Q, L, nmul, Delta in [(1, 6, 1, 3), (1, 6, 4, 5), (1, 6, 1, 28), (2, 12, 1, 3)]:
        K = L ** Q
        n = K * K * nmul
        words = list(product(range(L), repeat=Q))
        s = [words[v % K] for v in range(n)]
        # random clauses with at most Delta occurrences per variable
        occ_left = [Delta] * n
        clauses = []
        order = [v for v in range(n) for _ in range(Delta)]
        rng.shuffle(order)
        i = 0
        while i < len(order):
            sz = rng.choice((1, 2, 3, 3, 3))
            cl = list(dict.fromkeys(order[i:i + sz]))
            clauses.append(cl)
            i += sz
        M = sum(len(c) for c in clauses)
        load = {}
        maxload = 0
        for cl in clauses:
            allowed = [w for w in words if all(all(a != b for a, b in zip(w, s[v])) for v in cl)]
            assert len(allowed) >= K / 2
            bestw, best = None, None
            tot = 0
            for w in allowed:
                val = sum(load.get((s[v], w), 0) for v in cl)
                tot += val
                if best is None or val < best:
                    best, bestw = val, w
            assert F(tot, len(allowed)) <= F(12 * Delta * n, K * K)
            assert best <= 12 * Delta * n / K / K
            for v in cl:
                load[(s[v], bestw)] = load.get((s[v], bestw), 0) + 1
                maxload = max(maxload, load[(s[v], bestw)])
        h = ceil(F(13 * Delta * n, K * K))
        assert maxload <= h
        N = K * (L - 1) ** Q * h
        assert N <= K * K * h <= 14 * Delta * n
        assert all(sum(1 for x in s if x == w) <= 2 * n / K for w in words[:5])
        # cells with first word letter g at digit t: exactly N/L
        cnt = sum((L - 1) ** Q * h for u in words if u[0] == 0)
        assert cnt * L == N
        print(f"  Q={Q} L={L} K={K} n={n} Delta={Delta} M={M}: max load {maxload} <= c={h}, N={N} <= 14 Delta n={14*Delta*n}")


def check_sign_fact():
    print("== The block fact, on random matrices with labels")
    rng = random.Random(13)
    def perm_sign(p):
        s = 1
        for i in range(len(p)):
            for j in range(i + 1, len(p)):
                if p[i] > p[j]:
                    s = -s
        return s
    for _ in range(300):
        n = rng.randint(1, 7)
        k = rng.randint(1, 3)
        rl = [rng.randrange(k) for _ in range(n)]
        cl = [rng.randrange(k) for _ in range(n)]
        A = [[F(rng.randint(-3, 3)) if rl[i] == cl[j] else F(0) for j in range(n)] for i in range(n)]
        d = det_F(A)
        if any(rl.count(g) != cl.count(g) for g in range(k)):
            assert d == 0
            continue
        rows = [i for g in range(k) for i in range(n) if rl[i] == g]
        cols = [j for g in range(k) for j in range(n) if cl[j] == g]
        v = F(perm_sign(rows) * perm_sign(cols))
        for g in range(k):
            rs = [i for i in range(n) if rl[i] == g]
            cs = [j for j in range(n) if cl[j] == g]
            v *= det_F([[A[i][j] for j in cs] for i in rs]) if rs else 1
        assert v == d
    print("  ok")


def check_pigeonhole(Q, R, M, seed=1):
    """det <T>_z on M cells of one cube, by a subset dynamic program, with exact integers, for every T with |T|<=r.
    Checks: every monomial has total degree<QJ; sum_t Sum_t(det <T>_z)=det <T>; sum_T (-1)^|T| det <T> = den^M prod [x_j=y_j];
    det <T>=0 for |T|=r+1."""
    import math
    rng = random.Random(seed)
    window = [k for k in range(Q + 1) if abs(Q - 2 * k) <= R]
    kap = kappa_by_size(Q, R, lagrange(window))
    den = 1
    for sz in range(R + 1):
        den = den * kap[sz].denominator // math.gcd(den, kap[sz].denominator)
    b = 2 ** Q
    used = sorted(rng.sample(range(b), M))
    idx = {a: i for i, a in enumerate(used)}
    full = b - 1
    Bm = [[F(0)] * M for _ in range(M)]
    for i, a in enumerate(used):
        for sz in range(R + 1):
            for E in combinations(range(Q), sz):
                j = idx.get(a ^ sum(1 << t for t in E) ^ full)
                if j is not None:
                    Bm[i][j] += kap[sz]
    rk = rank_mod([[int((Bm[i][j] - (1 if i == j else 0)) * den) for j in range(M)] for i in range(M)])
    r = 2 * rk
    J = (M * R + r * Q) // Q + 1
    x = [rng.randint(0, 1) for _ in range(M)]
    y = x[:]
    B = 64
    def enc(E):
        return sum(B ** t for t in E)
    short_rows = []
    for i, a in enumerate(used):
        row = {}
        for sz in range(R + 1):
            for E in combinations(range(Q), sz):
                j = idx.get(a ^ sum(1 << t for t in E) ^ full)
                if j is None or x[i] != y[j]:
                    continue
                val = int(kap[sz] * den)
                if val:
                    d = row.setdefault(j, {})
                    d[enc(E)] = d.get(enc(E), 0) + val
        short_rows.append(row)
    def det_T(T):
        layer = {0: {0: 1}}
        for i in range(M):
            row = {j: dict(p) for j, p in short_rows[i].items()}
            if i in T and x[i] == y[i]:
                row.setdefault(i, {})
                fe = enc(range(Q))
                row[i][fe] = row[i].get(fe, 0) - den
            new = {}
            for mask, poly in layer.items():
                for j, ent in row.items():
                    if mask >> j & 1:
                        continue
                    sign = -1 if bin(mask >> (j + 1)).count("1") % 2 else 1
                    nm = mask | (1 << j)
                    tgt = new.setdefault(nm, {})
                    for e2, c2 in ent.items():
                        s2 = sign * c2
                        for e1, c1 in poly.items():
                            ee = e1 + e2
                            tgt[ee] = tgt.get(ee, 0) + c1 * s2
            layer = {m: {e: c for e, c in p.items() if c} for m, p in new.items()}
        return layer.get((1 << M) - 1, {})
    target = den ** M * (1 if all(u == v for u, v in zip(x, y)) else 0)
    total = 0
    monos = 0
    maxdeg = 0
    for k in range(0, min(r, M) + 1):
        for T in combinations(range(M), k):
            poly = det_T(set(T))
            monos += len(poly)
            per_t = [0] * Q
            for e, c in poly.items():
                a = [(e // B ** t) % B for t in range(Q)]
                assert sum(a) < Q * J, (a, J)
                maxdeg = max(maxdeg, sum(a))
                per_t[next(t for t in range(Q) if a[t] < J)] += c
            assert sum(per_t) == sum(poly.values()), "Sum_t"
            total += (-1) ** k * sum(poly.values())
    assert total == target, "expansion over T"
    if r < M:
        for T in list(combinations(range(M), r + 1))[:20]:
            assert sum(det_T(set(T)).values()) == 0, "more than r rows"
    print(f"  Q={Q} R={R} M={M}: rank={rk}, r={r}, J={J}, monomials over all T={monos}, max degree {maxdeg} < QJ={Q*J}; "
          f"sum_T sum_t Sum_t=prod: ok")


if __name__ == "__main__":
    check_lemma()
    check_trade()
    check_real_matrix()
    check_constants()
    check_sign_fact()
    check_placement()
    print("== Section 3: pigeonhole, det <T>_z in full")
    check_pigeonhole(4, 2, 8)
    if "--slow" in sys.argv:
        check_pigeonhole(4, 2, 12)
    print("all checks passed")
