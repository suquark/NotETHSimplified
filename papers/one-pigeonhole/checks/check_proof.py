#!/usr/bin/env python3
"""End-to-end exact test, against brute force, of the formula in proof.tex.

Occurrences j of variables v in clauses e.  Words s(v), o(e) in [L]^Q that differ in every digit on each occurrence.
Cell c_j=(s(v),o(e),layer), transposed cell d_j=(o(e),s(v),layer).  Tested formula, equation (5):

    #solutions = sum_{|T|<=r} (-1)^|T| sum_t sum_{|S|<J, S balanced} sgn(t,S) sum_{xi in {0,1}^S} Sum_t( prod_g sum_{bits of g} Psi_g ),

where Psi_g is a polynomial in z_1..z_Q, and Sum_t adds the coefficients of the monomials z^a with a_t<J and a_t'>=J for all t'<t.
In proof.tex, r=Delta n/m and J=2r+1 (a_t<J means a_t<=2r).  Here r is twice the rank of the matrix of Lemma 1 on the occurrences,
and J is the least integer with MR+rQ<QJ, since the bound of the text is far above M on instances this small.
A letter function receives only the bits of its letter: reading another bit raises KeyError.
Node functions may be arbitrary integer tables (variable weights and clause tables), not only 1-prod y_j.
"""
import random, sys
from fractions import Fraction as F
from itertools import combinations, product
from math import comb


# ---- window polynomial by Lagrange interpolation, kappa by |E|
def lagrange_values(window):
    def p(k):
        tot = F(0)
        for a in window:
            term = F((-1) ** a)
            for b in window:
                if b != a:
                    term *= F(k - b, a - b)
            tot += term
        return tot
    return p


def kappa(Q, R, window=None):
    if window is None:
        k0 = (Q - R) // 2
        window = list(range(k0, k0 + R + 1))
    p = lagrange_values(window)
    pv = [p(k) for k in range(Q + 1)]
    out = []
    for e in range(Q + 1):
        s = F(0)
        for k in range(Q + 1):
            kr = sum((-1) ** i * comb(e, i) * comb(Q - e, k - i) for i in range(0, min(e, k) + 1) if k - i <= Q - e)
            s += pv[k] * kr
        out.append(s / 2 ** Q)
    assert all(out[e] == 0 for e in range(R + 1, Q + 1)), "degree above R"
    return out[: R + 1]


def rank(A):
    A = [r[:] for r in A]
    if not A:
        return 0
    n, m = len(A), len(A[0])
    r = 0
    for c in range(m):
        p = next((i for i in range(r, n) if A[i][c] != 0), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        for i in range(r + 1, n):
            if A[i][c] != 0:
                g = A[i][c] / A[r][c]
                A[i] = [x - g * y for x, y in zip(A[i], A[r])]
        r += 1
    return r


# ---- polynomials in (w,z): dict exponent tuple -> Fraction
def padd(p, q):
    o = dict(p)
    for k, v in q.items():
        o[k] = o.get(k, 0) + v
        if o[k] == 0:
            del o[k]
    return o


def pmul(p, q):
    o = {}
    for k, v in p.items():
        for l, u in q.items():
            m = tuple(a + b for a, b in zip(k, l))
            o[m] = o.get(m, 0) + v * u
    return {k: v for k, v in o.items() if v != 0}


def pscale(p, c):
    if c == 0:
        return {}
    return {k: v * c for k, v in p.items()}


def pdet(M, one):
    n = len(M)
    if n == 0:
        return one
    res = {}
    row = M[0]
    for j, e in enumerate(row):
        if not e:
            continue
        sub = [r[:j] + r[j + 1:] for r in M[1:]]
        d = pmul(e, pdet(sub, one))
        if j % 2:
            d = {k: -v for k, v in d.items()}
        res = padd(res, d)
    return res


def perm_sign(p):
    s = 1
    for i in range(len(p)):
        for j in range(i + 1, len(p)):
            if p[i] > p[j]:
                s = -s
    return s


def swap(E, c, Q):
    u, v, l = c
    return (tuple(v[i] if i in E else u[i] for i in range(Q)), tuple(u[i] if i in E else v[i] for i in range(Q)), l)


def run(Q, R, s, o, occ, var_w=None, cl_t=None, window=None, verbose=False):
    """s: dict var->word, o: dict clause->word, occ: list of (var, clause, neg).
    var_w[v][val]: weight of the variable; cl_t[e][y-tuple]: table of the clause.  Default: the CNF count."""
    M = len(occ)
    variables = sorted({v for v, e, n in occ})
    clauses = sorted({e for v, e, n in occ})
    occ_of_cl = {e: [j for j in range(M) if occ[j][1] == e] for e in clauses}
    if cl_t is None:
        cl_t = {}
        for e in clauses:
            cl_t[e] = {ys: (1 - all(ys)) for ys in product((0, 1), repeat=len(occ_of_cl[e]))}
    if var_w is None:
        var_w = {v: {0: 1, 1: 1} for v in variables}
    # cells, each occurrence its own layer on the pair
    used = {}
    cj, dj = [], []
    for v, e, n in occ:
        u, w = s[v], o[e]
        assert all(a != b for a, b in zip(u, w)), "words must differ in every digit"
        l = used.get((u, w), 0)
        used[(u, w)] = l + 1
        cj.append((u, w, l))
        dj.append((w, u, l))
    assert len(set(cj)) == M and len(set(dj)) == M
    kap = kappa(Q, R, window)
    short = [E for sz in range(R + 1) for E in combinations(range(Q), sz)]
    assert R < Q
    full = tuple(range(Q))
    # the matrix B, and which E reach which column
    col_of = {d: j for j, d in enumerate(dj)}
    reach = [[[] for _ in range(M)] for _ in range(M)]
    B = [[F(0)] * M for _ in range(M)]
    for i, c in enumerate(cj):
        for E in short:
            j = col_of.get(swap(set(E), c, Q))
            if j is not None:
                reach[i][j].append(E)
                B[i][j] += kap[len(E)]
    rk = rank([[B[i][j] - (1 if i == j else 0) for j in range(M)] for i in range(M)])
    r = 2 * rk
    J = (M * R + r * Q) // Q + 1
    # brute force
    def xbit(val, neg):
        return val ^ (1 - neg)
    truth = F(0)
    for vals in product((0, 1), repeat=len(variables)):
        asg = dict(zip(variables, vals))
        v = F(1)
        for u in variables:
            v *= var_w[u][asg[u]]
        for e in clauses:
            ys = tuple(xbit(asg[occ[j][0]], occ[j][2]) for j in occ_of_cl[e])
            v *= cl_t[e][ys]
        truth += v
    zero = (0,) * Q
    one = {zero: F(1)}
    def mono(E):
        return tuple(1 if i in E else 0 for i in range(Q))
    # kappa_E z^E, and the entry of -D in a row of T
    def short_term(E):
        return {mono(E): kap[len(E)]}
    long_term = {mono(full): F(-1)}
    total = F(0)
    # A row outside S has only entries with t not in E, so only T & S changes H.  The inner sum is kept for each T & S.
    tsets = [set(T) for k in range(0, min(r, M) + 1) for T in combinations(range(M), k)]
    balanced = 0
    tried = 0
    for t in range(Q):
        s_i = [s[occ[i][0]][t] for i in range(M)]
        o_i = [o[occ[i][1]][t] for i in range(M)]
        groups = sorted(set(s_i) | set(o_i))
        vars_g = {g: [v for v in variables if s[v][t] == g] for g in groups}
        ys_g = {g: [j for j in range(M) if o_i[j] == g] for g in groups}
        occx_g = {g: [j for j in range(M) if s_i[j] == g] for g in groups}
        cls_g = {g: [e for e in clauses if o[e][t] == g] for g in groups}
        for sz in range(0, min(J, M + 1)):
            for S in combinations(range(M), sz):
                tried += 1
                Sset = set(S)
                rows, cols = {}, {}
                for i in range(M):
                    g = o_i[i] if i in Sset else s_i[i]
                    rows.setdefault(g, []).append(i)
                for j in range(M):
                    cols.setdefault(o_i[j], []).append(j)
                labels = set(rows) | set(cols)
                if any(len(rows.get(b, [])) != len(cols.get(b, [])) for b in labels):
                    continue
                balanced += 1
                order = sorted(labels, key=str)
                rlist = [i for b in order for i in rows.get(b, [])]
                clist = [j for b in order for j in cols.get(b, [])]
                sgn = perm_sign(rlist) * perm_sign(clist)
                weight = {}
                for Tset in tsets:
                    key = frozenset(Tset & Sset)
                    weight[key] = weight.get(key, 0) + (-1) ** len(Tset)
                for key, wt in weight.items():
                  if wt == 0:
                    continue
                  # the coefficients gamma_ij, which do not depend on the bits
                  h = {}
                  for i in range(M):
                    for j in range(M):
                        e = {}
                        for E in reach[i][j]:
                            if (t in E) == (i in Sset):
                                e = padd(e, short_term(E))
                        if i == j and i in key:
                            e = padd(e, long_term)
                        h[i, j] = e
                  # check equation (4): gamma_ij != 0 => o_j = g_i
                  for i in range(M):
                    gi = o_i[i] if i in Sset else s_i[i]
                    for j in range(M):
                        if h[i, j]:
                            assert gi == o_i[j]
                  for xivals in product((0, 1), repeat=sz):
                    xi = dict(zip(S, xivals))
                    prod_poly = {zero: F(sgn)}
                    for g in groups:
                        grp = {}
                        for vals in product((0, 1), repeat=len(vars_g[g])):
                            asg = dict(zip(vars_g[g], vals))
                            x = {j: xbit(asg[occ[j][0]], occ[j][2]) for j in occx_g[g]}
                            fac = F(1)
                            for v_ in vars_g[g]:
                                fac *= var_w[v_][asg[v_]]
                            for j in occx_g[g]:
                                if j in Sset and x[j] != xi[j]:
                                    fac = F(0)
                            if fac == 0:
                                continue
                            for yv in product((0, 1), repeat=len(ys_g[g])):
                                y = dict(zip(ys_g[g], yv))
                                val = fac
                                for e in cls_g[g]:
                                    val *= cl_t[e][tuple(y[j] for j in occ_of_cl[e])]
                                if val == 0:
                                    continue
                                rs, cs = rows.get(g, []), cols.get(g, [])
                                mat = [[pscale(h[i, j], F(1 if (xi[i] if i in Sset else x[i]) == y[j] else 0)) for j in cs] for i in rs]
                                grp = padd(grp, pmul({zero: val}, pdet(mat, one)))
                        prod_poly = pmul(prod_poly, grp)
                        if not prod_poly:
                            break
                    # the monomials of the product, with their weight from the sets T.  A term of det <T>_z has low degree for
                    # each T; the product here is the sum over the bits of the determinant, so the same bound holds.
                    for a, v_ in prod_poly.items():
                        assert sum(a) < Q * J
                        least = next(i for i in range(Q) if a[i] < J)
                        if least == t:
                            total += wt * v_
    assert total == truth, (total, truth)
    return dict(M=M, r=r, J=J, truth=truth, balanced_over_tried=f"{balanced}/{tried}")


def rand_tables(rng, s, o, occ):
    variables = sorted({v for v, e, n in occ})
    clauses = sorted({e for v, e, n in occ})
    vals = (-3, -2, -1, 1, 2, 3, 4)
    var_w = {v: {0: rng.choice(vals), 1: rng.choice(vals)} for v in variables}
    cl_t = {}
    for e in clauses:
        n = sum(1 for _, e2, _ in occ if e2 == e)
        cl_t[e] = {ys: rng.choice(vals) for ys in product((0, 1), repeat=n)}
    return var_w, cl_t


def split_instance(rng, cells, max_cl=3, share_var=0.3):
    """Turn a list of (u,w) word pairs into occurrences: occurrences on one word u share a variable with probability share_var;
    those on one word w fill clauses of size at most max_cl."""
    s, o, occ = {}, {}, []
    var_on = {}
    cl_on = {}
    nv = ne = 0
    for u, w in cells:
        if u in var_on and rng.random() < share_var:
            v = rng.choice(var_on[u])
        else:
            v = nv
            nv += 1
            s[v] = u
            var_on.setdefault(u, []).append(v)
        if w in cl_on and cl_on[w][-1][1] < max_cl and rng.random() < 0.6:
            e = cl_on[w][-1][0]
            cl_on[w][-1][1] += 1
        else:
            e = ne
            ne += 1
            o[e] = w
            cl_on.setdefault(w, []).append([e, 1])
        occ.append((v, e, rng.randint(0, 1)))
    return s, o, occ


def comp(a):
    return tuple(1 - x for x in a)


if __name__ == "__main__":
    rng = random.Random(7)
    # one square fully used, four occurrences, tables
    sq = [(a, comp(a)) for a in product((0, 1), repeat=2)]
    for _ in range(4):
        s, o, occ = split_instance(rng, sq, share_var=0.0)
        var_w, cl_t = rand_tables(rng, s, o, occ)
        print("square, tables", run(2, 1, s, o, occ, var_w, cl_t), flush=True)
    # one square with a real CNF: shared variables and clauses
    for _ in range(4):
        s, o, occ = split_instance(rng, sq, share_var=0.8)
        print("square, CNF", run(2, 1, s, o, occ), flush=True)
    # two layers: six occurrences, then eight
    two = sq + sq[:2]
    s, o, occ = split_instance(rng, two, share_var=0.4)
    var_w, cl_t = rand_tables(rng, s, o, occ)
    print("two layers, six, tables", run(2, 1, s, o, occ, var_w, cl_t), flush=True)
    s, o, occ = split_instance(rng, two, share_var=0.6)
    print("two layers, six, CNF", run(2, 1, s, o, occ), flush=True)
    if "--slow" in sys.argv:
        s, o, occ = split_instance(rng, sq + sq, share_var=0.5)
        print("two layers, eight, CNF", run(2, 1, s, o, occ), flush=True)
    # three digits, part of a cube
    cube3 = [(a, comp(a)) for a in product((0, 1), repeat=3)]
    s, o, occ = split_instance(rng, cube3[:6], share_var=0.0)
    var_w, cl_t = rand_tables(rng, s, o, occ)
    print("Q=3 six, tables", run(3, 2, s, o, occ, var_w, cl_t), flush=True)
    s, o, occ = split_instance(rng, cube3[:6], share_var=0.5)
    print("Q=3 six, CNF", run(3, 2, s, o, occ), flush=True)
    if "--slow" in sys.argv:
        s, o, occ = split_instance(rng, cube3, share_var=0.5)
        print("Q=3 eight, CNF", run(3, 2, s, o, occ), flush=True)
    # three letters: several cubes, partly used, rank may be large (r>=M is allowed in this form)
    w3 = list(product((0, 1, 2), repeat=2))
    pairs = [(u, v) for u in w3 for v in w3 if all(a != b for a, b in zip(u, v))]
    for _ in range(3):
        cells = rng.sample(pairs, 5)
        s, o, occ = split_instance(rng, cells, share_var=0.5)
        print("three letters, five, CNF", run(2, 1, s, o, occ), flush=True)
    if "--slow" in sys.argv:
        for _ in range(6):
            s, o, occ = split_instance(rng, sq + sq[:rng.randint(0, 4)], share_var=rng.choice((0.0, 0.5)))
            var_w, cl_t = rand_tables(rng, s, o, occ)
            print("more tables", run(2, 1, s, o, occ, var_w, cl_t), flush=True)
        for _ in range(4):
            cells = rng.sample(cube3, rng.randint(4, 7))
            s, o, occ = split_instance(rng, cells, share_var=rng.choice((0.0, 0.5)))
            var_w, cl_t = rand_tables(rng, s, o, occ)
            print("more Q=3 tables", run(3, 2, s, o, occ, var_w, cl_t), flush=True)
    # r>=M: cells in different cubes
    cells = [((0, 0), (1, 1)), ((2, 0), (0, 1)), ((0, 2), (1, 0))]
    s, o, occ = split_instance(rng, cells, share_var=0.0)
    var_w, cl_t = rand_tables(rng, s, o, occ)
    print("r>=M", run(2, 1, s, o, occ, var_w, cl_t), flush=True)
