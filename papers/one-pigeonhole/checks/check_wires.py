#!/usr/bin/env python3
"""End-to-end exact test of the proof in the form indexed by wires, against brute force.

Words [L]^Q are nodes. A wire j has a cell c_j=(u,w,layer): its tail u holds the bit x_j, its head w holds the bit y_j.
Each node has an arbitrary integer table on its bits.  Claim: the network sum equals the formula of the paper:
sum over t, S, T, U of (coefficient extraction) of a product over the groups of digit t of sums over the bits of the group.
Each group function receives only the bits of its group; reading another bit raises KeyError.
"""
import random, sys
from fractions import Fraction as F
from itertools import combinations, product
from math import comb

def kraw(Q,k,w): return sum((-1)**j*comb(w,j)*comb(Q-w,k-j) for j in range(k+1))
def kappa(Q,R):
    w0=(Q-R)//2; win=range(w0,w0+R+1)
    A=[[F(kraw(Q,k,w)) for k in range(R+1)]+[F((-1)**w)] for w in win]; n=R+1
    for c in range(n):
        p=next(i for i in range(c,n) if A[i][c]!=0); A[c],A[p]=A[p],A[c]
        A[c]=[x/A[c][c] for x in A[c]]
        for i in range(n):
            if i!=c and A[i][c]!=0:
                g=A[i][c]; A[i]=[x-g*y for x,y in zip(A[i],A[c])]
    return [A[k][n] for k in range(n)]
def rank(A):
    A=[r[:] for r in A]
    if not A: return 0
    n=len(A); m=len(A[0]); r=0
    for c in range(m):
        p=next((i for i in range(r,n) if A[i][c]!=0),None)
        if p is None: continue
        A[r],A[p]=A[p],A[r]
        for i in range(r+1,n):
            if A[i][c]!=0:
                g=A[i][c]/A[r][c]
                A[i]=[x-g*y for x,y in zip(A[i],A[r])]
        r+=1
    return r
# polynomials in y: dict exponent tuple -> Fraction
def padd(p,q):
    o=dict(p)
    for k,v in q.items():
        o[k]=o.get(k,0)+v
        if o[k]==0: del o[k]
    return o
def pmul(p,q):
    o={}
    for k,v in p.items():
        for l,w in q.items():
            m=tuple(a+b for a,b in zip(k,l)); o[m]=o.get(m,0)+v*w
    return {k:v for k,v in o.items() if v!=0}
def pdet(M,Q):
    n=len(M); one={(0,)*Q:F(1)}
    if n==0: return one
    # expansion along the first row
    res={}
    row=M[0]
    for j,e in enumerate(row):
        if not e: continue
        sub=[r[:j]+r[j+1:] for r in M[1:]]
        d=pmul(e,pdet(sub,Q))
        if j%2: d={k:-v for k,v in d.items()}
        res=padd(res,d)
    return res
def perm_sign(p):
    s=1
    for i in range(len(p)):
        for j in range(i+1,len(p)):
            if p[i]>p[j]: s=-s
    return s
def run(Q,R,L,wires,tables,seed=0):
    M=len(wires)
    swap=lambda E,c:(tuple(c[1][i] if i in E else c[0][i] for i in range(Q)),tuple(c[0][i] if i in E else c[1][i] for i in range(Q)),c[2])
    tr=lambda c:(c[1],c[0],c[2])
    kap=kappa(Q,R)
    reads=[E for n in range(R+1) for E in combinations(range(Q),n)]
    d=[tr(c) for c in wires]
    key=lambda c:(tuple((min(a,b),max(a,b)) for a,b in zip(c[0],c[1])),c[2])
    # k matrix: entries by read
    k=[[F(0)]*M for _ in range(M)]
    rd=[[[] for _ in range(M)] for _ in range(M)]
    for i,c in enumerate(wires):
        for E in reads:
            t2=swap(E,c)
            for j in range(M):
                if d[j]==t2:
                    k[i][j]+=kap[len(E)]; rd[i][j].append(E)
    B=[[k[i][j]-(1 if i==j else 0) for j in range(M)] for i in range(M)]
    rk=rank(B); r=2*rk
    # the bits
    tail=[c[0] for c in wires]; head=[c[1] for c in wires]
    nodes=sorted(set(tail)|set(head))
    def node_val(u,bits):
        idx=tuple(bits[('x',j)] for j in range(M) if tail[j]==u)+tuple(bits[('y',j)] for j in range(M) if head[j]==u)
        return tables[u][idx]
    # brute force
    truth=F(0)
    for z in product((0,1),repeat=M):
        bits={}
        for j in range(M): bits[('x',j)]=z[j]; bits[('y',j)]=z[j]
        v=F(1)
        for u in nodes: v*=node_val(u,bits)
        truth+=v
    if r>=M:
        return ('trivial',M,r,truth)
    J=(M*R+r*Q)//Q+1
    c=[(-1)**(r-j)*comb(M-j-1,r-j) for j in range(r+1)]
    zero=(0,)*Q
    def mono(E):
        return tuple(1 if i in E else 0 for i in range(Q))
    total=F(0)
    for t in range(Q):
        groups=sorted({u[t] for u in nodes})
        for sz in range(0,min(J,M+1)):
            for S in combinations(range(M),sz):
                Sset=set(S)
                # the partition of rows and columns
                rowsB={}; colsB={}
                for i in range(M):
                    g=(head[i][t] if i in Sset else tail[i][t])
                    rowsB.setdefault((key(wires[i]),g),[]).append(i)
                for j in range(M):
                    g=head[j][t]
                    colsB.setdefault((key(wires[j]),g),[]).append(j)
                allb=set(rowsB)|set(colsB)
                if any(len(rowsB.get(b,[]))!=len(colsB.get(b,[])) for b in allb):
                    continue
                order=sorted(allb,key=str)
                rlist=[i for b in order for i in rowsB.get(b,[])]
                clist=[j for b in order for j in colsB.get(b,[])]
                sgn=perm_sign(rlist)*perm_sign(clist)
                for tz in range(0,min(sz,r)+1):
                    for T in combinations(S,tz):
                        Tset=set(T)
                        for uz in range(sz+1):
                            for U in combinations(S,uz):
                                Uset=set(U)
                                prod_poly={zero:F(sgn*c[tz])}
                                for g in groups:
                                    # the bits of this group
                                    names=[('x',j) for j in range(M) if tail[j][t]==g]+[('y',j) for j in range(M) if head[j][t]==g]
                                    grp={}
                                    for vals in product((0,1),repeat=len(names)):
                                        bits=dict(zip(names,vals))
                                        v=F(1)
                                        for u in nodes:
                                            if u[t]==g: v*=node_val(u,bits)
                                        for i in range(M):
                                            if tail[i][t]==g:
                                                x=bits[('x',i)]
                                                v*=(1-2*x)
                                                if i in Sset and i not in Uset: v*=-x
                                        if v==0: continue
                                        p={zero:v}
                                        for b in order:
                                            if b[1]!=g: continue
                                            rs=rowsB.get(b,[]); cs=colsB.get(b,[])
                                            mat=[]
                                            for i in rs:
                                                row=[]
                                                for j in cs:
                                                    yv=bits[('y',j)]
                                                    e={}
                                                    if i in Sset:
                                                        if i in Tset:
                                                            if i==j: e={tuple(1 for _ in range(Q)):F(1)}
                                                        else:
                                                            for E in rd[i][j]:
                                                                if t in E: e=padd(e,{mono(E):kap[len(E)]})
                                                        fac=F(1-yv) if i in Uset else F(1)
                                                    else:
                                                        if i in Tset: e={}
                                                        else:
                                                            for E in rd[i][j]:
                                                                if t not in E: e=padd(e,{mono(E):kap[len(E)]})
                                                        fac=F(1-yv-bits[('x',i)])
                                                    e={kk:vv*fac for kk,vv in e.items() if vv*fac!=0}
                                                    row.append(e)
                                                mat.append(row)
                                            p=pmul(p,pdet(mat,Q))
                                            if not p: break
                                        grp=padd(grp,p)
                                    prod_poly=pmul(prod_poly,grp)
                                    if not prod_poly: break
                                for ex,v in prod_poly.items():
                                    assert sum(ex)<Q*J
                                    # the least digit below J must be t
                                    if ex[t]<J and all(ex[i]>=J for i in range(t)):
                                        total+=v
    assert total==truth,(total,truth)
    return ('agrees',M,r,truth)
rng=random.Random(4)
def rand_tables(wires):
    tail=[c[0] for c in wires]; head=[c[1] for c in wires]
    t={}
    for u in sorted(set(tail)|set(head)):
        n=sum(1 for x in tail if x==u)+sum(1 for x in head if x==u)
        t[u]={bits:rng.randint(-2,3) for bits in product((0,1),repeat=n)}
    return t
# one square fully used: four wires in one cube of Q=2, L=2
sq=[((0,0),(1,1),0),((1,1),(0,0),0),((0,1),(1,0),0),((1,0),(0,1),0)]
for _ in range(6):
    print('full square',run(2,1,2,sq,rand_tables(sq)),flush=True)
# two squares: six wires
two=sq+[((0,0),(1,1),1),((0,1),(1,0),1)]
for _ in range(1):
    print('two squares, six wires',run(2,1,2,two,rand_tables(two)),flush=True)
# three digits, part of a cube: rank may leave room
cube3=[]
for a in product((0,1),repeat=3):
    cube3.append((tuple(a),tuple(1-x for x in a),0))
sub=cube3[:6]
print('Q=3 six wires',run(3,2,2,sub,rand_tables(sub)),flush=True)
