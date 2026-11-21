# Exact gap-set derivation for B(alpha) ∩ B(beta), alpha,beta in Q(sqrt D), via a circle rotation.
# Numbers are a + b*sqrt(D) with rational a,b; all comparisons are exact.
from fractions import Fraction as F
from math import isqrt, floor
import sys
class Q:
    D=3
    def __init__(s,a,b=0): s.a=F(a); s.b=F(b)
    def __add__(s,o): o=o if isinstance(o,Q) else Q(o); return Q(s.a+o.a,s.b+o.b)
    def __sub__(s,o): o=o if isinstance(o,Q) else Q(o); return Q(s.a-o.a,s.b-o.b)
    def __neg__(s): return Q(-s.a,-s.b)
    def scale(s,k): return Q(s.a*k,s.b*k)
    def sign(s):
        a,b=s.a,s.b
        if b==0: return (a>0)-(a<0)
        if a==0: return (b>0)-(b<0)
        if a>0 and b>0: return 1
        if a<0 and b<0: return -1
        # opposite signs: compare a^2 with b^2 D
        l,r=a*a,b*b*Q.D
        if l==r: return 0
        big_a = l>r
        return ((a>0)-(a<0)) if big_a else ((b>0)-(b<0))
    def __lt__(s,o): return (s-o).sign()<0
    def __le__(s,o): return (s-o).sign()<=0
    def __eq__(s,o): return (s-o).sign()==0
    def __float__(s): return float(s.a)+float(s.b)*Q.D**0.5
    def __repr__(s): return f"({s.a}{'+' if s.b>=0 else ''}{s.b}√{Q.D})"
def reduce(x,L):               # x mod L in [0,L), exact
    k=floor(float(x)/L)
    for kk in (k-1,k,k+1):
        y=x-Q(kk*L)
        if Q(0)<=y and y<Q(L): return y
    raise ValueError
def norm(ivs):                 # sort + merge list of (lo,hi) in [0,L]
    ivs=sorted([iv for iv in ivs if iv[0]<iv[1]],key=lambda t:float(t[0]))
    out=[]
    for lo,hi in ivs:
        if out and not (out[-1][1]<lo): 
            if out[-1][1]<hi: out[-1]=(out[-1][0],hi)
        else: out.append((lo,hi))
    return out
def inter(A,B):
    out=[]
    for a in A:
        for b in B:
            lo=a[0] if b[0]<=a[0] else b[0]; hi=a[1] if a[1]<=b[1] else b[1]
            if lo<hi: out.append((lo,hi))
    return norm(out)
def diff(A,B):
    cur=A
    for b in B:
        nxt=[]
        for a in cur:
            if b[1]<=a[0] or a[1]<=b[0]: nxt.append(a); continue
            if a[0]<b[0]: nxt.append((a[0],b[0]))
            if b[1]<a[1]: nxt.append((b[1],a[1]))
        cur=nxt
    return norm(cur)
def shift(A,x,L):              # A - x  (mod L)
    out=[]
    for lo,hi in A:
        l=reduce(lo-x,L); h=l+(hi-lo)
        if h<=Q(L): out.append((l,h))
        else: out.append((l,Q(L))); out.append((Q(0),h-Q(L)))
    return norm(out)
def measure(A):
    t=Q(0)
    for lo,hi in A: t=t+(hi-lo)
    return t
def window(L,conds):           # conds: list of (period p, lower endpoint e): u mod p in (e,p)
    W=[(Q(0),Q(L))]
    for p,e in conds:
        W=inter(W,[(e+Q(k*p),Q((k+1)*p)) for k in range(L//p)])
    return W
def run(name,D,L,rho,conds,brute):
    Q.D=D
    W=window(L,conds); mW=measure(W)
    print(f"== {name}: circle R/{L}Z, rotation {rho}, window {W}")
    print(f"   density = |W|/L = {mW.scale(F(1,L))} ≈ {float(mW)/L:.6f}")
    rem=W; res={}; g=0
    while rem:
        g+=1
        hit=inter(rem,shift(W,rho.scale(g),L))
        if hit: res[g]=measure(hit); rem=diff(rem,hit)
        if g>200: print('   did not close'); break
    tot=Q(0)
    for g,m in res.items(): tot=tot+m
    print("   exact gap set:",sorted(res), "| partition complete:", tot==mW)
    for g,m in sorted(res.items()):
        fr=float(m)/float(mW)
        print(f"     gap {g}: measure {m}  freq ≈ {fr:.5f}   brute-force freq {brute.get(g,0):.5f}")
# A352676: alpha=sqrt3, beta=1+sqrt3 ; u = m(3+sqrt3) mod 6
run("A352676  B(√3) ∩ B(1+√3)",3,6,Q(3,1),[(3,Q(3,-1)),(2,Q(3,-1))],{2:.13397,3:.36603,5:.26795,6:.23205})
# A351415: alpha=phi, beta=sqrt5 ; u = m(5+sqrt5) mod 10
#   m in B(phi)   iff {u/2} > (3-√5)/2  iff u mod 2 in (3-√5, 2)
#   m in B(sqrt5) iff {u/5} > 1-√5/5    iff u mod 5 in (5-√5, 5)
run("A351415  B(φ) ∩ B(√5)",5,10,Q(5,1),[(2,Q(3,-1)),(5,Q(5,-1))],{2:.41982,3:.16036,4:.1225,5:.19821,6:.09911})
