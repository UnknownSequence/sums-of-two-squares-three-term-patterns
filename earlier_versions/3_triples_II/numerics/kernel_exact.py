"""Exact value of the second kernel in Proposition 6.5 (Lemma 6.4, Remark 8.1).

For the data (E, H_d, d) of Section 9 and kappa in {1,3}, computes <alpha|K_q k|alpha> for k = 1{u_1 <= 1} and
alpha = alpha_{Q^kappa}, via the unfolding in Step 2 of the proof of Lemma 6.4:
    <alpha|K_q k|alpha> = (1/2) sum_{z1 in Lambda_N} sum_{tau1 in T_q: tau1<>z1 in Q^kappa}
                                #{w in Q_N: tau1<>w in Q^kappa, u(w, z1) <= 1},
where T_q is realised as P^1(Z/4E) x P^1(F_d).  Also prints the diagonal contribution <1>_alpha and the
largest number of cosets tau with tau<>z in Q^kappa (bounded by 12E in Lemma 6.4).
Written by an independent referee from the text of the manuscript.  Run: python3 kernel_exact.py"""
# Exact <alpha|K_q k|alpha> for k = 1{u_1<=1}, alpha = alpha_{Q^kappa}, via the unfolding of Lemma 6.4 Step 2:
#   = (1/2) sum_{z1 in Lambda} sum_{tau1: tau1<>z1 in Q} #{w in Q_N: tau1<>w in Q, u(w,z1)<=1}
import math, numpy as np
from math import gcd
def egcd(a,b):
    if b==0: return (a,1,0)
    g,x,y=egcd(b,a%b); return (g,y,x-(a//b)*y)
def reduced(N):
    out=[]
    for c in range(1,math.isqrt(4*N//3)+2):
        for b in range(-(c//2),c//2+1):
            if (b*b+N)%c==0:
                a=(b*b+N)//c
                if a>=c:
                    if (2*abs(b)==c or a==c) and b<0: continue
                    out.append((a,b,c))
    return out
def P1(q2pow,p):
    # reps of P^1(Z/2^r) x P^1(F_p), combined by CRT into P^1(Z/q)
    m=q2pow
    A=[(c,1) for c in range(m)]+[(1,2*y) for y in range(m//2)]
    Bp=[(c,1) for c in range(p)]+[(1,0)]
    q=m*p; out=[]
    inv_m=pow(m,-1,p); inv_p=pow(p,-1,m)
    for (c1,d1) in A:
        for (c2,d2) in Bp:
            c=(c1*p*inv_p+c2*m*inv_m)%q; d=(d1*p*inv_p+d2*m*inv_m)%q
            dd=d
            while gcd(c,dd)!=1: dd+=q
            g,x,y=egcd(dd,c); a0,b0=x,-y
            assert a0*dd-b0*c==1
            out.append((a0,b0,c,dd))
    return out
def act_arr(t,A,B,C):
    a0,b0,c0,d0=t
    B2=a0*c0*A+(a0*d0+b0*c0)*B+b0*d0*C
    C2=c0*c0*A+2*c0*d0*B+d0*d0*C
    return B2,C2
def near(N,z):
    a1,b1,c1=z; res=[]
    lo=int(c1*(3-2*math.sqrt(2)))-1; hi=int(c1*(3+2*math.sqrt(2)))+1
    for c in range(max(1,lo),hi+1):
        S=4*N*c*c1-N*(c-c1)**2
        if S<0: continue
        W=math.isqrt(S)
        bmin=-((-(b1*c-W))//c1); bmax=(b1*c+W)//c1
        for b in range(bmin,bmax+1):
            if (b*b+N)%c==0 and (b*c1-b1*c)**2+N*(c-c1)**2<=4*N*c*c1:
                res.append(((b*b+N)//c,b,c))
    return res
def run(E,H,d,kappa):
    N=E*H; q=4*E*d; lam=reduced(N); T=P1(4*E,d)
    assert len(T)==q*3//2*(d+1)//d
    tot=0; one=0; npairs=0; ntau_max=0
    for z in lam:
        W=near(N,z); npairs+=len(W)
        A=np.array([w[0] for w in W],dtype=object); B=np.array([w[1] for w in W],dtype=object); C=np.array([w[2] for w in W],dtype=object)
        ntau=0
        for t in T:
            b1,c1=act_arr(t,z[0],z[1],z[2])
            if b1%E==0 and (c1-kappa*E*d)%(4*E*d)==0:
                ntau+=1
                B2,C2=act_arr(t,A,B,C)
                ok=[(bb%E==0 and (cc-kappa*E*d)%(4*E*d)==0) for bb,cc in zip(B2,C2)]
                tot+=sum(ok)
        one+=ntau; ntau_max=max(ntau_max,ntau)
    K=tot/2; one=one/2
    print(f"E={E} H={H} d={d} kappa={kappa} N={N}: #Lam={len(lam)} pairs(all)={npairs} (/N={npairs/N:.2f}) "
          f"max#tau={ntau_max} (<=12E={12*E}) <1>_alpha={one} <alpha|K k|alpha>={K} (/N={K/N:.4f}, /(N/d)={K*d/N:.3f})")
for (E,H,d) in [(8,1057,89),(8,285,53),(8,3869,181)]:
    for kappa in (1,3):
        run(E,H,d,kappa)
