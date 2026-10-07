# Verify Gauss correspondence + reciprocity formula used in Lemma W
from math import gcd, isqrt
from fractions import Fraction
import random

def reduced_forms(Det):
    """All reduced positive definite forms [A,2B,C] with AC-B^2=Det, |2B|<=A<=C,
    one per SL2(Z)-class (boundary convention: B>=0 if |2B|==A or A==C)."""
    out=[]
    A=1
    while 3*A*A <= 4*Det:
        for B in range(-(A//2), A//2+1):
            if (B*B+Det) % A: continue
            C=(B*B+Det)//A
            if C < A: continue
            if (abs(2*B)==A or A==C) and B<0: continue
            out.append((A,B,C))
        A+=1
    return out

def egcd(a,b):
    if b==0: return (a,1,0)
    g,x,y=egcd(b,a%b); return (g,y,x-(a//b)*y)

def complete(R,S):
    # find T,V with R*V - S*T = 1
    g,x,y=egcd(R,S)  # R*x+S*y=g=±1
    assert abs(g)==1
    # R*x + S*y = g  -> V=x*g, T=-y*g
    V=x*g; T=-y*g
    assert R*V-S*T==1
    return T,V

def check(Det, Mmod):
    forms=reduced_forms(Det)
    roots_direct=sorted(w for w in range(Mmod) if (w*w+Det)%Mmod==0)
    got={}
    for (A,B,C) in forms:
        # enumerate primitive (R,S) with phi(R,S)=Mmod, S>=0 (and R>0 if S==0)
        Smax=isqrt(A*Mmod//Det)+2
        for S in range(0,Smax+1):
            # A*phi = (A R + B S)^2 + Det S^2
            rem=A*Mmod-Det*S*S
            if rem<0: break
            t=isqrt(rem)
            if t*t!=rem: continue
            for sgn in ([1,-1] if t else [1]):
                num=sgn*t-B*S
                if num % A: continue
                R=num//A
                if S==0 and R<=0: continue
                if gcd(R,S)!=1: continue
                assert A*R*R+2*B*R*S+C*S*S==Mmod
                T,V=complete(R,S)
                om=(T*(A*R+B*S)+V*(B*R+C*S)) % Mmod
                assert (om*om+Det)%Mmod==0, "not a root"
                assert om not in got, "collision"
                got[om]=(A,B,C,R,S)
                if S!=0:
                    Rbar=pow(R% S, -1, S) if S>1 else 0
                    lhs=Fraction(om,Mmod)
                    rhs=Fraction(Rbar,S)-Fraction(A*R+B*S,S*Mmod)
                    assert (lhs-rhs).denominator==1, ("formula fails",A,B,C,R,S,om,lhs,rhs)
    assert sorted(got)==roots_direct, (len(got),len(roots_direct))
    return len(forms), len(roots_direct)

random.seed(1)
tests=0
for d in [1,3,5,9,17,41]:
    m=d*d+1
    for Det in [m, 64*m]:
        for _ in range(25):
            Mmod=random.randint(2,4000)
            if Det==64*m: Mmod=64*random.randint(1,300)
            nf,nr=check(Det,Mmod); tests+=1
print("all correspondence/formula checks passed:",tests)
