# Check: S_mu(h) = sum_{w mod mu, 16w^2+m=0 (mu)} e(hw/mu) equals the form-side expression
import cmath, random
from math import gcd, isqrt, pi
from gauss_check import reduced_forms, complete
def e(x): return cmath.exp(2j*pi*x)
def S_direct(mu,m,h):
    return sum(e(h*w/mu) for w in range(mu) if (16*w*w+m)%mu==0)
def S_forms(mu,m,h):
    Det=64*m; Mmod=64*mu; tot=0
    for (A,B,C) in reduced_forms(Det):
        Smax=isqrt(A*Mmod//Det)+2
        for S in range(0,Smax+1):
            rem=A*Mmod-Det*S*S
            if rem<0: break
            t=isqrt(rem)
            if t*t!=rem: continue
            for sgn in ([1,-1] if t else [1]):
                num=sgn*t-B*S
                if num%A: continue
                R=num//A
                if S==0 and R<=0: continue
                if gcd(R,S)!=1: continue
                T,V=complete(R,S)
                om=(T*(A*R+B*S)+V*(B*R+C*S))%Mmod
                if om%32: continue          # condition 32 | omega
                if S==0:
                    tot+=e(2*h*om/Mmod)
                else:
                    Rbar=pow(R%S,-1,S) if S>1 else 0
                    tot+=e(2*h*Rbar/S)*e(-2*h*(A*R+B*S)/(Mmod*S))
    return tot/2
random.seed(2)
worst=0
for d in [1,5,9,17,41]:
    m=d*d+1
    for _ in range(30):
        mu=random.choice([k for k in range(1,600) if k%2==1])
        h=random.randint(-7,7)
        a=S_direct(mu,m,h); b=S_forms(mu,m,h)
        worst=max(worst,abs(a-b))
print("max discrepancy:",worst)
