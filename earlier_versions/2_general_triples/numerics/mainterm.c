/* Weighted counts along T_d(u) = (u^2+m_d)/(2 kappa d) for the pattern {0,a,b} (Section 9).
   Usage:  ./mainterm a b d x J d0 u0
   Sums over u >= 1 with u = u0 (mod 2^J) and d | u^2+g^2 (then T_d(u) is an integer by Prop. 3.4):
     sharp  = sum_{T <= x} r(T)
     smooth = sum r(T) F(T/x),  F(t) = exp(-0.05/((t-1/2)(1-t))) on (1/2,1), 0 elsewhere.
   Also counts the n = T-a >= 1 with T in S (these n are counted by S_{a,b}(x)), the n for which
   n or n+b is NOT a sum of two squares (Lemma 2.2 says there are none), and the u for which
   T_d(u) is not an integer (Proposition 3.4 says there are none).
   Compile: gcc -O2 -o mainterm mainterm.c -lm                                                  */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef long long ll; typedef unsigned long long ull;
static int *pr; static int np;
static void sieve(ll L){
  char *c=calloc(L+1,1); pr=malloc(sizeof(int)*(L/2+10)); np=0;
  for(ll i=2;i<=L;i++){ if(!c[i]){ pr[np++]=(int)i; for(ll j=i*i;j<=L;j+=i) c[j]=1; } }
  free(c); }
/* r(N)/4 = sum_{k|N} chi(k); requires N <= (largest sieved prime)^2 */
static ll r4(ull N){ ll res=1; while(N%2==0) N/=2;
  for(int i=1;i<np;i++){ ull p=pr[i]; if(p*p>N) break;
    if(N%p==0){ int e=0; while(N%p==0){ N/=p; e++; } if(p%4==3){ if(e&1) return 0; } else res*=(e+1); } }
  if(N>1){ if(N%4==3) return 0; res*=2; } return res; }
static double F(double t){ return (t>0.5 && t<1.0) ? exp(-0.05/((t-0.5)*(1.0-t))) : 0.0; }
int main(int argc,char **argv){
  if(argc<8){ fprintf(stderr,"usage: %s a b d x J d0 u0\n",argv[0]); return 1; }
  ll a=atoll(argv[1]), b=atoll(argv[2]), d=atoll(argv[3]); double x=atof(argv[4]);
  ll J=atoll(argv[5]), d0=atoll(argv[6]), u0=atoll(argv[7]);
  ll kappa=(b%2==0)?1:2, g=kappa*b/2, c=kappa*a-g, mod=1LL<<J;
  if((d-d0)%mod){ fprintf(stderr,"d is not = d0 mod 2^J\n"); return 1; }
  ll m=(d+c)*(d+c)+kappa*kappa*a*(b-a);
  sieve((ll)sqrt(x+b)+10);
  double sharp=0, smooth=0; ll cnt=0, inS=0, badsplit=0, nonint=0;
  for(ll u=((u0%mod)+mod)%mod; ; u+=mod){
    if(u<1) continue;
    ull Q=(ull)u*u+m; if((double)Q/(2.0*kappa*d) > x) break;
    if(((ull)u*u+(ull)(g*g))%d) continue;
    if(Q%(2*kappa*d)){ nonint++; continue; }
    ull T=Q/(2*kappa*d); ll n=(ll)T-a; if(n<1) continue;
    cnt++; ll rT=4*r4(T);
    sharp+=rT; smooth+=rT*F((double)T/x);
    if(rT>0) inS++;
    if(r4(n)==0 || r4(n+b)==0) badsplit++; }
  printf("%lld %lld %lld %.0f %lld %lld %lld  count=%lld sharp=%.0f smooth=%.2f inS=%lld badsplit=%lld nonint=%lld\n",
         a,b,d,x,J,d0,u0,cnt,sharp,smooth,inS,badsplit,nonint);
  return 0; }
