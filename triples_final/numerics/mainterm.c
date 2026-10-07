/* Weighted counts along the families of triples_final.pdf (Sections 2-4, 7, 14, Table 4).
   Automatic pair (P, P+B), B odd, detected element T = P + A' (Lemma 2.3).
   m_d = (d + 2A' - B)^2 + 4A'(B - A'),  T_d(u) = (u^2 + m_d)/(4d),  u = 0 (mod 2^j),  d | u^2 + B^2.
   Usage: ./mainterm B A d x J d0 j      (sums over u >= 1 only)
   Prints the number of u with T_d(u) <= x, the sharp sum of r(T), the smoothed sum of r(T)F(T/x) with
   F(t) = exp(-1/(20(t-1/2)(1-t))) on (1/2,1), the number of T in S, the number of u for which P or P+B
   is not a sum of two squares (Lemma 2.5 says none) and the number of u with T_d(u) not an integer or
   with odd part of T not 1 mod 4 (Proposition 3.2 says none).
   Compile: gcc -O2 -o mainterm mainterm.c -lm                                                       */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef long long ll; typedef unsigned long long ull; typedef __int128 i128;
static int *pr; static int np;
static void sieve(ll L){
  char *c=calloc(L+1,1); pr=malloc(sizeof(int)*(L/2+10)); np=0;
  for(ll i=2;i<=L;i++){ if(!c[i]){ pr[np++]=(int)i; for(ll j=i*i;j<=L;j+=i) c[j]=1; } }
  free(c); }
static ll r4(ull N){ ll res=1; while(N%2==0) N/=2;
  for(int i=1;i<np;i++){ ull p=pr[i]; if(p*p>N) break;
    if(N%p==0){ int e=0; while(N%p==0){ N/=p; e++; } if(p%4==3){ if(e&1) return 0; } else res*=(e+1); } }
  if(N>1){ if(N%4==3) return 0; res*=2; } return res; }
static double F(double t){ return (t>0.5 && t<1.0) ? exp(-0.05/((t-0.5)*(1.0-t))) : 0.0; }
int main(int argc,char **argv){
  if(argc<8){ fprintf(stderr,"usage: %s B A d x J d0 j\n",argv[0]); return 1; }
  ll B=atoll(argv[1]), A=atoll(argv[2]), d=atoll(argv[3]); double x=atof(argv[4]);
  ll J=atoll(argv[5]), d0=atoll(argv[6]), j=atoll(argv[7]);
  ll modJ=1LL<<J, step=1LL<<j;
  if(((d-d0)%modJ+modJ)%modJ){ fprintf(stderr,"d is not = d0 mod 2^J\n"); return 1; }
  ll c=2*A-B, D0=4*A*(B-A); ll m=(d+c)*(d+c)+D0;
  sieve((ll)sqrt(x+llabs(A)+B)+10);
  double sharp=0, smooth=0; ll cnt=0, inS=0, badsplit=0, bad2=0;
  for(ll u=step; ; u+=step){
    ull Q=(ull)u*u+(ull)m; if((double)Q/(4.0*d) > x) break;
    if(((ull)u*u+(ull)(B*B))%d) continue;
    if(Q%(4*d)){ bad2++; continue; }
    ull T=Q/(4*d); ull Tp=T; while(Tp%2==0) Tp/=2; if(Tp%4!=1) bad2++;
    ll P=(ll)T-A; if(P<1) continue;
    cnt++; ll rT=4*r4(T);
    sharp+=rT; smooth+=rT*F((double)T/x);
    if(rT>0) inS++;
    if(r4(P)==0 || r4(P+B)==0) badsplit++; }
  printf("B=%lld A=%lld d=%lld x=%.0f  count=%lld sharp=%.0f smooth=%.2f inS=%lld badsplit=%lld bad2adic=%lld\n",
         B,A,d,x,cnt,sharp,smooth,inS,badsplit,bad2);
  return 0; }
