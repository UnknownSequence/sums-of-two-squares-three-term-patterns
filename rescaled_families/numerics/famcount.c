/* Sharp weighted counts along one rescaled family (Sections 4-6 of the note).
   T(l) = 2^(s-t) (E l^2 + H) / L,  L = p1 p2,  over l in Z (odd = 0) or odd l only (odd = 1), with L | E l^2 + H
   and T(l) <= x.  Prints: number of l, sum of r(T), number of T in S, and the number of l for which
   v_2(E l^2 + H) != t or the odd part of T is not 1 mod 4 (should be 0).  If B, A are given (triples),
   also counts l for which P = T - A or P + B is not a sum of two squares (should be 0).
   Usage: ./famcount E H p1 p2 odd s t x [B A]          Compile: gcc -O2 -o famcount famcount.c -lm */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef long long ll; typedef unsigned long long ull; typedef __int128 i128;
static int *pr; static int np;
static void sieve(ll L){ char *c=calloc(L+1,1); pr=malloc(sizeof(int)*(L/2+10)); np=0;
  for(ll i=2;i<=L;i++){ if(!c[i]){ pr[np++]=(int)i; for(ll j=i*i;j<=L;j+=i) c[j]=1; } } free(c); }
static ll r4(ull N){ ll res=1; while(N%2==0) N/=2;
  for(int i=1;i<np;i++){ ull p=pr[i]; if(p*p>N) break;
    if(N%p==0){ int e=0; while(N%p==0){ N/=p; e++; } if(p%4==3){ if(e&1) return 0; } else res*=(e+1); } }
  if(N>1){ if(N%4==3) return 0; res*=2; } return res; }
int main(int argc,char**argv){
  if(argc<9){ fprintf(stderr,"usage\n"); return 1; }
  ll E=atoll(argv[1]), H=atoll(argv[2]), p1=atoll(argv[3]), p2=atoll(argv[4]); int odd=atoi(argv[5]);
  int s=atoi(argv[6]), t=atoi(argv[7]); double x=atof(argv[8]);
  int tri = argc>=11; ll B= tri?atoll(argv[9]):0, A= tri?atoll(argv[10]):0;
  ll L=p1*p2; ll *rt=malloc(sizeof(ll)*64); int nr=0;
  for(ll l=0;l<L;l++) if((((i128)E*l*l+H)%L)==0) rt[nr++]=l;
  sieve((ll)sqrt(x)+100);
  double kap = ldexp(1.0, s-t);
  double lmax = sqrt((x*L/kap - (double)H)/E) + 2;
  double sharp=0; ll cnt=0, inS=0, bad2=0, badsplit=0;
  for(int i=0;i<nr;i++){
    for(ll l=rt[i]-(ll)(ceil((rt[i]+lmax)/L))*L; l<=lmax; l+=L){
      if(odd && (l%2==0)) continue;
      i128 num=(i128)E*l*l+H; if(num%L) { bad2++; continue; }
      i128 q=num/L; /* = 2^t T' */
      int v=0; while(q%2==0){ q/=2; v++; }
      if(v!=t || (q%4)!=1) bad2++;
      i128 T=((i128)num/L); if(s>=t) T = T<<(s-t); else T = T>>(t-s);
      if((double)T > x || T<1) continue;
      cnt++; ll rr=4*r4((ull)T); sharp+=rr; if(rr) inS++;
      if(tri){ ll P=(ll)T-A; if(P>=1 && (r4(P)==0 || r4(P+B)==0)) badsplit++; } } }
  printf("%lld %.0f %lld %lld %lld\n", cnt, sharp, inS, bad2, badsplit);
  return 0; }
