// For d prime = 1 mod 8: compute Sum_{w>=1, N_w<=x} r(N_w), count of w, and L_d = sum chi(k) f_d(k)/k (smoothed)
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <stdint.h>
typedef long long ll; typedef unsigned long long ull;
static int *primes; static int np;
void sieve(int L){ char *c=calloc(L+1,1); primes=malloc(sizeof(int)*(L/2+10)); np=0;
  for(int i=2;i<=L;i++){ if(!c[i]){primes[np++]=i; for(ll j=(ll)i*i;j<=L;j+=i) c[j]=1;} } free(c);}
// r(N)/4 = prod over p=1(4): (e+1); zero if p=3(4) with odd exponent
ll r4(ull N){ ll res=1; while(N%2==0) N/=2;
  for(int i=1;i<np;i++){ ull p=primes[i]; if(p*p>N) break; if(N%p==0){ int e=0; while(N%p==0){N/=p;e++;}
      if(p%4==3){ if(e&1) return 0; } else res*=(e+1);} }
  if(N>1){ if(N%4==3) return 0; else res*=2; } return res; }
int legendre(ll a, ll p){ a%=p; if(a<0)a+=p; if(a==0) return 0; ll r=1,b=a,e=(p-1)/2; while(e){ if(e&1) r=r*b%p; b=b*b%p; e>>=1;} return r==1?1:-1; }
int main(int argc,char**argv){
  ll d=atoll(argv[1]); double x=atof(argv[2]); ll Y=atoll(argv[3]);
  sieve(2000000); ll m=d*d+1;
  // sum over w
  ll cnt=0; double sumr=0; ll wmax=(ll)(sqrt(2.0*d*x-m)/4.0)+2;
  for(ll w=1; w<=wmax; w++){ if((16*w*w+1)%d) continue; ull num=16ULL*w*w+m; if(num%(2*d)) {printf("ERR\n");return 1;}
    ull N=num/(2*d); if((double)N > x) continue; if(N%8!=1){printf("ERR mod8 %llu\n",N);return 1;}
    cnt++; sumr+=4.0*r4(N); }
  // L_d: multiplicative f_d via smallest-prime-factor sieve up to Lim
  ll Lim=Y*30; int *spf=calloc(Lim+1,sizeof(int));
  for(ll i=2;i<=Lim;i++) if(!spf[i]) for(ll j=i;j<=Lim;j+=i) if(!spf[j]) spf[j]=i;
  double *g=malloc(sizeof(double)*(Lim+1)); g[1]=1.0; double L=1.0*exp(-1.0/Y);
  for(ll k=2;k<=Lim;k++){ ll p=spf[k]; ll kk=k; int e=0; while(kk%p==0){kk/=p;e++;}
    double val;
    if(p==2) val=0; else {
      int chi = (p%4==1)?1:-1; double chie = (e%2==0)?1:chi;
      double f;
      if(d%p==0) f=1;
      else if(m%p==0){ // rho_m(p^e): count nu mod p^e with nu^2 = -m (small p only expected)
        ll pe=1; for(int t=0;t<e;t++) pe*=p; ll c=0; for(ll nu=0;nu<pe;nu++) if(( (nu*nu)%pe + m%pe)%pe==0) c++; f=c; }
      else f = 1+legendre(-m,p);
      val=chie*f; }
    g[k]=g[kk]*val; L+=g[k]/k*exp(-(double)k/Y); }
  double main_pred=2*sqrt(2.0)*2*L*sqrt(x/d);
  printf("d=%lld x=%.3g  #w=%lld  sum r=%.0f  avg r=%.4f  8L_d=%.4f  pred main=%.0f ratio=%.4f\n",d,x,cnt,sumr,sumr/cnt,8*L,main_pred,sumr/main_pred);
  return 0; }
