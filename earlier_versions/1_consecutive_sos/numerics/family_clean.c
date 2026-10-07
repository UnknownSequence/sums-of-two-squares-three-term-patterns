#include <stdio.h>
#include <stdlib.h>
typedef long long ll;
int isprime(ll n){ if(n<2) return 0; for(ll q=2;q*q<=n;q++) if(n%q==0) return 0; return 1; }
int main(){
  ll X=100000000LL;
  unsigned char *sos=calloc(X+3,1);
  for(ll a=0;a*a<=X+2;a++) for(ll b=a;a*a+b*b<=X+2;b++) sos[a*a+b*b]=1;
  ll S=0; for(ll n=1;n<=X;n++) if(sos[n-1]&&sos[n]&&sos[n+1]) S++;
  printf("S(1e8) incl. n=1: %lld\n",S);
  ll Dl[]={1000,10000,30000}; 
  for(int t=0;t<3;t++){
    for(int mode=0;mode<2;mode++){ // mode 0: all d=1 mod 8 ; mode 1: primes only
      unsigned char *hit=calloc(X+1,1); ll distinct=0;
      for(ll d=1; d<=Dl[t]; d+=8){
        if(mode==1 && !isprime(d)) continue;
        for(ll w=1;;w++){ ll num=16*w*w+d*d+1; if(num/(2*d)>X) break; if((16*w*w+1)%d) continue;
          ll N=num/(2*d); if(!(sos[N-1]&&sos[N+1])){printf("BAD\n");return 1;}
          if(sos[N]&&!hit[N]){hit[N]=1;distinct++;} } }
      printf("D=%lld %s: distinct middles = %lld\n",Dl[t],mode?"primes d=1(8)":"all d=1(8)",distinct);
      free(hit);
    } }
  return 0; }
