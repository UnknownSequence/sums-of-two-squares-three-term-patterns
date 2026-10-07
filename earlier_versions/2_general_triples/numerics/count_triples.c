/* S_{a,b}(x) = #{1 <= n <= x : n, n+a, n+b are sums of two squares}   (Section 9).
   Usage: ./count_triples a b x      Compile: gcc -O2 -o count_triples count_triples.c -lm */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef long long ll;
int main(int argc, char **argv){
  if(argc<4){ fprintf(stderr,"usage: %s a b x\n",argv[0]); return 1; }
  ll a=atoll(argv[1]), b=atoll(argv[2]), x=(ll)atof(argv[3]), N=x+b;
  unsigned char *s=calloc(N+1,1);
  for(ll u=0;u*u<=N;u++) for(ll v=u;u*u+v*v<=N;v++) s[u*u+v*v]=1;
  ll cnt=0; for(ll n=1;n<=x;n++) if(s[n]&&s[n+a]&&s[n+b]) cnt++;
  printf("S_{%lld,%lld}(%lld) = %lld,   S*(log x)^{3/2}/x = %.4f\n",a,b,x,cnt,cnt*pow(log((double)x),1.5)/x);
  return 0; }
