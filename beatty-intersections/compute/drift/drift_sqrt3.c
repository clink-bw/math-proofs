// Drift of OEIS A352676: a(n) = n-th integer in B(sqrt 3) ∩ B(1 + sqrt 3),
// d(n) = a(n) - floor(n * (3/2)(1 + sqrt 3)).  Exact 64-bit integer arithmetic throughout.
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <stdint.h>
typedef uint64_t u64; typedef int64_t i64;
static inline u64 isqrt(u64 x){ u64 r=(u64)sqrt((double)x); while(r*r>x) r--; while((r+1)*(r+1)<=x) r++; return r; }
int main(int argc,char**argv){
  u64 M = argc>1 ? strtoull(argv[1],0,10) : 1000000000ULL;
  u64 n=0, zeros=0, lastzero=0; i64 dmax=-1000, dmin=1000;
  u64 hist[41]={0};
  u64 w = isqrt(3);                       // floor(1*sqrt3)
  for(u64 m=1;m<=M;m++){
    u64 w1 = isqrt(3*(m+1)*(m+1));       // floor((m+1) sqrt3)
    int inA = (w1/3) > (w/3);            // m in B(sqrt3)
    int inB = ((w1-(m+1))/2) > ((w-m)/2);// m in B(1+sqrt3)
    w = w1;
    if(inA && inB){
      n++;
      u64 fl = (3*n + isqrt(27*n*n))/2;  // floor(n*(3/2)(1+sqrt3))
      i64 d = (i64)m - (i64)fl;
      if(d>=-20 && d<=20) hist[d+20]++;
      if(d==0){ zeros++; lastzero=n; if(zeros<=40) printf("zero #%llu at n=%llu a=%llu\n",zeros,n,m); }
      if(d>dmax){ dmax=d; printf("new max d=%lld at n=%llu a=%llu\n",d,n,m); }
      if(d<dmin){ dmin=d; printf("new min d=%lld at n=%llu a=%llu\n",d,n,m); }
    }
  }
  printf("M=%llu n=%llu zeros=%llu lastzero_n=%llu dmin=%lld dmax=%lld\n",M,n,zeros,lastzero,dmin,dmax);
  for(int i=0;i<41;i++) if(hist[i]) printf("  d=%d : %llu\n",i-20,hist[i]);
  return 0; }
