"""Exact arithmetic in Z[omega] and its small residue fields."""
from math import isqrt
UNITS = [(1,0),(1,1),(0,1),(-1,0),(-1,-1),(0,-1)]
def add(x,y): return x[0]+y[0],x[1]+y[1]
def mul(x,y):
 a,b=x;c,d=y
 return a*c-b*d,a*d+b*c-b*d
def conjugate(x): return x[0]-x[1],-x[1]
def norm(x): return x[0]*x[0]-x[0]*x[1]+x[1]*x[1]
def trace(x): return 2*x[0]-x[1]
def is_prime(n):
 return n>=2 and all(n%d for d in range(2,isqrt(n)+1))
def split_generators(bound):
 out=[]
 lim=2*isqrt(bound)+3
 for a in range(-lim,lim+1):
  if a%3!=1: continue
  for b in range(-lim,lim+1):
   if b%3: continue
   q=norm((a,b))
   if 3<q<=bound and is_prime(q):out.append((a,b))
 return sorted(out,key=lambda x:(norm(x),x))
class Field:
 def __init__(self,pi):
  self.pi=pi;self.q=norm(pi)
  if pi[1] and is_prime(self.q):
   self.p=self.q;self.degree=1;self.r=(-pi[0]*pow(pi[1],-1,self.p))%self.p
  else:
   self.p=abs(pi[0]);self.degree=2;self.r=None
   assert pi[1]==0 and is_prime(self.p) and self.p%3==2
  self.elements=[(x,0) for x in range(self.p)] if self.degree==1 else [(a,b) for a in range(self.p) for b in range(self.p)]
  self.roots=[self.reduce(x) for x in UNITS]
 def reduce(self,x):
  return ((x[0]+self.r*x[1])%self.p,0) if self.degree==1 else (x[0]%self.p,x[1]%self.p)
 def multiply(self,x,y):return self.reduce(mul(x,y))
 def power(self,x,n):
  y=(1,0);x=self.reduce(x)
  while n:
   if n&1:y=self.multiply(y,x)
   x=self.multiply(x,x);n>>=1
  return y
 def index(self,x):
  x=self.reduce(x)
  if x==(0,0):return None
  return self.roots.index(self.power(x,(self.q-1)//6))
 def jacobi(self,j,k):
  ans=(0,0)
  for x in self.elements:
   y=self.reduce((1-x[0],-x[1]));u=self.index(x);v=self.index(y)
   if u is not None and v is not None:ans=add(ans,UNITS[(j*u+k*v)%6])
  return ans
