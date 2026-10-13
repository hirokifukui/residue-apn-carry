#!/usr/bin/env python3
"""C6 P6-02..06 independent finite calibration (Claude main, 2026-10-11). Own GF(2^m) arithmetic; imports nothing from C1-C5 or the GPT checks."""
import sys, json, random
POLY={3:0b1011,5:0b100101,7:0b10000011,9:0b1000010001}
def mk(m):
    P=POLY[m]; q=1<<m
    def mul(a,b):
        r=0
        while b:
            if b&1: r^=a
            b>>=1; a<<=1
            if a&q: a^=P
        return r
    def pw(a,e):
        r=1
        while e:
            if e&1: r=mul(r,a)
            a=mul(a,a); e>>=1
        return r
    def tr(x):
        t=0;y=x
        for _ in range(m): t^=y; y=mul(y,y)
        return t
    return q,mul,pw,tr
out={}
ok=True
def chk(c,msg):
    global ok
    if not c: ok=False; print('FAIL',msg)
for m in (3,5,7,9):
    q,mul,pw,tr=mk(m); inv=lambda x: pw(x,q-2)
    assert all(tr(x) in (0,1) for x in range(q))
    H=[r for r in range(q) if tr(r)==1]
    # P6-02: power sums of r^{-j}
    ps={}
    for j in (1,2,3,4,5):
        s=0
        for r in H: s^=pw(inv(r),j)
        ps[j]=s
    chk((ps[1],ps[2],ps[3],ps[5])==(1,1,0,0),('ps',m,ps))
    # r(F)=H for odd m, 2-to-1
    R=[mul(a,a)^a^1 for a in range(q)]
    chk(sorted(R)==sorted(H+H),('image',m))
    # elementary symmetric of 1/r via product of (1+X/r) coefficients up to X^6
    e=[1]+[0]*6
    for r in H:
        u=inv(r); e=[e[k]^(mul(e[k-1],u) if k else 0) for k in range(7)]
    want=[1,1,1,0,1,0,0] if m>3 else [1,1,1,0,1,0,0]
    chk(e[:6]==want[:6],('esym',m,e))
    out['m%d_powersums'%m]=ps; out['m%d_esym'%m]=e
    if m==9: continue
    s=q//2-1
    d=[mul(R[a],R[a]) for a in range(q)]
    rng=random.Random(20261011+m)
    def phi_coeffs(z):
        # full coefficients of Phi(C)=sum_a (z_a+d_a C)^s, binom(s,k)=1 mod 2 for all k<=s
        co=[0]*(s+1)
        for a in range(q):
            dp=[1]
            for k in range(s): dp.append(mul(dp[-1],d[a]))
            zp=[1]
            for k in range(s): zp.append(mul(zp[-1],z[a]))
            for k in range(s+1): co[k]^=mul(zp[s-k],dp[k])
        return co
    def ev(co,c):
        v=0
        for k in range(len(co)-1,-1,-1): v=mul(v,c)^co[k]
        return v
    def AB(h):
        A=B=0
        for a in range(q):
            r=R[a]
            if a<(a^1):
                D=h[a]^h[a^1]
                A^=mul(pw(inv(r),3),D); B^=mul(pw(inv(r),5),mul(D,D))
        return A,B
    sq=lambda x: pw(x,q//2)
    def randlin():
        img=[rng.randrange(q) for _ in range(m)]
        return [ (lambda a: __import__('functools').reduce(lambda u,i: u^(img[i] if a>>i&1 else 0), range(m),0))(a) for a in range(q)]
    cases=0; full=0; repair=0
    h3=[pw(a,3) for a in range(q)]
    for trial in range(40 if m<7 else 8):
        kind=trial%4
        if kind==0: h=h3
        elif kind==1: h=[rng.randrange(q) for _ in range(q)]
        elif kind==2:
            zeta=rng.randrange(q); H0=[rng.randrange(q) for _ in range(q)]
            h=[h3[a]^mul(zeta,a)^H0[R[a]^1] for a in range(q)]  # a^2+a = r+1
        else:
            h=[rng.randrange(q) for _ in range(q)]; A0,B0=AB(h); l0=A0^sq(B0)
            h=[h[a]^mul(l0,h3[a]) for a in range(q)]  # forces ell=0
        A,B=AB(h); ell=A^sq(B)
        if kind in (0,2): chk(ell==1,('ell1',m,kind,ell))
        if kind==3: chk(ell==0,('ell0',m))
        chk(mul(ell,ell)==(mul(A,A)^B),('ell2',m))
        L=randlin(); mu=rng.randrange(q); tau=L[1]
        z=[h[a]^mul(d[a],L[a])^mu for a in range(q)]
        co=phi_coeffs(z); cases+=1
        chk(co[s]==0 and co[s-1]==A^tau and co[s-2]==(B^mul(tau,tau)),('coef',m,trial))
        if m<=5:
            full+=1
            for c in range(q):
                psi=0
                for a in range(q): psi^=inv(h[a]^mul(d[a],c^L[a])^mu)
                chk(psi==mul(ev(co,c),ev(co,c)),('psi=phi2',m,c))
            nz=sum(1 for c in range(q) if ev(co,c))
            if ell: chk(nz>=q//2+2,('nz',m,nz))
        # repair: ell(h+lam a^3)=ell+lam for all lam
        if m<=5 and kind in (1,3):
            for lam in range(q):
                A2,B2=AB([h[a]^mul(lam,h3[a]) for a in range(q)]); chk((A2^sq(B2))==ell^lam,('rep',m)); repair+=1
    out['m%d'%m]={'coef_cases':cases,'psi_full_cases':full,'repair_checks':repair}
# P6-06: h=a^21 on F32, F2[X,C] expansion
from collections import Counter
f=Counter({(1,0):1,(12,1):1,(6,1):1,(0,1):1})  # X + C(X^12+X^6+1)
def mulp(P,Qp):
    R=Counter()
    for (a,b),u in P.items():
        for (c,dd),v in Qp.items(): R[(a+c,b+dd)]^=1
    return Counter({k:1 for k,v in R.items() if v&1})
def frob(P,k): return Counter({(a*k,b*k):1 for (a,b) in P})
prod=Counter({(0,0):1})
for k in (2,4,8,16): prod=mulp(prod,frob(f,k))
mons=sorted(prod)
bad=[(a,b) for (a,b) in mons if a>0 and a%31==0]
zero=[(a,b) for (a,b) in mons if a==0]
chk(len(mons)==128,('nmon',len(mons))); chk(not bad,('bad',bad))
# direct: Psi(c)=sum_a (a^21 + d(a) c)^30 on F32 for all c
q,mul,pw,tr=mk(5)
for c in range(32):
    s_=0
    for a in range(32): s_^=pw(pw(a,21)^mul(pw(a,4)^pw(a,2)^1,c),30)
    chk(s_==0,('a21',c))
out['P606']={'monomials':len(mons),'pos_mult31':len(bad),'xdeg0':len(zero),'xdeg_max':max(a for a,b in mons)}
out['ALL_OK']=ok
json.dump(out,open(sys.argv[1],'w'),indent=1,default=str); print(json.dumps(out,default=str)); sys.exit(0 if ok else 1)
