"""gd lane (C7) independent finite-calibration library.
Own GF(2^m) arithmetic; no import from gpt_input / c1 / c6.
Encoding: integer, bit i = coefficient of x^i (low m bits = digit 0 first).
Irreducible polynomials (all primitive):
  m=3: x^3+x+1      (0b1011)
  m=4: x^4+x+1      (0b10011)
  m=5: x^5+x^2+1    (0b100101)
"""
import random

MOD = {3: 0b1011, 4: 0b10011, 5: 0b100101}
MODSTR = {3: "x^3+x+1", 4: "x^4+x+1", 5: "x^5+x^2+1"}


class GF:
    def __init__(self, m):
        self.m = m
        self.q = q = 1 << m
        self.mod = MOD[m]
        self.T = [[self._mul0(a, b) for b in range(q)] for a in range(q)]
        # sanity: field axioms on table (commutative, each nonzero row a permutation)
        for a in range(1, q):
            assert sorted(self.T[a]) == list(range(q))
        self.inv = [0] * q
        for a in range(1, q):
            for b in range(1, q):
                if self.T[a][b] == 1:
                    self.inv[a] = b
        self.sq = [self.T[a][a] for a in range(q)]
        self.sqrt = [0] * q
        for a in range(q):
            self.sqrt[self.sq[a]] = a
        self.trt = [self._tr(a) for a in range(q)]

    def _mul0(self, a, b):
        c = 0
        while b:
            if b & 1:
                c ^= a
            b >>= 1
            a <<= 1
            if a & self.q:
                a ^= self.mod
        return c

    def mul(self, a, b):
        return self.T[a][b]

    def pow(self, a, n):
        z = 1
        while n:
            if n & 1:
                z = self.T[z][a]
            a = self.T[a][a]
            n >>= 1
        return z

    def Inv(self, x):  # x^(q-2), Inv(0)=0
        return self.pow(x, self.q - 2)

    def _tr(self, a):
        t = 0
        x = a
        for _ in range(self.m):
            t ^= x
            x = self._mul0(x, x)
        assert t in (0, 1)
        return t

    def tr(self, a):
        return self.trt[a]


def lin_table(q, cols):
    """F2-linear map given by images of basis vectors e_i (cols[i])."""
    t = [0] * q
    for a in range(q):
        z = 0
        i = 0
        x = a
        while x:
            if x & 1:
                z ^= cols[i]
            x >>= 1
            i += 1
        t[a] = z
    return t


def span(vecs):
    S = {0}
    for v in vecs:
        S |= {x ^ v for x in S}
    return S


def is_indep(vecs):
    return len(span(vecs)) == 1 << len(vecs)


def make_d(F, rng, rho):
    """d(a)=eps+K(a): K F2-linear, ker K={0,rho}, Im K = random hyperplane W, eps notin W.
    Built from a random basis {rho,b2..bm} of F and a random basis {w2..wm} of W.
    Returns dict with tables."""
    q, m = F.q, F.m
    while True:
        Wb = [rng.randrange(1, q) for _ in range(m - 1)]
        if is_indep(Wb):
            break
    W = span(Wb)
    while True:
        bb = [rng.randrange(1, q) for _ in range(m - 1)]
        if is_indep([rho] + bb):
            break
    basis = [rho] + bb
    imgs = [0] + Wb
    K = [None] * q
    for mask in range(q):
        e = 0
        im = 0
        for i in range(m):
            if mask >> i & 1:
                e ^= basis[i]
                im ^= imgs[i]
        K[e] = im
    eps = rng.choice([z for z in range(q) if z not in W])
    d = [eps ^ K[a] for a in range(q)]
    return {"rho": rho, "eps": eps, "W_basis": Wb, "K": K, "d": d}


def check_K(F, K, rho):
    q = F.q
    # linearity
    lin = all(K[a ^ b] == K[a] ^ K[b] for a in range(q) for b in range(q))
    ker = sorted(a for a in range(q) if K[a] == 0)
    return lin, ker


def dset(m, F):
    """Deterministic list of d's per m (seeded). Different rho / hyperplane / K."""
    rng = random.Random(7020 + m)
    q = F.q
    if m == 3:
        rhos = [1, 2, 4, 3, 6, 7]
    elif m == 4:
        rhos = [1, 8, 3, 5, 14, 15]
    else:
        rhos = [2, 16, 3, 13, 31, 22]
    out = []
    for rho in rhos:
        D = make_d(F, rng, rho)
        D["name"] = "m%d_rho%d_r" % (m, rho)
        out.append(D)
    if m == 5:
        # C6 special case d0(a)=(a^2+a+1)^2, rho=1
        d = [F.sq[F.sq[a] ^ a ^ 1] for a in range(q)]
        K = [d[a] ^ d[0] for a in range(q)]
        out.append({"rho": 1, "eps": d[0], "W_basis": None, "K": K, "d": d, "name": "m5_d0"})
    return out


def derive(F, D):
    """eta (unique by scan), beta, r, H, representatives."""
    q = F.q
    d = D["d"]
    Imd = sorted(set(d))
    etas = [e for e in range(1, q) if all(F.tr(F.mul(e, z)) == 1 for z in Imd)]
    eta = etas[0] if len(etas) == 1 else None
    beta = F.inv[eta] if eta else None
    r = [F.pow(F.mul(eta, d[a]), q // 2) for a in range(q)] if eta else None
    return {"Imd": Imd, "etas": etas, "eta": eta, "beta": beta, "r": r}


def AB(F, D, Dv, h):
    """A_d(h), B_d(h), ell_d(h) computed over r in H via one representative per pair."""
    q = F.q
    rho = D["rho"]
    r = Dv["r"]
    A = 0
    B = 0
    seen = set()
    for a in range(q):
        if r[a] in seen:
            continue
        seen.add(r[a])
        Dh = h[a] ^ h[a ^ rho]
        ri = F.inv[r[a]]
        A ^= F.mul(F.pow(ri, 3), Dh)
        B ^= F.mul(F.pow(ri, 5), F.sq[Dh])
    assert len(seen) == q // 2
    return A, B, A ^ F.sqrt[B]


# polynomials over F: list of coeffs, index = degree
def pmul(F, P, Q):
    R = [0] * (len(P) + len(Q) - 1)
    for i, x in enumerate(P):
        if x:
            row = F.T[x]
            for j, y in enumerate(Q):
                R[i + j] ^= row[y]
    return R


def padd(P, Q):
    n = max(len(P), len(Q))
    return [(P[i] if i < len(P) else 0) ^ (Q[i] if i < len(Q) else 0) for i in range(n)]


def peval(F, P, x):
    y = 0
    for c in reversed(P):
        y = F.T[y][x] ^ c
    return y


def pdeg(P):
    ds = [i for i, c in enumerate(P) if c]
    return max(ds) if ds else -1


def Phi_poly(F, d, h, Lt, mu):
    """Phi(C)=sum_a (u_a + d_a C)^s by explicit polynomial multiplication (no binomial formula)."""
    q = F.q
    s = q // 2 - 1
    tot = [0] * (s + 1)
    for a in range(q):
        u = h[a] ^ F.mul(d[a], Lt[a]) ^ mu
        base = [u, d[a]]
        P = [1]
        for _ in range(s):
            P = pmul(F, P, base)
        tot = padd(tot, P)
    return tot


def Psi(F, d, h, Lt, mu, c):
    q = F.q
    z = 0
    for a in range(q):
        z ^= F.Inv(h[a] ^ F.mul(d[a], c ^ Lt[a]) ^ mu)
    return z


def Psi_all(F, d, h, Lt, mu):
    """Psi for all c, using inverse table."""
    q = F.q
    iv = F.inv
    T = F.T
    out = []
    base = [h[a] ^ T[d[a]][Lt[a]] ^ mu for a in range(q)]
    for c in range(q):
        z = 0
        for a in range(q):
            z ^= iv[base[a] ^ T[d[a]][c]]
        out.append(z)
    return out


def rand_lin(F, rng):
    return lin_table(F.q, [rng.randrange(F.q) for _ in range(F.m)])


def mobius_deg(bits, m):
    a = list(bits)
    for i in range(m):
        for j in range(1 << m):
            if j >> i & 1:
                a[j] ^= a[j ^ (1 << i)]
    return max((bin(j).count("1") for j, c in enumerate(a) if c), default=-1)


def coord_degs(F, g):
    return [mobius_deg([(g[a] >> j) & 1 for a in range(F.q)], F.m) for j in range(F.m)]


def parity(x):
    return bin(x).count("1") & 1
