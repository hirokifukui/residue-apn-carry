# Independent audit core for P8-07 (written from scratch; does not import ../code).
# Ring GR(4,m) represented by Z4 coefficient vectors; addition = coefficient-wise mod 4
# (no carry lemma used). Field GF(2^m) by log/exp tables.
import numpy as np

POLYS = {3: 0b1011, 5: 0b100101, 7: 0b10000011, 9: 0b1000010001, 11: 0b100000000101}
ALT_POLYS = {3: 0b1101, 5: 0b111101}


class GF:
    def __init__(self, m, poly=None):
        self.m = m; self.q = q = 1 << m
        self.poly = poly if poly is not None else POLYS[m]
        # find primitive element by brute force
        def mulslow(x, y):
            r = 0
            while y:
                if y & 1: r ^= x
                y >>= 1; x <<= 1
                if x & q: x ^= self.poly
            return r
        self.mulslow = mulslow
        for g in range(2, q):
            exp = [1]
            for _ in range(q - 2):
                exp.append(mulslow(exp[-1], g))
            if len(set(exp)) == q - 1:
                break
        exp = np.array(exp + exp, dtype=np.int64)
        log = np.zeros(q, dtype=np.int64)
        for i in range(q - 1):
            log[exp[i]] = i
        self.exp, self.log = exp, log

    def mul(self, x, y):
        x = np.asarray(x); y = np.asarray(y)
        r = self.exp[(self.log[x] + self.log[y]) % (self.q - 1)]
        return np.where((x == 0) | (y == 0), 0, r)

    def inv(self, x):
        x = np.asarray(x)
        return np.where(x == 0, 0, self.exp[(-self.log[x]) % (self.q - 1)])

    def div(self, x, y):
        return self.mul(x, self.inv(y))

    def pw(self, x, e):
        x = np.asarray(x)
        r = self.exp[(self.log[x] * e) % (self.q - 1)]
        return np.where(x == 0, 0 if e > 0 else 1, r)


def popc(x):
    x = np.asarray(x, dtype=np.int64)
    c = np.zeros_like(x)
    while np.any(x):
        c += x & 1; x = x >> 1
    return c


def ip(x, y):
    return popc(np.bitwise_and(x, y)) & 1


# ---- ring: element (a,b) <-> Z4 digits c_i = a_i + 2 b_i ----
def z4add(a1, b1, a2, b2, m):
    """coefficient-wise Z4 addition; returns (a,b)."""
    A = np.zeros(np.broadcast(a1, a2).shape, dtype=np.int64); Bv = np.zeros_like(A)
    for i in range(m):
        c = (((a1 >> i) & 1) + 2 * ((b1 >> i) & 1) + ((a2 >> i) & 1) + 2 * ((b2 >> i) & 1)) % 4
        A |= (c & 1) << i; Bv |= ((c >> 1) & 1) << i
    return A, Bv


def z4neg(a, b, m):
    A = np.zeros_like(np.asarray(a)); Bv = np.zeros_like(A)
    for i in range(m):
        c = (-(((a >> i) & 1) + 2 * ((b >> i) & 1))) % 4
        A |= (c & 1) << i; Bv |= ((c >> 1) & 1) << i
    return A, Bv


def ddt_B(F, p, d, h):
    """delta_B(alpha,beta), alpha,beta indexed as a*q+b. B(a,b)=(h(a)^d(a)b, p(a))."""
    q, m = F.q, F.m
    N = q * q
    xa = np.repeat(np.arange(q), q); xb = np.tile(np.arange(q), q)
    def B(a, b):
        return h[a] ^ F.mul(d[a], b), p[a]
    Bx0, Bx1 = B(xa, xb)
    nB0, nB1 = z4neg(Bx0, Bx1, m)
    D = np.zeros((N, N), dtype=np.int64)
    for alpha in range(N):
        ua, va = alpha // q, alpha % q
        ya, yb = z4add(xa, xb, ua, va, m)
        o0, o1 = B(ya, yb)
        r0, r1 = z4add(o0, o1, nB0, nB1, m)
        D[alpha] = np.bincount(r0 * q + r1, minlength=N)
    return D


def physical_blocks(F, D, rho):
    """Return tau and block norms ||M_G||,||M_E||,||M_Z|| from Pi_perp T'^T Pi_perp in
    physical coordinates (no Walsh)."""
    q = F.q; N = q * q
    T = D / N
    W = np.arange(1, N)
    Tp = T[np.ix_(W, W)]
    low = W // q
    # projector onto perp: within each low-digit fibre restricted to W, subtract mean
    P = np.eye(N - 1)
    for s in range(q):
        idx = np.where(low == s)[0]
        P[np.ix_(idx, idx)] -= 1.0 / len(idx)
    # operator X = P T'^T P ; input = alpha (columns of T'^T)
    X = P @ Tp.T @ P
    tau = np.linalg.norm(X, 2)
    colG = np.where((low != 0) & (low != rho))[0]
    colE = np.where(low == rho)[0]
    colZ = np.where(low == 0)[0]
    nG = np.linalg.norm(X[:, colG], 2)
    nE = np.linalg.norm(X[:, colE], 2)
    nZ = np.linalg.norm(X[:, colZ], 2)
    return tau, nG, nE, nZ


def walsh_g(F, D, rho):
    """g = q^2 That restricted to rows (u in U, eta!=0), cols (s, xi!=0) (all s incl. 0).
    That = q^{-1} H_v T H_t per fibre, T=D/N -> g = q * H D H / N * ... compute integer."""
    q = F.q; N = q * q
    Hm = (-1.0) ** ip(np.arange(q)[:, None], np.arange(q)[None, :])
    D4 = D.reshape(q, q, q, q).astype(float)  # [u,v,s,t]
    That = np.einsum('ev,uvst,xt->uesx', Hm, D4, Hm, optimize=True) / q / N
    g = q * q * That
    U = [u for u in range(q) if u not in (0, rho)]
    G = g[U][:, 1:, :, 1:]  # u in U, eta!=0, all s, xi!=0
    return G, U, g


def M_count(F, p, d, K, rho):
    """M(p,d) = max_{y,nu} #{(u,a): u not in {0,rho}, D_u p(a)=y, d(a)=nu K(u)}"""
    q = F.q
    a = np.arange(q)
    cnt = np.zeros(q * q, dtype=np.int64)
    for u in range(1, q):
        if u == rho: continue
        y = p[a ^ u] ^ p[a]
        nu = F.div(d[a], np.full(q, K[u]))
        np.add.at(cnt, y * q + nu, 1)
    return int(cnt.max())


def linK_from_coeffs(F, coeffs):
    """K(x)=sum_j k_j x^{2^j}"""
    x = np.arange(F.q); r = np.zeros(F.q, dtype=np.int64)
    for j, k in enumerate(coeffs):
        if k: r ^= F.mul(np.full(F.q, k), F.pw(x, 1 << j))
    return r


def is_linear(F, K):
    q = F.q
    return all(K[x ^ y] == K[x] ^ K[y] for x in range(q) for y in range(q)) if q <= 64 else \
        all(K[1 << i ^ 1 << j] == K[1 << i] ^ K[1 << j] for i in range(F.m) for j in range(F.m)) and \
        all(K[x] == np.bitwise_xor.reduce([K[1 << i] for i in range(F.m) if x >> i & 1] or [0]) for x in range(q))


def pd_check(F, p, K, eps):
    q = F.q
    assert len(set(p.tolist())) == q, "p not perm"
    # APN
    for u in range(1, q):
        c = np.bincount(p[np.arange(q) ^ u] ^ p, minlength=q)
        assert c.max() <= 2, "p not APN"
    ker = [x for x in range(q) if K[x] == 0]
    assert len(ker) == 2, "ker K"
    assert eps not in set(K.tolist()), "eps in Im K"
    return ker[1]
