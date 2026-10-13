# C3 (pointwise ring (Z/4)^m), C4 (companion matrix over Z/4), C5 (GR(4,m) mixer identification)
import itertools, sys
import numpy as np

fails = 0
def chk(cond, msg):
    global fails
    if not cond:
        fails += 1; print("FAIL:", msg)

# ---------------- C3 ----------------
print("=== C3 ===")
U = [1, 3]
dets = set()
for m11, m12, m21, m22 in itertools.product(U, repeat=4):
    d = (m11 * m22 - m12 * m21) % 4
    dets.add(d)
    print(f"  ({m11},{m12};{m21},{m22}) det={d} unit={d % 2 == 1}")
    chk(d % 2 == 0, "m=1 unit det found")
print("  m=1: det values over all 16 unit patterns:", sorted(dets))
cnt = 0
R2units = list(itertools.product(U, U))
for q in itertools.product(R2units, repeat=4):
    det = tuple((q[0][i] * q[3][i] - q[1][i] * q[2][i]) % 4 for i in range(2))
    cnt += 1
    chk(not all(x % 2 == 1 for x in det), "m=2 unit det found")
print(f"  m=2: checked {cnt} all-unit quadruples in (Z/4)^2; unit determinant found: {fails > 0}")

# ---------------- helpers ----------------
def f2_mulmod_irred(m):
    # list binary irreducible polys of degree m as int bitmasks (bit i = coeff t^i)
    def pmod(a, b):
        db = b.bit_length() - 1
        while a and a.bit_length() - 1 >= db:
            a ^= b << (a.bit_length() - 1 - db)
        return a
    out = []
    for p in range(1 << m, 1 << (m + 1)):
        ok = True
        for d in range(1, m // 2 + 1):
            for q in range(1 << d, 1 << (d + 1)):
                if pmod(p, q) == 0: ok = False; break
            if not ok: break
        if ok: out.append(p)
    return out

def companion(p, m):
    c = [(p >> i) & 1 for i in range(m)]   # lifted 0/1 coefficients of fhat, monic
    T = np.zeros((m, m), dtype=np.int64)
    for i in range(m - 1): T[i + 1, i] = 1
    for i in range(m): T[i, m - 1] = (-c[i]) % 4
    return T, c

def inv_mod4(A):
    m = A.shape[0]
    M = np.concatenate([A % 4, np.eye(m, dtype=np.int64)], axis=1)
    for col in range(m):
        piv = next((r for r in range(col, m) if M[r, col] % 2 == 1), None)
        if piv is None: return None
        M[[col, piv]] = M[[piv, col]]
        M[col] = (M[col] * (M[col, col] % 4)) % 4    # units 1,3 are self-inverse mod 4
        for r in range(m):
            if r != col and M[r, col] % 4:
                M[r] = (M[r] - M[r, col] * M[col]) % 4
    return M[:, m:] % 4

def det_mod(A, mod):
    # Bareiss-free integer det via fractions-free expansion (small m) : use exact integer det
    from fractions import Fraction
    m = A.shape[0]; B = [[Fraction(int(x)) for x in row] for row in A]; d = Fraction(1)
    for i in range(m):
        p = next((r for r in range(i, m) if B[r][i] != 0), None)
        if p is None: return 0
        if p != i: B[i], B[p] = B[p], B[i]; d = -d
        d *= B[i][i]
        for r in range(i + 1, m):
            f = B[r][i] / B[i][i]
            B[r] = [x - f * y for x, y in zip(B[r], B[i])]
    return int(d) % mod

def tmul(vec, c, m):
    # multiply polynomial (coeff vector over Z/4) by t modulo fhat = t^m + sum c_i t^i
    top = vec[m - 1]
    out = [0] + list(vec[:m - 1])
    return tuple((out[i] - top * c[i]) % 4 for i in range(m))

# ---------------- C4 ----------------
print("=== C4 ===")
I = lambda m: np.eye(m, dtype=np.int64)
m = 5; p = 0b100101  # x^5 + x^2 + 1
T, c = companion(p, m)
Ti = inv_mod4(T); Ni = inv_mod4((T - I(m)) % 4)
np.set_printoptions(linewidth=200)
print("f = x^5+x^2+1, Theta =\n", T % 4)
print("Theta^{-1} =\n", Ti)
print("(Theta-I)^{-1} =\n", Ni)
chk(((T @ Ti) % 4 == I(m)).all() and ((Ti @ T) % 4 == I(m)).all(), "Theta inverse")
chk(((((T - I(m)) % 4) @ Ni) % 4 == I(m)).all(), "Theta-I inverse")
print("  identities Theta*Theta^-1=I, (Theta-I)*(Theta-I)^-1=I mod 4:", fails == 0)

counts = {}
nmat_ok = 0; nexh = 0
for m in range(2, 9):
    irr = f2_mulmod_irred(m); counts[m] = len(irr)
    for p in irr:
        T, c = companion(p, m)
        chk(c[0] == 1, "f(0)=1"); chk(sum(c) % 2 == 0, "f(1)=1 means 1+sum c_i odd -> sum c_i even")
        dT = det_mod(T, 4); dN = det_mod((T - I(m)) % 4, 4)
        Ti = inv_mod4(T); Ni = inv_mod4((T - I(m)) % 4)
        ok = Ti is not None and Ni is not None and dT % 2 == 1 and dN % 2 == 1
        ok &= ((T @ Ti) % 4 == I(m)).all() and ((((T - I(m)) % 4) @ Ni) % 4 == I(m)).all()
        # det formulas: det(Theta) = (-1)^m fhat(0)?  char poly det(xI-Theta)=fhat(x)
        fh1 = (1 + sum(c)) % 4
        ok &= dT == ((-1) ** m * c[0]) % 4 and dN == ((-1) ** m * fh1) % 4
        # block mixer M = [[I,I],[I,Theta]] and its claimed inverse
        Z = I(m)
        Mb = np.block([[Z, Z], [Z, T]]) % 4
        Minv = np.block([[(Z + Ni) % 4, (-Ni) % 4], [(-Ni) % 4, Ni]]) % 4
        ok &= ((Mb @ Minv) % 4 == I(2 * m)).all() and ((Minv @ Mb) % 4 == I(2 * m)).all()
        # Cayley-Hamilton over Z/4: fhat(Theta) = 0
        P = np.zeros((m, m), dtype=np.int64); Pw = I(m)
        for i in range(m): P = (P + c[i] * Pw) % 4; Pw = (Pw @ T) % 4
        ok &= ((P + Pw) % 4 == 0).all()
        if ok: nmat_ok += 1
        else: chk(False, f"matrix identities m={m} p={bin(p)}")
        if m <= 6:
            nexh += 1
            for v in itertools.product(range(4), repeat=m):
                a = tmul(v, c, m)
                b = tuple(int(x) for x in (T @ np.array(v)) % 4)
                if a != b: chk(False, f"tmul vs Theta m={m} p={bin(p)} v={v}"); break
                # two-digit coordinates: c_i = a_i + 2 b_i  (bijection {0,1}^2 <-> Z/4); same map by construction
                dig = lambda w: (tuple(x % 2 for x in w), tuple(x // 2 for x in w))
                und = lambda ab: tuple(x + 2 * y for x, y in zip(*ab))
                chk(und(dig(a)) == a and dig(und(dig(v))) == dig(v), "digit bijection")
print("  irreducible counts deg2..8:", counts, " (expected 1,2,3,6,9,18,30)")
chk([counts[k] for k in range(2, 9)] == [1, 2, 3, 6, 9, 18, 30], "irreducible counts")
print(f"  all matrix identities (inverses, det formulas, block-M inverse, Cayley-Hamilton) OK for {nmat_ok}/{sum(counts.values())} polys")
print(f"  t-multiplication == Theta action on all 4^m vectors for {nexh} polys with m<=6")

# is the (a,b)-digit map F2-linear?  (side note: it is not, because of carries)
m = 3; p = 0b1011; T, c = companion(p, m)
def onbits(bits):
    v = tuple(bits[i] + 2 * bits[m + i] for i in range(m))
    w = tmul(v, c, m)
    return tuple([x % 2 for x in w] + [x // 2 for x in w])
nonlin = 0
for x in itertools.product(range(2), repeat=2 * m):
    for y in itertools.product(range(2), repeat=2 * m):
        s = tuple((a + b) % 2 for a, b in zip(x, y))
        if onbits(s) != tuple((a + b) % 2 for a, b in zip(onbits(x), onbits(y))): nonlin += 1
print(f"  side note: t-mult in digit coords (a,b) as map F2^{2*m}->F2^{2*m} fails F2-additivity on {nonlin}/{4**(2*m)} pairs (m=3)")

# ---------------- C5 ----------------
print("=== C5 ===")
for m, p in [(3, 0b1011), (3, 0b1101), (5, 0b100101), (5, 0b111101)]:
    T, c = companion(p, m)
    allv = np.array(list(itertools.product(range(4), repeat=m)), dtype=np.int64)   # 4^m x m
    # ring side: t*y by polynomial shift/reduction (independent of matrix)
    ty = np.array([tmul(tuple(v), c, m) for v in allv], dtype=np.int64)
    Mb = np.block([[I(m), I(m)], [I(m), T]]) % 4
    N = len(allv); bad = 0
    for i in range(N):
        x = allv[i]
        ring = np.concatenate([(x + allv) % 4, (x + ty) % 4], axis=1)          # all y at once
        mat = (np.concatenate([np.broadcast_to(x, allv.shape), allv], axis=1) @ Mb.T) % 4
        bad += int((ring != mat).any(axis=1).sum())
    print(f"  m={m} f={bin(p)}: exhaustive {N*N} pairs (x,y), mismatches = {bad}")
    chk(bad == 0, f"C5 m={m}")
    # bijectivity of the ring mixer
    imgs = set()
    for i in range(N):
        x = allv[i]
        r = np.concatenate([(x + allv) % 4, (x + ty) % 4], axis=1)
        imgs.update(map(bytes, r.astype(np.uint8)))
    print(f"    image size {len(imgs)} of {N*N} -> bijective: {len(imgs) == N*N}")
    chk(len(imgs) == N * N, "mixer bijective")

print("TOTAL FAILS:", fails)
sys.exit(0 if fails == 0 else 1)
