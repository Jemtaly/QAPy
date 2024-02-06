#!/usr/bin/python3
import random
import sys
sys.setrecursionlimit(0x10000)
def sample(a, b, n):
    # take n elements from [a, b) distinctively
    res = set()
    while len(res) < n:
        res.add(random.randrange(a, b))
    return res
def choice(a, b, n):
    # take n elements from [a, b) independently
    res = []
    while len(res) < n:
        res.append(random.randrange(a, b))
    return res
def root(x, n):
    # input: x, n
    # output: y such that y ** n <= x < (y + 1) ** n
    l, r = 0, x + 1
    while r - l > 1:
        m = (r + l) // 2
        if m ** n > x:
            r = m
        else:
            l = m
    return l
def exgcd(a, b):
    # input: a, b
    # output: d, (x, y) such that d == (a, b) == a * x + b * y
    if b == 0:
        return abs(a), ((a > 0) - (a < 0), 0)
    d, (x, y) = exgcd(b, a % b)
    return d, (y, x - a // b * y)
def modinv(a, m):
    # input: a, m such that (a, m) == 1
    # output: the inverse of a modulo m
    d, (r, _) = exgcd(a, m)
    assert d == 1
    return r % m
def moddiv(a, b, m):
    # input: a, b, m such that (b, m) | a
    # output: k, n such that c == a / b (mod m) if and only if c == k (mod n)
    d, (r, _) = exgcd(b, m)
    assert a % d == 0
    k = a // d * r
    n = m // d
    return k % n, n
def crt(D):
    # input: D, which is a list of r, m pairs
    # output: R, M such that x == r (mod m) for all r, m in D if and only if x == R (mod M)
    R, M = 0, 1
    for r, m in D:
        d, (N, n) = exgcd(M, m)
        c = r - R
        assert c % d == 0
        R = R + c // d * N * M
        M = M * m // d
    return R % M, M
def rref(m, h, w, q):
    # input: m, h, w, q such that m is a h * w matrix over Z / q
    # output: reduced row echelon form of m
    for J in range(w):
        I = next((I for I in range(h) if all(m[I][j] == 0 for j in range(J)) and m[I][J] != 0), None)
        if I is None:
            continue
        for i in range(h):
            if i == I:
                continue
            mrecord = m[i][J]
            for j in range(J, w):
                m[i][j] = (m[i][j] * m[I][J] - m[I][j] * mrecord) % q
def lagrange(points, q):
    # input: n points, each of which is a pair of x and y
    # output: coefficients list of the n - 1 degree polynomial that passes through all the points
    n = len(points)
    T = [0 for _ in range(n)]
    Y = [0 for _ in range(n)]
    Z = [1]
    for x, y in points:
        Z = [(v - x * u) % q for u, v in zip(Z + [0], [0] + Z)]
    for j, (x, y) in enumerate(points):
        d = 1
        for m, (u, v) in enumerate(points):
            if m != j:
                d = d * (x - u) % q
        k = modinv(d, q)
        r = modinv(x, q)
        t = 0
        for i in range(n):
            T[i] = t = (t - Z[i]) * r % q
            Y[i] = (Y[i] + y * k * t) % q
    return Y
def polyadd(a, b, m):
    res = [0] * max(len(a), len(b))
    for i in range(len(a)):
        res[i] += a[i]
    for i in range(len(b)):
        res[i] += b[i]
    return [x % m for x in res]
def polysub(a, b, m):
    res = [0] * max(len(a), len(b))
    for i in range(len(a)):
        res[i] += a[i]
    for i in range(len(b)):
        res[i] -= b[i]
    return [x % m for x in res]
def polymul(a, b, m):
    res = [0] * (len(a) + len(b) - 1)
    for i in range(len(a)):
        for j in range(len(b)):
            res[i + j] += a[i] * b[j]
    return [x % m for x in res]
def polydm(a, b, m):
    q = []
    r = a[::-1]
    d = b[::-1]
    for _ in range(len(a) - len(d) + 1):
        t = r[0] * modinv(d[0], m) % m
        for i in range(len(d)):
            r[i] = (r[i] - t * d[i]) % m
        q.append(t)
        r.pop(0)
    return q[::-1], r[::-1]
def polyshow(coeffs):
    return ' + '.join('{} * x ** {}'.format(c, i) for i, c in enumerate(coeffs) if c != 0) or '0'
def polyval(coeffs, x, q):
    return sum(c * pow(x, i, q) for i, c in enumerate(coeffs)) % q
def chkprime(n, k = 16):
    if n == 2:
        return True
    if n < 2 or n % 2 == 0:
        return False
    s, t = n - 1, 0
    while s % 2 == 0:
        s, t = s // 2, t + 1
    for _ in range(k):
        a = random.randrange(1, n)
        x = pow(a, s, n)
        if x == 1:
            continue
        for _ in range(t):
            if x == n - 1:
                break
            x = x * x % n
        else:
            return False
    return True
def genprime(l):
    while True:
        n = random.randrange(1 << l - 1, 1 << l)
        if chkprime(n):
            return n
