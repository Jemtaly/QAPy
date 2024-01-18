#!/usr/bin/python3
import random
import sys
sys.setrecursionlimit(0x10000)
def exgcd(a, b):
    if b == 0:
        return abs(a), ((a > 0) - (a < 0), 0)
    d, (x, y) = exgcd(b, a % b)
    return d, (y, x - a // b * y)
def modinv(a, m):
    d, (r, _) = exgcd(a, m)
    assert d == 1
    return r % m
def moddiv(a, b, m):
    d, (r, _) = exgcd(b, m)
    assert a % d == 0
    n = m // d
    return a // d * r % n, n
def sample(a, b, n): # take n elements from [a, b) distinctively
    res = set()
    while len(res) < n:
        res.add(random.randrange(a, b))
    return res
def choice(a, b, n): # take n elements from [a, b) independently
    res = []
    while len(res) < n:
        res.append(random.randrange(a, b))
    return res
def crt(D):
    R, M = 0, 1
    for r, m in D:
        d, (N, n) = exgcd(M, m)
        assert (r - R) % d == 0
        R += (r - R) // d * N * M
        M *= m // d
    return R % M, M
def rref(m, h, w, q): # reduced row echelon form
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
    n = len(points)
    coeffs = [0 for _ in range(n)]
    prod = [1]
    for x, y in points:
        prod = [(v - x * u) % q for u, v in zip(prod + [0], [0] + prod)]
    for j, (xj, yj) in enumerate(points):
        dj = 1
        for m, (xm, ym) in enumerate(points):
            if m != j:
                dj = dj * (xj - xm) % q
        qj = modinv(dj, q)
        rj = modinv(xj, q)
        temp = 0
        for i in range(n):
            temp = (temp - prod[i]) * rj % q
            coeffs[i] = (coeffs[i] + yj * qj * temp) % q
    return coeffs
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
    return sum(c * x ** i for i, c in enumerate(coeffs)) % q
def nsqrt(n):
    l, r = 0, n + 1
    while r - l > 1:
        m = (r + l) // 2
        if m * m > n:
            r = m
        else:
            l = m
    return l
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
        r = random.randrange(1 << l - 1, 1 << l)
        if chkprime(r):
            return r
def legendre(x, p, q = 2):
    assert chkprime(p) and (p - 1) % q == 0
    return pow(x, (p - 1) // q, p)
def cipolla(x, p):
    assert chkprime(p) and (p - 1) % 2 == 0
    assert pow(x, (p - 1) // 2, p) <= 1
    for y in range(0, p):
        z = (y * y - x) % p
        if pow(z, (p - 1) // 2, p) != 1:
            break
    def mul(a, b, c, d):
        return (a * c + b * d * z) % p, (a * d + b * c) % p
    a, b = 1, 0
    c, d = y, 1
    q = p + 1
    while q := q // 2:
        if q % 2 == 1:
            a, b = mul(a, b, c, d)
        c, d = mul(c, d, c, d)
    return a
def tonelli(x, p):
    assert chkprime(p) and (p - 1) % 2 == 0
    assert pow(x, (p - 1) // 2, p) <= 1
    for z in range(2, p):
        if pow(z, (p - 1) // 2, p) != 1:
            break
    s, t = p - 1, 0
    while s % 2 == 0:
        s, t = s // 2, t + 1
    k = (s + 1) // 2
    h = pow(x, k, p)
    a = pow(z, s, p)
    b = pow(x, s, p)
    for i in range(1, t):
        d = pow(b, 2 ** (t - i - 1), p)
        if d == 1:
            a = a * a % p
        else:
            h = h * a % p
            a = a * a % p
            b = b * a % p
    return h
def adleman(x, q, p): # q-th root of x (q | p - 1 and q is prime)
    assert chkprime(p) and (p - 1) % q == 0
    assert pow(x, (p - 1) // q, p) <= 1
    for z in range(2, p):
        if pow(z, (p - 1) // q, p) != 1:
            break
    s, t = p - 1, 0
    while s % q == 0:
        s, t = s // q, t + 1
    k = modinv(q, s)
    S = k * q - 1
    h = pow(x, k, p)
    a = pow(z, s, p)
    b = pow(x, S, p)
    c = pow(a, q ** (t - 1), p)
    for i in range(1, t):
        d = pow(b, q ** (t - 1 - i), p)
        j, e = 0, 1
        while d != e:
            j, e = j - 1, e * c % p
        h = pow(a, j, p) * h % p
        a = pow(a, q, p)
        b = pow(a, j, p) * b % p
    return h
def genroot(n, p): # n-th root of unity (n | p - 1)
    assert chkprime(p) and (p - 1) % n == 0
    g = 1
    q = 2
    while n > 1:
        a = 0
        while n % q == 0:
            n, a = n // q, a + 1
        if a > 0:
            for z in range(2, p):
                if pow(z, (p - 1) // q, p) != 1:
                    break
            g = pow(z, (p - 1) // q ** a, p) * g % p
        q = q + 1
    return g
def rootset(x, n, p): # all n-th roots of x
    assert chkprime(p)
    n, (u, _) = exgcd(n, p - 1)
    x = pow(x, u, p)
    N = n
    g = 1
    q = 2
    while n > 1:
        a = 0
        while n % q == 0:
            n, a = n // q, a + 1
            x = adleman(x, q, p)
        if a > 0:
            for z in range(2, p):
                if pow(z, (p - 1) // q, p) != 1:
                    break
            g = pow(z, (p - 1) // q ** a, p) * g % p
        q = q + 1
    return {x * pow(g, i, p) % p for i in range(N)}
