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
    coeffs = [0 for _ in range(n)]
    poly = [1]
    for x, y in points:
        poly = [(v - x * u) % q for u, v in zip(poly + [0], [0] + poly)]
    for j, (xj, yj) in enumerate(points):
        dj = 1
        for m, (xm, ym) in enumerate(points):
            if m != j:
                dj = dj * (xj - xm) % q
        kj = modinv(dj, q)
        rj = modinv(xj, q)
        temp = 0
        for i in range(n):
            temp = (temp - poly[i]) * rj % q
            coeffs[i] = (coeffs[i] + yj * kj * temp) % q
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
def phi(fact):
    # input: a dictionary that represents the prime factorization of n
    # output: the number of integers less than n and coprime to n
    f = 1
    for p, a in fact.items():
        assert chkprime(p)
        f *= p ** a - p ** a // p
    return f
def num(fact):
    # input: a dictionary that represents the prime factorization of n
    # output: the value of n
    n = 1
    for p, a in fact.items():
        assert chkprime(p)
        n *= p ** a
    return n
def modroot(x, fact, n):
    # input: x, n and a dictionary that represents the prime factorization of m
    # output: x ** (1 / n) (mod m)
    return pow(x, modinv(n, phi(fact)), num(fact))
def rthroot(x, p, m, r):
    # input: x, p, m, r such that p is odd prime, r is a prime factor of p ** m * (1 - 1 / p)
    # output: h such that h ** r == x (mod p ** m)
    assert chkprime(p) and p != 2
    q, f = p ** m, p ** m - p ** m // p
    assert f % r == 0
    assert pow(x, f // r, q) == 1
    for z in range(2, p):
        if pow(z, f // r, q) != 1:
            break
    s, t = f, 0
    while s % r == 0:
        s, t = s // r, t + 1
    k = modinv(r, s)
    S = k * r - 1
    h = pow(x, k, q)
    a = pow(z, s, q)
    b = pow(x, S, q)
    c = pow(a, r ** (t - 1), q)
    for i in range(1, t):
        d = pow(b, r ** (t - 1 - i), q)
        j, e = 0, 1
        while d != e:
            j, e = j - 1, e * c % q
        h = pow(a, j, q) * h % q
        a = pow(a, r, q)
        b = pow(a, j, q) * b % q
    return h
def nthroot(x, p, m, n):
    # input: x, p, m, n such that p is odd prime, n | p ** m * (1 - 1 / p)
    # output: all h in Z / p ** m such that h ** n == x (mod p ** m)
    assert chkprime(p) and p != 2
    q, f = p ** m, p ** m - p ** m // p
    assert f % n == 0
    assert pow(x, f // n, q) == 1
    g = 1 # g ** n == 1 (mod p ** m) and g ** i != 1 (mod p ** m) for all i < n
    r = 2
    while n > 1:
        a = 0
        while n % r == 0:
            n, a = n // r, a + 1
            x = rthroot(x, p, m, r)
        if a > 0:
            for z in range(2, p):
                if pow(z, f // r, q) != 1:
                    break
            g = pow(z, f // r ** a, q) * g % q
        r = r + 1
    S = set()
    while x not in S:
        S.add(x)
        x = x * g % q
    return S
def binsqrt(x, m):
    # input: x, m such that m >= 3 and x == 1 (mod 8)
    # output: y such that y ** 2 == x (mod 2 ** m), y == 1 (mod 8) and 0 <= y < 2 ** (m - 1)
    assert m >= 3
    assert x % 8 == 1
    a = 1
    for i in range(2, m - 1):
        if (a * a - x) % 2 ** (i + 2) != 0:
            a = a + 2 ** i
    return a
def binroot(x, m, k):
    # input: x, k, m such that m >= k + 2 >= 3 and x == 1 (mod 2 ** (k + 2))
    # output: a, b, c such that y ** n == x (mod 2 ** m) if and only if y == a or b (mod c), where n == 2 ** k
    assert m >= k + 2 >= 3
    assert x % 2 ** (k + 2) == 1
    for i in range(k):
        x = binsqrt(x, m - i)
    return x, 2 ** (m - k) - x, 2 ** (m - k)
