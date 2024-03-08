#!/usr/bin/env python3
import random
def pows(a, n, p):
    r = 1
    for _ in range(n):
        yield r
        r = r * a % p
def pru(n, p): # primitive root of unity
    assert n & n - 1 == 0 and p - 1 & n - 1 == 0
    for Z in range(2, p):
        if pow(Z, (p - 1) // 2, p) != 1:
            break
    return pow(Z, (p - 1) // n, p)
def fft(a, w, p):
    n = len(a)
    if n == 1:
        return a
    t = w * w % p
    b = fft(a[0::2], t, p)
    c = fft(a[1::2], t, p)
    k = 1
    for i in range(n // 2):
        b[i], c[i], k = (b[i] + k * c[i]) % p, (b[i] - k * c[i]) % p, k * w % p
    return b + c
def ifft(a, w, p):
    n = len(a)
    w = pow(w, -1, p)
    m = pow(n, -1, p)
    return [x * m % p for x in fft(a, w, p)]
if __name__ == '__main__':
    # p = 998244353
    # n = 1 << 10
    # w = pru(n, p)
    # a = [random.randrange(p) for _ in range(n)]
    # x = list(pows(random.randrange(2, p), n, p))
    # A = ifft(a, w, p)
    # X = ifft(x, w, p)
    # aX = [ai * Xi % p for ai, Xi in zip(a, X)]
    # Ax = [Ai * xi % p for Ai, xi in zip(A, x)]
    # print(set(aX) & set(Ax))
    p = 998244353
    n = 1 << 10
    w = pru(n, p)
    aI = [random.randrange(p) for _ in range(n)]
    xI = [random.randrange(p) for _ in range(n)]
    AI = ifft(aI, w, p)
    XI = ifft(xI, w, p)
    Xa = sum(X * a for X, a in zip(XI, aI))
    Ax = sum(A * x for A, x in zip(AI, xI))
    assert Xa % p == Ax % p
