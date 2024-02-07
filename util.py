#!/usr/bin/python3
import random
import sys
sys.setrecursionlimit(0x10000)
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
def genfftwp(l, N):
    while True:
        p = random.randrange(1 << l - 1, 1 << l) & -N | 1
        if chkprime(p):
            for z in range(2, p):
                if pow(z, (p - 1) // 2, p) != 1:
                    break
            return pow(z, (p - 1) // N, p), p
def fft(a, w, p):
    N = len(a)
    if N == 1:
        return a
    b = fft(a[0::2], w * w % p, p)
    c = fft(a[1::2], w * w % p, p)
    t = 1
    r = [0] * N
    for i in range(N // 2):
        r[i + 0 // 2] = (b[i] + t * c[i]) % p
        r[i + N // 2] = (b[i] - t * c[i]) % p
        t = t * w % p
    return r
def ifft(a, w, p):
    N = len(a)
    w = modinv(w, p)
    N = modinv(N, p)
    return [x * N % p for x in fft(a, w, p)]
