#!/usr/bin/python3
import sys
sys.setrecursionlimit(0x10000)
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
    w = pow(w, -1, p)
    N = pow(N, -1, p)
    return [x * N % p for x in fft(a, w, p)]
