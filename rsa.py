#!/usr/bin/python3
import random
import util
def RSAGenKey(l):
    p = util.genprime(l)
    q = util.genprime(l)
    phi = (p - 1) * (q - 1)
    while True:
        e = random.randrange(0, phi)
        try:
            d = util.modinv(e, phi)
            return p, q, e, d
        except AssertionError:
            pass
def RSACrypt(n, k, x):
    return pow(x, k, n)
def CRTCrypt(p, q, k, x): # Optimized by CRT (private key is required)
    xp = x % p
    xq = x % q
    kp = k % (p - 1)
    kq = k % (q - 1)
    mp = pow(xp, kp, p)
    mq = pow(xq, kq, q)
    _, (r, s) = util.exgcd(p, q)
    return (mp * s * q + mq * r * p) % (p * q)
if __name__ == '__main__':
    p, q, e, d = RSAGenKey(1024)
    n = p * q
    M = 0xfedcba9876543210
    S = CRTCrypt(p, q, e, M) # signature
    V = RSACrypt(n, d, S)    # verification
    assert M == V
    C = RSACrypt(n, e, M)    # encryption
    P = CRTCrypt(p, q, d, C) # decryption
    assert M == P
