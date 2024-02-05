#!/usr/bin/python3
import random
import util
Q = util.genprime(16)
def genshares(secret, k, n):
    coeffs = [secret]
    for _ in range(1, k - 1):
        coeffs.append(random.randrange(0, Q))
    coeffs.append(random.randrange(1, Q))
    return [(x, sum(c * x ** i for i, c in enumerate(coeffs)) % Q) for x in util.sample(1, Q, n)]
def recsecret(shares):
    Y = 0
    Z = 1
    for x, y in shares:
        Z = Z * x % Q
    for j, (x, y) in enumerate(shares):
        d = 1
        for m, (u, v) in enumerate(shares):
            if m != j:
                d = d * (u - x) % Q
        k = util.modinv(d, Q)
        r = util.modinv(x, Q)
        Y = (Y + y * k * r) % Q
    return Y * Z % Q
if __name__ == '__main__':
    print('GF({})'.format(Q))
    K, N = 3, 5
    secret = random.randrange(0, Q)
    print('secret:', secret)
    shares = genshares(secret, K, N)
    print('shares:', ', '.join('({}, {})'.format(x, y) for x, y in shares))
    sample = random.sample(shares, K)
    print('sample:', ', '.join('({}, {})'.format(x, y) for x, y in sample))
    recons = recsecret(sample)
    print('recons:', recons)
