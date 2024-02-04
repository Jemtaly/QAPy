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
    secret = 0
    prod = 1
    for x, y in shares:
        prod = prod * x % Q
    for j, (xj, yj) in enumerate(shares):
        dj = 1
        for m, (xm, ym) in enumerate(shares):
            if m != j:
                dj = dj * (xm - xj) % Q
        kj = util.modinv(dj, Q)
        rj = util.modinv(xj, Q)
        secret = (secret + yj * kj * rj) % Q
    return secret * prod % Q
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
