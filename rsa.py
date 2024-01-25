#!/usr/bin/python3
import random
import util
class RSAPubl:
    def __init__(self, n, e):
        self.n = n
        self.e = e
    def encrypt(self, x):
        return pow(x, self.e, self.n)
class RSAPriv:
    def __init__(self, l):
        p = util.genprime(l)
        q = util.genprime(l)
        phi = (p - 1) * (q - 1)
        while True:
            e = random.randrange(0, phi)
            try:
                d = util.modinv(e, phi)
                break
            except AssertionError:
                pass
        self.p = p
        self.q = q
        self.n = p * q
        self.d = d
        self.e = e
        # CRT optimization parameters
        self.r = p * util.modinv(p, q)
        self.s = q * util.modinv(q, p)
        self.u = d % (p - 1)
        self.v = d % (q - 1)
    def decrypt(self, x):
        m = pow(x % self.p, self.u, self.p)
        n = pow(x % self.q, self.v, self.q)
        return (m * self.s + n * self.r) % self.n
    def genpubl(self):
        return RSAPubl(self.n, self.e)
if __name__ == '__main__':
    server = RSAPriv(1024)
    client = server.genpubl()
    # sign and verify
    m = random.randrange(server.n)
    s = server.decrypt(m) # signature
    v = client.encrypt(s) # verification
    assert m == v
    # encrypt and decrypt
    m = random.randrange(client.n)
    c = client.encrypt(m) # encryption
    p = server.decrypt(c) # decryption
    assert m == p
    # 1-out-of-n oblivious transfer
    n = 10
    M = [random.randrange(server.n) for i in range(n)] # secret messages
    X = [random.randrange(server.n) for i in range(n)] # random messages
    b = random.randrange(n) # secret choice
    k = random.randrange(client.n) # random key
    q = (X[b] + client.encrypt(k)) % client.n # blinded query
    N = [(server.decrypt(q - x) + m) % server.n for x, m in zip(X, M)] # responses
    m = (N[b] - k) % client.n # decryption
    assert m == M[b]
