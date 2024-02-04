#!/usr/bin/python3
import time
import util
P = util.genprime(64)
class Timer:
    def __init__(self, text):
        self.text = text
    def __enter__(self):
        print(self.text, end = ' ')
        self.beg = time.time()
    def __exit__(self, *args):
        self.end = time.time()
        print('{:.3f} sec'.format(self.end - self.beg))
class Program:
    def __init__(self):
        self.cons = []
        self.dims = [lambda getw, **args: 1]
        self.pubs = {0}
    def con_count(self):
        return len(self.cons)
    def dim_count(self):
        return len(self.dims)
    def R1CS(self):
        M = self.dim_count()
        N = self.con_count()
        A = [[0 for _ in range(M)] for _ in range(N)]
        B = [[0 for _ in range(M)] for _ in range(N)]
        C = [[0 for _ in range(M)] for _ in range(N)]
        for i, con in enumerate(self.cons):
            a, b, c = con
            for k, v in a.items():
                A[i][k] = v
            for k, v in b.items():
                B[i][k] = v
            for k, v in c.items():
                C[i][k] = v
        return A, B, C
    def QAP(self):
        M = self.dim_count()
        N = self.con_count()
        poly = [1]
        for k in range(1, N + 1):
            poly = [(v - k * u) % P for u, v in zip(poly + [0], [0] + poly)]
        def lagrange(points, q):
            coeffs = [0 for _ in range(N)]
            for j, (xj, yj) in enumerate(points):
                if yj == 0:
                    continue
                dj = 1
                for m, (xm, ym) in enumerate(points):
                    if m != j:
                        dj = dj * (xj - xm) % q
                kj = util.modinv(dj, q)
                rj = util.modinv(xj, q)
                temp = 0
                for i in range(N):
                    temp = (temp - poly[i]) * rj % q
                    coeffs[i] = (coeffs[i] + yj * kj * temp) % q
            return coeffs
        A, B, C = self.R1CS()
        Aips = [lagrange(list(enumerate((A[j][i] for j in range(N)), 1)), P) for i in range(M)]
        Bips = [lagrange(list(enumerate((B[j][i] for j in range(N)), 1)), P) for i in range(M)]
        Cips = [lagrange(list(enumerate((C[j][i] for j in range(N)), 1)), P) for i in range(M)]
        return poly, Aips, Bips, Cips
    def witness(self, **args):
        M = self.dim_count()
        witness = [0 for _ in range(M)]
        getw = lambda x: sum(witness[k] * v for k, v in x.items()) % P
        for i, func in enumerate(self.dims):
            witness[i] = func(getw, **args)
        for a, b, c in self.cons:
            assert getw(a) * getw(b) % P == getw(c)
        return witness
    def __bind(self, func, public = False):
        i = len(self.dims)
        self.dims.append(func)
        if public:
            self.pubs.add(i)
        return {i: 1}
    def VAR(self, name, public = False):
        return self.__bind(lambda getw, **args: args[name], public)
    def ASSERT(self, x, y, z):
        if isinstance(x, int) and isinstance(y, int) and isinstance(z, int):
            assert x * y % P == z
            return
        if isinstance(x, int):
            x = {0: x}
        if isinstance(y, int):
            y = {0: y}
        if isinstance(z, int):
            z = {0: z}
        self.cons.append((x, y, z))
    def ADD(self, x, y):
        if isinstance(x, int) and isinstance(y, int):
            return (x + y) % P
        if isinstance(y, int):
            y = {0: y}
        if isinstance(x, int):
            x = {0: x}
        return {k: (x.get(k, 0) + y.get(k, 0)) % P for k in x.keys() | y.keys()}
    def SUB(self, x, y):
        if isinstance(x, int) and isinstance(y, int):
            return (x - y) % P
        if isinstance(y, int):
            y = {0: y}
        if isinstance(x, int):
            x = {0: x}
        return {k: (x.get(k, 0) - y.get(k, 0)) % P for k in x.keys() | y.keys()}
    def MUL(self, x, y):
        if isinstance(x, int) and isinstance(y, int):
            return x * y % P
        if isinstance(y, int):
            return {i: m * y % P for i, m in x.items()}
        if isinstance(x, int):
            return {i: m * x % P for i, m in y.items()}
        z = self.__bind(lambda getw, **args: getw(x) * getw(y) % P)
        self.ASSERT(x, y, z)
        return z
    def DIV(self, x, y):
        if isinstance(x, int) and isinstance(y, int):
            return x * util.modinv(y, P) % P
        if isinstance(y, int):
            return {i: m * util.modinv(y, P) % P for i, m in x.items()}
        if isinstance(x, int):
            x = {0: x}
        z = self.__bind(lambda getw, **args: getw(x) * util.modinv(getw(y), P) % P)
        self.ASSERT(z, y, x)
        return z
    def SUM(self, List):
        r = 0
        for i in List:
            r = self.ADD(r, i)
        return r
    def SWITCH(self, x, Keys):
        if isinstance(x, int):
            assert x in Keys
            return {K: pow(x - K, P - 1, P) for K in Keys}
        xChk = {K: 0 for K in Keys}
        bind = lambda K: self.__bind(lambda getw, **args: pow(getw(x) - K, P - 1, P))
        for K in Keys:
            b = xChk[K] = bind(K)
            self.ASSERT_ISBOOL(b)
        t = self.SUM(self.MUL(b, K) for K, b in xChk.items())
        e = self.SUM(self.MUL(b, 1) for K, b in xChk.items())
        self.ASSERT_EQ(x, t)
        self.ASSERT_EQ(1, e)
        return xChk
    def BINARY(self, x, xLen):
        if isinstance(x, int):
            assert 0 <= x < 2 ** xLen
            return [x >> I & 1 for I in range(xLen)]
        bind = lambda I: self.__bind(lambda getw, **args: getw(x) >> I & 1)
        xBin = [0 for _ in range(xLen)]
        for I in range(xLen):
            b = xBin[I] = bind(I)
            self.ASSERT_ISBOOL(b)
        t = self.SUM(self.MUL(b, 1 << I) for I, b in enumerate(xBin))
        self.ASSERT_EQ(x, t)
        return xBin
    def DIVMOD(self, x, y, qLen, rLen):
        if isinstance(x, int) and isinstance(y, int):
            assert 0 <= x // y < 2 ** qLen
            assert 0 <= x % y < 2 ** rLen
            return [x // y >> I & 1 for I in range(qLen)], [x % y >> I & 1 for I in range(rLen)]
        if isinstance(x, int):
            x = {0: x}
        if isinstance(y, int):
            y = {0: y}
        q = self.__bind(lambda getw, **args: getw(x) // getw(y))
        r = self.__bind(lambda getw, **args: getw(x) % getw(y))
        self.ASSERT(q, y, self.SUB(x, r)) # assert y * q == x - r
        self.ASSERT_GE(q, 0, qLen)
        self.ASSERT_GE(r, 0, rLen)
        self.ASSERT_LT(r, y, rLen)
        return q, r
    def BOOL(self, x):
        if isinstance(x, int):
            return pow(x, P - 1, P)
        v = self.__bind(lambda getw, **args: pow(getw(x), P - 2, P))
        o = self.__bind(lambda getw, **args: pow(getw(x), P - 1, P))
        self.ASSERT(o, x, x)
        self.ASSERT(x, v, o)
        return o
    def NOT(self, x):
        return self.SUB(1, x)
    def AND(self, x, y):
        return self.MUL(x, y)
    def OR(self, x, y):
        return self.SUB(1, self.MUL(self.SUB(1, x), self.SUB(1, y)))
    def XOR(self, x, y):
        return self.DIV(self.SUB(1, self.MUL(self.SUB(1, self.MUL(x, 2)), self.SUB(1, self.MUL(y, 2)))), 2)
    def IF(self, b, t, f):
        return self.ADD(self.MUL(b, self.SUB(t, f)), f)
    def GETITEM(self, Dict, iChk):
        return self.SUM(self.MUL(Dict[K], iChk[K]) for K in Dict)
    def SETITEM(self, Dict, iChk, v):
        for K in Dict:
            Dict[K] = self.IF(iChk[K], v, Dict[K])
    def INDEX(self, List, iBin):
        for b in iBin:
            List = [self.IF(b, r, l) for l, r in zip(List[0::2], List[1::2])]
        return List[0]
    def VAL(self, xBin):
        return self.SUM(self.MUL(b, 1 << I) for I, b in enumerate(xBin))
    def POW(self, x, nBin):
        b, *nBin = nBin
        r = self.IF(b, x, 1)
        for b in nBin:
            x = self.MUL(x, x)
            r = self.MUL(r, self.IF(b, x, 1))
        return r
    def BITNOT(self, xBin):
        return [self.NOT(b) for b in xBin]
    def BITAND(self, xBin, yBin):
        return [self.AND(a, b) for a, b in zip(xBin, yBin, strict = True)]
    def BITOR(self, xBin, yBin):
        return [self.OR(a, b) for a, b in zip(xBin, yBin, strict = True)]
    def BITXOR(self, xBin, yBin):
        return [self.XOR(a, b) for a, b in zip(xBin, yBin, strict = True)]
    def BINADD(self, xBin, yBin, c, sLen):
        zBin = self.BINARY(self.ADD(self.VAL(xBin), self.ADD(self.VAL(self.ADD(0, b) for b in yBin), self.ADD(0, c))), sLen + 1)
        return zBin[:sLen], self.ADD(0, zBin[sLen])
    def BINSUB(self, xBin, yBin, c, sLen):
        zBin = self.BINARY(self.ADD(self.VAL(xBin), self.ADD(self.VAL(self.SUB(1, b) for b in yBin), self.SUB(1, c))), sLen + 1)
        return zBin[:sLen], self.SUB(1, zBin[sLen])
    def BINMUL(self, xBin, yBin, cBin, dBin, sLen):
        zBin = self.BINARY(self.ADD(self.MUL(self.VAL(xBin), self.VAL(yBin)), self.ADD(self.VAL(cBin), self.VAL(dBin))), sLen * 2)
        return zBin[:sLen], zBin[sLen:]
    def GE(self, x, y, dLen): # 0 <= x - y < 2 ** dLen
        return self.BINARY(self.ADD(2 ** dLen, self.SUB(x, y)), dLen + 1)[dLen]
    def LE(self, x, y, dLen): # 0 <= y - x < 2 ** dLen
        return self.BINARY(self.ADD(2 ** dLen, self.SUB(y, x)), dLen + 1)[dLen]
    def GT(self, x, y, dLen): # 0 < x - y <= 2 ** dLen
        return self.BINARY(self.ADD(2 ** dLen, self.SUB(self.SUB(x, y), 1)), dLen + 1)[dLen]
    def LT(self, x, y, dLen): # 0 < y - x <= 2 ** dLen
        return self.BINARY(self.ADD(2 ** dLen, self.SUB(self.SUB(y, x), 1)), dLen + 1)[dLen]
    def ASSERT_GE(self, x, y, dLen): # 0 <= x - y < 2 ** dLen
        return self.BINARY(self.SUB(x, y), dLen)
    def ASSERT_LE(self, x, y, dLen): # 0 <= y - x < 2 ** dLen
        return self.BINARY(self.SUB(y, x), dLen)
    def ASSERT_GT(self, x, y, dLen): # 0 < x - y <= 2 ** dLen
        return self.BINARY(self.SUB(self.SUB(x, y), 1), dLen)
    def ASSERT_LT(self, x, y, dLen): # 0 < y - x <= 2 ** dLen
        return self.BINARY(self.SUB(self.SUB(y, x), 1), dLen)
    def ASSERT_EQ(self, x, y):
        self.ASSERT(1, x, y)
    def ASSERT_NE(self, x, y):
        self.DIV(1, self.SUB(x, y))
    def ASSERT_ISBOOL(self, x):
        self.ASSERT(x, x, x)
    def ASSERT_CHK(self, x, Keys):
        self.SWITCH(x, Keys)
    def ASSERT_LEN(self, x, xLen):
        self.BINARY(x, xLen)
def dot(Mips, w):
    return [sum(i * j for i, j in zip(u, w)) % P for u in zip(*Mips)]
if __name__ == '__main__':
    print('GF({})'.format(P))
    # Example Program
    pro = Program()
    x = pro.VAR('x', public = 0) # x
    y = pro.VAR('y', public = 0) # y
    z = pro.VAR('z', public = 0) # z
    xBin = pro.BINARY(x, 16) # binary representation of x
    yBin = pro.BINARY(y, 16) # binary representation of y
    tBin = [pro.XOR(a, b) for a, b in zip(xBin, yBin)] # binary representation of x ^ y
    t = pro.VAL(tBin) # x ^ y
    q, r = pro.DIVMOD(t, z, 16, 16) # x // y, x % y
    print('Number of constraints:', pro.con_count())
    print('Number of dimensions:', pro.dim_count())
    with Timer('Calculating R1CS and QAP...'):
        t, A, B, C = pro.QAP()
    with Timer('Calculating witness...'):
        w = pro.witness(x = 65535, y = 12345, z = 17)
    print('witness = [{}]'.format(', '.join(('{} (pub)' if i in pro.pubs else '{}').format(v) for i, v in enumerate(w))))
    with Timer('Verifying witness...'):
        a = dot(A, w)
        b = dot(B, w)
        c = dot(C, w)
        d = util.polysub(util.polymul(a, b, P), c, P)
        q, r = util.polydm(d, t, P)
    if any(r):
        print('Verification failed!')
        print('a(x) =', util.polyshow(a))
        print('b(x) =', util.polyshow(b))
        print('c(x) =', util.polyshow(c))
        print('d(x) =', util.polyshow(d))
        print('t(x) =', util.polyshow(t))
        print('q(x) =', util.polyshow(q))
        print('r(x) =', util.polyshow(r))
    else:
        print('Verification passed!')
