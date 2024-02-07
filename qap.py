#!/usr/bin/python3
import time
import util
import random
import py_ecc
P = py_ecc.optimized_bls12_381.curve_order
K = 1
while (P - 1) % (K * 2) == 0:
    K = K * 2
for Z in range(2, P):
    if pow(Z, (P - 1) // 2, P) != 1:
        break
T = pow(Z, (P - 1) // K, P)
G = py_ecc.optimized_bls12_381.G1
H = py_ecc.optimized_bls12_381.G2
dot = py_ecc.optimized_bls12_381.multiply
add = py_ecc.optimized_bls12_381.add
neg = py_ecc.optimized_bls12_381.neg
mul = py_ecc.optimized_bls12_381.pairing
Add = py_ecc.optimized_bls12_381.FQ12.__mul__
Chk = py_ecc.optimized_bls12_381.FQ12.__eq__
class Timer:
    def __init__(self, text):
        self.text = text
    def __enter__(self):
        print(self.text, end = ' ', flush = True)
        self.beg = time.time()
    def __exit__(self, *info):
        self.end = time.time()
        print('{:.3f} sec'.format(self.end - self.beg))
class Program:
    def __init__(self):
        self.cons = [] # constraints
        self.dims = [lambda getw, args: 1] # variables
        self.pubs = {0: 'unit'}
    def con_count(self):
        return len(self.cons)
    def dim_count(self):
        return len(self.dims)
    def setup(self, α, β, γ, δ, x):
        M = self.dim_count()
        N = self.con_count()
        I = 1
        while I < N:
            I = I * 2
        J = I * 2
        R = pow(T, K // I, P)
        S = pow(T, K // J, P)
        y = x * util.modinv(S, P) % P
        Zx = pow(x, I, P) - 1
        xI = [pow(x, i, P) for i in range(I)]
        XI = util.ifft(xI, R, P)
        AxM = [0 for _ in range(M)]
        BxM = [0 for _ in range(M)]
        CxM = [0 for _ in range(M)]
        for X, (aM, bM, cM) in zip(XI, self.cons):
            for m, a in aM.items():
                AxM[m] += a * X
            for m, b in bM.items():
                BxM[m] += b * X
            for m, c in cM.items():
                CxM[m] += c * X
        Γ = util.modinv(γ, P)
        Δ = util.modinv(δ, P)
        αG = dot(G, α)
        βG = dot(G, β)
        δG = dot(G, δ)
        βH = dot(H, β)
        γH = dot(H, γ)
        δH = dot(H, δ)
        uGU = [dot(G, (β * Ax + α * Bx + Cx) * Γ) for m, (Ax, Bx, Cx) in enumerate(zip(AxM, BxM, CxM)) if (m in pro.pubs) == 1]
        vGV = [dot(G, (β * Ax + α * Bx + Cx) * Δ) for m, (Ax, Bx, Cx) in enumerate(zip(AxM, BxM, CxM)) if (m in pro.pubs) == 0]
        xGI = [dot(G, pow(x, i, P)) for i in range(I)]
        xHI = [dot(H, pow(x, i, P)) for i in range(I)]
        yGI = [dot(G, pow(y, i, P) * Δ * Zx) for i in range(I - 1)]
        return αG, βG, δG, βH, γH, δH, uGU, vGV, xGI, xHI, yGI
    def prove(self, args, r, s, αG, βG, δG, βH, δH, vGV, xGI, xHI, yGI):
        N = self.con_count()
        I = 1
        while I < N:
            I = I * 2
        J = I * 2
        R = pow(T, K // I, P)
        S = pow(T, K // J, P)
        wM = []
        getw = lambda xM: sum(wM[m] * x for m, x in xM.items()) % P
        for func in self.dims:
            wM.append(func(getw, args))
        uU = [w for m, w in enumerate(wM) if (m in pro.pubs) == 1]
        vV = [w for m, w in enumerate(wM) if (m in pro.pubs) == 0]
        awN = []
        bwN = []
        cwN = []
        for aM, bM, cM in self.cons:
            awN.append(getw(aM))
            bwN.append(getw(bM))
            cwN.append(getw(cM))
        AwI = util.ifft(awN + [0] * (I - N), R, P)
        BwI = util.ifft(bwN + [0] * (I - N), R, P)
        CwI = util.ifft(cwN + [0] * (I - N), R, P)
        awJ = util.fft(AwI + [0] * I, S, P)
        bwJ = util.fft(BwI + [0] * I, S, P)
        cwJ = util.fft(CwI + [0] * I, S, P)
        hI = [(P - 1) // 2 * (aw * bw - cw) % P for j, (aw, bw, cw) in enumerate(zip(awJ, bwJ, cwJ)) if j % 2 == 1]
        HI = util.ifft(hI, R, P)
        AG = add(αG, dot(δG, r))
        for Aw, xG in zip(AwI, xGI):
            AG = add(AG, dot(xG, Aw))
        BG = add(βG, dot(δG, s))
        for Bw, xG in zip(BwI, xGI):
            BG = add(BG, dot(xG, Bw))
        BH = add(βH, dot(δH, s))
        for Bw, xH in zip(BwI, xHI):
            BH = add(BH, dot(xH, Bw))
        CG = add(add(dot(AG, s), dot(BG, r)), neg(dot(δG, r * s)))
        for H, hG in zip(HI, yGI):
            CG = add(CG, dot(hG, H))
        for v, vG in zip(vV, vGV):
            CG = add(CG, dot(vG, v))
        return AG, BH, CG, uU
    @staticmethod
    def verify(αG, βH, γH, δH, uGU, AG, BH, CG, uU):
        DG = dot(G, 0)
        for u, uG in zip(uU, uGU):
            DG = add(DG, dot(uG, u))
        return Chk(mul(BH, AG), Add(mul(βH, αG), Add(mul(γH, DG), mul(δH, CG))))
    def __bind(self, func, pubname = None):
        i = len(self.dims)
        self.dims.append(func)
        if pubname is not None:
            self.pubs[i] = pubname
        return {i: 1}
    def VAR(self, name, public = False):
        return self.__bind(lambda getw, args: args[name], name if public else None)
    def RET(self, name, x):
        if isinstance(x, int):
            x = {0: x}
        return self.__bind(lambda getw, args: getw(x), name if name else 'unnamed')
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
        return {k: v for k in x.keys() | y.keys() if (v := (x.get(k, 0) + y.get(k, 0)) % P)}
    def SUB(self, x, y):
        if isinstance(x, int) and isinstance(y, int):
            return (x - y) % P
        if isinstance(y, int):
            y = {0: y}
        if isinstance(x, int):
            x = {0: x}
        return {k: v for k in x.keys() | y.keys() if (v := (x.get(k, 0) - y.get(k, 0)) % P)}
    def MUL(self, x, y):
        if isinstance(x, int) and isinstance(y, int):
            return x * y % P
        if isinstance(y, int):
            return {i: m * y % P for i, m in x.items()}
        if isinstance(x, int):
            return {i: m * x % P for i, m in y.items()}
        z = self.__bind(lambda getw, args: getw(x) * getw(y) % P)
        self.ASSERT(x, y, z)
        return z
    def DIV(self, x, y):
        if isinstance(x, int) and isinstance(y, int):
            return x * util.modinv(y, P) % P
        if isinstance(y, int):
            return {i: m * util.modinv(y, P) % P for i, m in x.items()}
        if isinstance(x, int):
            x = {0: x}
        z = self.__bind(lambda getw, args: getw(x) * util.modinv(getw(y), P) % P)
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
            return {K: 1 - pow(x - K, P - 1, P) for K in Keys}
        xChk = {K: 0 for K in Keys}
        bind = lambda K: self.__bind(lambda getw, args: 1 - pow(getw(x) - K, P - 1, P))
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
        bind = lambda I: self.__bind(lambda getw, args: getw(x) >> I & 1)
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
        q = self.__bind(lambda getw, args: getw(x) // getw(y))
        r = self.__bind(lambda getw, args: getw(x) % getw(y))
        self.ASSERT(q, y, self.SUB(x, r)) # assert y * q == x - r
        self.ASSERT_GE(q, 0, qLen)
        self.ASSERT_GE(r, 0, rLen)
        self.ASSERT_LT(r, y, rLen)
        return q, r
    def BOOL(self, x):
        if isinstance(x, int):
            return pow(x, P - 1, P)
        v = self.__bind(lambda getw, args: pow(getw(x), P - 2, P))
        o = self.__bind(lambda getw, args: pow(getw(x), P - 1, P))
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
        if isinstance(t, list) and isinstance(f, list):
            return list(self.IF(b, u, v) for u, v in zip(t, f))
        if isinstance(t, tuple) and isinstance(f, tuple):
            return tuple(self.IF(b, u, v) for u, v in zip(t, f))
        return self.ADD(self.MUL(b, self.SUB(t, f)), f)
    def GETDI(self, Dict, iChk):
        return self.SUM(self.MUL(Dict[K], iChk[K]) for K in Dict)
    def SETDI(self, Dict, iChk, v):
        for K, b in iChk.items():
            Dict[K] = self.IF(b, v, Dict[K])
    def GETLI(self, List, iBin):
        for b in iBin:
            List = [self.IF(b, r, l) for l, r in zip(List[0::2], List[1::2])]
        return List[0]
    def SETLI(self, List, iBin, v):
        iDec = [1]
        for b in iBin:
            iDec = [self.AND(self.NOT(b), i) for i in iDec] + [self.AND(b, i) for i in iDec]
        for I, b in enumerate(iDec):
            List[I] = self.IF(b, v, List[I])
        return List
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
    def ASSERT_GE(self, x, y, dLen): # assert 0 <= x - y < 2 ** dLen
        return self.BINARY(self.SUB(x, y), dLen)
    def ASSERT_LE(self, x, y, dLen): # assert 0 <= y - x < 2 ** dLen
        return self.BINARY(self.SUB(y, x), dLen)
    def ASSERT_GT(self, x, y, dLen): # assert 0 < x - y <= 2 ** dLen
        return self.BINARY(self.SUB(self.SUB(x, y), 1), dLen)
    def ASSERT_LT(self, x, y, dLen): # assert 0 < y - x <= 2 ** dLen
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
if __name__ == '__main__':
    with Timer('Compiling program...'):
        # example: RC4 key scheduling algorithm
        pro = Program()
        SBox = list(range(256))
        jBin = pro.BINARY(0, 8)
        for i in range(1):
            iBin = pro.BINARY(i, 8)
            u = pro.GETLI(SBox, iBin)
            k = pro.VAR('k[0x{:02x}]'.format(i))
            tBin = pro.BINARY(u, 8)
            kBin = pro.BINARY(k, 8)
            jBin = pro.BINADD(jBin, kBin, 0, 8)[0]
            jBin = pro.BINADD(jBin, tBin, 0, 8)[0]
            v = pro.GETLI(SBox, jBin)
            pro.SETLI(SBox, iBin, v)
            pro.SETLI(SBox, jBin, u)
        eBin = pro.BINARY(1, 8)
        xBin = pro.BINARY(0, 8)
        yBin = pro.BINARY(0, 8)
        for i in range(1):
            xBin = pro.BINADD(xBin, eBin, 0, 8)[0]
            a = pro.GETLI(SBox, xBin)
            aBin = pro.BINARY(a, 8)
            yBin = pro.BINADD(yBin, aBin, 0, 8)[0]
            b = pro.GETLI(SBox, yBin)
            bBin = pro.BINARY(b, 8)
            pro.SETLI(SBox, xBin, b)
            pro.SETLI(SBox, yBin, a)
            sBin = pro.BINADD(aBin, bBin, 0, 8)[0]
            o = pro.GETLI(SBox, sBin)
            pro.RET('r[0x{:02x}]'.format(i), o)
    print('Number of constraints:', pro.con_count())
    print('Number of dimensions:', pro.dim_count())
    with Timer('Setting up QAP...'):
        x = random.randrange(1, P)
        α = random.randrange(1, P)
        β = random.randrange(1, P)
        γ = random.randrange(1, P)
        δ = random.randrange(1, P)
        αG, βG, δG, βH, γH, δH, uGU, vGV, xGI, xHI, yGI = pro.setup(α, β, γ, δ, x)
    with Timer('Generating witness...'):
        args = {'k[0x{:02x}]'.format(i): i for i in range(256)}
        r = random.randrange(1, P)
        s = random.randrange(1, P)
        AG, BH, CG, uU = pro.prove(args, r, s, αG, βG, δG, βH, δH, vGV, xGI, xHI, yGI)
    with Timer('Verifying...'):
        passed = pro.verify(αG, βH, γH, δH, uGU, AG, BH, CG, uU)
    if passed:
        print('Verification passed!')
    else:
        print('Verification failed!')
