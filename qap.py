#!/usr/bin/python3
import time
import util
import random
from py_ecc.optimized_bn128 import G1, G2, curve_order, multiply, add, neg, pairing
P = curve_order
K = 1 # maxium exponent of 2 that divides P - 1 (the number of constraints should not exceed K, otherwise FFT cannot be applied)
while (P - 1) % (K * 2) == 0:
    K = K * 2
for Z in range(2, P):
    if pow(Z, (P - 1) // 2, P) != 1:
        break
R = pow(Z, (P - 1) // K, P) # primitive K-th root of unity
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
        S = pow(R, K // I, P) # primitive I-th root of unity
        xI = [pow(x, i, P) for i in range(I)]
        XI = util.ifft(xI, S, P)
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
        Zx = pow(x, I, P) - 1
        Γ = util.modinv(γ, P)
        Δ = util.modinv(δ, P)
        α1 = multiply(G1, α)
        β1 = multiply(G1, β)
        δ1 = multiply(G1, δ)
        β2 = multiply(G2, β)
        γ2 = multiply(G2, γ)
        δ2 = multiply(G2, δ)
        u1U = [multiply(G1, (β * Ax + α * Bx + Cx) * Γ) for m, (Ax, Bx, Cx) in enumerate(zip(AxM, BxM, CxM)) if m     in pro.pubs]
        v1V = [multiply(G1, (β * Ax + α * Bx + Cx) * Δ) for m, (Ax, Bx, Cx) in enumerate(zip(AxM, BxM, CxM)) if m not in pro.pubs]
        x1I = [multiply(G1, pow(x, i, P)) for i in range(I)]
        x2I = [multiply(G2, pow(x, i, P)) for i in range(I)]
        y1I = [multiply(G1, pow(x, i, P) * Δ * Zx) for i in range(I - 1)]
        return α1, β1, δ1, β2, γ2, δ2, u1U, v1V, x1I, x2I, y1I
    def prove(self, α1, β1, δ1, β2, δ2, v1V, x1I, x2I, y1I, args, r, s):
        N = self.con_count()
        I = 1
        while I < N:
            I = I * 2
        J = I * 2
        S = pow(R, K // I, P) # primitive I-th root of unity
        T = pow(R, K // J, P) # primitive J-th root of unity
        wM = []
        getw = lambda xM: sum(wM[m] * x for m, x in xM.items()) % P
        for func in self.dims:
            wM.append(func(getw, args))
        uU = [w for m, w in enumerate(wM) if m     in pro.pubs]
        vV = [w for m, w in enumerate(wM) if m not in pro.pubs]
        awN = []
        bwN = []
        cwN = []
        for aM, bM, cM in self.cons:
            awN.append(getw(aM))
            bwN.append(getw(bM))
            cwN.append(getw(cM))
        AwI = util.ifft(awN + [0] * (I - N), S, P)
        BwI = util.ifft(bwN + [0] * (I - N), S, P)
        CwI = util.ifft(cwN + [0] * (I - N), S, P)
        awI = util.fft([Aw * pow(T, i, P) for i, Aw in enumerate(AwI)], S, P)
        bwI = util.fft([Bw * pow(T, i, P) for i, Bw in enumerate(BwI)], S, P)
        cwI = util.fft([Cw * pow(T, i, P) for i, Cw in enumerate(CwI)], S, P)
        hI = [(P - 1) // 2 * (aw * bw - cw) % P for aw, bw, cw in zip(awI, bwI, cwI)]
        HI = [H * pow(T, 0 - i, P) for i, H in enumerate(util.ifft(hI, S, P))]
        A1 = add(α1, multiply(δ1, r))
        for Aw, x1 in zip(AwI, x1I):
            A1 = add(A1, multiply(x1, Aw))
        B1 = add(β1, multiply(δ1, s))
        for Bw, x1 in zip(BwI, x1I):
            B1 = add(B1, multiply(x1, Bw))
        B2 = add(β2, multiply(δ2, s))
        for Bw, x2 in zip(BwI, x2I):
            B2 = add(B2, multiply(x2, Bw))
        C1 = add(add(multiply(A1, s), multiply(B1, r)), neg(multiply(δ1, r * s)))
        for H, y1 in zip(HI, y1I):
            C1 = add(C1, multiply(y1, H))
        for v, v1 in zip(vV, v1V):
            C1 = add(C1, multiply(v1, v))
        return A1, B2, C1, uU
    @staticmethod
    def verify(α1, β2, γ2, δ2, u1U, A1, B2, C1, uU):
        D1 = multiply(G1, 0)
        for u, u1 in zip(uU, u1U):
            D1 = add(D1, multiply(u1, u))
        return pairing(B2, A1) == pairing(β2, α1) * pairing(γ2, D1) * pairing(δ2, C1)
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
        return {k: v for k in x.keys() | y.keys() if (v := (x.get(k, 0) + y.get(k, 0)) % P)} or 0
    def SUB(self, x, y):
        if isinstance(x, int) and isinstance(y, int):
            return (x - y) % P
        if isinstance(y, int):
            y = {0: y}
        if isinstance(x, int):
            x = {0: x}
        return {k: v for k in x.keys() | y.keys() if (v := (x.get(k, 0) - y.get(k, 0)) % P)} or 0
    def MUL(self, x, y):
        if x == 0 or y == 0:
            return 0
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
        if x == 0:
            return 0
        if y == 0:
            raise ZeroDivisionError
        if isinstance(x, int) and isinstance(y, int):
            return x * util.modinv(y, P) % P
        if isinstance(y, int):
            return {i: m * util.modinv(y, P) % P for i, m in x.items()}
        if isinstance(x, int):
            x = {0: x}
        z = self.__bind(lambda getw, args: getw(x) * util.modinv(getw(y), P) % P)
        self.ASSERT(z, y, x)
        return z
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
        if x == 0:
            return [0] * qLen, [0] * rLen
        if y == 0:
            raise ZeroDivisionError
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
    def SUM(self, List):
        r = 0
        for i in List:
            r = self.ADD(r, i)
        return r
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
        SBox = list(range(256))                    # S := [0, 1, 2, ..., 255]
        jBin = pro.BINARY(0, 8)                    # j := 0
        for i in range(256):                       # for each i in 0..255 do
            iBin = pro.BINARY(i, 8)                #
            k = pro.VAR('K[0x{:02x}]'.format(i))   #     k := K[i]
            kBin = pro.BINARY(k, 8)                #
            jBin = pro.BINADD(jBin, kBin, 0, 8)[0] #     j := j + k & 0xff
            u = pro.GETLI(SBox, iBin)              #     u := S[i]
            uBin = pro.BINARY(u, 8)                #
            jBin = pro.BINADD(jBin, uBin, 0, 8)[0] #     j := j + u & 0xff
            v = pro.GETLI(SBox, jBin)              #     v := S[j]
            pro.SETLI(SBox, iBin, v)               #     S[i] := v
            pro.SETLI(SBox, jBin, u)               #     S[j] := u
        eBin = pro.BINARY(1, 8)                    # e := 1
        xBin = pro.BINARY(0, 8)                    # x := 0
        yBin = pro.BINARY(0, 8)                    # y := 0
        for i in range(256):                       # for each i in 0..255 do
            xBin = pro.BINADD(xBin, eBin, 0, 8)[0] #     x := x + 1 & 0xff
            a = pro.GETLI(SBox, xBin)              #     a := S[x]
            aBin = pro.BINARY(a, 8)                #
            yBin = pro.BINADD(yBin, aBin, 0, 8)[0] #     y := y + a & 0xff
            b = pro.GETLI(SBox, yBin)              #     b := S[y]
            bBin = pro.BINARY(b, 8)                #
            pro.SETLI(SBox, xBin, b)               #     S[x] := b
            pro.SETLI(SBox, yBin, a)               #     S[y] := a
            sBin = pro.BINADD(aBin, bBin, 0, 8)[0] #     s := a + b & 0xff
            o = pro.GETLI(SBox, sBin)              #     o := S[s]
            pro.RET('R[0x{:02x}]'.format(i), o)    #     R[i] := o
    print('Number of constraints:', pro.con_count())
    print('Number of dimensions:', pro.dim_count())
    with Timer('Setting up QAP...'):
        x = random.randrange(1, P)
        α = random.randrange(1, P)
        β = random.randrange(1, P)
        γ = random.randrange(1, P)
        δ = random.randrange(1, P)
        α1, β1, δ1, β2, γ2, δ2, u1U, v1V, x1I, x2I, y1I = pro.setup(α, β, γ, δ, x)
    with Timer('Generating witness...'):
        args = {'K[0x{:02x}]'.format(i): i for i in range(256)}
        r = random.randrange(1, P)
        s = random.randrange(1, P)
        A1, B2, C1, uU = pro.prove(α1, β1, δ1, β2, δ2, v1V, x1I, x2I, y1I, args, r, s)
    with Timer('Verifying...'):
        passed = pro.verify(α1, β2, γ2, δ2, u1U, A1, B2, C1, uU)
    if passed:
        print('Verification passed!')
        print('Public witness:', '{{{}}}'.format(', '.join('{} = {}'.format(k, u) for (_, k), u in zip(sorted(pro.pubs.items()), uU))))
    else:
        print('Verification failed!')
